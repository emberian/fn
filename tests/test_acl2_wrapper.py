"""Checks for `tools/acl2`: the `ld` path's entry to the ACL2 slot pool.

Every case drives the real wrapper against a fake ACL2 that records its
environment and can be made to sleep, the way `tests/test_certify_runner.py`
does.  The properties that matter are that an interactive run cannot exceed
the machine-wide pool, that it releases its slot however it ends, and that the
environment an `ld` session sees is the one certification will see.
"""

import contextlib
import functools
import importlib.machinery
import importlib.util
import io
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "tools" / "acl2"

# `tools/acl2` has no extension: it is a command, not a module other tools
# import, so the loader is named explicitly.  Executing it also puts `tools/`
# on `sys.path`, which is how `wrapper.acl2_slots` resolves below.
LOADER = importlib.machinery.SourceFileLoader("fn_acl2_wrapper", str(WRAPPER))
SPEC = importlib.util.spec_from_loader(LOADER.name, LOADER)
wrapper = importlib.util.module_from_spec(SPEC)
sys.modules[LOADER.name] = wrapper
LOADER.exec_module(wrapper)
slots = wrapper.acl2_slots


FAKE_ACL2 = r"""#!/bin/sh
# Stands in for the ACL2 executable.  It reports the environment it was given
# and then, on request, sleeps (a runaway proof) or copies its driver from
# stdin to stdout (an `ld` session echoing what it read).
{
  printf 'started\n'
  printf 'ACL2_CUSTOMIZATION=%s\n' "${ACL2_CUSTOMIZATION-unset}"
  printf 'ACL2_BOOK_HASH_ALISTP=%s\n' "${ACL2_BOOK_HASH_ALISTP-unset}"
  printf 'ACL2_SYSTEM_BOOKS=%s\n' "${ACL2_SYSTEM_BOOKS-unset}"
  printf 'args=%s\n' "$*"
} >> "$FAKE_EVENTS"
# `exec` so a terminate reaches the sleep itself rather than this shell.
[ -n "${FAKE_SLEEP:-}" ] && exec sleep "$FAKE_SLEEP"
[ -n "${FAKE_CAT:-}" ] && cat
exit "${FAKE_EXIT:-0}"
"""


@contextlib.contextmanager
def free_slot():
    """One slot if the pool has a free one, else raise ``TimeoutError``.

    The pool blocks rather than refusing, so a probe for "is anything free"
    is a short wait on a worker thread.
    """
    taken, release = threading.Event(), threading.Event()

    def hold() -> None:
        with slots.slot("probe", log=lambda _message: None, poll=0.01):
            taken.set()
            release.wait(10)

    worker = threading.Thread(target=hold, daemon=True)
    worker.start()
    if not taken.wait(0.5):
        release.set()
        raise TimeoutError("no free slot")
    try:
        yield
    finally:
        release.set()
        worker.join(10)


class Harness:
    """A fake ACL2 and a private slot pool, in a throwaway directory."""

    def __init__(self, directory: str, slot_count: int = 4) -> None:
        self.root = Path(directory).resolve()
        self.acl2 = self.root / "fake-acl2.sh"
        self.acl2.write_text(FAKE_ACL2)
        self.acl2.chmod(self.acl2.stat().st_mode | stat.S_IXUSR)
        self.events = self.root / "events.log"
        self.events.write_text("")
        self.slot_dir = self.root / "slots"
        self.slot_count = slot_count

    def environment(self, **extra: str) -> dict[str, str]:
        base = {
            "FN_ACL2": str(self.acl2),
            "FAKE_EVENTS": str(self.events),
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            # A private pool: a unit test must never contend with this
            # machine's real ACL2 runs, nor occupy a slot a lane waits on.
            "FN_ACL2_SLOTS": str(self.slot_count),
            "FN_ACL2_SLOT_DIR": str(self.slot_dir),
        }
        base.update(extra)
        return base

    def run(self, arguments: list[str], stdin: bytes = b"",
            **extra: str) -> subprocess.CompletedProcess[bytes]:
        return subprocess.run([sys.executable, str(WRAPPER), *arguments],
                              input=stdin, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, cwd=str(self.root),
                              env=self.environment(**extra), check=False)

    def recorded(self) -> list[str]:
        return self.events.read_text().splitlines()

    def free_slots(self) -> int:
        """How many of the pool's slots can be taken right now."""
        with mock.patch.dict(os.environ, self.environment(), clear=True), \
                contextlib.ExitStack() as stack:
            held = 0
            for _ in range(self.slot_count):
                try:
                    stack.enter_context(free_slot())
                except TimeoutError:
                    break
                held += 1
            return held


class PassThroughTests(unittest.TestCase):
    """An `ld` session sees its own stdio and the runner's environment."""

    def test_the_driver_on_stdin_reaches_acl2_and_its_output_comes_back(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory)
            result = harness.run([], stdin=b'(ld "driver.lsp")\n', FAKE_CAT="1")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, b'(ld "driver.lsp")\n')

    def test_the_child_gets_the_runners_environment(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory)
            result = harness.run([], ACL2_CUSTOMIZATION="/home/me/custom.lsp",
                                 ACL2_BOOK_HASH_ALISTP="T",
                                 ACL2_SYSTEM_BOOKS="/elsewhere/books")
            self.assertEqual(result.returncode, 0, result.stderr)
            recorded = harness.recorded()
            self.assertIn("ACL2_CUSTOMIZATION=NONE", recorded)
            self.assertIn("ACL2_BOOK_HASH_ALISTP=NIL", recorded)
            self.assertIn("ACL2_SYSTEM_BOOKS=unset", recorded)

    def test_acl2s_exit_code_is_the_wrappers_exit_code(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory)
            self.assertEqual(harness.run([], FAKE_EXIT="3").returncode, 3)

    def test_arguments_after_the_separator_reach_acl2(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory)
            harness.run(["--", "--eval", "(quit)"])
            self.assertIn("args=--eval (quit)", harness.recorded())

    def test_a_missing_acl2_is_refused_before_any_slot_is_taken(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory)
            result = harness.run([], FN_ACL2=str(harness.root / "absent"))
            self.assertEqual(result.returncode, 2)
            self.assertIn(b"no executable ACL2", result.stderr)
            self.assertFalse(harness.slot_dir.exists(),
                             "a refused run still touched the pool")


class TimeoutTests(unittest.TestCase):
    """The brief's three-minute rule, mechanical instead of remembered."""

    def test_a_runaway_is_killed_and_reported_as_124(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory)
            started = time.monotonic()
            result = harness.run(["--timeout", "0.5"], FAKE_SLEEP="60")
            elapsed = time.monotonic() - started
            self.assertEqual(result.returncode, 124, result.stderr)
            self.assertIn(b"exceeded --timeout", result.stderr)
            self.assertLess(elapsed, 20, "the child outlived its timeout")
            self.assertIn("started", harness.recorded())

    def test_a_timed_out_run_leaves_its_slot_free(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory, slot_count=1)
            self.assertEqual(harness.run(["--timeout", "0.5"],
                                         FAKE_SLEEP="60").returncode, 124)
            self.assertEqual(harness.free_slots(), 1,
                             "the killed run leaked the pool's only slot")

    def test_a_non_positive_timeout_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory)
            result = harness.run(["--timeout", "0"])
            self.assertEqual(result.returncode, 2)
            self.assertIn(b"--timeout must be positive", result.stderr)
            self.assertEqual(harness.recorded(), [])


class SlotTests(unittest.TestCase):
    """The measured defect: six ACL2 processes against a four-slot pool."""

    def test_an_occupied_pool_makes_the_wrapper_wait_and_say_so(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory, slot_count=1)
            outcome: list[int] = []
            stderr = io.StringIO()

            def wait_and_run() -> None:
                with contextlib.redirect_stderr(stderr):
                    outcome.append(wrapper.main([]))

            with mock.patch.dict(os.environ, harness.environment(), clear=True), \
                    mock.patch.object(wrapper.acl2_slots, "slot",
                                      functools.partial(slots.slot,
                                                        report_every=0.05)):
                holder = slots.slot("holder", log=lambda _message: None)
                holder.__enter__()
                worker = threading.Thread(target=wait_and_run, daemon=True)
                worker.start()
                # The pool is full, so no ACL2 may start however long we wait.
                time.sleep(0.4)
                self.assertEqual(harness.recorded(), [],
                                 "ACL2 started while the pool was full")
                holder.__exit__(None, None, None)
                worker.join(10)
            self.assertFalse(worker.is_alive(), "the wrapper never got a slot")
            self.assertEqual(outcome, [0])
            self.assertIn("started", harness.recorded())
            self.assertIn("waiting for one of 1 ACL2 slots", stderr.getvalue())

    def test_a_finished_run_leaves_the_pool_as_it_found_it(self):
        with tempfile.TemporaryDirectory() as directory:
            harness = Harness(directory, slot_count=2)
            self.assertEqual(harness.run([]).returncode, 0)
            self.assertEqual(harness.free_slots(), 2)


if __name__ == "__main__":
    unittest.main()
