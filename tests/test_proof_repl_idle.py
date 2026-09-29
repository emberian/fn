"""tools/proof_repl.py: the idle timeout, its note, and `reap --idle` (post-alloc-3).

hbox's 22-slot ACL2 pool was held mostly by other lanes' idle sessions under
the old two-hour default.  A session now stops itself after 20 minutes with
no form sent, frees its slot, and leaves a note the next `send` reads; `reap
--idle MIN` stops idle sessions across every session tree on a machine.
The end-to-end cases run against the fake ACL2 of tests/test_proof_repl.py
with a private slot pool and a timeout of seconds (`--idle-seconds`).
"""
from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import pathlib
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import acl2_slots  # noqa: E402
import proof_repl  # noqa: E402
from tests.test_proof_repl import FAKE_ACL2  # noqa: E402


class DefaultTests(unittest.TestCase):
    def test_the_default_is_twenty_minutes_and_the_environment_changes_it(self):
        self.assertEqual(proof_repl.default_idle_seconds({}), 1200)
        self.assertEqual(proof_repl.default_idle_seconds({"FN_REPL_IDLE_MIN": "90"}), 5400)
        self.assertEqual(proof_repl.default_idle_seconds({"FN_REPL_IDLE_MIN": "0"}), 0)
        with self.assertRaises(SystemExit):
            proof_repl.default_idle_seconds({"FN_REPL_IDLE_MIN": "soon"})

    def test_idle_timeout_minutes_win_over_seconds_and_the_default(self):
        both = argparse.Namespace(idle_timeout=2.0, idle_seconds=5.0)
        self.assertEqual(proof_repl.idle_from_args(both), 120)
        self.assertEqual(proof_repl.idle_from_args(argparse.Namespace(idle_timeout=None,
                                                                      idle_seconds=5.0)), 5)
        self.assertEqual(proof_repl.idle_from_args(argparse.Namespace(idle_timeout=0.0)), 0)
        with mock.patch.dict(os.environ, {"FN_REPL_IDLE_MIN": "7"}):
            self.assertEqual(proof_repl.idle_from_args(argparse.Namespace()), 420)

    def test_reap_idle_chooses_only_live_sessions_past_the_threshold(self):
        live = {"state": {}, "server": True, "socket": True, "idle": 3700, "deadline": 0}
        fresh = dict(live, idle=60)
        self.assertIn("idle 1h01m", proof_repl.reap_reason(live, None, 3600))
        self.assertIsNone(proof_repl.reap_reason(fresh, None, 3600))
        # Never stopping (deadline 0) is honoured unless an idle threshold is given.
        self.assertIsNone(proof_repl.reap_reason(live, None, None))


class GcTests(unittest.TestCase):
    """Q7g: `gc` stops every session idle 30 min or more, on this machine or each box."""

    def test_gc_reaps_idle_thirty_minutes_in_every_tree(self):
        seen = []
        with mock.patch.object(proof_repl, "reap", lambda a: seen.append(a) or 0):
            self.assertEqual(proof_repl.main(["gc", "--dry-run"]), 0)
        (a,) = seen
        self.assertEqual((a.idle, a.all, a.dry_run, a.lane), (30.0, True, True, None))
        self.assertIsNone(proof_repl.reap_reason(
            {"state": {}, "server": True, "socket": True, "idle": 29 * 60, "deadline": 0}, None, a.idle * 60))
        self.assertIsNotNone(proof_repl.reap_reason(
            {"state": {}, "server": True, "socket": True, "idle": 31 * 60, "deadline": 0}, None, a.idle * 60))

    def test_gc_each_box_runs_it_on_every_box_and_survives_one_unreachable(self):
        calls = []
        real_main = proof_repl.main

        def fake_main(argv=None):
            if argv and argv[0] == "gc" and "--host" in argv:
                calls.append(argv)
                if argv[argv.index("--host") + 1] == "hbox":
                    raise SystemExit("ssh: connect to host hbox: refused")
                return 0
            return real_main(argv)
        with mock.patch.object(proof_repl, "main", fake_main), \
                contextlib.redirect_stdout(io.StringIO()):
            rc = proof_repl.gc(argparse.Namespace(each_box=True, idle=45.0, dry_run=False, root=None))
        self.assertEqual(rc, 1)
        self.assertEqual(sorted(argv[argv.index("--host") + 1] for argv in calls), sorted(proof_repl.REMOTE_TREES))
        self.assertTrue(all(argv[:3] == ["gc", "--idle", "45"] for argv in calls))


class DiffAndKeepGoingTests(unittest.TestCase):
    """Q7g: `diff NAME BOOK` (owner-relation's false green) and `send --keep-going`."""
    BOOK = """(in-package "ACL2")
(include-book "std/lists/rev" :dir :system)
(defun f (x) x)
(local (defthm f-id (equal (f x) x)))
(defthmd f-id-2 (equal (f x) x) :rule-classes nil)
(define-ish g (x) x)
"""

    def test_items_unwrap_local_and_compare_defthmd_as_defthm(self):
        items = dict(proof_repl.diff_items(self.BOOK))
        self.assertEqual(sorted(items), ["f", "f-id", "f-id-2", "g"])
        self.assertTrue(items["f-id"].startswith("(defthm f-id"))
        self.assertTrue(items["f-id-2"].startswith("(defthm f-id-2"))
        form = proof_repl.diff_form(list(items.items()))
        self.assertIn("(get-event 'f-id-2 (w state))", form)
        self.assertEqual(form.count("(cons '"), 4)

    def test_diff_reports_a_differing_event_and_fails(self):
        with tempfile.TemporaryDirectory() as d:
            book = pathlib.Path(d) / "b.lisp"
            book.write_text(self.BOOK)
            answer = {"output": "((F . :SAME) (F-ID . :DIFFERS) (F-ID-2 . :SAME) (G . :MACRO))\n"}
            out = io.StringIO()
            with mock.patch.object(proof_repl, "ask", lambda *a, **k: answer), contextlib.redirect_stdout(out):
                rc = proof_repl.main(["diff", "s", str(book), "--host", "laptop"])
            self.assertEqual(rc, 1)
            self.assertIn("DIFFERS    f-id", out.getvalue())
            self.assertIn("1 differs, 1 macro, 2 same of 4", out.getvalue())
            answer["output"] = "((F . :SAME) (F-ID . :SAME) (F-ID-2 . :SAME) (G . :MACRO))"
            with mock.patch.object(proof_repl, "ask", lambda *a, **k: answer), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(proof_repl.main(["diff", "s", str(book), "--host", "laptop"]), 0)

    def test_send_keep_going_sends_past_a_refusal(self):
        sent = []

        def fake_ask(name, request, **kw):
            sent.append(request["form"])
            return {"output": "", "error": len(sent) == 1}
        with mock.patch.object(proof_repl, "ask", fake_ask), contextlib.redirect_stdout(io.StringIO()):
            rc = proof_repl.main(["send", "s", "(defthm a t) (defthm b t)", "--keep-going", "--host", "laptop"])
        self.assertEqual((rc, len(sent)), (1, 2))
        sent.clear()
        with mock.patch.object(proof_repl, "ask", fake_ask), contextlib.redirect_stdout(io.StringIO()):
            proof_repl.main(["send", "s", "(defthm a t) (defthm b t)", "--host", "laptop"])
        self.assertEqual(len(sent), 1)


class DiscoveryTests(unittest.TestCase):
    def test_box_trees_finds_every_tree_with_sessions_under_the_bases(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            for tree in ("a-repl", "b-r1"):
                (base / tree / "build" / "proof-repl" / "s").mkdir(parents=True)
            (base / "no-sessions").mkdir()
            with mock.patch.object(proof_repl, "BOX_TREE_BASES", (str(base),)):
                trees = proof_repl.box_trees()
            self.assertIn(str(base / "a-repl"), trees)
            self.assertIn(str(base / "b-r1"), trees)
            self.assertNotIn(str(base / "no-sessions"), trees)

    def test_running_servers_name_their_trees_through_proc(self):
        with tempfile.TemporaryDirectory() as temporary:
            proc = pathlib.Path(temporary)
            deep = proc / "deep" / "tree"
            deep.mkdir(parents=True)
            for pid, words, cwd in (("41", [b"python3", b"/x/tools/proof_repl.py", b"serve",
                                            b"s", b"books/y"], deep),
                                    ("42", [b"python3", b"other.py", b"serve"], proc),
                                    ("self", [b"python3"], proc)):
                (proc / pid).mkdir()
                (proc / pid / "cmdline").write_bytes(b"\0".join(words) + b"\0")
                os.symlink(cwd, proc / pid / "cwd")
            self.assertEqual(proof_repl.live_server_trees(proc), [deep])
            self.assertEqual(proof_repl.live_server_trees(proc / "absent"), [])

    def test_a_lane_given_as_a_path_is_its_name(self):
        with mock.patch.dict(os.environ, {"FN_LANE": "/Users/e/dev/fn/build/lanes/batch-aw"}):
            self.assertEqual(proof_repl.default_lane(), "batch-aw")

    def test_a_server_pid_of_another_tree_is_not_this_sessions(self):
        words = f"{sys.executable} /t/tools/proof_repl.py serve s books/x"
        with mock.patch.object(proof_repl, "_command_of", return_value=words):
            with mock.patch.object(proof_repl, "_process_cwd",
                                   return_value=pathlib.Path("/elsewhere")):
                self.assertFalse(proof_repl._is_server(1234, "s", pathlib.Path("/t")))
                self.assertTrue(proof_repl._is_server(1234, "s"))
            with mock.patch.object(proof_repl, "_process_cwd", return_value=None):
                self.assertTrue(proof_repl._is_server(1234, "s", pathlib.Path("/t")))
            self.assertFalse(proof_repl._is_server(1234, "other", pathlib.Path("/t")))


class IdleSessionTests(unittest.TestCase):
    """End to end through the command line, against the fake ACL2."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        base = pathlib.Path(cls.tmp.name)
        fake = base / "fake-acl2"
        fake.write_text(FAKE_ACL2)
        fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
        cls.slots = base / "slots"
        cls.env = {**os.environ, "FN_ACL2": str(fake), "FN_ACL2_SLOT_DIR": str(cls.slots),
                   "FN_ACL2_SLOTS": "4"}
        cls.env.pop("FN_REPL_IDLE_MIN", None)
        cls.scratch = ROOT / "build" / ("proof-repl-idle-" + str(os.getpid()))
        cls.scratch.mkdir(parents=True, exist_ok=True)
        (cls.scratch / "tiny.lisp").write_text('(in-package "ACL2")\n(defun f (x) x)\n')
        cls.book = str((cls.scratch / "tiny").relative_to(ROOT))
        cls.names = []

    @classmethod
    def tearDownClass(cls):
        for name in cls.names:
            cls.cli("stop", name)
            shutil.rmtree(proof_repl.SESSIONS / name, ignore_errors=True)
        shutil.rmtree(cls.scratch, ignore_errors=True)
        cls.tmp.cleanup()

    @classmethod
    def cli(cls, *words, timeout=60):
        return subprocess.run([sys.executable, str(ROOT / "tools" / "proof_repl.py"), *words],
                              capture_output=True, text=True, env=cls.env, cwd=ROOT,
                              timeout=timeout)

    def start(self, suffix, *extra):
        name = f"idle-{suffix}-{os.getpid()}"
        self.names.append(name)
        answer = self.cli("start", name, self.book, "--load-timeout", "20", *extra)
        self.assertEqual(answer.returncode, 0, answer.stdout + answer.stderr)
        return name

    def held(self):
        return acl2_slots.holders(self.slots, 4)

    def wait_gone(self, name, seconds=20):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline and (proof_repl.SESSIONS / name / "sock").exists():
            time.sleep(0.2)
        return not (proof_repl.SESSIONS / name / "sock").exists()

    def test_an_idle_session_stops_frees_its_slot_and_the_next_send_says_why(self):
        name = self.start("self", "--idle-seconds", "2")
        self.assertEqual(len(self.held()), 1)
        live = self.cli("status", name)
        self.assertIn("last send", live.stdout)
        self.assertIn("idle deadline 0m02s", live.stdout)
        self.assertIn("stops in", live.stdout)
        self.assertTrue(self.wait_gone(name))
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline and self.held():
            time.sleep(0.1)
        self.assertEqual(self.held(), [])
        note = json.loads((proof_repl.SESSIONS / name / "stopped.json").read_text())
        self.assertEqual(note["reason"], "idle")
        self.assertGreaterEqual(note["idle"], 2)
        refused = self.cli("send", name, "(+ 1 2)")
        self.assertNotEqual(refused.returncode, 0)
        words = refused.stdout + refused.stderr
        self.assertIn(f"session {name} stopped after 0 min idle", words)
        self.assertIn("start it again", words)
        self.assertIn("stopped after", self.cli("status", name).stdout)
        # A fresh start clears the note.
        again = self.start("self", "--idle-seconds", "30")
        self.assertEqual(again, name)
        self.assertFalse((proof_repl.SESSIONS / name / "stopped.json").exists())
        self.assertEqual(self.cli("stop", name).returncode, 0)

    def test_idle_timeout_zero_never_stops_and_minutes_are_recorded(self):
        never = self.start("never", "--idle-timeout", "0")
        minutes = self.start("minutes", "--idle-timeout", "3")
        self.assertEqual(json.loads((proof_repl.SESSIONS / minutes / "state.json")
                                    .read_text())["idle_seconds"], 180)
        self.assertIn("none (never stops)", self.cli("status", never).stdout)
        time.sleep(1.5)
        self.assertTrue((proof_repl.SESSIONS / never / "sock").exists())
        for name in (never, minutes):
            self.assertEqual(self.cli("stop", name).returncode, 0)

    def test_a_touch_resets_the_clock_and_a_status_does_not(self):
        name = self.start("touch", "--idle-seconds", "3")
        for _ in range(4):
            time.sleep(1)
            proof_repl.ask(name, {"op": "touch"}, timeout=10)
        self.assertTrue((proof_repl.SESSIONS / name / "sock").exists())
        started = time.monotonic()
        while (proof_repl.SESSIONS / name / "sock").exists() and time.monotonic() - started < 15:
            self.cli("status", name)
            time.sleep(0.5)
        self.assertFalse((proof_repl.SESSIONS / name / "sock").exists())

    def test_reap_idle_lists_then_stops_only_sessions_past_the_threshold(self):
        old = self.start("reap-old", "--idle-timeout", "0")
        young = self.start("reap-young", "--idle-timeout", "0")
        time.sleep(2.5)
        self.assertEqual(self.cli("send", young, "(+ 1 2)").returncode, 0)
        threshold = str(2.0 / 60)  # two seconds, in minutes
        dry = self.cli("reap", "--idle", threshold, "--root", str(ROOT), "--dry-run")
        self.assertIn(f"would reap {old}", dry.stdout)
        self.assertNotIn(young, dry.stdout)
        self.assertTrue((proof_repl.SESSIONS / old / "sock").exists())
        reaped = self.cli("reap", "--idle", threshold, "--root", str(ROOT))
        self.assertIn(f"reaped {old}", reaped.stdout)
        self.assertIn("stopped through its socket", reaped.stdout)
        self.assertNotIn(young, reaped.stdout)
        self.assertTrue(self.wait_gone(old, 5))
        note = json.loads((proof_repl.SESSIONS / old / "stopped.json").read_text())
        self.assertEqual((note["reason"], note["by"]), ("idle", "proof_repl.py reap"))
        self.assertTrue((proof_repl.SESSIONS / young / "sock").exists())
        self.assertEqual(self.cli("stop", young).returncode, 0)


if __name__ == "__main__":
    unittest.main()
