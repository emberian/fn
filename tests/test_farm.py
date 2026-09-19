"""Unit checks for the farm submitter: what it asks the box to do.

No ssh runs here.  `tools/farm.py` keeps the two shell-touching calls behind
module-level seams, so these tests read the exact commands the tool would
issue: the mirror that excludes build/, the detached runner with its own log
and status file, the bounded wait that sleeps rather than spins, and the fetch
that brings back the evidence directory and the new certificate pairs.
"""

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
SPEC = importlib.util.spec_from_file_location("farm", TOOLS / "farm.py")
farm = importlib.util.module_from_spec(SPEC)
sys.modules["farm"] = farm
SPEC.loader.exec_module(farm)


class Fake:
    """Records every command and answers the ones `wait` reads."""

    def __init__(self, statuses: list[str], log: str = "") -> None:
        self.commands: list[list[str]] = []
        self.statuses = list(statuses)
        self.log = log

    def __call__(self, command, **kwargs):
        self.commands.append(list(command))
        output = ""
        if command[0] == "ssh":
            script = command[-1]
            if "STATUS" in script:
                state = self.statuses.pop(0) if self.statuses else "0"
                output = f"STATUS {state}\nMARKERS 7\nTAIL working\n"
            elif script.startswith("cat "):
                output = self.log
        return subprocess.CompletedProcess(command, 0, stdout=output, stderr="")

    def scripts(self) -> list[str]:
        return [command[-1] for command in self.commands if command[0] == "ssh"]

    def rsyncs(self) -> list[list[str]]:
        return [command for command in self.commands if command[0] == "rsync"]


@contextlib.contextmanager
def driving(fake, cache: Path):
    with mock.patch.object(farm, "RUN", fake), \
            mock.patch.object(farm, "SLEEP", lambda seconds: None), \
            mock.patch.dict(os.environ, {"FN_CERT_CACHE": str(cache)}), \
            contextlib.redirect_stdout(io.StringIO()):
        yield


class SubmitTests(unittest.TestCase):
    def test_submit_mirrors_the_worktree_and_starts_a_detached_runner(self):
        fake = Fake([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("persvati", root, ["books/alpha"],
                                         jobs=12, timeout_seconds=900,
                                         affected_by=[])
            mirror = fake.rsyncs()[0]
            self.assertIn("--delete", mirror)
            self.assertIn("--exclude=build/", mirror)
            self.assertEqual(mirror[-2:], [f"{root}/", f"persvati:{root}/"])
            script = fake.scripts()[0]
            self.assertIn(f"cd {root}", script)
            self.assertIn("nohup sh -c", script)
            self.assertIn("tools/certify_books.py", script)
            self.assertIn("--jobs 12", script)
            self.assertIn("books/alpha", script)
            self.assertIn("FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2", script)
            self.assertIn("FN_ACL2_TIMEOUT_SECONDS=900", script)
            self.assertIn(f"build/farm/{identifier}.log", script)
            self.assertIn(f"echo $? > build/farm/{identifier}.status", script)
            record = json.loads(farm.record_path(root, identifier).read_text())
            self.assertEqual((record["host"], record["jobs"], record["books"]),
                             ("persvati", 12, ["books/alpha"]))

    def test_hbox_runs_under_swarm_build_and_affected_by_is_passed_through(self):
        fake = Fake([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                farm.submit("hbox", root, [], jobs=8, timeout_seconds=1800,
                            affected_by=["books/wire.lisp"])
            script = fake.scripts()[0]
            self.assertIn("swarm-build python3 tools/certify_books.py", script)
            self.assertIn("--affected-by books/wire.lisp", script)
            self.assertIn("FN_ACL2=/tank/fn/acl2-8.7/saved_acl2", script)
            self.assertIn("FN_CERT_CACHE=/tank/fn/certcache", script)


class WaitTests(unittest.TestCase):
    LOG = ("ACL2 certification passed: books/alpha\n"
           "Certification evidence: build/acl2/certify-20260919T000000Z-11\n")

    def test_wait_polls_until_the_status_file_appears_then_fetches(self):
        fake = Fake(["running", "running", "0"], log=self.LOG)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "books").mkdir()
            with driving(fake, root / "cache"):
                code = farm.wait("hbox", "run-x", root, poll=30, timeout_seconds=600)
            self.assertEqual(code, 0)
            self.assertEqual(sum("STATUS" in s for s in fake.scripts()), 3)
            fetched = fake.rsyncs()
            self.assertTrue(any("build/acl2/certify-20260919T000000Z-11" in part
                                for command in fetched for part in command))
            cert_syncs = [c for c in fetched if "--include=*.cert" in c]
            self.assertEqual(len(cert_syncs), 2)  # books/ and tests/acl2/
            for command in cert_syncs:
                self.assertIn("--update", command)
                self.assertIn("--exclude=*", command)
            self.assertTrue((root / "build/farm/run-x.log").is_file())

    def test_wait_uses_the_remote_path_and_records_it_as_the_origin(self):
        # Certificates name their sub-books by absolute path, so what the run
        # used on the box is their origin -- and a path that does not exist
        # here is what makes them installable in any local worktree.
        fake = Fake(["0"], log=self.LOG)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "books").mkdir()
            with driving(fake, root / "cache"):
                identifier = farm.submit("hbox", root, [], jobs=2,
                                         timeout_seconds=60, affected_by=[],
                                         remote=Path("/tank/fn/tree"))
            self.assertEqual(fake.rsyncs()[0][-1], "hbox:/tank/fn/tree/")
            published: dict = {}

            def spy(*positional, **keyword):
                published.update(keyword)
                return farm.certs.Report("publish", "cache")

            with mock.patch.object(farm.certs, "publish", spy), \
                    driving(fake, root / "cache"):
                farm.wait("hbox", identifier, root, poll=1, timeout_seconds=60)
            self.assertEqual((published["origin"], published["origin_host"]),
                             ("/tank/fn/tree", "hbox"))
            self.assertTrue(any("hbox:/tank/fn/tree/books/" in part
                                for command in fake.rsyncs() for part in command))

    def test_wait_returns_the_remote_exit_code(self):
        fake = Fake(["1"], log=self.LOG)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                self.assertEqual(farm.wait("hbox", "run-y", root, poll=1,
                                           timeout_seconds=600), 1)

    def test_wait_is_bounded_and_sleeps_between_polls(self):
        slept: list[int] = []
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with mock.patch.object(farm, "RUN", Fake(["running"] * 3, log=self.LOG)), \
                    mock.patch.object(farm, "SLEEP", slept.append), \
                    contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(farm.wait("hbox", "run-z", root, poll=30,
                                           timeout_seconds=0), 3)
                self.assertEqual(slept, [])  # gave up before sleeping at all
            with mock.patch.object(farm, "RUN", Fake(["running", "0"], log=self.LOG)), \
                    mock.patch.object(farm, "SLEEP", slept.append), \
                    mock.patch.dict(os.environ, {"FN_CERT_CACHE": str(root / "cache")}), \
                    contextlib.redirect_stdout(io.StringIO()):
                farm.wait("hbox", "run-z", root, poll=30, timeout_seconds=600)
            self.assertEqual(slept, [30])  # one poll interval, not a busy loop

    def test_progress_parsing_ignores_unrelated_output(self):
        fields = farm.parse_progress(
            "Warning: something\nSTATUS running\nMARKERS 12\nTAIL a b c\n")
        self.assertEqual(fields["STATUS"], "running")
        self.assertEqual(fields["MARKERS"], "12")


class StatusTests(unittest.TestCase):
    def test_status_lists_runs_without_starting_anything(self):
        fake = Fake([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                self.assertEqual(farm.status("persvati", root), 0)
            script = fake.scripts()[0]
            self.assertIn("build/farm", script)
            self.assertNotIn("certify_books.py", script)
            self.assertEqual(fake.rsyncs(), [])


if __name__ == "__main__":
    unittest.main()
