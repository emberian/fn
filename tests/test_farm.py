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
    """Records every command and answers the ones the tool reads.

    `codes` maps a substring of the command to the exit code the box would
    give it, which is how a failing `cd`, a failing mirror and a runner that
    never started are told apart here.
    """

    def __init__(self, statuses: list[str], log: str = "",
                 home: str = "/home/ember", codes: dict[str, int] | None = None,
                 certs: str = "") -> None:
        self.commands: list[list[str]] = []
        self.statuses = list(statuses)
        self.log = log
        self.home = home
        self.codes = dict(codes or {})
        # What `tools/certs.py` on the box prints: submit reads its counts.
        self.certs = certs

    def code_for(self, command) -> int:
        joined = " ".join(command)
        for needle, code in self.codes.items():
            if needle in joined:
                return code
        return 0

    def __call__(self, command, **kwargs):
        self.commands.append(list(command))
        output = ""
        if command[0] == "ssh":
            script = command[-1]
            if script == "echo $HOME":
                output = f"{self.home}\n"
            elif "STATUS" in script:
                state = self.statuses.pop(0) if self.statuses else "0"
                output = f"STATUS {state}\nMARKERS 7\nTAIL working\n"
            elif "tools/certs.py" in script:
                output = self.certs
            elif script.startswith("cat "):
                output = self.log
        code = self.code_for(command)
        if code and kwargs.get("check"):
            raise subprocess.CalledProcessError(code, command, output=output)
        return subprocess.CompletedProcess(command, code, stdout=output, stderr="")

    def scripts(self) -> list[str]:
        return [command[-1] for command in self.commands if command[0] == "ssh"]

    def runner_script(self) -> str:
        started = [s for s in self.scripts() if "certify_books.py" in s]
        assert len(started) == 1, started
        return started[0]

    def rsyncs(self) -> list[list[str]]:
        return [command for command in self.commands if command[0] == "rsync"]


@contextlib.contextmanager
def driving(fake, cache: Path):
    with mock.patch.object(farm, "RUN", fake), \
            mock.patch.object(farm, "SLEEP", lambda seconds: None), \
            mock.patch.dict(os.environ, {"FN_CERT_CACHE": str(cache)}), \
            contextlib.redirect_stderr(io.StringIO()), \
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
            script = fake.runner_script()
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
            script = fake.runner_script()
            self.assertIn("swarm-build python3 tools/certify_books.py", script)
            self.assertIn("--affected-by books/wire.lisp", script)
            self.assertIn("FN_ACL2=/tank/fn/acl2-8.7/saved_acl2", script)
            self.assertIn("FN_CERT_CACHE=/tank/fn/certcache", script)


class RemoteRootTests(unittest.TestCase):
    """A `~` that reaches the remote `cd` makes the whole run a no-op."""

    def test_remote_quote_leaves_the_tilde_for_the_shell_to_expand(self):
        self.assertEqual(farm.remote_quote("~/fn-lanes/w5"), '"$HOME"/fn-lanes/w5')
        self.assertEqual(farm.remote_quote("~"), '"$HOME"')
        self.assertEqual(farm.remote_quote("/tank/fn/tree"), "/tank/fn/tree")
        # The defect: shlex.quote makes it literal, so `cd` lands nowhere and
        # the run produces no log at all.
        self.assertNotEqual(farm.remote_quote("~/fn-lanes/w5"), "'~/fn-lanes/w5'")

    def test_a_tilde_remote_root_is_resolved_once_and_recorded_absolute(self):
        fake = Fake([], home="/home/ember")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("persvati", root, [], jobs=4,
                                         timeout_seconds=60, affected_by=[],
                                         remote=Path("~/fn-lanes/w5"))
            self.assertEqual([s for s in fake.scripts() if s == "echo $HOME"],
                             ["echo $HOME"])  # one ssh, not one per script
            self.assertEqual(fake.rsyncs()[0][-1],
                             "persvati:/home/ember/fn-lanes/w5/")
            script = fake.runner_script()
            self.assertIn("cd /home/ember/fn-lanes/w5 ||", script)
            self.assertNotIn("~/fn-lanes", script)
            record = json.loads(farm.record_path(root, identifier).read_text())
            # The origin the pairs are published under must be the absolute
            # path the certificates name their sub-books by.
            self.assertEqual(record["remote_path"], "/home/ember/fn-lanes/w5")

    def test_the_remote_path_is_made_before_the_mirror_runs(self):
        fake = Fake([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                farm.submit("hbox", root, [], jobs=2, timeout_seconds=60,
                            affected_by=[], remote=Path("/tank/fn/tree"))
            # rsync creates the last component only; a missing parent is
            # exit 11 and nothing else.
            self.assertEqual(fake.commands[0][-1], "mkdir -p /tank/fn/tree")
            self.assertEqual(fake.commands[1][0], "rsync")


class FailureTests(unittest.TestCase):
    """submit reports what did not happen; it never prints a run id for it."""

    def test_a_runner_that_did_not_start_fails_the_submit(self):
        fake = Fake([], codes={"certify_books.py": 9})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                with self.assertRaises(farm.FarmError) as refused:
                    farm.submit("persvati", root, [], jobs=2,
                                timeout_seconds=60, affected_by=[])
            self.assertIn("did not start", str(refused.exception))
            self.assertEqual(sorted((root / "build" / "farm").glob("*.json")), [])

    def test_a_failing_mirror_is_reported_rather_than_swallowed(self):
        fake = Fake([], codes={"rsync": 11})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                with self.assertRaises(farm.FarmError) as refused:
                    farm.submit("hbox", root, [], jobs=2, timeout_seconds=60,
                                affected_by=[], remote=Path("/tank/fn/tree"))
            self.assertIn("11", str(refused.exception))
            self.assertNotIn("certify_books.py", " ".join(fake.scripts()))

    def test_main_exits_non_zero_and_says_so(self):
        fake = Fake([], codes={"certify_books.py": 9})
        errors = io.StringIO()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"), contextlib.redirect_stderr(errors):
                code = farm.main(["submit", "persvati", "--root", str(root),
                                  "--remote-root", "~/fn-lanes/w5"])
            self.assertEqual(code, 2)
            self.assertIn("did not start", errors.getvalue())

    def test_every_step_of_the_submit_script_has_its_own_exit(self):
        script = farm.remote_script("persvati", Path("/tank/fn/tree"), "run-1",
                                    [], 4, 60, [])
        # `cd X && ... &` backgrounds the whole list, so ssh exited 0 whatever
        # happened; each guard now exits on its own.
        self.assertNotIn("&& mkdir -p build/farm &&", script)
        self.assertIn("cd /tank/fn/tree || ", script)
        self.assertIn("exit 9", script)
        self.assertIn("test -f tools/certify_books.py", script)
        self.assertIn("exit 10", script)
        self.assertIn("kill -0 $pid", script)
        self.assertIn("exit 12", script)


class ClosureTests(unittest.TestCase):
    def test_closure_reaches_the_runner_and_the_record(self):
        fake = Fake([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                code = farm.main(["submit", "hbox", "--root", str(root),
                                  "--closure", "--affected-by",
                                  "books/article.lisp"])
            self.assertEqual(code, 0)
            self.assertIn("--affected-by books/article.lisp --closure",
                          fake.runner_script())
            record = json.loads(next((root / "build" / "farm").glob("*.json"))
                                .read_text())
            self.assertTrue(record["closure"])


INSTALLED = ("install: 220 books, cache /home/ember/fn-certcache\n"
             "  installed 31, kept identical local 2, no cached pair 4, "
             "foreign-local 0, removed foreign 0\n")


class CacheTests(unittest.TestCase):
    """The box's cache is what a run should start from, and add to.

    Measured 2026-09-20: a lane's `--closure` submit onto an empty remote root
    certified the whole substrate for four new books, 30 minutes, because
    nothing on the box offered its certificates to a lane.
    """

    def test_submit_installs_the_boxs_cache_before_the_runner_starts(self):
        fake = Fake([], certs=INSTALLED)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("persvati", root, [], jobs=4,
                                         timeout_seconds=60, affected_by=[],
                                         remote=Path("/home/ember/fn-lanes/w5"))
            scripts = fake.scripts()
            install = next(i for i, s in enumerate(scripts) if "tools/certs.py" in s)
            runner = next(i for i, s in enumerate(scripts) if "certify_books.py" in s)
            self.assertLess(install, runner)  # certify only what is not cached
            self.assertIn('--cache "$HOME"/fn-certcache install', scripts[install])
            self.assertIn("cd /home/ember/fn-lanes/w5 ||", scripts[install])
            # The mirror overwrites the tree, so the install follows it.
            self.assertEqual(fake.commands[fake.commands.index(
                next(c for c in fake.commands if c[0] == "rsync")) + 1][0], "ssh")
            record = json.loads(farm.record_path(root, identifier).read_text())
            self.assertEqual(record["cache_install"],
                             {"installed": 31, "kept": 2, "uncached": 4,
                              "foreign_local": 0})

    def test_an_install_that_did_not_run_is_recorded_not_raised(self):
        fake = Fake([], certs="Traceback: no such cache\n",
                    codes={"tools/certs.py": 1})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("hbox", root, [], jobs=4,
                                         timeout_seconds=60, affected_by=[],
                                         remote=Path("/tank/fn/tree"))
            self.assertIn("certify_books.py", " ".join(fake.scripts()))
            record = json.loads(farm.record_path(root, identifier).read_text())
            self.assertIn("no such cache", record["cache_install"]["error"])

    def test_the_runner_publishes_its_pairs_as_a_snapshot_of_this_run(self):
        # A finished run root is not a live worktree, and the pairs say so, so
        # the next lane on the box installs them instead of certifying again.
        script = farm.remote_script("persvati", Path("/home/ember/fn-lanes/w5"),
                                    "run-1", [], 4, 60, [])
        self.assertIn("FN_CERT_CACHE=~/fn-certcache", script)
        self.assertIn("FN_CERT_ORIGIN_KIND=run", script)

    def test_wait_publishes_the_new_pairs_into_the_boxs_cache_too(self):
        fake = Fake(["0"], log=WaitTests.LOG, certs="publish: 3 books\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "books").mkdir()
            with driving(fake, root / "cache"):
                identifier = farm.submit("hbox", root, [], jobs=2,
                                         timeout_seconds=60, affected_by=[],
                                         remote=Path("/tank/fn/tree"))
                farm.wait("hbox", identifier, root, poll=1, timeout_seconds=60)
            published = [s for s in fake.scripts()
                         if "--origin-kind run publish" in s]
            self.assertEqual(len(published), 1)
            self.assertIn("--cache /tank/fn/certcache", published[0])
            self.assertIn("cd /tank/fn/tree ||", published[0])
            # After the runner: the pairs it made are what is published.
            self.assertGreater(fake.scripts().index(published[0]),
                               next(i for i, s in enumerate(fake.scripts())
                                    if "certify_books.py" in s))


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
