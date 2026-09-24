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
import shlex
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


COHERENT = ("install-set: 3 books, cache /home/ember/fn-certcache\n"
            "  artifact-set set-a origin /home/ember/fn-lanes/w5 "
            "source source-a toolchain tool-a; installed 2, kept 1, "
            "missing 0, removed 0\n")


class Fake:
    """Records every command and answers the ones the tool reads.

    `codes` maps a substring of the command to the exit code the box would
    give it, which is how a failing `cd`, a failing mirror and a runner that
    never started are told apart here.
    """

    def __init__(self, statuses: list[str], log: str = "",
                 home: str = "/home/ember", codes: dict[str, int] | None = None,
                 certs: str | None = None) -> None:
        self.commands: list[list[str]] = []
        self.statuses = list(statuses)
        self.log = log
        self.home = home
        self.codes = dict(codes or {})
        # What `tools/certs.py` on the box prints: submit reads its counts.
        self.certs = COHERENT if certs is None else certs

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
        started = [s for s in self.scripts()
                   if "certify_books.py" in s and "nohup sh -c" in s]
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
            self.assertIn("FN_ACL2=/home/ember/fn-gates/toolchains/w25/acl2-literal",
                          script)
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
            self.assertIn("FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g", script)
            self.assertIn("FN_CERT_CACHE=/tank/fn/certcache", script)

    def test_default_toolchain_paths_reach_cache_preflight(self):
        self.assertIn(
            'acl2=/home/ember/fn-gates/toolchains/w25/acl2-literal;',
            farm.cache_preflight_script("persvati", Path("/home/ember/fn-lanes/x"),
                                        ["books/base"], [], False))
        self.assertIn(
            'acl2=/tank/fn/toolchains/w28/acl2-literal-4g;',
            farm.cache_preflight_script("hbox", Path("/tank/fn/lanes/x"),
                                        ["books/base"], [], False))


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
        fake = Fake([], codes={"nohup sh -c": 9})
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
        fake = Fake([], codes={"nohup sh -c": 9})
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


INSTALLED = ("install-set: 220 books, cache /home/ember/fn-certcache\n"
             "  artifact-set set-123 origin /home/ember/fn-lanes/w5 "
             "source source-123 toolchain toolchain-123; installed 31, kept 2, "
             "missing 0, removed 0\n")


COMPOSED = ("install-set: 220 books, cache /home/ember/fn-certcache\n"
            "  artifact-set set-c origin composed source source-c toolchain "
            "toolchain-c; installed 200, kept 3, missing 0, removed 0; "
            "origins /home/ember/fn-gates/dev-head=150,"
            "/home/ember/fn-gates/w31-treewide=53\n")


PARTIAL = ("install-partial: 409 books, cache /home/ember/fn-certcache\n"
           "  toolchain tool-p; installed 330, kept 8, missing 71, removed 0; "
           "roots installed 160 of 233; origins "
           "/home/ember/fn-gates/dev-head=300,/home/ember/fn-gates/tool-cache=38\n"
           "  uncached: books/served\n")


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
            runner = next(i for i, s in enumerate(scripts) if "nohup sh -c" in s)
            self.assertLess(install, runner)  # certify only what is not cached
            self.assertIn('--cache "$HOME"/fn-certcache', scripts[install])
            # A plain-roots run installs whatever of the roots' closure is
            # cached, each book from its own origin, and certifies the rest:
            # ACL2 does not compare sub-books by full-book-name
            # (certificate-cache-2026-09-23).
            self.assertNotIn("--require-origin", scripts[install])
            self.assertIn("install-partial $roots", scripts[install])
            self.assertIn("--incremental", scripts[runner])
            self.assertIn("tools/acl2_toolchain.py identity \"$acl2\"", scripts[install])
            self.assertIn("--toolchain-identity \"$toolchain\"", scripts[install])
            self.assertIn("cd /home/ember/fn-lanes/w5 ||", scripts[install])
            # The mirror overwrites the tree, so the install follows it.
            self.assertEqual(fake.commands[fake.commands.index(
                next(c for c in fake.commands if c[0] == "rsync")) + 1][0], "ssh")
            record = json.loads(farm.record_path(root, identifier).read_text())
            self.assertEqual(record["cache_install"],
                             {"artifact_set": "set-123",
                              "origin": "/home/ember/fn-lanes/w5",
                              "source_identity": "source-123",
                              "toolchain_identity": "toolchain-123",
                              "installed": 31, "kept": 2,
                              "missing": 0, "removed": 0})

    def test_a_composed_set_is_recorded_with_the_origins_it_drew_from(self):
        fake = Fake([], certs=COMPOSED)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("persvati", root, ["books/alpha"], jobs=4,
                                         timeout_seconds=60, affected_by=[],
                                         remote=Path("/home/ember/fn-gates/lane"))
            self.assertIn("nohup sh -c", fake.runner_script())
            record = json.loads(farm.record_path(root, identifier).read_text())
            self.assertEqual(record["cache_install"]["origin"], "composed")
            self.assertEqual(record["cache_install"]["origins"],
                             {"/home/ember/fn-gates/dev-head": 150,
                              "/home/ember/fn-gates/w31-treewide": 53})
            self.assertEqual(farm.cache_summary(record), "200+3/2")

    def test_an_incremental_install_is_recorded_with_what_is_left_to_certify(self):
        fake = Fake([], certs=PARTIAL)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("persvati", root, ["books/alpha"], jobs=8,
                                         timeout_seconds=60, affected_by=[],
                                         remote=Path("/home/ember/fn-gates/dev-head"))
            self.assertIn("tools/certify_books.py --jobs 8 --incremental",
                          fake.runner_script())
            record = json.loads(farm.record_path(root, identifier).read_text())
            self.assertTrue(record["incremental"])
            self.assertEqual(record["cache_install"], {
                "mode": "incremental", "books": 409,
                "toolchain_identity": "tool-p", "installed": 330, "kept": 8,
                "missing": 71, "removed": 0, "roots_installed": 160,
                "roots": 233, "certify": 71,
                "origins": {"/home/ember/fn-gates/dev-head": 300,
                            "/home/ember/fn-gates/tool-cache": 38}})
            self.assertEqual(farm.cache_summary(record), "330+8/2")

    def test_an_incremental_miss_does_not_refuse(self):
        missing = ("install-partial: 3 books, cache /tank/fn/certcache\n"
                   "  toolchain tool-p; installed 0, kept 0, missing 3, removed 0; "
                   "roots installed 0 of 1\n  uncached: books/alpha\n")
        fake = Fake([], certs=missing)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                farm.submit("hbox", root, ["books/alpha"], jobs=4,
                            timeout_seconds=60, affected_by=[],
                            remote=Path("/tank/fn/tree"))
            self.assertIn("--incremental", fake.runner_script())

    def test_affected_by_is_incremental_too(self):
        fake = Fake([], certs=PARTIAL)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                farm.submit("hbox", root, [], jobs=4, timeout_seconds=60,
                            affected_by=["books/article.lisp"],
                            remote=Path("/tank/fn/tree"))
            install = next(s for s in fake.scripts() if "tools/certs.py" in s)
            self.assertIn("--dry-run --affected-by books/article.lisp", install)
            self.assertIn("install-partial $roots", install)
            self.assertIn("--affected-by books/article.lisp --incremental",
                          fake.runner_script())

    def test_require_origin_demands_one_complete_set_and_refuses_a_miss(self):
        missing = ("install-set: 3 books, cache /tank/fn/certcache\n"
                   "  artifact-set NONE origin NONE source NONE toolchain NONE; "
                   "installed 0, kept 0, missing 3, removed 0\n")
        fake = Fake([], certs=missing, codes={"tools/certs.py": 1})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                code = farm.main(["submit", "hbox", "books/alpha", "--root", str(root),
                                  "--remote-root", "/tank/fn/tree",
                                  "--require-origin", "/tank/fn/gate"])
            self.assertEqual(code, 2)
            install = next(s for s in fake.scripts() if "tools/certs.py" in s)
            self.assertIn("--require-origin /tank/fn/gate --dependencies-only "
                          "install-set $roots", install)
            self.assertFalse(any("nohup sh -c" in script for script in fake.scripts()))

    def test_require_origin_runs_without_incremental_when_the_set_is_whole(self):
        fake = Fake([], certs=INSTALLED)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                farm.submit("hbox", root, ["books/alpha"], jobs=4,
                            timeout_seconds=60, affected_by=[],
                            remote=Path("/tank/fn/tree"),
                            require_origin="/home/ember/fn-lanes/w5")
            self.assertNotIn("--incremental", fake.runner_script())

    def test_the_older_identity_line_still_parses(self):
        parsed = farm.parse_installed(INSTALLED)
        self.assertNotIn("origins", parsed)
        self.assertEqual(parsed["installed"], 31)

    def test_acl2_override_is_quoted_for_preflight_and_runner_and_recorded(self):
        fake = Fake([], certs=INSTALLED)
        override = "/tank/fn/task wrappers/acl2'; touch /tmp/not-run; '"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                code = farm.main([
                    "submit", "hbox", "books/alpha", "--jobs", "2",
                    "--timeout-seconds", "60", "--root", str(root),
                    "--remote-root", "/tank/fn/tree", "--acl2", override])
            self.assertEqual(code, 0)
            install = next(s for s in fake.scripts() if "tools/certs.py" in s)
            runner = fake.runner_script()
            quoted = shlex.quote(override)
            self.assertIn("acl2=" + quoted, install)
            runner_words = shlex.split(runner)
            inner = runner_words[runner_words.index("-c") + 1]
            self.assertIn("FN_ACL2=" + quoted, inner)
            self.assertNotIn("FN_ACL2=" + override, inner)
            identifier = next((root / "build" / "farm").glob("*.json")).stem
            record = json.loads(farm.record_path(root, identifier).read_text())
            self.assertEqual(record["acl2"], override)

    def test_an_install_that_did_not_run_refuses_before_acl2(self):
        fake = Fake([], certs="Traceback: no such cache\n",
                    codes={"tools/certs.py": 1})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                with self.assertRaises(farm.FarmError) as refused:
                    farm.submit("hbox", root, [], jobs=4,
                                timeout_seconds=60, affected_by=[],
                                remote=Path("/tank/fn/tree"))
            self.assertIn("ACL2 was not started", str(refused.exception))
            self.assertIn("no such cache", str(refused.exception))
            self.assertFalse(any("nohup sh -c" in script
                                 for script in fake.scripts()))

    def test_closure_is_the_explicit_recertification_plan_on_a_set_miss(self):
        missing = ("install-set: 3 books, cache /tank/fn/certcache\n"
                   "  artifact-set NONE origin NONE source NONE toolchain NONE; "
                   "installed 0, kept 0, missing 3, removed 4\n")
        fake = Fake([], certs=missing, codes={"tools/certs.py": 1})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("hbox", root, ["books/alpha"], jobs=4,
                                         timeout_seconds=60, affected_by=[],
                                         remote=Path("/tank/fn/tree"), closure=True)
            install = next(s for s in fake.scripts() if "tools/certs.py" in s)
            self.assertIn("--purge-on-miss", install)
            # Root's recertification plan keeps the single-origin rule.
            self.assertIn("--require-origin /tank/fn/tree", install)
            self.assertIn("--closure", install)
            self.assertIn("--closure", fake.runner_script())
            record = json.loads(farm.record_path(root, identifier).read_text())
            self.assertTrue(record["cache_install"]["recertify_closure"])
            self.assertEqual(record["cache_install"]["removed"], 4)

    def test_the_runner_publishes_its_pairs_as_a_snapshot_of_this_run(self):
        # A finished run root is not a live worktree, and the pairs say so, so
        # the next lane on the box installs them instead of certifying again.
        script = farm.remote_script("persvati", Path("/home/ember/fn-lanes/w5"),
                                    "run-1", [], 4, 60, [])
        self.assertIn("FN_CERT_CACHE=~/fn-certcache", script)
        self.assertIn("FN_CERT_ORIGIN_KIND=run", script)

    def test_wait_publishes_the_new_pairs_into_the_boxs_cache_too(self):
        fake = Fake(["0"], log=WaitTests.LOG)
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
            # The same tree, the same label here as on the box: mirrored back
            # up, the entry is usable by the next lane there too.
            self.assertEqual(published["origin_kind"], "run")
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

    def test_the_timeout_path_fetches_and_publishes_before_giving_up(self):
        """Returning 3 with nothing fetched loses the run's finished pairs.

        The run keeps going on the box; the lane that gave up waiting has
        left every pair it paid for behind, and the next lane there certifies
        them again.  The timeout brings home what exists at that moment and
        says what it left running.
        """
        fake = Fake(["running"] * 3, log=self.LOG)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "books").mkdir()
            errors = io.StringIO()
            with mock.patch.object(farm, "RUN", fake), \
                    mock.patch.object(farm, "SLEEP", lambda seconds: None), \
                    mock.patch.dict(os.environ,
                                    {"FN_CERT_CACHE": str(root / "cache")}), \
                    contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(errors):
                self.assertEqual(farm.wait("hbox", "run-t", root, poll=30,
                                           timeout_seconds=0), 3)
            self.assertTrue((root / "build/farm/run-t.log").is_file())
            self.assertTrue(any("--include=*.cert" in command
                                for command in fake.rsyncs()))
            self.assertTrue(any("tools/certs.py" in script and "publish" in script
                                for script in fake.scripts()))
            said = errors.getvalue()
            self.assertIn("left running", said)
            self.assertIn("7 books were certified", said)
            self.assertIn("farm.py wait hbox run-t", said)

    def test_the_host_cache_override_reaches_install_publish_and_the_runner(self):
        fake = Fake(["0"], log=self.LOG,
                    certs="install-set: 2 books, cache /scratch/cache\n"
                          "  artifact-set set-s origin /tank/fn/tree "
                          "source source-s toolchain tool-s; installed 1, "
                          "kept 1, missing 0, removed 0\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "books").mkdir()
            with driving(fake, root / "cache"):
                identifier = farm.submit("hbox", root, ["books/alpha"], jobs=2,
                                         timeout_seconds=60, affected_by=[],
                                         cache="/scratch/cache")
            installs = [s for s in fake.scripts()
                        if "tools/certs.py" in s and "install-partial $roots" in s]
            self.assertEqual(len(installs), 1)
            self.assertIn("--cache /scratch/cache", installs[0])
            self.assertIn("FN_CERT_CACHE=/scratch/cache", fake.runner_script())
            record = json.loads(
                (root / "build/farm" / f"{identifier}.json").read_text())
            self.assertEqual(record["cache"], "/scratch/cache")
            # `wait` reuses what `submit` recorded, so the sweep publishes
            # into the same cache the install read.
            with driving(fake, root / "cache"):
                farm.wait("hbox", identifier, root, poll=1, timeout_seconds=60)
            sweeps = [s for s in fake.scripts()
                      if "tools/certs.py" in s and "publish" in s]
            self.assertTrue(sweeps)
            self.assertIn("--cache /scratch/cache", sweeps[-1])

    def test_progress_parsing_ignores_unrelated_output(self):
        fields = farm.parse_progress(
            "Warning: something\nSTATUS running\nMARKERS 12\nSTARTED 40\nTAIL a b c\n")
        self.assertEqual(fields["STATUS"], "running")
        self.assertEqual(fields["MARKERS"], "12")
        self.assertEqual(fields["STARTED"], "40")

    def test_progress_counts_markers_in_the_run_directory_not_the_farm_log(self):
        # Until 2026-09-22 the script grepped the farm log, which carries no
        # per-book marker, so every progress line read "0 books certified".
        script = farm.progress_script(Path("/remote/root"), "run-x")
        self.assertIn("build/acl2/certify-*/", script)
        self.assertIn("grep -lE '^(ACL2 [^[:space:]]*>)?FN_CERTIFY_SUCCESS", script)
        self.assertIn("*.certify.log", script)
        self.assertIn("STARTED", script)
        self.assertNotIn("grep -c FN_CERTIFY_SUCCESS build/farm", script)

    def test_live_progress_does_not_count_an_echoed_driver_form(self):
        marker = "FN_CERTIFY_SUCCESS " + "a" * 32 + " " + "b" * 12
        echoed = f'(cw "{marker}~%")\n'
        actual = f"ACL2 !>{marker}\n"
        self.assertEqual(subprocess.run(
            ["grep", "-E", farm.SUCCESS_LINE], input=echoed,
            text=True, capture_output=True, check=False).returncode, 1)
        self.assertEqual(subprocess.run(
            ["grep", "-E", farm.SUCCESS_LINE], input=actual,
            text=True, capture_output=True, check=False).returncode, 0)


class StatusTests(unittest.TestCase):
    @staticmethod
    def snapshot(root: Path) -> list[dict]:
        result = subprocess.run(["sh", "-c", farm.status_script(root)],
                                text=True, capture_output=True, check=True)
        return json.loads(result.stdout)

    @staticmethod
    def make_run(root: Path, identifier: str, state: str | None = None) -> None:
        directory = root / "build/farm"
        directory.mkdir(parents=True, exist_ok=True)
        (directory / f"{identifier}.log").write_text("runner output comes later\n")
        if state is not None:
            (directory / f"{identifier}.status").write_text(state + "\n")

    def test_live_snapshot_counts_exited_and_active_without_a_verdict(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            identifier = "run-20260924T045402Z-31bd"
            self.make_run(root, identifier)
            evidence = root / "build/acl2/certify-20260924T045427Z-915676"
            evidence.mkdir(parents=True)
            (evidence / "books--done.certify.log").write_text("ACL2 !> theorem failed\n")
            (evidence / "books--failed.certify.log").write_text("ACL2 error\n")
            (evidence / "books--active.certify.log").write_text("current goal\n")
            for name, status, code in (("done", "exited", 0),
                                       ("failed", "exited", 1),
                                       ("active", "running", None)):
                record = {"book": f"books/{name}", "status": status,
                          "started_utc": "2026-09-24T04:54:27+00:00",
                          "log": f"books--{name}.certify.log"}
                if code is not None:
                    record["exit_code"] = code
                (evidence / f"books--{name}.active.json").write_text(json.dumps(record))
            row, = self.snapshot(root)
            self.assertEqual((row["state"], row["data"], row["exited"],
                              row["active"]),
                             ("unfinalized", "observed", 2, 1))
            # ACL2 may exit 0 on a theorem failure; only the final manifest
            # has a book verdict, even when every child has exited.
            self.assertNotIn("passed", row)
            self.assertNotIn("failed", row)
            self.assertGreaterEqual(row["age_seconds"], 0)

    def test_terminal_manifest_replaces_live_observations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.make_run(root, "run-20260924T045402Z-31bd", "1")
            evidence = root / "build/acl2/certify-20260924T045427Z-915676"
            evidence.mkdir(parents=True)
            (evidence / "books--stale.active.json").write_text(json.dumps(
                {"status": "running", "started_utc": "2026-09-24T04:54:27+00:00"}))
            (evidence / "manifest.json").write_text(json.dumps(
                {"status": "failed", "book_results": {"books/a": "passed",
                                                       "books/b": "failed"}}))
            row, = self.snapshot(root)
            self.assertEqual((row["state"], row["data"], row["manifest"],
                              row["passed"], row["failed"], row["active"]),
                             ("1", "manifest", "failed", 1, 1, 0))

    def test_missing_or_stale_activity_is_unknown_not_zero(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.make_run(root, "run-20260924T045402Z-31bd")
            stale = root / "build/acl2/certify-20260924T044000Z-123"
            stale.mkdir(parents=True)
            (stale / "books--old.active.json").write_text('{"status":"running"}')
            row, = self.snapshot(root)
            self.assertEqual(row["data"], "missing")
            self.assertNotIn("passed", row)
            fresh = root / "build/acl2/certify-20260924T045427Z-915676"
            fresh.mkdir(parents=True)
            row, = self.snapshot(root)
            self.assertEqual(row["data"], "missing")
            self.assertNotIn("active", row)

    def test_terminal_without_manifest_does_not_claim_zero_failures(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.make_run(root, "run-20260924T045402Z-31bd", "1")
            evidence = root / "build/acl2/certify-20260924T045427Z-915676"
            evidence.mkdir(parents=True)
            (evidence / "books--a.active.json").write_text(json.dumps(
                {"status": "exited", "exit_code": 0}))
            row, = self.snapshot(root)
            self.assertEqual((row["state"], row["data"]), ("1", "missing"))
            self.assertNotIn("failed", row)

    def test_status_lists_runs_without_starting_anything(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            commands = []
            def local_ssh(host, script, check=False):
                commands.append(script)
                return subprocess.run(["sh", "-c", script], text=True,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            with mock.patch.object(farm, "ssh", local_ssh):
                self.assertEqual(farm.status("persvati", root), 0)
            self.assertEqual(len(commands), 1)
            self.assertIn("python3 -c", commands[0])
            self.assertNotIn("certify_books.py", commands[0])


if __name__ == "__main__":
    unittest.main()
