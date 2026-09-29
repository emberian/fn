"""Unit checks for the farm submitter: what it asks the box to do.

No ssh runs here.  `tools/farm.py` keeps the two shell-touching calls behind
module-level seams, so these tests read the exact commands the tool would
issue: the mirror that excludes build/, the detached runner with its own log
and status file, the bounded wait that sleeps rather than spins, and the fetch
that brings back the evidence directory and the new certificate pairs.
"""

import contextlib
import datetime as dt
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
from types import SimpleNamespace
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
SPEC = importlib.util.spec_from_file_location("farm", TOOLS / "farm.py")
farm = importlib.util.module_from_spec(SPEC)
sys.modules["farm"] = farm
SPEC.loader.exec_module(farm)
# No test reaches a real box's reservation lease (tools/boxes.sh wait).
BOX_WAITS = []
farm.BOXES = lambda words, **_: BOX_WAITS.append(words) or SimpleNamespace(returncode=0)
# No test mirrors into a real box's cache (tools/cert_cache_sync.py).
MIRRORS = []
farm.MIRROR = lambda host, since: MIRRORS.append((host, since)) or 0


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
                 certs: str | None = None, certs_stderr: str = "") -> None:
        self.commands: list[list[str]] = []
        self.certs_stderr = certs_stderr
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
        error = ""
        if command[0] == "ssh":
            script = command[-1]
            if script == "echo $HOME":
                output = f"{self.home}\n"
            elif "STATUS" in script:
                state = self.statuses.pop(0) if self.statuses else "0"
                output = f"STATUS {state}\nMARKERS 7\nTAIL working\n"
            elif "tools/certs.py" in script:
                output = self.certs
                error = self.certs_stderr
            elif script.startswith("cat "):
                output = self.log
        code = self.code_for(command)
        if code and kwargs.get("check"):
            raise subprocess.CalledProcessError(code, command, output=output)
        return subprocess.CompletedProcess(command, code, stdout=output,
                                           stderr=error)

    def scripts(self) -> list[str]:
        return [command[-1] for command in self.commands if command[0] == "ssh"]

    def runner_script(self) -> str:
        started = [s for s in self.scripts()
                   if "certify_books.py" in s and "nohup sh -c" in s]
        assert len(started) == 1, started
        return started[0]

    def rsyncs(self) -> list[list[str]]:
        return [command for command in self.commands if command[0] == "rsync"]


FIXTURE_BOOKS = ("books/alpha", "books/beta", "books/article", "books/wire",
                 "books/base")


def seed_books(root: Path) -> None:
    """The book sources `submit` checks exist before it mirrors anything."""
    for book in FIXTURE_BOOKS:
        path = root / f"{book}.lisp"
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists():
            path.write_text("(in-package \"ACL2\")\n", encoding="utf-8")


@contextlib.contextmanager
def driving(fake, cache: Path):
    # Every test's cache sits inside its worktree root.
    seed_books(cache.parent)
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
            self.assertIn("FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k",
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
            self.assertIn("FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k", script)
            self.assertIn("FN_CERT_CACHE=/tank/fn/certcache", script)

    def test_default_toolchain_paths_reach_cache_preflight(self):
        self.assertIn(
            'acl2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k;',
            farm.cache_preflight_script("persvati", Path("/home/ember/fn-lanes/x"),
                                        ["books/base"], [], False))
        self.assertIn(
            'acl2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k;',
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

    def test_unmerged_real_index_refuses_before_remote_io(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            blob = subprocess.run(
                ["git", "-C", str(root), "hash-object", "-w", "--stdin"],
                input="unfinished source\n", text=True, capture_output=True,
                check=True).stdout.strip()
            subprocess.run(
                ["git", "-C", str(root), "update-index", "--index-info"],
                input=f"100644 {blob} 1\tMakefile\n100644 {blob} 2\tMakefile\n",
                text=True, check=True)
            with mock.patch.object(farm, "push") as push, \
                    mock.patch.object(farm, "ssh") as ssh:
                with self.assertRaisesRegex(farm.FarmError, "unmerged.*Makefile"):
                    farm.submit("hbox", root, [], jobs=2, timeout_seconds=60,
                                affected_by=[], remote=Path("~/unused"))
            push.assert_not_called()
            ssh.assert_not_called()
            self.assertFalse((root / "build" / "farm").exists())

    def test_clean_index_allows_uncommitted_lane_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            source = root / "book.lisp"
            source.write_text("original\n")
            subprocess.run(["git", "-C", str(root), "add", "book.lisp"],
                           check=True)
            source.write_text("uncommitted proof attempt\n")
            farm.refuse_unmerged_source(root)

    def test_broken_git_metadata_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ".git").write_text("gitdir: missing-directory\n")
            with self.assertRaisesRegex(farm.FarmError, "cannot inspect source index"):
                farm.refuse_unmerged_source(root)

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
                code = farm.main(["submit", "persvati", "--all", "--root", str(root),
                                  "--remote-root", "~/fn-lanes/w5"])
            self.assertEqual(code, 2)
            self.assertIn("did not start", errors.getvalue())

    def test_the_images_choice_reaches_the_runner_on_the_box(self):
        # FN_CERT_IMAGES in the submitting shell never reaches the box.
        off = farm.remote_script("persvati", Path("/tank/fn/tree"), "run-1",
                                 [], 4, 60, [], images="off")
        self.assertIn("--images off", off)
        default = farm.remote_script("persvati", Path("/tank/fn/tree"), "run-1",
                                     [], 4, 60, [])
        self.assertNotIn("--images", default)

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

    def test_a_submit_with_nothing_to_certify_says_so_loudly(self):
        everything = ("install-partial: 12 books, cache /home/ember/fn-certcache\n"
                      "  toolchain tool-p; installed 10, kept 2, missing 0, removed 0; "
                      "roots installed 3 of 3; origins /home/ember/fn-gates/dev-head=12\n")
        fake = Fake([], certs=everything)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            err = io.StringIO()
            with driving(fake, root / "cache"), contextlib.redirect_stderr(err):
                farm.submit("persvati", root, ["books/alpha"], jobs=8, timeout_seconds=60,
                            affected_by=[], remote=Path("/home/ember/fn-gates/dev-head"))
        self.assertIn("ALL 12 BOOKS CAME FROM THE CACHE -- this run certified NOTHING",
                      err.getvalue())

    def test_recertify_reaches_the_cache_preflight_and_the_runner(self):
        fake = Fake([], certs=PARTIAL)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("persvati", root, ["books/alpha"], jobs=8,
                                         timeout_seconds=60, affected_by=[],
                                         remote=Path("/home/ember/fn-gates/dev-head"),
                                         recertify=["books/beta"])
            preflight = [s for s in fake.scripts() if "install-partial" in s]
            self.assertEqual(len(preflight), 1)
            self.assertIn("--recertify books/beta install-partial", preflight[0])
            self.assertIn("--incremental --recertify books/beta books/alpha",
                          fake.runner_script())
            record = json.loads(farm.record_path(root, identifier).read_text())
            self.assertEqual(record["recertify"], ["books/beta"])
            # The installer names the recertified books after its origins.
            parsed = farm.parse_installed(
                "install-partial: 3 books, cache /c\n  toolchain t; installed 2, "
                "kept 0, missing 1, removed 1; roots installed 0 of 1; "
                "origins /o=2; recertify books/beta; fasl 1 missing 1\n")
            self.assertEqual(parsed["origins"], {"/o": 2})
            self.assertEqual((parsed["installed"], parsed["fasl_installed"],
                              parsed["fasl_missing"]), (2, 1, 1))
            with self.assertRaises(farm.FarmError):
                farm.submit("persvati", root, ["books/alpha"], jobs=8,
                            timeout_seconds=60, affected_by=[], closure=True,
                            recertify=["books/beta"])

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

    def test_fetch_mirrors_the_runs_pairs_to_the_other_box(self):
        """One toolchain on both boxes (lane toolchain-unify): a run's pairs
        reach the other box's cache from the submit time on; a run with its
        own cache (a measurement's isolation) is not mirrored."""
        for cache, mirrored in ((None, True), ("/tank/fn/probe-cache", False)):
            fake = Fake(["0"], log=self.LOG)
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                (root / "books").mkdir()
                with driving(fake, root / "cache"):
                    identifier = farm.submit("hbox", root, [], jobs=2,
                                             timeout_seconds=60, affected_by=[],
                                             remote=Path("/tank/fn/tree"),
                                             cache=cache)
                submitted = dt.datetime.fromisoformat(
                    farm.run_record(root, identifier)["submitted_at"]).timestamp()
                del MIRRORS[:]
                with driving(fake, root / "cache"):
                    farm.wait("hbox", identifier, root, poll=1, timeout_seconds=60)
                if mirrored:
                    self.assertEqual(MIRRORS, [("hbox", submitted - 600)])
                else:
                    self.assertEqual(MIRRORS, [])

    def test_a_no_publish_run_publishes_nowhere(self):
        # tooling-obstructions: a measurement run seeded both caches.
        fake = Fake(["0"], log=self.LOG)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "books").mkdir()
            with driving(fake, root / "cache"):
                identifier = farm.submit("hbox", root, [], jobs=2, timeout_seconds=60,
                                         affected_by=[], remote=Path("/tank/fn/tree"),
                                         no_publish=True)
            self.assertIn("--no-publish", fake.runner_script())
            self.assertTrue(farm.run_record(root, identifier)["no_publish"])
            del MIRRORS[:]
            with mock.patch.object(farm.certs, "publish",
                                   lambda *a, **k: self.fail("published locally")), \
                    driving(fake, root / "cache"), \
                    contextlib.redirect_stdout(io.StringIO()) as out:
                farm.wait("hbox", identifier, root, poll=1, timeout_seconds=60)
            self.assertEqual(MIRRORS, [])
            self.assertFalse([s for s in fake.scripts() if "--origin-kind run publish" in s])
            self.assertIn("not published to any cache", out.getvalue())
        with mock.patch.object(farm, "submit", return_value="run-np") as submitted, \
                mock.patch.object(farm, "honour_reservation"), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(farm.main(["submit", "hbox", "books/x", "--jobs", "2",
                                        "--no-publish"]), 0)
        self.assertTrue(submitted.call_args.kwargs["no_publish"])

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

    def test_wait_returns_on_a_final_manifest_before_the_status_file(self):
        """A final manifest is the verdict: the runner may still be publishing.

        depth-debt-2 and d27-representation-2: waits that never returned
        while `farm.py status` already showed manifest(passed/failed).
        """
        class Final(Fake):
            def __call__(self, command, **kwargs):
                result = super().__call__(command, **kwargs)
                if command[0] == "ssh" and "STATUS" in command[-1]:
                    result.stdout = ("STATUS running\nKNOWN yes\nMARKERS 3\n"
                                     "MANIFEST failed certify-20260929T000000Z-7\n")
                return result
        fake = Final([], log=self.LOG)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            out = io.StringIO()
            with driving(fake, root / "cache"), contextlib.redirect_stdout(out):
                code = farm.wait("hbox", "run-m", root, poll=1, timeout_seconds=600)
            self.assertEqual(code, 1)
            self.assertEqual(sum("STATUS" in s for s in fake.scripts()), 1)
            said = out.getvalue()
            self.assertIn("is final (failed)", said)
            self.assertIn("manifest certify-20260929T000000Z-7 failed", said)
            # The verdict comes before the collection's phase, not after it.
            self.assertLess(said.index("finished with exit code 1"),
                            said.index("collected in"))

    def test_a_provisional_manifest_is_not_a_verdict(self):
        script = farm.progress_script(Path("/r"), "run-p")
        self.assertIn("finished_utc", farm.MANIFEST_VERDICT)
        self.assertIn("MANIFEST", script)
        with tempfile.TemporaryDirectory() as directory:
            run_dir = Path(directory) / "certify-x"
            run_dir.mkdir()
            (run_dir / "manifest.json").write_text(json.dumps({"status": "failed"}))
            said = subprocess.run([sys.executable, "-c", farm.MANIFEST_VERDICT,
                                   str(run_dir)], capture_output=True, text=True)
            self.assertEqual(said.stdout.strip(), "")
            (run_dir / "manifest.json").write_text(json.dumps(
                {"status": "passed", "finished_utc": "2026-09-29T00:00:00+00:00"}))
            said = subprocess.run([sys.executable, "-c", farm.MANIFEST_VERDICT,
                                   str(run_dir)], capture_output=True, text=True)
            self.assertEqual(said.stdout.strip(), "passed certify-x")

    def test_wait_refuses_a_run_that_is_not_under_its_remote_root(self):
        for answer, words in (("NOROOT\n", "no such directory"),
                              ("STATUS running\nKNOWN no\n", "neither its log")):
            class Missing(Fake):
                def __call__(self, command, **kwargs):
                    result = super().__call__(command, **kwargs)
                    if command[0] == "ssh" and "STATUS" in command[-1]:
                        result.stdout = answer
                    return result
            fake = Missing([], log=self.LOG)
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with driving(fake, root / "cache"):
                    with self.assertRaises(farm.FarmError) as raised:
                        farm.wait("hbox", "run-q", root, poll=1, timeout_seconds=600)
                self.assertIn(words, str(raised.exception))
                self.assertIn("--remote-root", str(raised.exception))
                self.assertEqual(fake.rsyncs(), [])

    def test_progress_parsing_ignores_unrelated_output(self):
        fields = farm.parse_progress(
            "Warning: something\nSTATUS running\nMARKERS 12\nSTARTED 40\nTAIL a b c\n")
        self.assertEqual(fields["STATUS"], "running")
        self.assertEqual(fields["MARKERS"], "12")
        self.assertEqual(fields["STARTED"], "40")

    def test_progress_carries_the_runners_plan_line(self):
        script = farm.progress_script(Path("/remote/root"), "run-x")
        self.assertIn("grep -m1 '^Critical chain: ' build/farm/run-x.log", script)
        fields = farm.parse_progress(
            "STATUS running\nPLAN Critical chain: 47 books, 180 s quiet; 12 jobs\n")
        self.assertEqual(fields["PLAN"], "Critical chain: 47 books, 180 s quiet; 12 jobs")

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


class CancelAndUnionTests(unittest.TestCase):
    """obstructions-2 item 2: cancel, the union help, --recertify-list."""

    def test_submit_records_the_wrapper_pid_and_cancel_stops_that_tree(self):
        class Started(Fake):
            def __call__(self, command, **kwargs):
                result = super().__call__(command, **kwargs)
                if command[0] == "ssh" and "nohup sh -c" in command[-1]:
                    result.stdout = "FN_FARM_STARTED run-x 4242\n"
                if command[0] == "ssh" and "kill -TERM" in command[-1]:
                    result.stdout = "CANCELLED 3\n"
                return result
        fake = Started([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("hbox", root, ["books/alpha"], jobs=2,
                                         timeout_seconds=60, affected_by=[])
            record = farm.run_record(root, identifier)
            self.assertEqual(record["pid"], 4242)
            out = io.StringIO()
            with driving(fake, root / "cache"), contextlib.redirect_stdout(out):
                self.assertEqual(farm.cancel("hbox", identifier, root), 0)
            script = fake.scripts()[-1]
            self.assertIn("for p in 4242;", script)
            self.assertIn(f"echo 143 > build/farm/{identifier}.status", script)
            self.assertIn("stopped 3 process(es); status 143", out.getvalue())
            with self.assertRaises(farm.FarmError):
                farm.cancel("persvati", identifier, root)

    def test_cancel_script_really_stops_a_tree_and_finalises_it(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "build/farm").mkdir(parents=True)
            (root / "build/farm/run-c.log").write_text("")
            child = subprocess.Popen(["sh", "-c", "sleep 300 & wait"])
            try:
                script = farm.cancel_script(root, "run-c", child.pid)
                done = subprocess.run(["sh", "-c", script], capture_output=True,
                                      text=True, timeout=30)
                self.assertTrue(done.stdout.strip().startswith("CANCELLED"), done.stdout)
                self.assertEqual(child.wait(timeout=10) != 0, True)
                self.assertEqual((root / "build/farm/run-c.status").read_text().strip(),
                                 "143")
                again = subprocess.run(["sh", "-c", script], capture_output=True,
                                       text=True, timeout=30)
                self.assertEqual(again.stdout.strip(), "ALREADY 143")
            finally:
                if child.poll() is None:
                    child.kill()
            unknown = subprocess.run(["sh", "-c", farm.cancel_script(root, "run-none", None)],
                                     capture_output=True, text=True, timeout=30)
            self.assertEqual((unknown.returncode, unknown.stdout.strip()), (8, "UNKNOWN"))

    def test_the_help_states_the_union_and_recertify_list_is_an_alias(self):
        help_text = io.StringIO()
        with contextlib.redirect_stdout(help_text), self.assertRaises(SystemExit):
            farm.main(["--help"])
        self.assertIn("UNION", help_text.getvalue())
        self.assertIn("cancel", help_text.getvalue())
        with tempfile.TemporaryDirectory() as directory:
            listing = Path(directory) / "list"
            listing.write_text("books/alpha\n")
            with mock.patch.object(farm, "submit", return_value="run-l") as submitted, \
                    mock.patch.object(farm, "honour_reservation"), \
                    contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                farm.main(["submit", "hbox", "--recertify-list", str(listing)])
            self.assertEqual(submitted.call_args.kwargs["recertify"], ["books/alpha"])


class CacheChooserTests(unittest.TestCase):
    """obstructions-2 item 3: `submit auto` follows the certificates."""

    def choose(self, counts: dict[str, str], keys=("k1", "k2")):
        scripts: list[str] = []

        def answer(command, **kwargs):
            scripts.append(command[-1])
            host = command[-2]
            code = 0 if host in counts else 255
            return subprocess.CompletedProcess(command, code,
                                               stdout=counts.get(host, ""))
        picked: list[str] = []
        with mock.patch.object(farm, "RUN", answer), \
                mock.patch.object(farm, "closure_keys", lambda *a: list(keys)), \
                contextlib.redirect_stderr(io.StringIO()):
            host = farm.choose_host(Path("/r"), ["books/alpha"], [],
                                    pick=lambda: picked.append(1) or "persvati")
        return host, picked, scripts

    def test_the_box_holding_clearly_more_certificates_wins_over_load(self):
        keys = [f"k{i}" for i in range(600)]
        host, picked, scripts = self.choose({"hbox": "590\n", "persvati": "106\n"}, keys)
        self.assertEqual((host, picked), ("hbox", []))
        self.assertIn("k599", scripts[0])
        self.assertIn("os.path.isdir", scripts[0])

    def test_close_caches_leave_the_choice_to_the_load(self):
        keys = [f"k{i}" for i in range(600)]
        host, picked, _ = self.choose({"hbox": "590\n", "persvati": "580\n"}, keys)
        self.assertEqual((host, picked), ("persvati", [1]))

    def test_an_unanswering_box_or_uncountable_closure_falls_back_to_load(self):
        host, picked, _ = self.choose({"hbox": "2\n"})
        self.assertEqual((host, picked), ("persvati", [1]))

        def broken(*arguments):
            raise ValueError("no Makefile")
        with mock.patch.object(farm, "closure_keys", broken), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(farm.choose_host(Path("/r"), [], ["books/x"],
                                              pick=lambda: "hbox"), "hbox")

    def test_the_count_script_counts_existing_key_directories(self):
        with tempfile.TemporaryDirectory() as directory:
            for key in ("aa", "bb"):
                (Path(directory) / key).mkdir()
            done = subprocess.run([sys.executable, "-c", farm.COUNT_KEYS],
                                  input="aa\nbb\ncc\n", capture_output=True,
                                  text=True, cwd=directory)
            self.assertEqual(done.stdout.strip(), "2")


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



class CertifyIdTests(unittest.TestCase):
    """submit and status name the run's certify id (evidence_manifests add)."""

    def test_submit_records_the_certify_id_the_runner_names(self):
        class Named(Fake):
            def __call__(self, command, **kwargs):
                if command[0] == "ssh" and "Certification (run|evidence)" in command[-1]:
                    self.commands.append(list(command))
                    return subprocess.CompletedProcess(
                        command, 0, stdout="Certification run: build/acl2/"
                        "certify-20260929T101010Z-4242\n", stderr="")
                return super().__call__(command, **kwargs)

        fake = Named([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                identifier = farm.submit("persvati", root, ["books/alpha"], jobs=4,
                                         timeout_seconds=60, affected_by=[])
            record = json.loads(farm.record_path(root, identifier).read_text())
        self.assertEqual(record["certify_id"], "certify-20260929T101010Z-4242")

    def test_submit_without_the_id_yet_says_status_will_name_it(self):
        fake = Fake([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            err = io.StringIO()
            with driving(fake, root / "cache"), contextlib.redirect_stderr(err):
                identifier = farm.submit("persvati", root, ["books/alpha"], jobs=4,
                                         timeout_seconds=60, affected_by=[])
            record = json.loads(farm.record_path(root, identifier).read_text())
        self.assertNotIn("certify_id", record)
        self.assertIn("has not named its certify id yet", err.getvalue())
        asks = [s for s in fake.scripts() if "Certification (run|evidence)" in s]
        self.assertEqual(len(asks), farm.CERTIFY_ID_ATTEMPTS)

    def test_status_reads_the_id_from_the_log_and_records_it(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            identifier = "run-20260929T101000Z-abcd"
            farm_dir = root / "build/farm"
            farm_dir.mkdir(parents=True)
            (farm_dir / f"{identifier}.log").write_text(
                "Certification run: build/acl2/certify-20260929T101500Z-77\n")
            (farm_dir / f"{identifier}.json").write_text(json.dumps({"run_id": identifier}))
            # A second directory in the time window: the log decides, not the clock.
            for name in ("certify-20260929T101001Z-11", "certify-20260929T101500Z-77"):
                (root / "build/acl2" / name).mkdir(parents=True)
            rows = StatusTests.snapshot(root)
            self.assertEqual(rows[0]["certify_id"], "certify-20260929T101500Z-77")

            def local_ssh(host, script, check=False):
                return subprocess.run(["sh", "-c", script], text=True,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            out = io.StringIO()
            with mock.patch.object(farm, "ssh", local_ssh), contextlib.redirect_stdout(out):
                farm.status("persvati", root, root)
            self.assertIn("certify-20260929T101500Z-77", out.getvalue())
            self.assertEqual(farm.run_record(root, identifier)["certify_id"],
                             "certify-20260929T101500Z-77")
            import evidence_manifests
            self.assertEqual(evidence_manifests.certify_ids_of_farm_run(root, identifier),
                             ["certify-20260929T101500Z-77"])


class FrictionTests(unittest.TestCase):
    """The 2026-09-26 friction review's farm findings (sections 2 and 3)."""

    def test_a_failed_preflight_reports_exit_code_and_whole_stderr_cause_first(self):
        books = "".join(f"  uncached: books/b{index}\n" for index in range(200))
        fake = Fake([], certs=books,
                    certs_stderr=("usage: certs.py ...\n"
                                  "certs.py: error: install-partial needs "
                                  "--toolchain-identity\n"),
                    codes={"tools/certs.py": 2})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with driving(fake, root / "cache"):
                with self.assertRaises(farm.FarmError) as refused:
                    farm.submit("persvati", root, ["books/alpha"], jobs=2,
                                timeout_seconds=60, affected_by=[])
        text = str(refused.exception)
        self.assertIn("exit 2", text)
        self.assertIn("first error: certs.py: error: install-partial needs", text)
        self.assertIn("install-partial needs --toolchain-identity", text)
        self.assertLess(text.index("needs --toolchain-identity"),
                        text.index("uncached: books/b199"))
        self.assertIn("ACL2 was not started", text)

    def test_preflight_exit_codes_are_named(self):
        detail = farm.preflight_detail(13, "", "")
        self.assertIn("exit 13 (tools/certify_books.py --dry-run refused", detail)

    def test_bad_book_words_refuse_before_any_remote_command(self):
        cases = [
            ([], ["books/alpha --affected-by books/beta"], "whitespace"),
            ([], [" --affected-by books/alpha"], "whitespace"),
            ([], ["--closure"], "is an option"),
            ([], ["/abs/books/alpha.lisp"], "not a repository-relative"),
            ([], ["books/alpah"], "no books/alpah.lisp"),
            (["books/alpha.lisp.bak"], [], "not a repository-relative"),
        ]
        for books, affected, needle in cases:
            fake = Fake([])
            with self.subTest(books=books, affected=affected), \
                    tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with driving(fake, root / "cache"):
                    with self.assertRaises(farm.FarmError) as refused:
                        farm.submit("persvati", root, books, jobs=2,
                                    timeout_seconds=60, affected_by=affected)
                self.assertIn(needle, str(refused.exception))
                self.assertIn("no farm run started", str(refused.exception))
                self.assertEqual(fake.commands, [])

    def test_an_unbalanced_source_refuses_before_any_remote_command(self):
        fake = Fake([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed_books(root)
            (root / "host").mkdir(exist_ok=True)
            (root / "host" / "io.lisp").write_text("(defun a (x)\n  x\n(defun b (y) y)\n")
            with driving(fake, root / "cache"):
                with self.assertRaises(farm.FarmError) as refused:
                    farm.submit("persvati", root, ["books/alpha"], jobs=2,
                                timeout_seconds=60, affected_by=[])
        text = str(refused.exception)
        self.assertIn("no farm run started", text)
        self.assertIn("form starting at host/io.lisp:1 never closes", text)
        self.assertEqual(fake.commands, [])

    def test_a_selection_the_runner_refuses_is_refused_before_the_sync(self):
        # shared-books: a book in no Makefile root's closure cost a whole mirror.
        fake = Fake([])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed_books(root)
            (root / "tools").mkdir(exist_ok=True)
            (root / "tools" / "certify_books.py").write_text(
                "import sys\nprint('certify_books: in no Makefile root closure: '"
                " + sys.argv[-1], file=sys.stderr)\nsys.exit(2)\n")
            with driving(fake, root / "cache"):
                with self.assertRaises(farm.FarmError) as refused:
                    farm.submit("persvati", root, [], jobs=2, timeout_seconds=60,
                                affected_by=["books/alpha"])
        text = str(refused.exception)
        self.assertIn("before any sync", text)
        self.assertIn("in no Makefile root closure: books/alpha", text)
        self.assertEqual(fake.commands, [])

    def test_submit_with_no_box_picks_the_least_loaded(self):
        picked = farm.pick_host(lambda *a, **k: SimpleNamespace(returncode=0,
                                                               stdout="persvati\n"))
        self.assertEqual(picked, "persvati")
        with self.assertRaises(farm.FarmError):
            farm.pick_host(lambda *a, **k: SimpleNamespace(returncode=3, stdout=""))
        calls = []
        with mock.patch.object(farm, "pick_host", lambda: "hbox"), \
                mock.patch.object(farm, "submit",
                                  lambda host, root, books, *a, **k: calls.append(
                                      (host, books)) or "run-x"), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(farm.main(["submit", "books/wire", "books/x"]), 0)
            self.assertEqual(farm.main(["submit", "auto", "books/y"]), 0)
        self.assertEqual(calls, [("hbox", ["books/wire", "books/x"]), ("hbox", ["books/y"])])

    def test_a_named_box_waits_for_its_reservation_and_a_held_one_starts_nothing(self):
        calls = []
        with mock.patch.object(farm, "submit",
                               lambda host, root, books, *a, **k: calls.append(host) or "run-x"), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()) as err:
            del BOX_WAITS[:]
            self.assertEqual(farm.main(["submit", "persvati", "books/y"]), 0)
            self.assertEqual([w[-2:] for w in BOX_WAITS], [["wait", "persvati"]])
            with mock.patch.object(farm, "BOXES",
                                   lambda words, **_: SimpleNamespace(returncode=4)):
                self.assertEqual(farm.main(["submit", "hbox", "books/y"]), 2)
        self.assertEqual(calls, ["persvati"])
        self.assertIn("hbox is reserved", err.getvalue())

    def test_valid_words_with_lisp_suffix_pass_validation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed_books(root)
            farm.refuse_bad_book_names(root, ["books/alpha"],
                                       ["books/beta.lisp", "books/wire"])

    def test_a_submit_refuses_a_tree_a_run_is_still_certifying(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "build" / "farm").mkdir(parents=True)
            (root / "build" / "farm" / "run-a.json").write_text(json.dumps(
                {"run_id": "run-a", "host": "hbox", "remote_path": str(root)}))
            running = lambda host, script, check=False: SimpleNamespace(
                stdout="RUNNING run-a\n", returncode=0)
            with self.assertRaises(farm.FarmError):
                farm.refuse_a_running_run_in_the_same_tree("hbox", root, root, running)
            finished = lambda host, script, check=False: SimpleNamespace(stdout="", returncode=0)
            farm.refuse_a_running_run_in_the_same_tree("hbox", root, root, finished)
            # another box's tree is another tree
            farm.refuse_a_running_run_in_the_same_tree("persvati", root, root, running)

    def test_an_empty_selection_is_refused_without_all(self):
        calls = []
        with mock.patch.object(farm, "pick_host", lambda: "hbox"), \
                mock.patch.object(farm, "submit",
                                  lambda host, root, books, *a, **k: calls.append(
                                      (host, books)) or "run-x"), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            for words in (["submit", "hbox"], ["submit", "auto"],
                          ["submit", "hbox", "--all", "books/x"]):
                with self.assertRaises(SystemExit):
                    farm.main(words)
            self.assertEqual(farm.main(["submit", "hbox", "--all"]), 0)
        self.assertEqual(calls, [("hbox", [])])

    def test_recertify_takes_a_host_book_of_the_closure(self):
        # batch AY: --recertify-uncited listed host/native-operator-host and
        # the name check refused it, so the union cite's half never started.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed_books(root)
            (root / "host").mkdir()
            (root / "host" / "op-host.lisp").write_text("(in-package \"ACL2\")\n")
            farm.refuse_bad_book_names(root, ["books/alpha"], [],
                                       ["host/op-host", "books/beta"])
            with self.assertRaises(farm.FarmError):
                farm.refuse_bad_book_names(root, ["host/op-host"], [])
            with self.assertRaises(farm.FarmError):
                farm.refuse_bad_book_names(root, ["books/alpha"], [], ["../x"])
            with self.assertRaises(farm.FarmError):
                farm.refuse_bad_book_names(root, ["books/alpha"], [], ["host/none"])

    def test_affected_by_takes_a_host_file(self):
        # decision-keystones: `--affected-by host/bp-node-host` was refused
        # although a test book includes that host file.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed_books(root)
            (root / "host").mkdir()
            (root / "host" / "op-host.lisp").write_text("(in-package \"ACL2\")\n")
            farm.refuse_bad_book_names(root, [], ["host/op-host.lisp"])
            with self.assertRaises(farm.FarmError):
                farm.refuse_bad_book_names(root, [], ["host/none"])

    def test_uncached_list_is_a_count_unless_verbose(self):
        lines = ["publish: 3 books, cache c", "  uncached: books/a",
                 "  uncached: books/b", "  unverified: books/c",
                 "  foreign-local (made in another live worktree): books/d"]
        folded = farm.report_lines(lines)
        self.assertNotIn("  uncached: books/a", folded)
        self.assertIn("  foreign-local (made in another live worktree): books/d",
                      folded)
        self.assertIn("  uncached: 2 books (list with --verbose)", folded)
        self.assertIn("  unverified: 1 books (list with --verbose)", folded)
        self.assertEqual(farm.report_lines(lines, verbose=True), lines)

    def write_run(self, root: Path, manifest: dict, logs: dict[str, str]) -> None:
        run_dir = root / "build/acl2/certify-20260926T000000Z-1"
        run_dir.mkdir(parents=True)
        (run_dir / "manifest.json").write_text(json.dumps(manifest))
        for book, text in logs.items():
            (run_dir / (book.replace("/", "--") + ".certify.log")).write_text(text)
        (root / "build/farm").mkdir(parents=True)
        (root / "build/farm/run-v.log").write_text(
            "Certification evidence: build/acl2/certify-20260926T000000Z-1\n")

    def test_verdict_names_failing_books_first_error_log_and_slow_books(self):
        manifest = {
            "status": "failed", "jobs_effective": 2,
            "book_results": {"books/alpha": "passed", "books/beta": "failed",
                             "tests/acl2/beta-tests": "failed"},
            "book_failures": {
                "books/beta": ["failure marker in this book's log: ACL2 Error"],
                "tests/acl2/beta-tests": ["timed out after 300 s"]},
            "book_wall_seconds": {"books/alpha": 12.5, "books/beta": 3.0},
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.write_run(root, manifest, {
                "books/beta": ("ok\nACL2 Error [Failure] in ( DEFTHM BETA-OK ...): "
                               "See :DOC failure.\n** FAILED **\n"),
            })
            lines = farm.verdict_lines(root, "run-v", 1)
        text = "\n".join(lines)
        self.assertEqual(lines[0], "== verdict run-v: exit 1")
        self.assertIn("certified here: passed 1, failed 2; installed from the "
                      "cache 0", text)
        self.assertIn("FAILED books/beta: ACL2 Error [Failure] in ( DEFTHM BETA-OK",
                      text)
        self.assertIn("books--beta.certify.log", text)
        # No log for the test book: the manifest's reason stands in.
        self.assertIn("FAILED tests/acl2/beta-tests: timed out after 300 s", text)
        self.assertIn("12.5 s  books/alpha  (at 2 jobs)", text)
        self.assertNotIn("books/beta  (at", text)

    def test_verdict_names_installed_books_no_committed_manifest_certified(self):
        # Batch AY, 2026-09-28: a union cite installed books from the cache
        # whose certifying run was never committed; green_check owed them.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "books").mkdir()
            for name in ("cited", "uncited", "top"):
                (root / f"books/{name}.lisp").write_text(f'(in-package "ACL2")\n; {name}\n')
            digest = farm.certs.content_hash(root / "books/cited.lisp")
            archive = root / "planning/evidence/manifests"
            archive.mkdir(parents=True)
            (archive / "certify-20260925T000000Z-9.json").write_text(json.dumps({
                "book_results": {"books/cited": "passed"},
                "source_digests_sha256": {"books/cited.lisp": digest}}))
            self.write_run(root, {
                "status": "passed", "book_results": {"books/top": "passed"},
                "book_provenance": {"books/top": "certified", "books/cited": "installed",
                                    "books/uncited": "installed"}}, {})
            text = "\n".join(farm.verdict_lines(root, "run-v", 0))
            self.assertIn("installed-without-cited-manifest: 1: books/uncited", text)
            self.assertIn("--recertify-uncited", text)
            import certified_claims
            self.assertEqual(certified_claims.uncited_books(
                root, ["books/cited", "books/uncited"]), ["books/uncited"])

    def test_a_signal_exit_is_killed_not_failed(self):
        manifest = {
            "status": "failed", "jobs_effective": 8,
            "book_results": {"books/alpha": "passed", "books/beta": "failed",
                             "books/gamma": "failed"},
            "book_failures": {"books/beta": ["ACL2 exited -9"],
                              "books/gamma": ["ACL2 exited 1"]},
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.write_run(root, manifest, {})
            lines = farm.verdict_lines(root, "run-v", 143)
        text = "\n".join(lines)
        self.assertTrue(lines[0].startswith("== verdict run-v: exit 143 -- KILLED by "
                                            "SIGTERM (earlyoom"), lines[0])
        self.assertIn("not failed", lines[0])
        self.assertIn("KILLED books/beta: ACL2 ended by SIGKILL (no verdict)", text)
        self.assertNotIn("FAILED books/beta", text)
        self.assertIn("FAILED books/gamma", text)
        self.assertIn("passed 1, failed 1, killed 1;", text)
        self.assertEqual(farm.killed_signal(137), 9)
        self.assertEqual(farm.killed_signal(-15), 15)
        self.assertIsNone(farm.killed_signal(1))
        self.assertIsNone(farm.killed_signal("running"))

    def test_a_run_that_certified_nothing_says_so_loudly(self):
        manifest = {"status": "passed", "book_results": {},
                    "book_provenance": {"books/alpha": "installed",
                                        "books/beta": "installed"}}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.write_run(root, manifest, {})
            text = "\n".join(farm.verdict_lines(root, "run-v", 0))
        self.assertIn("ALL 2 BOOKS CAME FROM THE CACHE -- this run certified NOTHING", text)

    def test_verdict_without_a_manifest_is_unknown_not_green(self):
        with tempfile.TemporaryDirectory() as directory:
            lines = farm.verdict_lines(Path(directory), "run-q", 0)
        self.assertIn("verdict is unknown (not green)", "\n".join(lines))

    def test_main_wait_ends_with_the_verdict_block(self):
        fake = Fake(["0"], log=WaitTests.LOG)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            out = io.StringIO()
            with driving(fake, root / "cache"), contextlib.redirect_stdout(out):
                code = farm.main(["wait", "hbox", "run-w", "--root", str(root),
                                  "--poll-seconds", "1"])
            self.assertEqual(code, 0)
            printed = out.getvalue().splitlines()
            start = next(index for index, line in enumerate(printed)
                         if line.startswith("== verdict run-w: exit 0"))
            self.assertIn("verdict is unknown", printed[start + 1])


class RecertifyFromTests(unittest.TestCase):
    """--recertify-from FILE: a book list that no shell word splitting can merge."""

    def submitted(self, text: str, *extra: str) -> tuple[list[str], list[str]]:
        with tempfile.TemporaryDirectory() as directory:
            listing = Path(directory) / "books.txt"
            listing.write_text(text)
            with mock.patch.object(farm, "submit", return_value="run-1") as submit, \
                    mock.patch.object(farm, "honour_reservation"), \
                    contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                code = farm.main(["submit", "hbox", "--recertify-from", str(listing),
                                  "--root", directory, *extra])
            self.assertEqual(code, 0)
            books = submit.call_args.args[2]
            return books, submit.call_args.kwargs["recertify"]

    def test_commas_whitespace_and_comments_read_as_one_list(self):
        books, recertify = self.submitted(
            "books/config, books/stx-lace  # pasted from green_check\n\nbooks/config\n")
        self.assertEqual(recertify, ["books/config", "books/stx-lace"])
        self.assertEqual(books, ["books/config", "books/stx-lace"])

    def test_named_roots_stay_the_roots(self):
        books, recertify = self.submitted("books/config\n", "books/owner")
        self.assertEqual(books, ["books/owner"])
        self.assertEqual(recertify, ["books/config"])

    def test_an_empty_list_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            listing = Path(directory) / "books.txt"
            listing.write_text("# nothing\n")
            with mock.patch.object(farm, "submit") as submit, \
                    contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit) as raised:
                farm.main(["submit", "hbox", "--recertify-from", str(listing),
                           "--root", directory])
            self.assertEqual(raised.exception.code, 2)
            submit.assert_not_called()


class FailedSummaryTests(unittest.TestCase):
    """obstructions-5 item 35: status --failed-summary RUN prints each failed
    book's checkpoint; the run record names the box path as such."""

    LOG = ("(defthm a ...)\n"
           "*** Key checkpoint at the top level: ***\n"
           "Goal'\n(IMPLIES (CONSP X) (EQUAL (F X) (G X)))\n"
           "Summary\n******** FAILED ********\n"
           "later noise\n")

    def test_each_failed_book_with_its_checkpoint(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)

            def fetcher(host, identifier, root_, remote, into):
                directory = into / "certify-x"
                directory.mkdir(parents=True)
                (directory / "manifest.json").write_text(json.dumps({
                    "book_results": {"books/a": "failed", "books/b": "passed"},
                    "book_failures": {"books/a": ["ACL2 exited 1"]}}))
                (directory / "books--a.certify.log").write_text(self.LOG)
                return [directory]
            lines = farm.failed_summary("persvati", "run-1", root, Path("/box/tree"),
                                        fetcher=fetcher)
        text = "\n".join(lines)
        self.assertIn("-- FAILED books/a: ACL2 exited 1", text)
        self.assertIn("   | *** Key checkpoint at the top level: ***", text)
        self.assertIn("   | (IMPLIES (CONSP X) (EQUAL (F X) (G X)))", text)
        self.assertIn("   | ******** FAILED ********", text)
        self.assertNotIn("later noise", text)
        self.assertNotIn("books/b", text)
        self.assertEqual(lines[-1], "== 1 failed book(s)")

    def test_excerpt_without_a_checkpoint_keeps_the_lines_before_the_failure(self):
        with tempfile.TemporaryDirectory() as scratch:
            log = Path(scratch) / "x.log"
            log.write_text("\n".join(f"line {n}" for n in range(30)) + "\nACL2 Error in X\n")
            excerpt = farm.checkpoint_excerpt(log)
        self.assertEqual(excerpt[0], "line 18")
        self.assertEqual(excerpt[-1], "ACL2 Error in X")

    def test_the_record_names_the_box_path(self):
        text = Path(farm.__file__).read_text()
        for field in ('"local_path": str(root)', '"box_path": str(remote)', '"box_log"'):
            self.assertIn(field, text)


class WaitReadsTheRunsOwnDirectoryTests(unittest.TestCase):
    """obstructions-6 item 60: wait polls the directory `status` finds, and never
    answers "unknown" when the box has decided."""

    def recorded_run(self, directory: str) -> Path:
        root = Path(directory)
        (root / "build" / "farm").mkdir(parents=True)
        own = root / "build" / "acl2" / "certify-20260929T010000Z-11"
        later = root / "build" / "acl2" / "certify-20260929T020000Z-22"
        own.mkdir(parents=True)
        later.mkdir(parents=True)
        (own / "manifest.json").write_text(json.dumps(
            {"status": "passed", "finished_utc": "2026-09-29T01:30:00Z"}))
        (later / "manifest.json").write_text(json.dumps({"status": "failed"}))
        os.utime(later, (2e9, 2e9))  # the newest directory is another run's
        (root / "build" / "farm" / "run-20260929T005959Z-ab12.log").write_text(
            f"Certification run: {own}\n")
        return root

    def test_progress_reads_the_directory_the_log_names(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.recorded_run(directory)
            script = farm.progress_script(root, "run-20260929T005959Z-ab12")
            out = subprocess.run(["sh", "-c", script], capture_output=True, text=True).stdout
            progress = farm.parse_progress(out)
            self.assertEqual(progress["MANIFEST"], "passed certify-20260929T010000Z-11")
            self.assertEqual(progress["STATUS"], "running")

    def test_verdict_names_the_boxs_manifest_rather_than_unknown(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "build" / "farm").mkdir(parents=True)
            farm.record_path(root, "run-x").write_text(json.dumps({"host": "hbox"}))
            farm.note_certify_id(root, "run-x", "certify-20260929T010000Z-11")
            farm.note_box_manifest(root, "run-x", "passed")
            lines = farm.verdict_lines(root, "run-x", 0)
            self.assertNotIn("unknown", " ".join(lines))
            self.assertIn("manifest certify-20260929T010000Z-11 passed on the box", lines[1])
            farm.record_path(root, "run-y").write_text(json.dumps({"host": "hbox"}))
            self.assertIn("unknown", " ".join(farm.verdict_lines(root, "run-y", 1)))


class RunsOwnManifestTests(unittest.TestCase):
    """obstructions-7 item 63: `wait` takes only this run's manifest, and
    `status RUN` finds the run's record in any worktree."""

    def tree(self, directory: str, certify: str, final: bool = True) -> Path:
        root = Path(directory)
        (root / "build" / "farm").mkdir(parents=True)
        own = root / "build" / "acl2" / certify
        own.mkdir(parents=True)
        manifest = {"status": "passed"}
        if final:
            manifest["finished_utc"] = "2026-09-29T01:30:00Z"
        (own / "manifest.json").write_text(json.dumps(manifest))
        return root

    def progress(self, root: Path, run: str) -> dict:
        (root / "build" / "farm" / f"{run}.log").write_text("starting\n")
        out = subprocess.run(["sh", "-c", farm.progress_script(root, run)],
                             capture_output=True, text=True).stdout
        return farm.parse_progress(out)

    def test_a_previous_runs_final_manifest_is_not_this_runs_verdict(self):
        with tempfile.TemporaryDirectory() as directory:
            # The only directory is an hour older than the run: its runner
            # has not made one yet (operability-3).
            root = self.tree(directory, "certify-20260929T010000Z-11")
            progress = self.progress(root, "run-20260929T020000Z-ab12")
            self.assertEqual(progress.get("MANIFEST", ""), "")
            self.assertEqual(progress.get("MARKERS"), "0")

    def test_this_runs_newest_directory_counts_within_the_clock_skew(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory, "certify-20260929T020100Z-11")
            progress = self.progress(root, "run-20260929T020000Z-ab12")
            self.assertEqual(progress["MANIFEST"], "passed certify-20260929T020100Z-11")
        with tempfile.TemporaryDirectory() as directory:
            # A box clock a minute behind the laptop's is still this run.
            root = self.tree(directory, "certify-20260929T015900Z-11")
            progress = self.progress(root, "run-20260929T020000Z-ab12")
            self.assertEqual(progress["MANIFEST"], "passed certify-20260929T015900Z-11")

    def test_status_run_finds_the_record_in_another_worktree(self):
        with tempfile.TemporaryDirectory() as mine, tempfile.TemporaryDirectory() as theirs:
            other = Path(theirs)
            (other / "build" / "farm").mkdir(parents=True)
            farm.record_path(other, "run-x").write_text(json.dumps(
                {"host": "hbox", "box_path": "/tank/fn/gates/theirs"}))

            def listing(*_args, **_kwargs):
                return subprocess.CompletedProcess(
                    [], 0, f"worktree {mine}\nHEAD abc\n\nworktree {other}\nHEAD def\n", "")
            where, record = farm.find_run_record(Path(mine), "run-x", runner=listing)
            self.assertEqual(where, other)
            self.assertEqual(record["box_path"], "/tank/fn/gates/theirs")
            self.assertEqual(farm.find_run_record(Path(mine), "run-none", runner=listing),
                             (Path(mine), {}))

    def test_status_run_prints_only_that_run_and_its_certify_id(self):
        rows = [{"run_id": "run-a", "state": "0", "data": "manifest", "manifest": "passed",
                 "passed": 3, "failed": 0, "certify_id": None},
                {"run_id": "run-b", "state": "running", "data": "missing", "certify_id": None}]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "build" / "farm").mkdir(parents=True)
            farm.record_path(root, "run-a").write_text(json.dumps(
                {"host": "persvati", "box_path": "/home/u/fn-gates/x"}))
            calls = []

            def fake_ssh(host, script, check=False):
                calls.append((host, script))
                if script.startswith("cd ") and "grep -m1 -E" in script:
                    return subprocess.CompletedProcess([], 0, "Certification run: /x/build/acl2/"
                                                       "certify-20260929T010000Z-7\n", "")
                return subprocess.CompletedProcess([], 0, json.dumps(rows), "")
            out = io.StringIO()
            with mock.patch.object(farm, "ssh", fake_ssh), contextlib.redirect_stdout(out):
                self.assertEqual(farm.run_status(None, "run-a", root), 0)
            text = out.getvalue()
            self.assertIn("run-a on persvati:/home/u/fn-gates/x", text)
            self.assertNotIn("run-b", text)
            self.assertIn("certify id certify-20260929T010000Z-7", text)
            self.assertEqual(farm.run_record(root, "run-a")["certify_id"],
                             "certify-20260929T010000Z-7")
            self.assertTrue(all(host == "persvati" for host, _ in calls))


if __name__ == "__main__":
    unittest.main()
