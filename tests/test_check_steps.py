"""tools/check_steps.py: every step of `make check` runs, and the table names the red ones."""
from __future__ import annotations

import io
import json
import pathlib
import shlex
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import check_steps  # noqa: E402

PY = sys.executable


class CheckStepsTests(unittest.TestCase):
    def test_a_red_step_does_not_stop_the_next_and_the_summary_fails(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = pathlib.Path(temporary) / "steps"
            out = io.StringIO()
            with redirect_stdout(out):
                self.assertEqual(check_steps.main(["begin", str(directory)]), 0)
                self.assertEqual(check_steps.main(
                    ["run", str(directory), "--", PY, "-c",
                     "print('checked 3 files'); print('harness_check: arity mismatch at x:1');"
                     " raise SystemExit(2)"]), 0)
                self.assertEqual(check_steps.main(
                    ["run", str(directory), "--", PY, "-c", "print('all green')"]), 0)
                verdict = check_steps.main(["summary", str(directory)])
            self.assertEqual(verdict, 1)
            text = out.getvalue()
            self.assertIn("all green", text)
            self.assertIn("== check: 2 steps, 1 failed", text)
            self.assertIn("exit 2", text)
            self.assertIn("harness_check: arity mismatch at x:1", text)
            rows = check_steps.read_results(directory)
            self.assertEqual([row["exit"] for row in rows], [2, 0])
            self.assertEqual(rows[1]["finding"], "")

    def test_all_green_passes_and_nothing_recorded_fails(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = pathlib.Path(temporary)
            with redirect_stdout(io.StringIO()):
                self.assertEqual(check_steps.summary(directory), 1)
                check_steps.run(directory, [PY, "-c", "pass"])
                self.assertEqual(check_steps.summary(directory), 0)

    def test_names_and_findings(self):
        self.assertEqual(check_steps.step_name(["python3", "tools/cite_check.py", "--summary"]),
                         "cite_check")
        self.assertEqual(check_steps.step_name(
            ["python3", "-m", "unittest", "-q", "tests.test_x.Y"]), "tests.test_x.Y")
        self.assertEqual(check_steps.first_finding(["ok", "3 stale citations", "tail"]),
                         "3 stale citations")
        self.assertEqual(check_steps.first_finding(["ok", "", "last words", ""]), "last words")
        # harness_check: the counted finding, not a waiver line that says "not"
        self.assertEqual(check_steps.first_finding(
            ["harness_check acl2-arity: 2 findings (11769 definitions)",
             "  waiver-ok x.py:1: environment -- it reads a command, not its exit"]),
            "harness_check acl2-arity: 2 findings (11769 definitions)")
        self.assertEqual(check_steps.first_finding(
            ["spec-cite: 5721 citations; 323 known stale",
             "  UNDEFINED fn-x: specs/host.md:596"]), "UNDEFINED fn-x: specs/host.md:596")


def plan(directory: pathlib.Path, *commands: list[str]) -> None:
    check_steps.begin(directory)
    for command in commands:
        check_steps.add(directory, command)


def execute(directory: pathlib.Path, cache: pathlib.Path, jobs: int = 3,
            use_cache: bool = True, **scoped) -> tuple[int, str, list[dict]]:
    out = io.StringIO()
    with redirect_stdout(out):
        verdict = check_steps.execute(directory, jobs, use_cache, cache, **scoped)
    return verdict, out.getvalue(), check_steps.read_results(directory)


class ExecuteBase(unittest.TestCase):
    """`execute`: parallel, input-hashed, same table.  Inputs live under build/,
    since the trace ignores reads under the temporary directories."""

    def setUp(self):
        (ROOT / "build").mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(dir=ROOT / "build",
                                                     prefix="test-check-steps-")
        self.base = pathlib.Path(self.temporary.name)
        self.steps, self.cache = self.base / "steps", self.base / "cache"
        self.data = self.base / "data"
        self.data.mkdir()

    def tearDown(self):
        self.temporary.cleanup()

    def reader(self, name: str) -> list[str]:
        return [PY, "-c", f"import pathlib; print('read', pathlib.Path({str(self.data / name)!r})"
                          ".read_text().strip())"]



class ExecuteTests(ExecuteBase):
    """The execute tests."""

    def test_parallel_rows_in_plan_order_and_red_is_red(self):
        (self.data / "a").write_text("alpha\n")
        plan(self.steps, [PY, "-c", "import time; time.sleep(0.3); print('slow')"],
             [PY, "-c", "print('boom: 1 failures'); raise SystemExit(4)"], self.reader("a"))
        verdict, text, rows = execute(self.steps, self.cache)
        self.assertEqual(verdict, 1)
        self.assertEqual([row["index"] for row in rows], [0, 1, 2])
        self.assertEqual([row["exit"] for row in rows], [0, 4, 0])
        self.assertIn("== check: 3 steps, 1 failed (jobs 3", text)
        self.assertIn("boom: 1 failures", rows[1]["finding"])
        logs = sorted((self.steps / "logs").iterdir())
        self.assertEqual(len(logs), 3)
        self.assertIn("read alpha", logs[2].read_text())

    def test_unchanged_inputs_are_cached_and_a_change_reruns(self):
        (self.data / "a").write_text("alpha\n")
        plan(self.steps, self.reader("a"))
        self.assertEqual(execute(self.steps, self.cache)[0], 0)
        verdict, text, rows = execute(self.steps, self.cache)
        self.assertEqual(verdict, 0)
        self.assertTrue(rows[0].get("cached", "").startswith("cached (inputs unchanged since "))
        self.assertIn("read alpha", text)  # the stored output is replayed
        self.assertIn("1 cached", text)
        (self.data / "a").write_text("alphb\n")  # same size: the digest decides
        verdict, text, rows = execute(self.steps, self.cache)
        self.assertFalse(rows[0].get("cached"))
        self.assertIn("read alphb", text)
        verdict, text, rows = execute(self.steps, self.cache, use_cache=False)
        self.assertFalse(rows[0].get("cached"))
        self.assertIn("cache off", text)

    def test_an_input_rewritten_while_the_step_ran_is_not_cached(self):
        """S055: the key is taken after the step exits.  A file rewritten
        (same size) after the step read it would key the step's PASS to bytes
        it never judged, and the next run would replay "read one" over a
        tree that says "two"."""
        import threading
        (self.data / "a").write_text("one\n")
        slow = [PY, "-c", f"import pathlib, time; print('read', pathlib.Path("
                          f"{str(self.data / 'a')!r}).read_text().strip()); time.sleep(1.5)"]
        plan(self.steps, slow)
        rewrite = threading.Timer(0.8, (self.data / "a").write_text, args=("two\n",))
        rewrite.start()
        try:
            verdict, text, rows = execute(self.steps, self.cache)
        finally:
            rewrite.join()
        self.assertEqual(verdict, 0)
        self.assertIn("read one", text)
        self.assertIn("changed while it ran", text)
        verdict, text, rows = execute(self.steps, self.cache)
        self.assertFalse(rows[0].get("cached"))
        self.assertIn("read two", text)
        # Settled now: the next run may replay it.
        self.assertTrue(execute(self.steps, self.cache)[2][0].get("cached"))

    def test_a_hazard_drops_both_steps_cache_entries(self):
        """S055: a write hazard found after the run drops the writer's and the
        reader's entries, not only a warning."""
        target = self.data / "shared"
        target.write_text("old")
        writer = [PY, "-c", f"import time; time.sleep(0.2); open({str(target)!r}, 'w').write('new')"]
        reader = [PY, "-c", f"print(open({str(target)!r}).read())"]
        plan(self.steps, reader, writer)
        verdict, text, rows = execute(self.steps, self.cache)
        self.assertIn(f"wrote {target} which", text)
        for command in (reader, writer):
            self.assertFalse(
                (self.cache / "steps" / f"{check_steps.step_key(command)}.json").exists(),
                shlex.join(command))

    def test_a_listing_or_existence_change_reruns(self):
        lister = [PY, "-c", f"import os; print(sorted(os.listdir({str(self.data)!r})))"]
        prober = [PY, "-c", f"import os; print(os.path.exists({str(self.data / 'b')!r}))"]
        plan(self.steps, lister, prober)
        execute(self.steps, self.cache)
        rows = execute(self.steps, self.cache)[2]
        self.assertTrue(all(row.get("cached") for row in rows))
        (self.data / "b").write_text("")
        rows = execute(self.steps, self.cache)[2]
        self.assertEqual([bool(row.get("cached")) for row in rows], [False, False])

    def test_failures_and_untraceable_children_are_never_cached(self):
        (self.data / "a").write_text("x")
        failing = [PY, "-c", f"open({str(self.data / 'a')!r}).read(); raise SystemExit(1)"]
        child = [PY, "-c", "import subprocess; subprocess.run(['true'])"]
        blind = [PY, "-c", "import subprocess, sys; subprocess.run([sys.executable, '-c', "
                           "'pass'], env={})"]
        plan(self.steps, failing, child, blind)
        execute(self.steps, self.cache)
        verdict, text, rows = execute(self.steps, self.cache)
        self.assertEqual([bool(row.get("cached")) for row in rows], [False, False, False])
        self.assertIn("not cacheable (child process true)", text)
        self.assertIn("not cacheable (python child without the tracer", text)

    def test_a_python_child_is_traced(self):
        (self.data / "a").write_text("one")
        inner = f"print(open({str(self.data / 'a')!r}).read())"
        plan(self.steps, [PY, "-c", f"import subprocess, sys; subprocess.run([sys.executable, "
                                    f"'-c', {inner!r}])"])
        execute(self.steps, self.cache)
        self.assertTrue(execute(self.steps, self.cache)[2][0].get("cached"))
        (self.data / "a").write_text("two")
        verdict, text, rows = execute(self.steps, self.cache)
        self.assertFalse(rows[0].get("cached"))
        self.assertIn("two", text)

    def test_an_undeclared_writer_is_learned_and_runs_first(self):
        target = self.data / "shared"
        writer = [PY, "-c", f"open({str(target)!r}, 'w').write('w')"]
        reader = [PY, "-c", f"import os, time; time.sleep(0.3); print(os.path.exists({str(target)!r}))"]
        plan(self.steps, reader, writer)
        verdict, text, rows = execute(self.steps, self.cache, use_cache=False)
        self.assertIn(f"wrote {target} which", text)
        learned = json.loads((self.cache / "writers.json").read_text())
        self.assertEqual(learned, [shlex.join(writer)])
        verdict, text, rows = execute(self.steps, self.cache, use_cache=False)
        self.assertNotIn("WARNING", text)
        self.assertLess(text.index("== " + check_steps.step_name(writer)),
                        text.index("-- started"))  # alone, before the fan-out
        target.unlink()
        plan(self.steps, reader, [PY, "-c", "pass"])  # the writer is gone
        execute(self.steps, self.cache, use_cache=False)
        plan(self.steps, reader, writer)
        execute(self.steps, self.cache, use_cache=False)  # conflicts again: stays learned
        self.assertEqual(json.loads((self.cache / "writers.json").read_text()), [shlex.join(writer)])
        plan(self.steps, writer)  # alone in the plan: nothing to conflict with
        verdict, text, rows = execute(self.steps, self.cache, use_cache=False)
        self.assertIn("fans out again", text)
        self.assertEqual(json.loads((self.cache / "writers.json").read_text()), [])

    def test_a_git_read_is_replayed_to_key_the_step(self):
        probe = [PY, "-c", f"import subprocess; print(subprocess.run(['git', '-C', {str(ROOT)!r}, "
                           "'rev-parse', 'HEAD'], capture_output=True, text=True).stdout)"]
        plan(self.steps, probe)
        execute(self.steps, self.cache)
        self.assertTrue(execute(self.steps, self.cache)[2][0].get("cached"))
        entry = json.loads(next((self.cache / "steps").iterdir()).read_text())
        self.assertEqual(entry["inputs"]["g"][0][:2], [str(ROOT), ["rev-parse", "HEAD"]])

    def test_a_git_read_that_timed_out_is_never_cached(self):
        """S055: a git read that timed out keyed the step as "error ..." and
        the same timeout next run matched it, replaying a PASS."""
        import subprocess
        from unittest import mock
        probe = [PY, "-c", f"import subprocess; print(subprocess.run(['git', '-C', {str(ROOT)!r}, "
                           "'rev-parse', 'HEAD'], capture_output=True, text=True).stdout)"]
        plan(self.steps, probe)
        real = subprocess.run

        def slow_git(argv, *args, **kwargs):
            if argv[:1] == ["git"] and kwargs.get("timeout") == 120:
                raise subprocess.TimeoutExpired(argv, 120)
            return real(argv, *args, **kwargs)
        with mock.patch.object(check_steps.subprocess, "run", side_effect=slow_git):
            verdict, text, rows = execute(self.steps, self.cache)
            self.assertIn("did not answer", text)
            verdict, text, rows = execute(self.steps, self.cache)
            self.assertFalse(rows[0].get("cached"))

    def test_a_copied_tree_is_read_not_written(self):
        (self.data / "src").mkdir()
        (self.data / "src" / "f").write_text("f")
        copier = [PY, "-c", "import shutil, tempfile; "
                            f"shutil.copytree({str(self.data / 'src')!r}, tempfile.mkdtemp() + '/c')"]
        reader = [PY, "-c", f"print(open({str(self.data / 'src' / 'f')!r}).read())"]
        plan(self.steps, copier, reader)
        verdict, text, rows = execute(self.steps, self.cache)
        self.assertNotIn("WARNING", text)
        self.assertTrue(execute(self.steps, self.cache)[2][0].get("cached"))
        (self.data / "src" / "f").write_text("g")
        self.assertFalse(execute(self.steps, self.cache)[2][0].get("cached"))

    def test_steps_that_read_a_shared_cache_wait_for_its_warm_up(self):
        (ROOT / "build" / "cache").mkdir(parents=True, exist_ok=True)
        shared = pathlib.Path(tempfile.mkdtemp(dir=check_steps.SHARED_CACHES[0].rstrip("/"),
                                               prefix="test-check-steps-"))
        self.addCleanup(shutil.rmtree, shared, True)
        entry = shared / "entry"
        warm = [PY, "-c", f"import time, os; time.sleep(0.4); "
                          f"open({str(entry) + '.tmp'!r}, 'w').write('warm'); "
                          f"os.replace({str(entry) + '.tmp'!r}, {str(entry)!r})"]
        user = [PY, "-c", f"import os; p = {str(entry)!r}; "
                          "print('user saw', open(p).read() if os.path.exists(p) else 'nothing')"]
        check_steps.begin(self.steps)
        check_steps.add(self.steps, warm, warm=True)
        check_steps.add(self.steps, user)
        for _ in range(2):  # a step never traced waits; then its trace says so
            entry.unlink(missing_ok=True)
            verdict, text, rows = execute(self.steps, self.cache, use_cache=False)
            self.assertIn("user saw warm", text)
        worlds = json.loads((self.cache / "worlds.json").read_text())
        self.assertEqual(sorted(worlds.values()), [True, True])
        rows = execute(self.steps, self.cache)[2]
        self.assertEqual([bool(row.get("cached")) for row in rows], [False, True])  # warm-ups never

    def test_git_replay_is_for_reads_only(self):
        self.assertTrue(check_steps.git_replayable(["rev-parse", "HEAD"]))
        self.assertTrue(check_steps.git_replayable(["--no-pager", "log", "-1", "--", "x"]))
        self.assertFalse(check_steps.git_replayable(["add", "-f", "x"]))
        self.assertFalse(check_steps.git_replayable(["cat-file", "--batch"]))
        self.assertFalse(check_steps.git_replayable(["check-ignore", "--stdin"]))
        self.assertEqual(check_steps.git_command("/a", ["-C", "b", "log", "-1"]),
                         ["/a/b", ["log", "-1"]])
        self.assertFalse(check_steps.git_replayable(["-c", "core.pager=x", "log"]))
        self.assertFalse(check_steps.git_replayable(["config", "user.name", "x"]))
        self.assertTrue(check_steps.git_replayable(["config", "--get", "user.name"]))


    # ------------------------------------------------------------ scoped runs

    def rel(self, name: str) -> str:
        return str((self.data / name).relative_to(ROOT))

    def scoped(self, paths: dict[str, str], old_dirs: set[str] | None = None, **more):
        changed = check_steps.Changes({self.rel(k) if "/" not in k else k: v
                                       for k, v in paths.items()}, old_dirs)
        return execute(self.steps, self.cache, since="BASE", changed=changed, **more)

    def ran(self, rows: list[dict]) -> list[bool]:
        """Selected, whether it then ran or replayed its cached pass."""
        return [not row.get("skipped") for row in rows]

    def test_a_scoped_run_skips_steps_the_change_cannot_reach(self):
        (self.data / "a").write_text("alpha\n")
        (self.data / "b").write_text("beta\n")
        plan(self.steps, self.reader("a"), self.reader("b"))
        self.assertEqual(execute(self.steps, self.cache)[0], 0)
        verdict, text, rows = self.scoped({"a": "M"})
        self.assertEqual(verdict, 0)
        self.assertIn("1 of 2 steps can be affected", text)
        self.assertFalse(rows[0].get("skipped"))
        self.assertTrue(rows[1]["skipped"].startswith("skipped (unaffected by the 1 path(s)"))
        self.assertIn("1 skipped", text)
        self.assertNotIn("read beta", text)
        # nothing changed: nothing can be affected
        self.assertEqual([bool(r.get("skipped")) for r in self.scoped({})[2]], [True, True])

    def test_a_failed_step_keeps_its_inputs_so_a_docs_change_skips_it(self):
        (self.data / "a").write_text("alpha\n")
        red = [PY, "-c", f"import sys; print(open({str(self.data / 'a')!r}).read(), 'NOT RUN');"
                         " sys.exit(2)"]
        plan(self.steps, red)
        self.assertEqual(execute(self.steps, self.cache)[0], 1)
        self.assertEqual(list((self.cache / "steps").glob("*")), [])  # a failure is not cached
        verdict, text, rows = self.scoped({"other": "M"})
        self.assertEqual((verdict, [bool(r.get("skipped")) for r in rows]), (0, [True]))
        verdict, text, rows = self.scoped({"a": "M"})
        self.assertEqual((verdict, self.ran(rows)), (1, [True]))

    def test_a_step_never_traced_or_untraceable_always_runs(self):
        (self.data / "a").write_text("alpha\n")
        shell = [PY, "-c", "import subprocess; subprocess.run(['true'])"]
        plan(self.steps, self.reader("a"), shell)
        rows = self.scoped({"zzz": "M"})[2]  # nothing traced yet
        self.assertEqual(self.ran(rows), [True, True])
        rows = self.scoped({"zzz": "M"})[2]  # the reader is now known; the shell never is
        self.assertEqual([bool(r.get("skipped")) for r in rows], [True, False])
        record = json.loads(next(p for p in (self.cache / "scope").iterdir()
                                 if "subprocess" in p.read_text()).read_text())
        self.assertEqual(record["x"], "child process true")

    def test_a_changed_command_or_the_tracer_reaches_every_step(self):
        (self.data / "a").write_text("alpha\n")
        plan(self.steps, self.reader("a"))
        execute(self.steps, self.cache)
        for path in ("tools/check_steps.py", "tools/check_trace/sitecustomize.py"):
            self.assertEqual(self.ran(self.scoped({path: "M"})[2]), [True], path)
        check_steps.add(self.steps, [PY, "-c", "print('another')"])
        self.assertEqual(self.ran(self.scoped({"zzz": "M"})[2]), [False, True])

    def test_an_added_or_removed_file_moves_listings_an_edit_does_not(self):
        (self.data / "dir").mkdir()
        (self.data / "dir" / "x").write_text("x")
        lister = [PY, "-c", f"import os; print(sorted(os.listdir({str(self.data / 'dir')!r})))"]
        plan(self.steps, lister)
        execute(self.steps, self.cache)
        here = self.rel("dir")
        self.assertEqual(self.ran(self.scoped({here + "/x": "M"})[2]), [False])
        self.assertEqual(self.ran(self.scoped({here + "/y": "A"}, {here})[2]), [True])
        self.assertEqual(self.ran(self.scoped({here + "/x": "D"}, {here})[2]), [True])
        self.assertEqual(self.ran(self.scoped({"elsewhere/y": "A"}, {"elsewhere"})[2]), [False])

    def test_which_directories_a_change_lists(self):
        Changes = check_steps.Changes
        old = {"docs", "docs/a", "books"}
        self.assertEqual(Changes({"docs/a/n.md": "A"}, old).listed, {"docs/a"})
        self.assertEqual(Changes({"docs/new/deep/n.md": "A"}, old).listed, {"docs"})
        self.assertEqual(Changes({"top/n.md": "A"}, old).listed, {"."})
        self.assertEqual(Changes({"docs/a/n.md": "M"}, old).listed, set())

    def test_a_git_read_is_reached_only_by_what_can_move_it(self):
        git_reached, Changes = check_steps.git_reached, check_steps.Changes
        edit = Changes({"docs/x.md": "M"}, {"docs"})
        add = Changes({"docs/y.md": "A"}, {"docs"})
        self.assertEqual(git_reached(["ls-files", "--", "books"], edit), "")
        self.assertEqual(git_reached(["ls-files"], edit), "")
        self.assertEqual(git_reached(["ls-files"], add), "git ls-files: docs/y.md A")
        self.assertEqual(git_reached(["ls-files", "books"], add), "")
        self.assertEqual(git_reached(["ls-files", "docs"], add), "git ls-files: docs/y.md A")
        self.assertEqual(git_reached(["ls-files", "-s"], add), "git ls-files -s")  # blob ids
        self.assertEqual(git_reached(["rev-parse", "--show-toplevel"], edit), "")
        self.assertEqual(git_reached(["config", "--get", "user.name"], edit), "")
        self.assertTrue(git_reached(["rev-parse", "HEAD"], edit))
        self.assertTrue(git_reached(["log", "-1"], edit))
        self.assertEqual(git_reached(["log", "-1"], Changes({})), "")

    def test_changed_paths_of_a_real_diff(self):
        import subprocess
        repo = self.base / "repo"
        (repo / "docs").mkdir(parents=True)
        (repo / "books").mkdir()

        def git(*argv):
            subprocess.run(["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@t",
                            "-c", "commit.gpgsign=false", *argv], check=True,
                           capture_output=True)
        git("init", "-q")
        (repo / "docs" / "a.md").write_text("a")
        (repo / "books" / "b.lisp").write_text("b")
        git("add", ".")
        git("commit", "-qm", "base")
        git("tag", "base")
        (repo / "docs" / "a.md").write_text("a2")
        (repo / "docs" / "new").mkdir()
        (repo / "docs" / "new" / "n.md").write_text("n")
        git("add", ".")
        git("commit", "-qm", "docs")
        (repo / "books" / "b.lisp").unlink()
        (repo / "books" / "u.lisp").write_text("untracked")
        old, check_steps.ROOT = check_steps.ROOT, repo
        try:
            changed = check_steps.changed_paths("base")
            self.assertEqual(changed.paths, {"docs/a.md": "M", "docs/new/n.md": "A",
                                             "books/b.lisp": "D", "books/u.lisp": "A"})
            self.assertEqual(changed.listed, {"docs", "books"})
            self.assertEqual(check_steps.changed_paths("HEAD").paths,
                             {"books/b.lisp": "D", "books/u.lisp": "A"})
        finally:
            check_steps.ROOT = old

    def test_an_unreadable_cache_entry_falls_back_to_the_last_pass(self):
        (self.data / "a").write_text("alpha\n")
        plan(self.steps, self.reader("a"))
        execute(self.steps, self.cache)
        shutil.rmtree(self.cache / "scope")  # a cache from before scope records
        self.assertEqual(self.ran(self.scoped({"zzz": "M"})[2]), [False])
        self.assertEqual(self.ran(self.scoped({"a": "M"})[2]), [True])


TABLE = """remote_check: noise
== check: 6 steps, 3 failed (jobs 12, wall 99.0 s, 0 cached)
  ledger          ok          130.8 s
  host_check      exit 2        0.1 s  host_check: NOT RUN host/native/build-dtn.lisp
  host_check      exit 1       36.6 s  FAIL host/native/owner.lisp:645 fn-x: not defined
  host_check      ok           58.2 s
  reach_check     exit 1       71.9 s  reach_check: NEW unreachable subject -- books/a.lisp: f (PRF-322)
  docs_check      ok            1.6 s  cached (inputs unchanged since abc)
make: *** [Makefile:2677: check] Error 1
"""


def row(step: str, exit: int = 0, finding: str = "") -> dict:
    return {"step": step, "exit": exit, "finding": finding, "seconds": 1.0}


class BaselineTests(unittest.TestCase):
    def test_the_table_is_read_out_of_a_runner_log(self):
        rows = check_steps.read_baseline(TABLE)
        self.assertEqual([(r["step"], r["red"]) for r in rows],
                         [("ledger", False), ("host_check", True), ("host_check", True),
                          ("host_check", False), ("reach_check", True), ("docs_check", False)])
        self.assertEqual(rows[1]["finding"], "host_check: NOT RUN host/native/build-dtn.lisp")
        # the last table wins; text with no table has no rows
        self.assertEqual(len(check_steps.read_baseline(TABLE + TABLE.replace("host_check", "hc"))), 6)
        self.assertEqual(check_steps.read_baseline("nothing here\n"), [])

    def test_a_table_this_tool_writes_is_one_it_reads(self):
        rows = [{**row("a"), "cached": "cached (inputs unchanged since x)"},
                row("b", 2, "b: NOT RUN"), {**row("c"), "skipped": "skipped (unaffected)"}]
        text = "\n".join(check_steps.table_lines(rows, " (jobs 1, wall 1.0 s)"))
        self.assertEqual([(r["step"], r["red"], r["finding"])
                          for r in check_steps.read_baseline(text)],
                         [("a", False, "cached (inputs unchanged since x)"), ("b", True, "b: NOT RUN"),
                          ("c", False, "skipped (unaffected)")])

    def test_only_a_red_the_baseline_did_not_have_is_new(self):
        known = check_steps.read_baseline(TABLE)
        # the same reds, their line numbers drifted: nothing new
        again = [row("ledger"), row("host_check", 2, "host_check: NOT RUN host/native/build-dtn.lisp"),
                 row("host_check", 1, "FAIL host/native/owner.lisp:700 fn-x: not defined"),
                 row("host_check"), row("reach_check", 1, "reach_check: NEW unreachable subject -- "
                                                          "books/z.lisp: g (PRF-9)")]
        self.assertEqual(check_steps.new_reds(again, known), [])
        # a green step gone red; a step the baseline never had
        fresh = check_steps.new_reds(again + [row("docs_check", 1, "stale"),
                                              row("brand_new", 3, "x")], known)
        self.assertEqual([r["step"] for r in fresh], ["docs_check", "brand_new"])
        # the OK instance of a repeated name going red is new; the name's count decides
        three = [row("host_check", 2, "host_check: NOT RUN host/native/build-dtn.lisp"),
                 row("host_check", 1, "FAIL host/native/owner.lisp:700 fn-x: not defined"),
                 row("host_check", 1, "FAIL something else entirely")]
        self.assertEqual([r["finding"] for r in check_steps.new_reds(three, known)],
                         ["FAIL something else entirely"])
        # one step, red on a different line than the baseline: the same red
        self.assertEqual(check_steps.new_reds([row("reach_check", 1, "a different complaint")],
                                              known), [])
        # fewer reds than the baseline: nothing new
        self.assertEqual(check_steps.new_reds([row("ledger")], known), [])


class BaselineRunTests(ExecuteBase):
    """`execute --baseline` / `--write-baseline`: the verdict is the new reds."""

    def run_with(self, baseline_text: str | None, **more):
        if baseline_text is not None:
            (self.base / "baseline.txt").write_text(baseline_text)
        return execute(self.steps, self.cache, baseline=self.base / "baseline.txt", **more)

    def test_a_known_red_passes_and_a_new_red_fails(self):
        (self.data / "a").write_text("alpha\n")
        (self.data / "red.py").write_text("print('boom: 1 failures'); raise SystemExit(4)\n")
        (self.data / "reads.py").write_text(f"print(open({str(self.data / 'a')!r}).read())\n")
        plan(self.steps, [PY, str(self.data / "red.py")], [PY, str(self.data / "reads.py")])
        written = self.base / "out" / "baseline.txt"
        verdict, text, rows = execute(self.steps, self.cache, write_baseline=written)
        self.assertEqual(verdict, 1)
        self.assertIn(f"step table written to {written}", text)
        self.assertEqual([r["red"] for r in check_steps.read_baseline(written.read_text())],
                         [True, False])
        # the table we wrote is a baseline: its red is carried over, exit 0
        verdict, text, rows = self.run_with(written.read_text())
        self.assertEqual(verdict, 0)
        self.assertIn("no new reds vs baseline", text)
        self.assertNotIn("NEW reds", text)
        self.assertIn("1 carried over", text)
        # a baseline with that step green: the red is new
        verdict, text, rows = self.run_with(TABLE.replace("host_check", "other"))
        self.assertEqual(verdict, 1)
        self.assertIn("NEW reds vs baseline: ", text)
        # a step fixed since the baseline is named
        text_fixed = "== check: 1 steps, 1 failed\n  " + rows[1]["step"] + "  exit 1  1.0 s  x\n"
        verdict, text, rows = self.run_with(text_fixed)
        self.assertIn("1 fixed", text)

    def test_an_unreadable_or_empty_baseline_fails_closed(self):
        (self.data / "a").write_text("alpha\n")
        plan(self.steps, self.reader("a"))
        verdict, text, rows = execute(self.steps, self.cache, baseline=self.base / "absent.txt")
        self.assertEqual(verdict, 1)
        self.assertIn("cannot read the baseline", text)
        verdict, text, rows = self.run_with("no table\n")
        self.assertEqual(verdict, 1)
        self.assertIn("no step table in the baseline", text)

    def test_skipped_steps_are_never_new_reds(self):
        (self.data / "a").write_text("alpha\n")
        (self.data / "red.py").write_text(
            f"print(open({str(self.data / 'a')!r}).read(), 'bad'); raise SystemExit(3)\n")
        plan(self.steps, [PY, str(self.data / "red.py")])
        execute(self.steps, self.cache)
        changed = check_steps.Changes({"unrelated": "M"})
        verdict, text, rows = self.run_with(TABLE, since="BASE", changed=changed)
        self.assertEqual((verdict, rows[0].get("skipped") is not None), (0, True))
        self.assertIn("no new reds vs baseline", text)


if __name__ == "__main__":
    unittest.main()
