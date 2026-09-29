"""tools/check_steps.py: every step of `make check` runs, and the table names the red ones."""
from __future__ import annotations

import io
import json
import pathlib
import shlex
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
            use_cache: bool = True) -> tuple[int, str, list[dict]]:
    out = io.StringIO()
    with redirect_stdout(out):
        verdict = check_steps.execute(directory, jobs, use_cache, cache)
    return verdict, out.getvalue(), check_steps.read_results(directory)


class ExecuteTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
