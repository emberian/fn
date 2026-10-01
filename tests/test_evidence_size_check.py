"""Evidence-size rules exercised only in temporary trees, never the repository."""
import contextlib
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import evidence_size_check as evidence  # noqa: E402


class Rules(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def log(self, name, lines):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"line\n" * lines)
        return path

    def baseline(self, *names):
        path = self.root / evidence.BASELINE
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("# fixture baseline\n" + "\n".join(sorted(names)) + "\n")

    def run_tool(self, *arguments):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = evidence.main(list(arguments), self.root)
        return code, output.getvalue()

    def test_1001_lines_refused(self):
        self.log("planning/large.log", 1001)
        self.assertEqual(self.run_tool(), (1,
            "REFUSED planning/large.log: 1001 lines (limit 1000): commit a summary + "
            "the tail + where the full log lives (MODE §5)\n"
            "evidence_size_check: 1 raw logs, 1 refused, 0 baselined, 0 stale\n"))

    def test_1000_lines_accepted(self):
        self.log("planning/exact.log", 1000)
        self.assertEqual(self.run_tool(), (0,
            "evidence_size_check: 1 raw logs, 0 refused, 0 baselined, 0 stale\n"))

    def test_data_and_files_outside_planning_ignored(self):
        for suffix in (".json", ".md", ".log.gz", ".png", ".lisp"):
            self.log("planning/data" + suffix, 5000)
        self.log("docs/outside.log", 5000)
        self.assertEqual(self.run_tool(), (0,
            "evidence_size_check: 0 raw logs, 0 refused, 0 baselined, 0 stale\n"))

    def test_all_raw_suffixes_checked(self):
        for suffix in evidence.RAW_LOG_SUFFIXES:
            self.log("planning/nested/raw" + suffix, 1001)
        result = evidence.check(root=self.root)
        self.assertEqual((result.checked, result.refused), (7, 7))

    def test_baselined_oversized_accepted(self):
        self.log("planning/old.log", 1001)
        self.baseline("planning/old.log")
        self.assertEqual(self.run_tool(), (0,
            "evidence_size_check: 1 raw logs, 0 refused, 1 baselined, 0 stale\n"))

    def test_baselined_small_and_missing_stale(self):
        self.log("planning/small.log", 1000)
        self.baseline("planning/small.log", "planning/missing.log")
        self.assertEqual(self.run_tool(), (1,
            "STALE planning/missing.log: in the baseline but gone: "
            "drop it (the baseline only shrinks)\n"
            "STALE planning/small.log: in the baseline but now 1000 lines: "
            "drop it (the baseline only shrinks)\n"
            "evidence_size_check: 1 raw logs, 0 refused, 0 baselined, 2 stale\n"))

    def test_write_baseline_sorted_oversized_only_and_preserves_logs(self):
        paths = [self.log("planning/z.log", 1002), self.log("planning/a.txt", 1001),
                 self.log("planning/small.log", 1000), self.log("planning/data.json", 5000)]
        before = {path: path.read_bytes() for path in paths}
        code, output = self.run_tool("--write-baseline")
        self.assertEqual(code, 0)
        self.assertEqual(output,
            "evidence_size_check: 3 raw logs, 0 refused, 2 baselined, 0 stale\n")
        self.assertEqual((self.root / evidence.BASELINE).read_text(),
                         evidence.BASELINE_HEADER + "planning/a.txt\nplanning/z.log\n")
        self.assertEqual(before, {path: path.read_bytes() for path in paths})

    def test_rewriting_baseline_only_shrinks(self):
        self.log("planning/kept.log", 1001)
        self.log("planning/shrunk.log", 1000)
        self.log("planning/new.log", 1001)
        self.baseline("planning/kept.log", "planning/shrunk.log", "planning/gone.log")
        code, output = self.run_tool("--write-baseline")
        self.assertEqual(code, 1)
        self.assertIn("REFUSED planning/new.log:", output)
        self.assertEqual(evidence.read_baseline(self.root), {"planning/kept.log"})

    def test_file_arguments_restrict_findings_and_stale_entries(self):
        path = self.log("planning/selected.log", 1000)
        self.log("planning/other.log", 1001)
        self.baseline("planning/missing.log")
        for name in ("planning/selected.log", str(path)):
            self.assertEqual(self.run_tool(name), (0,
                "evidence_size_check: 1 raw logs, 0 refused, 0 baselined, 0 stale\n"))
        code, output = self.run_tool("planning/missing.log")
        self.assertEqual(code, 1)
        self.assertIn("STALE planning/missing.log:", output)

    def test_limit_override_and_unterminated_binary_line(self):
        path = self.log("planning/binary.log", 2)
        with path.open("ab") as output:
            output.write(b"\xff")
        code, output = self.run_tool("--limit", "2")
        self.assertEqual(code, 1)
        self.assertIn("3 lines (limit 2)", output)
        self.assertEqual(self.run_tool("--limit", "3")[0], 0)

    def test_git_scope_includes_intent_to_add_but_not_untracked(self):
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.log("planning/tracked.log", 1000)
        self.log("planning/probe.log", 1001)
        self.log("planning/untracked.log", 1001)
        subprocess.run(["git", "-C", str(self.root), "add", "planning/tracked.log"], check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "-N", "planning/probe.log"], check=True)
        result = evidence.check(root=self.root)
        self.assertEqual((result.checked, result.refused), (2, 1))
        self.assertIn("REFUSED planning/probe.log:", result.findings[0])
        self.assertEqual(self.run_tool("planning/untracked.log"), (0,
            "evidence_size_check: 0 raw logs, 0 refused, 0 baselined, 0 stale\n"))
        evidence.write_baseline(self.root)
        self.assertEqual(evidence.read_baseline(self.root), {"planning/probe.log"})


if __name__ == "__main__":
    unittest.main()
