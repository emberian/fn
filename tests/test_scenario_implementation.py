"""tools/check_scaffold.py: an implemented scenario names its test and its run log, in the tree or the evidence archive."""
import copy
import json
import os
import shutil
import tempfile
from unittest import mock
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "tools"))
import check_scaffold  # noqa: E402


class ScenarioImplementationTests(unittest.TestCase):
    def setUp(self):
        catalog = json.loads((ROOT / "tests/scenarios/catalog.json").read_text())
        self.entry = next(s for s in catalog["scenarios"] if s["id"] == "SCN-058")
        check_scaffold.ERRORS.clear()

    def errors(self, entry):
        check_scaffold.ERRORS.clear()
        check_scaffold.scenario_implementation(entry["id"], entry)
        return list(check_scaffold.ERRORS)

    def test_no_implementation_is_refused(self):
        entry = copy.deepcopy(self.entry)
        del entry["implementation"]
        self.assertTrue(any("needs an `implementation`" in e for e in self.errors(entry)))

    def test_a_case_the_module_does_not_have_is_refused(self):
        entry = copy.deepcopy(self.entry)
        entry["implementation"]["cases"] = ["test_no_such_case_anywhere"]
        self.assertTrue(any("does not occur" in e for e in self.errors(entry)))

    def test_an_uncommitted_log_is_refused(self):
        entry = copy.deepcopy(self.entry)
        entry["implementation"]["log"] = "build/native/run.log"
        self.assertTrue(any("committed file" in e for e in self.errors(entry)))

    def test_a_log_that_names_neither_the_test_nor_is_named_is_refused(self):
        entry = copy.deepcopy(self.entry)
        # Both committed (a cited planning/evidence/ path that left the tree
        # is not cross-read, D71), and neither names the other or the test.
        entry["implementation"]["log"] = "LICENSE"
        entry["implementation"]["record"] = "docs/testing.md"
        self.assertTrue(any("neither" in e for e in self.errors(entry)))

    def archive(self, paths):
        """Point check_scaffold at a temporary archive ledger holding PATHS."""
        directory = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, directory)
        Path(directory, "history-ledger-test.tsv").write_text(
            "".join(f"{'0' * 64} 1 {'0' * 40} {p}\n" for p in paths))
        patcher = mock.patch.dict(os.environ, {check_scaffold.ARCHIVE_ENV: directory})
        patcher.start()
        self.addCleanup(patcher.stop)
        check_scaffold.archive_paths.cache_clear()
        self.addCleanup(check_scaffold.archive_paths.cache_clear)

    def test_an_archived_log_passes(self):
        impl = self.entry["implementation"]
        self.archive([impl["log"], impl["record"]])
        self.assertEqual(self.errors(self.entry), [])

    def test_a_log_in_neither_tree_nor_archive_is_refused(self):
        self.archive([self.entry["implementation"]["record"]])
        self.assertTrue(any("neither in the tree nor in the evidence archive" in e
                            for e in self.errors(self.entry)))

    def test_without_a_readable_ledger_an_absent_log_is_refused(self):
        patcher = mock.patch.object(check_scaffold, "archive_paths", lambda: None)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.assertTrue(any("no evidence-archive ledger" in e for e in self.errors(self.entry)))

    def test_a_log_without_its_record_is_refused(self):
        entry = copy.deepcopy(self.entry)
        self.archive([entry["implementation"]["log"]])
        del entry["implementation"]["record"]
        self.assertTrue(any("implementation.record must name a file" in e
                            for e in self.errors(entry)))

    def test_native_must_be_stated(self):
        entry = copy.deepcopy(self.entry)
        del entry["implementation"]["native"]
        self.assertTrue(any("native" in e for e in self.errors(entry)))


if __name__ == "__main__":
    unittest.main()
