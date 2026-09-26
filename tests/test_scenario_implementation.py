"""tools/check_scaffold.py: an implemented scenario names its test and its log."""
import copy
import json
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

    def test_the_catalog_entry_passes(self):
        self.assertEqual(self.errors(self.entry), [])

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
        entry["implementation"]["log"] = "planning/evidence/width-producers-2-2026-09-26/gate-served.log"
        self.assertTrue(any("neither" in e for e in self.errors(entry)))

    def test_native_must_be_stated(self):
        entry = copy.deepcopy(self.entry)
        del entry["implementation"]["native"]
        self.assertTrue(any("native" in e for e in self.errors(entry)))


if __name__ == "__main__":
    unittest.main()
