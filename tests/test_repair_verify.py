"""Execute the real verifier against disposable Git histories, not mocked exits."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("repair", ROOT / "planning/repair/repair.py")
repair = importlib.util.module_from_spec(spec)
spec.loader.exec_module(repair)

TEST = """import unittest
from product import value
class Regression(unittest.TestCase):
    def test_value(self):
        self.assertEqual(value, 2, 'value must be two')
"""
ID = "tests.test_regression.Regression.test_value"
MESSAGE = "1 != 2 : value must be two"


class RepairVerifyTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / "repo"
        self.root.mkdir()
        self.git("init", "-q")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "user.name", "Verifier fixture")
        self.write("product.py", "value = 1\n")
        self.write("tests/__init__.py", "")
        self.commit("base")
        self.base = self.git("rev-parse", "HEAD").strip()
        self.items = self.root / "planning/repair/items"
        self.items.mkdir(parents=True)
        self.item = {"id": "FIX", "state": "in-progress", "scope": ["product.py", "tests/*"],
                     "budget": 100, "test": "python3 -m unittest tests.test_regression",
                     "harness": "tests/test_regression.py", "expect-failure": ID,
                     "failure-message": MESSAGE, "timeout": 2}

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, capture_output=True,
                              text=True, check=True).stdout

    def write(self, name, text):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def commit(self, message):
        self.git("add", "--", "product.py", "tests")
        for name in ("docs", "host"):
            if (self.root / name).exists():
                self.git("add", "--", name)
        self.git("commit", "-qm", message)

    def head(self, test=TEST, extra=None):
        self.write("product.py", "value = 2\n")
        if test is not None:
            self.write("tests/test_regression.py", test)
        if extra:
            self.write(*extra)
        self.commit("FIX repair")

    def verify(self, **updates):
        self.item.update(updates)
        self.write("planning/repair/items/FIX.json", json.dumps(self.item))
        with patch.object(repair, "ITEMS", str(self.items)), patch.object(repair, "repo_root", return_value=str(self.root)), \
                patch.dict(os.environ, {"FN_EVIDENCE_ARCHIVE": str(Path(self.tmp.name) / "archive"),
                                        "FN_EVIDENCE_CACHE": str(Path(self.tmp.name) / "cache")}), \
                contextlib.redirect_stdout(io.StringIO()):
            code = repair.verify(["FIX", "--base", self.base])
        result = json.loads((self.items / "FIX.json").read_text())["verify"]
        self.assertEqual(code, 0 if result["ok"] else 1)
        return result

    def test_new_regression_is_transplanted_and_intended_assertion_passes(self):
        self.head()
        r = self.verify()
        self.assertTrue(r["ok"], r)
        self.assertEqual(r["base_observation"]["result"]["assertions"][0]["message"], MESSAGE)
        evidence = json.loads((self.root / r["evidence"]["path"]).read_text())
        self.assertIn("AssertionError", evidence["base_observation"]["stderr"])
        self.assertTrue((self.root / "planning/evidence-index.tsv").exists())

    def test_no_test_is_refused(self):
        self.head()
        r = self.verify(test="")
        self.assertFalse(r["ok"])
        self.assertIn("no regression test", " ".join(r["problems"]))

    def test_absent_test_file_is_refused(self):
        self.head(test=None)
        self.assertFalse(self.verify()["ok"])

    def test_missing_selected_module_cannot_use_an_unrelated_harness(self):
        self.head()
        r = self.verify(test="python3 -m unittest tests.absent")
        self.assertFalse(r["red_at_base"])
        self.assertIn("unittest.loader._FailedTest.absent", r["base_observation"]["result"]["errors"])

    def test_bad_import_is_an_error_not_defect_red(self):
        self.head(TEST.replace("from product import value", "import missing_dependency\nfrom product import value"))
        r = self.verify()
        self.assertFalse(r["red_at_base"])
        self.assertTrue(r["base_observation"]["result"]["errors"])

    def test_missing_api_attribute_error_is_not_defect_red_even_when_head_passes(self):
        self.head(TEST.replace("from product import value", "import product").replace("value, 2", "product.new_api(), 2"))
        self.write("product.py", "def new_api(): return 2\n")
        self.commit("FIX new API")
        r = self.verify()
        self.assertFalse(r["red_at_base"])
        self.assertTrue(r["green_at_head"])
        self.assertIn("AttributeError", r["base_observation"]["stderr"])

    def test_unittest_subtest_assertion_is_observed(self):
        self.head(TEST.replace("        self.assertEqual", "        with self.subTest(case='value'):\n            self.assertEqual"))
        self.assertTrue(self.verify()["ok"])

    def test_timeout_is_recorded_and_refused(self):
        self.head(TEST.replace("        self.assertEqual", "        import time; time.sleep(1)\n        self.assertEqual"))
        r = self.verify(timeout=.1)
        self.assertFalse(r["red_at_base"])
        self.assertEqual(r["base_observation"]["infrastructure"], "timeout")

    def test_skip_and_expected_failure_are_not_green_or_red(self):
        for decorator in ("@unittest.skip('unavailable')", "@unittest.expectedFailure"):
            with self.subTest(decorator=decorator):
                self.head(TEST.replace("    def test_value", "    " + decorator + "\n    def test_value"))
                r = self.verify()
                self.assertFalse(r["red_at_base"])
                self.assertFalse(r["green_at_head"])

    def test_wrong_assertion_in_named_test_is_refused(self):
        self.head(TEST.replace("value must be two", "unrelated assertion"))
        r = self.verify()
        self.assertFalse(r["red_at_base"])
        self.assertTrue(r["green_at_head"])

    def test_missing_tool_is_not_red(self):
        self.head()
        r = self.verify(test="missing-python-fixture -m unittest tests.test_regression")
        self.assertFalse(r["ok"])
        self.assertIn("interpreter unavailable", " ".join(r["problems"]))

    def test_no_executed_tests_are_not_green(self):
        self.head("import unittest\n")
        r = self.verify()
        self.assertFalse(r["green_at_head"])

    def test_scope_and_forbidden_rejection_survive(self):
        self.head(extra=("host/native/owner.lisp", "changed\n"))
        r = self.verify()
        self.assertFalse(r["ok"])
        self.assertIn("outside", " ".join(r["problems"]))
        self.assertIn("forbidden", " ".join(r["problems"]))

    def test_explicit_documentation_exemption(self):
        self.write("docs/note.md", "A corrected sentence.\n")
        self.commit("FIX prose")
        r = self.verify(test="", **{"doc-only": "correct a prose typo", "scope": ["docs/note.md"]})
        self.assertTrue(r["ok"], r)

    def test_document_suffix_in_fixture_is_not_a_documentation_exemption(self):
        self.write("tests/script.txt", "executable fixture\n")
        self.commit("FIX fixture")
        self.assertFalse(self.verify(test="", **{"doc-only": "claimed prose"})["ok"])

    def test_planning_text_configuration_is_not_a_prose_exemption(self):
        self.write("planning/config.txt", "control option\n")
        self.git("add", "planning/config.txt")
        self.commit("FIX config")
        self.assertFalse(self.verify(test="", scope=["planning/config.txt"], **{"doc-only": "claimed prose"})["ok"])

    def test_document_executable_mode_is_not_a_prose_exemption(self):
        self.write("docs/program.md", "#!/bin/sh\nexit 0\n")
        (self.root / "docs/program.md").chmod(0o755)
        self.commit("FIX executable")
        self.assertFalse(self.verify(test="", scope=["docs/program.md"], **{"doc-only": "claimed prose"})["ok"])

    def test_archive_outage_preserves_semantic_result(self):
        self.head()
        with patch.object(repair, "archive_result", side_effect=OSError("archive offline")):
            r = self.verify()
        self.assertTrue(r["semantic_ok"])
        self.assertFalse(r["ok"])
        self.assertEqual(r["evidence_outcome"], "unavailable")

    def test_exact_list_filters_exclude_untagged_items(self):
        with patch.object(repair, "all_items", return_value=[
                {"id": "A", "state": "open", "title": "untagged"},
                {"id": "B", "state": "open", "title": "tagged", "category": "proof-owed"}]), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            repair.main(["list", "--category", "proof-owed"])
        self.assertNotIn("untagged", out.getvalue())
        self.assertIn("tagged", out.getvalue())


if __name__ == "__main__":
    unittest.main()
