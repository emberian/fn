"""Narrow controls for the physical stride rewrite; no Lisp/ACL2 evaluation."""
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from rewrite_checkpoint_storage_geometry import rewrite
import lisp_rewrite


class CheckpointGeometryRewrite(unittest.TestCase):
    def test_structural_fixtures_and_idempotence(self):
        fixtures = json.loads((ROOT / "tests/fixtures/lisp_rewrite/checkpoint_storage_geometry.json").read_text())
        for fixture in fixtures:
            with self.subTest(path=fixture["path"]):
                actual, _ = rewrite(fixture["path"], fixture["before"])
                self.assertEqual(actual, fixture["after"])
                self.assertEqual(rewrite(fixture["path"], actual), (actual, 0))

    def test_malformed_source_is_refused(self):
        with self.assertRaises(lisp_rewrite.ReadError):
            rewrite("books/checkpoint.lisp", "(floor unit 3))")


if __name__ == "__main__":
    unittest.main()
