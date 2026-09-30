"""The inventory sees tests inside branch lists but ignores quoted data."""
from __future__ import annotations
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
spec = importlib.util.spec_from_file_location("legacy_parser_inventory", ROOT / "tools/legacy_parser_inventory.py")
module = importlib.util.module_from_spec(spec)
assert spec and spec.loader
spec.loader.exec_module(module)

class InventoryTests(unittest.TestCase):
    def test_conditions_and_branch_bodies_are_seen(self):
        form = module.read_forms("(cond ((equal x 1) (f x)) ((equal x 2) (g x)))")[0]
        sites = module.calls(form)
        self.assertEqual(sites["equal"], 2)
        self.assertEqual((sites["f"], sites["g"]), (1, 1))

    def test_quoted_calls_are_data(self):
        form = module.read_forms("(list '(danger 1) (safe 2))")[0]
        sites = module.calls(form)
        self.assertNotIn("danger", sites)
        self.assertEqual(sites["safe"], 1)

    def test_current_name_choice_is_in_the_graph(self):
        row = module.inventory()["functions"]["fn-lpc-name-key"]
        self.assertIn("fn-lpc-at", row["calls"])
        self.assertIn("equal", row["source_sites"])

if __name__ == "__main__":
    unittest.main()
