"""Structural transformation fixtures; runtime assertions remain ACL2 controls."""
import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr
from rewrite_zero_kind_contracts import rewrite, TARGETS
class ZeroKindContracts(unittest.TestCase):
    def test_exact_transform(self):
        before = '; (posp okind) is a comment\n(and (posp okind) (unsigned-byte-p 8 okind) (unsigned-byte-p 60 ogen))'
        self.assertEqual(rewrite(before, 1), before.replace('(and (posp okind)', '(and (or (posp okind) (posp ogen))'))
    def test_count_drift_refuses(self):
        with self.assertRaises(ValueError):
            rewrite('(posp other)', 1)
    def test_transformed_sources(self):
        for name, count in TARGETS.items():
            parsed = lr.parse(ROOT / 'books' / name)
            self.assertEqual(len(lr.match('(or (posp okind) (posp ogen))', parsed.forms)), count, name)
            self.assertGreaterEqual(len(lr.match('(posp ogen)', parsed.forms)), count)
            self.assertGreaterEqual(len(lr.match('(unsigned-byte-p 8 okind)', parsed.forms)), count)
    def test_control_source_parses(self):
        lr.parse(ROOT / 'tests/retirement-dispatch-controls.lisp')
if __name__ == '__main__':
    unittest.main()
