"""Release registration recipe refuses duplicate or missing actual declarations."""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import release_core_rewrite as rw

class Registration(unittest.TestCase):
    def test_no_second_registration(self):
        with self.assertRaisesRegex(ValueError, 'already present'):
            rw.transform('(include-book "release-allocation-state")', '')

    def test_missing_actual_lifecycle_include(self):
        with self.assertRaisesRegex(ValueError, 'lifecycle include'):
            rw.transform('(include-book "columns")', '')

    def test_missing_actual_child(self):
        with self.assertRaisesRegex(ValueError, 'expected one'):
            rw.one('(defun unrelated () 0)', 'defcorechild', 'fn2-core-alloc-edges')

    def test_ambiguous_actual_child(self):
        with self.assertRaisesRegex(ValueError, 'expected one'):
            rw.one('(defcorechild x t)(defcorechild x nil)', 'defcorechild', 'x')

if __name__ == '__main__':
    unittest.main()
