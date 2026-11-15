"""Source transformation controls; these do not execute ACL2."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from rewrite_checkpoint_native_ownership import rewrite, FILES
import lisp_rewrite as lr
class NativeOwnership(unittest.TestCase):
    def test_both_comparators_and_cursor(self):
        source = '(and (equal (fn2-checkpoint-construction-live e fn2-checkpoint-construction) 1) (= (fn2-checkpoint-construction-live row fn2-checkpoint-construction) 1))'
        out, n = rewrite(source)
        self.assertEqual(n, 2)
        self.assertEqual(out, '(and (fn2-checkpoint-construction-native-p e fn2-checkpoint-construction) (fn2-checkpoint-construction-native-p row fn2-checkpoint-construction))')
    def test_free_preflight_and_foreign_table_preserved(self):
        source = '(and (equal (fn2-checkpoint-construction-live next fn2-checkpoint-construction) 0) (equal (fn2-checkpoint-construction-live e foreign) 1))'
        self.assertEqual(rewrite(source), (source, 0))
    def test_idempotent(self):
        source = '(fn2-checkpoint-construction-native-p e fn2-checkpoint-construction)'
        self.assertEqual(rewrite(source), (source, 0))
    def test_actual_class_drained(self):
        root = Path(__file__).resolve().parents[1]
        for stem in FILES:
            text = (root / 'books' / (stem+'.lisp')).read_text()
            lr.parse(text)
            self.assertEqual(rewrite(text), (text, 0), stem)
        text = (root / 'books/checkpoint-construction.lisp').read_text()
        self.assertIn('(defconst *fn2-checkpoint-owned-restored-role* 255)', text)
        self.assertIn('(<= (fn2-checkpoint-construction-role e fn2-checkpoint-construction) 6)', text)
if __name__ == '__main__': unittest.main()
