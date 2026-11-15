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
class ProjectionOwnership(unittest.TestCase):
    def test_actual_face_has_one_source_bound_writer(self):
        root = Path(__file__).resolve().parents[1]
        source = (root / 'books/checkpoint-owned-projection.lisp').read_text()
        parsed = lr.parse(source)
        self.assertEqual(len(lr.match('(fn2-checkpoint-construction-put ?*args)', parsed.forms)), 1)
        self.assertIn('(fn2-checkpoint-projection-step ', source)
        self.assertIn('(fn2-checkpoint-projection-current-p ', source)
        self.assertIn('(fn2-checkpoint-restore-reach-row-p ', source)
        self.assertIn('(= (fn2-checkpoint-projection-cursor 0 fn2-checkpoint-projection) (+ e 1))', source)
        self.assertIn('(intended-bytes 0) (completed-bytes 0)', source)
        self.assertIn('(token 0) (owner-kind 0) (owner-slot 0) (owner-gen 0)', source)
        self.assertNotIn('role-journal', source)
        self.assertIn('(fn2-checkpoint-projection-step-op *fn2-checkpoint-master-kind*)', (root / 'books/boot.lisp').read_text())
if __name__ == '__main__': unittest.main()
