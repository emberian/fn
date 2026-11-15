"""Same-definition layer extraction controls; no ACL2 execution."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import rewrite_checkpoint_cold_receipt_layers as rw

class ReceiptLayers(unittest.TestCase):
    def test_exact_forms_move_without_twins_or_other_edits(self):
        original='(in-package "ACL2")\n; retain\n(defun keep (x) x)\n(defun take (x) (+ 1 x))\n'
        out,leaf=rw.extract(original,('take',),'lower',('columns',))
        self.assertIn('(defun take (x) (+ 1 x))',leaf)
        self.assertNotIn('(defun take',out)
        self.assertIn('; retain\n(defun keep (x) x)',out)
        with self.assertRaises(ValueError):rw.extract(out,('take',),'lower',())
    def test_actual_sources_have_one_owner_and_low_dependencies(self):
        for high,low,includes,names in rw.CLASSES:
            upper=(ROOT/'books'/(high+'.lisp')).read_text()
            lower=(ROOT/'books'/(low+'.lisp')).read_text()
            self.assertIn('(include-book "'+low+'")',upper)
            for name in names:
                self.assertFalse(lr.match('(?head '+name+' ?*rest)',lr.parse(upper).forms,deep=False))
                self.assertEqual(len(lr.match('(?head '+name+' ?*rest)',lr.parse(lower).forms,deep=False)),1)
            self.assertNotIn('checkpoint-projection-protect',lower)
            self.assertNotIn('checkpoint-recovery-census',lower)
            self.assertNotIn('checkpoint-restore-events-source',lower)

if __name__=='__main__':unittest.main()
