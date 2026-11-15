from pathlib import Path
import unittest
from lisp_guard_freevars import findings
ROOT=Path(__file__).resolve().parents[1]
class Guards(unittest.TestCase):
 def test_frozen_actual_defect_and_fixed_whole_book(self):
  before=(ROOT/'tools/fixtures/checkpoint-summary-authority-live-before-freeguard.lisp').read_text()
  after=(ROOT/'books/checkpoint-summary-authority-live.lisp').read_text()
  count,red=findings(before);self.assertEqual(count,5)
  self.assertEqual(red,[('fn2-checkpoint-summary-live-published-hash-p',['fn2-checkpoint-lifecycle','fn2-checkpoint-writer','fn2-machines'])])
  self.assertEqual(findings(after),(5,[]))
  accidental=' (fn2-checkpoint-writer-wfp fn2-checkpoint-writer) (fn2-machines-wfp fn2-machines) (fn2-checkpoint-lifecycle-wfp fn2-checkpoint-lifecycle)'
  # The first occurrence is the two-carrier hash helper. Later real formal
  # domains and the entire actual live-source-p authorization body remain exact.
  self.assertEqual(before.replace(accidental,'',1),after)
 def test_lexical_scope_and_literal_constants(self):
  s="(defun f (x p) (declare (xargs :guard (let* ((y x) (z (+ y 1))) (and (g p z) (eq x :hello) (h '*global*))))) x)"
  self.assertEqual(findings(s),(1,[]))
 def test_readonly_carrier_is_still_formal(self):
  self.assertEqual(findings('(defun f (p) (declare (xargs :guard (and (wfp p) (wfp q)))) p)'),(1,[('f',['q'])]))
 def test_generated_literal_defun_is_checked(self):
  self.assertEqual(findings("(defmacro events () '(progn (defun f (x) (declare (xargs :guard (g x y))) x)))"),(1,[('f',['y'])]))
 def test_unknown_binding_refuses(self):
  with self.assertRaises(ValueError):findings('(defun f (x) (declare (xargs :guard (b* ((y x)) y))) x)')
if __name__=='__main__':unittest.main()
