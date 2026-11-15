"""Actual abort source-reader gate transformation; no ACL2 execution."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from rewrite_checkpoint_abort_reader_gate import transform,CHILDREN
class AbortReaderGate(unittest.TestCase):
 def test_constructor_and_actual_quoted_macro_body(self):
  old="(defmacro events () '(progn (defun fn2-checkpoint-master-preconstructionp (x) (declare (xargs :stobjs (x) :guard (and (xp x)))) (and (good x)))))"
  new,n=transform(old)
  self.assertEqual(n,4)
  for c in CHILDREN:self.assertIn(c,new)
  self.assertIn('fn2-checkpoint-source-reader-detachedp',new)
  self.assertEqual(transform(new),(new,0))
 def test_call_face_and_frame_readonly_threading(self):
  old='(fn2-checkpoint-master-abort-step-children budget x)\n(defcost op :child fn2-checkpoint-master-abort-step-children :tables (fn2-core-x))\n(fn2-checkpoint-root1-preserves fn2-checkpoint-master-abort-step-children (budget x) :hyps ((xp x)))'
  new,n=transform(old);self.assertEqual(n,4)
  self.assertIn('fn2-core-checkpoint-summary-leases',new)
  self.assertEqual(transform(new),(new,0))
 def test_foreign_untouched(self):
  old='(defun other (x) (declare (xargs :stobjs (x) :guard (and (xp x)))) (and (good x)))'
  self.assertEqual(transform(old),(old,0))
 def test_actual_family_is_fully_threaded_and_gated(self):
  text=(ROOT/'books/checkpoint-master-abort.lisp').read_text()
  self.assertEqual(transform(text),(text,0))
  self.assertEqual(text.count('(fn2-checkpoint-source-reader-detachedp'),2)
  self.assertEqual(text.count('fn2-core-run-loads'),4)
if __name__=='__main__':unittest.main()
