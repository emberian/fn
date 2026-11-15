import unittest
from event_source_carriers_rewrite import expand
class Rewrite(unittest.TestCase):
 def test_explicit_child_signature_guard_and_call(self):
  s='(defun target (s) (declare (xargs :stobjs (s) :guard (and (ok s)))) (target s))'
  out=expand(s,{'target':(1,['fn2-new'])})
  self.assertIn('(target s fn2-new)',out)
  self.assertIn(':stobjs (s fn2-new)',out)
  self.assertIn('(fn2-new-wfp fn2-new)',out)
 def test_core_projection_avoids_existing_formal(self):
  s='(defun wrap (fn2-known fn2-core) (stobj-let ((fn2-old (fn2-core-old fn2-core))) (x) (target fn2-old) x))'
  out=expand(s,{'target':(1,['fn2-known','fn2-new'])})
  self.assertIn('(fn2-new (fn2-core-new fn2-core))',out)
  self.assertNotIn('(fn2-known (fn2-core-known',out)
 def test_unknown_call_arity_refuses(self):
  with self.assertRaises(ValueError):expand('(target a b)',{'target':(1,['fn2-new'])})
 def test_missing_projection_refuses(self):
  with self.assertRaises(ValueError):expand('(defun wrap (x) (target x))',{'target':(1,['fn2-new'])})
if __name__=='__main__':unittest.main()
