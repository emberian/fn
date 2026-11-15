import sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from checkpoint_origin_rewrite import add_read_child,call_args
class CheckpointOriginRewrite(unittest.TestCase):
 def test_read_child_tracks_definition_call_guard_contract_and_cost(self):
  s='''(defun f (a p q) (declare (xargs :stobjs (p q) :guard (and (p-wfp p) (q-wfp q)))) (f a p q))
(p-preserves f (a p q) :position 1 :hyps ((pp p) (p-wfp p)))
(defcost f-op :child f :tables (fn2-core-p fn2-core-q))'''
  out,_=add_read_child(s,'f',3,'fn2-origin')
  for x in ['(a p fn2-origin q)','(f a p fn2-origin q)',':stobjs (p fn2-origin q)','(fn2-origin-wfp fn2-origin)','(fn2-originp fn2-origin)','fn2-core-p fn2-core-origin fn2-core-q']:self.assertIn(x,out)
 def test_only_designated_call_slots_change(self):
  s='(defun f (x) (page x 1 1 1)) (defun g (x) (page x 1 1 1))'
  out,n=call_args(s,'page',{2:('1','physical-history'),3:('1','physical-incarnation')},scope='f',expected_count=1)
  self.assertEqual(out,'(defun f (x) (page x 1 physical-history physical-incarnation)) (defun g (x) (page x 1 1 1))');self.assertEqual(n,1)
 def test_stale_signature_and_unexpected_identity_are_refused(self):
  with self.assertRaises(ValueError):add_read_child('(f a)','f',2,'p')
  with self.assertRaises(ValueError):call_args('(page x 2)','page',{1:('1','physical')},expected_count=1)
if __name__=='__main__':unittest.main()
