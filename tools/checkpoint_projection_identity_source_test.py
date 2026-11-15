"""Check the proof subject and actual atomic seam; no ACL2 proof claim."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class IdentityProofSource(unittest.TestCase):
 def setUp(self):
  self.forms=lr.parse((ROOT/'books/checkpoint-projection-identity-preservation.lisp').read_text()).forms
 def test_both_real_wrapper_signatures_are_the_subject(self):
  for file,name in [('checkpoint-projection','fn2-checkpoint-projection-step'),('checkpoint-owned-projection','fn2-checkpoint-projection-owned-step')]:
   runtime=lr.match('(defun '+name+' ?*body)',lr.parse((ROOT/'books'/f'{file}.lisp').read_text()).forms,deep=False)[0].node
   theorem=lr.match('(defthm '+name+'-preserves-index-loop ?*body)',self.forms,deep=False)[0].node
   calls=lr.match('('+name+' ?*args)',[theorem])
   self.assertEqual(len(calls),2)
   for call in calls:self.assertEqual([lr.flat(x) for x in call.node.items[1:]],[lr.flat(x) for x in runtime.items[2].items])
 def test_unprocessed_free_and_pending_map_subject_are_required(self):
  loop=lr.match('(defun fn2-checkpoint-projection-index-loop-p ?*body)',self.forms,deep=False)[0].node
  for name in ('fn2-checkpoint-projection-free-suffix-p','fn2-checkpoint-projection-prefix-counts-p','fn2-checkpoint-projection-pending-row-p','fn2-alloc-identity-clearing-p','fn2-alloc-identity-maintained-p'):
   self.assertTrue(lr.match('('+name+' ?*args)',[loop]))
 def test_runtime_row_put_and_publish_precede_the_only_return(self):
  text=(ROOT/'books/checkpoint-projection.lisp').read_text()
  start=text.index('(fn2-extents (fn2-extents-put e (state row-state)')
  publish=text.index('(fn2-alloc-identity-publish-existing-row ',start)
  after=text.index('(fn2-checkpoint-projection-answer (if (eq code :ok)',publish)
  self.assertLess(start,publish);self.assertLess(publish,after)
  # The private incomplete interval contains no return, turn, IO or yield call.
  between=text[start:publish]
  self.assertNotIn('fn2-checkpoint-projection-answer',between)
  self.assertNotIn(':yield',between)
if __name__=='__main__':unittest.main()
