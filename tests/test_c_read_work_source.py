"""Generated C-read work boundary controls; no runtime/admission claim."""
from pathlib import Path
import copy
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for v in x:yield from walk(v)
def top(name):
 return [read_sexp(f) for f in forms((ROOT/'books'/name).read_text())]
def find(fs,head,name):
 return next(x for f in fs for x in walk(f) if len(x)>1 and x[:2]==[head,name])
def recursive_after_advance(f):
 b=next(x for x in walk(f) if x and x[0]=='b*')
 return any(x and x[0]=='fn2-range-advance-all' for x in walk(b[2]))
class ReadWorkSource(unittest.TestCase):
 def test_range_advance_yields_after_one_real_source(self):
  f=find(top('range.lisp'),'defun','fn2-range-advance-all')
  self.assertFalse(recursive_after_advance(f))
  body=next(x for x in walk(f) if x and x[0]=='b*')[2]
  self.assertEqual(body,['mv',':more','fn2-range-sources','fn2-run-cursors','fn2-run-paths','fn2-fields'])
  broken=copy.deepcopy(f)
  b=next(x for x in walk(broken) if x and x[0]=='b*')
  b[2]=['fn2-range-advance-all','n']
  self.assertTrue(recursive_after_advance(broken))
 def test_finished_heads_skip_without_advancing_another_source(self):
  f=find(top('range.lisp'),'defun','fn2-range-advance-all')
  recursive=[x for x in walk(f[3:]) if x and x[0]=='fn2-range-advance-all']
  self.assertEqual(len(recursive),1)
  whens=[x for x in walk(f) if x and x[0]=='when']
  headskip=next(x for x in whens if '*fn2-range-state-head*' in str(x))
  self.assertIn('*fn2-range-state-end*',str(headskip))
 def test_seek_has_one_decode_attempt_per_served_phase(self):
  f=find(top('runs-assemble.lisp'),'defun','fn2-run-step-seek')
  seek=next(x for x in walk(f) if x and x[0]=='fn2-run-seek')
  self.assertEqual(seek[3],['min','budget','1'])
 def test_bounds_derive_every_registered_codec_and_key(self):
  fs=top('runs-assemble.lisp')
  dispatch=find(fs,'defun','fn2-ra-dispatch-events')
  for n in ('fn2-ra-layout-max-sizes','fn2-ra-key-octet-bounds'):
   self.assertTrue(any(x and x[0]==n for x in walk(dispatch)))
  step=find(fs,'defconst','*fn2-c-read-step-bytes*')
  for sym in ('*fn2-run-overlay-search-steps*','*fn2-run-restart-interval*','*fn2-run-layout-max-entry-bytes*','*fn2-run-layout-max-key-octets*','*fn2-run-active-source-cursors*'):
   self.assertIn(sym,str(step))
  key=find(fs,'defun','fn2-ra-key-octet-bound')
  self.assertIn(':digest',str(key));self.assertIn(':octets',str(key))
  self.assertNotIn('nfix',str(key))  # named MAX bounds remain emitted expressions
 def test_existing_ordering_functions_are_not_replaced(self):
  fs=top('range.lisp')
  for name in ('fn2-range-order','fn2-range-pick','fn2-range-consume','fn2-range-deliver'):
   self.assertTrue(find(fs,'defun',name))
  s=(ROOT/'tests/range-unit.lisp').read_text()
  self.assertIn('fn2-range-read-exact-positive',s);self.assertIn('fn2-range-read-exact-negative',s)
if __name__=='__main__':unittest.main()
