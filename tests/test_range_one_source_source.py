"""Source controls for actual range work and the prepared eight-source fixture.
No ACL2 admission, assertion execution, or query simulator is performed here.
"""
from pathlib import Path
import copy
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def defs(path):
 return {x[1]:x for raw in forms(path.read_text()) for x in walk(read_sexp(raw))
         if len(x)>2 and x[0]=='defun' and isinstance(x[1],str)}
def calls(f,name):return [x for x in walk(f[3:]) if x and x[0]==name]
def one_pending_advance(f):
 bodies=[x for x in f[3:] if isinstance(x,list) and x and x[0]!='declare']
 if len(bodies)!=1 or bodies[0][0]!='b*' or len(bodies[0])!=3:return False
 bstar=bodies[0]
 if not (isinstance(bstar[2],list) and bstar[2][:2]==['mv',':more']):return False
 recursive=calls(f,'fn2-range-advance-all')
 if len(recursive)!=1:return False
 guarded=[]
 for binding in bstar[1]:
  if isinstance(binding[0],list) and binding[0] and binding[0][0]=='when':
   guard=binding[0]
   if '*fn2-range-state-head*' in str(guard) and '*fn2-range-state-end*' in str(guard):
    guarded.append(binding[1])
 return len(guarded)==1 and guarded[0]==recursive[0]
def quoted(x):return x[1] if isinstance(x,list) and x and x[0]=='quote' else x
class RangeOneSource(unittest.TestCase):
 def setUp(self):
  self.r=defs(ROOT/'books/range.lisp')
  self.f=defs(ROOT/'tests/range-one-source-unit.lisp')
 def test_actual_generator_advances_one_pending_source(self):
  f=self.r['fn2-range-advance-all']
  self.assertTrue(one_pending_advance(f))
  self.assertEqual(len(calls(f,'fn2-range-advance-overlay')),1)
  self.assertEqual(len(calls(f,'fn2-range-advance-run')),1)
 def test_missing_more_and_restored_recursion_are_rejected(self):
  f=self.r['fn2-range-advance-all']
  bad=copy.deepcopy(f)
  body=next(x for x in bad[3:] if isinstance(x,list) and x and x[0]=='b*')
  body[2][1]=':ok'
  self.assertFalse(one_pending_advance(bad))
  bad=copy.deepcopy(f)
  body=next(x for x in bad[3:] if isinstance(x,list) and x and x[0]=='b*')
  body[2]=copy.deepcopy(calls(f,'fn2-range-advance-all')[0])
  self.assertFalse(one_pending_advance(bad))
 def test_fixture_builds_actual_encoded_nonempty_overlays(self):
  self.assertEqual(len(calls(self.f['fn2-ros-build-overlays'],'fn2-ov-start')),1)
  self.assertEqual(len(calls(self.f['fn2-ros-build-overlays'],'fn2-ov-freeze')),1)
  self.assertEqual(len(calls(self.f['fn2-ros-write-entries'],'fn2-ov-write')),1)
  self.assertEqual(len(calls(self.f['fn2-ros-write-entries'],'fn2-run-load-values')),1)
  src=str(self.f['fn2-ros-pending-p'])
  for term in ('*fn2-range-kind-overlay*','*fn2-range-state-seek*','*fn2-overlay-phase-frozen*','fn2-overlays-count'):
   self.assertIn(term,src)
  self.assertIn(['<','0',['fn2-overlays-count','o','fn2-overlays']],list(walk(self.f['fn2-ros-pending-p'])))
 def test_first_actual_call_requires_exactly_one_head(self):
  f=self.f['fn2-range-one-source-unit']
  self.assertEqual(len(calls(f,'fn2-range-start')),1)
  self.assertEqual(len(calls(f,'fn2-range-advance-all')),1)
  self.assertEqual(calls(f,'fn2-range-advance-all')[0][1:4],['*fn2-ros-count*','0','budget'])
  self.assertIn(['eq','advanced',':more'],list(walk(f)))
  self.assertEqual(len(calls(f,'fn2-ros-pending-p')),1)
  self.assertEqual(len(calls(f,'fn2-ros-one-head-p')),1)
  states=str(self.f['fn2-ros-one-head-p'])
  self.assertIn('*fn2-range-state-head*',states)
  self.assertIn('*fn2-range-state-seek*',states)
  self.assertIn(['equal','s',['-','*fn2-ros-count*','1']],list(walk(self.f['fn2-ros-one-head-p'])))
 def test_driver_uses_real_range_and_whole_decoded_values(self):
  f=self.f['fn2-ros-drive']
  self.assertEqual(len(calls(f,'fn2-range-step')),1)
  self.assertEqual(len(calls(f,'fn2-run-unload-values')),1)
  self.assertFalse(calls(f,'fn2-range-spec'))
  unit=self.f['fn2-range-one-source-unit']
  self.assertIn(['eq','end',':end'],list(walk(unit)))
  self.assertIn(['equal','rows','*fn2-ros-expected*'],list(walk(unit)))
  self.assertIn(['equal',['fn2-ranges-delivered','0','fn2-ranges'],'13'],list(walk(unit)))
 def test_eight_sources_and_complete_tie_override_rows(self):
  fs=[read_sexp(raw) for raw in forms((ROOT/'tests/range-one-source-unit.lisp').read_text())]
  consts={f[1]:quoted(f[2]) for f in fs if isinstance(f,list) and f and f[0]=='defconst'}
  inputs=consts['*fn2-ros-inputs*'];expected=consts['*fn2-ros-expected*']
  self.assertEqual(len(inputs),8)
  self.assertTrue(all(s for s in inputs))
  self.assertEqual(len(expected),13)
  self.assertEqual(expected[0],['1','1','300','10',['65','2']])
  self.assertEqual(expected[4],['1','5','705','50',['65','6']])
  self.assertEqual(expected[-1],['1','13','113','130',['65','0']])
  self.assertEqual(consts['*fn2-ros-sequences*'][:3],['10','10','20'])
  self.assertTrue(all(len(row)==5 and isinstance(row[-1],list) for row in expected))
if __name__=='__main__':unittest.main()
