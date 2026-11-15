"""Shared loader region/range source controls, not admission or runtime tests."""
from pathlib import Path
import copy
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from lisp_source import forms, read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for v in x: yield from walk(v)
def defs(file):
 return {f[1]:f for raw in forms((ROOT/'books'/file).read_text()) if isinstance((f:=read_sexp(raw)),list) and f and f[0]=='defun'}
def calls(f,name): return [x for x in walk(f[3:]) if x and x[0]==name]
def pairs(f): return calls(f,'fn2-run-load-region-pairp')
class RegionSource(unittest.TestCase):
 def test_actual_three_segments_have_pairwise_separation(self):
  f=defs('run-physical-region.lisp')['fn2-run-load-regionp']
  self.assertEqual(pairs(f),[['fn2-run-load-region-pairp','b0','n0','b1','n1'],['fn2-run-load-region-pairp','b0','n0','b2','n2'],['fn2-run-load-region-pairp','b1','n1','b2','n2']])
  self.assertIn(['<=',['fn2-run-load-region-count','n0','n1','n2'],'*fn2-b-query-loader-jobs*'],list(walk(f)))
  broken=copy.deepcopy(f)
  for x in walk(broken):
   if x and x[0]=='fn2-run-load-region-pairp': x[0]='DROPPED-disjoint'
  self.assertFalse(pairs(broken))
 def test_same_real_allocator_and_release_no_io_twin(self):
  d=defs('run-physical-region.lisp')
  self.assertEqual(len(calls(d['fn2-run-load-region-fill'],'fn2-run-load-reserve')),1)
  self.assertEqual(len(calls(d['fn2-run-load-region-clean'],'fn2-run-load-release')),1)
  self.assertFalse(any(calls(f,'fn2-block-read-children') for f in d.values()))
  f=d['fn2-run-load-region-reserve']
  self.assertEqual(len(calls(f,'fn2-run-load-roomp')),1)
  self.assertEqual(len(calls(f,'fn2-run-load-region-freep')),1)
  self.assertEqual(len(calls(f,'fn2-run-load-region-clean')),1)
  self.assertEqual(len(calls(f,'fn2-run-load-region-retainedp')),1)
 def test_member_release_requires_owned_suffix_and_pending_zero(self):
  d=defs('run-physical-region.lisp')
  self.assertEqual(len(calls(d['fn2-run-load-region-member-release'],'fn2-run-load-region-drain')),1)
  self.assertEqual(len(calls(d['fn2-run-load-region-drain'],'fn2-run-load-regionp')),1)
  self.assertIn(['equal',['fn2-run-loads-pending','c','fn2-run-loads'],'1'],list(walk(d['fn2-run-load-region-drain'])))
  self.assertEqual(len(calls(d['fn2-run-load-region-suffix'],'fn2-run-load-ownerp')),1)
 def test_query_bundle_delegates_same_region_implementation(self):
  d=defs('run-physical-bundle.lisp')
  self.assertEqual(len(calls(d['fn2-run-page-bundle-reserve-children'],'fn2-run-load-region-reserve')),1)
  for name in ('fn2-run-query-bundle-fill','fn2-run-query-bundle-clean','fn2-run-query-bundle-retainedp'):
   self.assertNotIn(name,d)
 def test_range_selection_uses_actual_retained_source_and_identity(self):
  f=defs('run-physical-range.lisp')['fn2-run-load-range-miss']
  terms=list(walk(f))
  for lhs,rhs in [(['fn2-run-cursors-schema','c','fn2-run-cursors'],'schema'),(['fn2-range-sources-cursor','s','fn2-range-sources'],'c'),(['fn2-run-cursors-source-row','c','fn2-run-cursors'],['fn2-range-sources-src','s','fn2-range-sources'])]:
   self.assertIn(['equal',lhs,rhs],terms)
  self.assertFalse(calls(f,'fn2-pool-read'))
  self.assertFalse(calls(f,'fn2-run-cache-lookup'))
if __name__=='__main__': unittest.main()
