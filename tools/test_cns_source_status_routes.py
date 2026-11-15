#!/usr/bin/env python3
"""Frozen actual d990/30e status-route checks, not leaf-stub runtime evidence."""
from pathlib import Path
import json,unittest
import lisp_rewrite as lr
import cns_source_status_routes as r
ROOT=Path(__file__).resolve().parents[1]
def canon(n):
 if isinstance(n,lr.Pre):return [n.prefix,canon(n.node)]
 if isinstance(n,lr.Lst):
  if r.head(n)==':do':return [':do',canon(n.items[1]),canon(n.items[2])]
  xs=[canon(x) for x in n.items]
  if r.head(n)=='defcost' and r.sym(n.items[1])=='fn2-cns-stream-source-step':
   xs[xs.index(':answers')+1]='t'
  return xs
 return n.low
class Routes(unittest.TestCase):
 def test_frozen_actual_sources(self):
  for item in json.loads((ROOT/'tests/fixtures/cns_source_status_routes.json').read_text()):
   with self.subTest(source=item['source']):
    before=item['text'];self.assertEqual(len(r.issues(before)),16)
    after=r.transform(before)
    self.assertEqual(r.issues(after),[])
    self.assertEqual(r.transform(after),after)
    b=lr.parse(before);a=lr.parse(after)
    # All calls, values, charges, budgets, table/effect metadata, physical
    # issue/ownership branches are identical. Only route options/STEP enum differ.
    self.assertEqual([canon(f) for f in b.forms],[canon(f) for f in a.forms])
    old=list(r.sites(b));new=list(r.sites(a));self.assertEqual(len(old),len(new))
    for (machine,name,n),(m2,name2,z) in zip(old,new):
     self.assertEqual((machine,name),(m2,name2))
     previous=r.option(n,':case',3);current=r.option(z,':case',3)
     if previous:self.assertEqual(canon(previous),canon(current))
     elif current:
      self.assertEqual(machine,'fn2-cns')
      self.assertIn(name,('fn2-cns-stream-source-finish','fn2-cns-stream-source-clear'))
      self.assertEqual(canon(current),[[[':stale'],[':stop',':machine-phase']]])
 def test_missing_why_detected(self):
  src='(defcost fn2-ctl-stream-hash :answers (:ok :more :bounds)) (defmachine-arms fn2-ctl :declare :arms ((:stream (:do (c n) (fn2-ctl-stream-hash 1) :accept (:ok :more :bounds)) (:charge))))'
  self.assertTrue(any('why' in problem for _,problem in r.issues(src)))
 def test_missing_normal_routes_detected(self):
  src='(defcost fn2-cns-stream-source-issue :answers (:ok :wait :bad)) (defmachine-arms fn2-cns :declare :arms ((:source (:do (c o g) (fn2-cns-stream-source-issue 1)) (:charge))))'
  self.assertTrue(any(':wait' in problem and ':bad' in problem for _,problem in r.issues(src)))
if __name__=='__main__':unittest.main()
