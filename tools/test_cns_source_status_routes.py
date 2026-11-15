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
  if r.head(n)==':do':
   result=[canon(x) for x in n.items[:3]]
   for i in range(3,len(n.items),2):
    if r.sym(n.items[i]) not in (':accept',':why',':case'):
     result.extend(canon(x) for x in n.items[i:i+2])
   return result
  # Normalize only the intentional relocation of an existing status CASE
  # into its acquiring DO, which makes operation ownership conditional on OK.
  projected=[]
  for x in n.items:
   projected.append(canon(x))
   if r.head(x)==':do' and r.head(x.items[2])=='fn2-cns-stream-source-issue':
    branch=r.option(x,':case',3)
    if branch is not None:
     projected.append([':case',canon(x.items[1].items[0])]+[canon(c) for c in branch.items])
  xs=projected
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
      self.assertIn(name,('fn2-cns-stream-source-finish','fn2-cns-stream-source-clear','fn2-cns-stream-source-issue'))
      if name.endswith('issue'):
       self.assertEqual(r.codes(r.option(z,':accept',3)),[])
      else:self.assertEqual(canon(current),[[[':stale'],[':stop',':machine-phase']]])
 def test_effects_mutation_is_not_erased(self):
  a=lr.parse('(:do (c) (fn2-cns-stream-source-issue 1) :accept (:ok) :effects ((:acquire (:operation))))').forms[0]
  b=lr.parse('(:do (c) (fn2-cns-stream-source-issue 1) :accept (:ok) :effects ((:release (:operation))))').forms[0]
  self.assertNotEqual(canon(a),canon(b))
 def test_transform_preserves_issue_effects(self):
  case=json.loads((ROOT/'tests/fixtures/cns_source_status_routes.json').read_text())[0]
  source=case['text'];parsed=lr.parse(source)
  node=next(n for machine,name,n in r.sites(parsed) if name=='fn2-cns-stream-source-issue')
  mutant=lr.write(source,[(node.end-1,node.end-1,' :effects ((:acquire (:operation)))')])
  transformed=r.transform(mutant)
  self.assertEqual([canon(f) for f in lr.parse(mutant).forms],[canon(f) for f in lr.parse(transformed).forms])
  updated=next(n for machine,name,n in r.sites(lr.parse(transformed)) if name=='fn2-cns-stream-source-issue')
  self.assertEqual(canon(r.option(updated,':effects',3)),[[':acquire',[':operation']]])
 def test_actual_return_closure(self):
  from cns_source_status_returns import status_closure
  expected=set(r.codes(lr.parse(r.STEP).forms[0]))
  for fixture in json.loads((ROOT/'tests/fixtures/cns_source_status_returns.json').read_text()):
   with self.subTest(source=fixture['source']):
    actual,callees=status_closure(fixture['texts'])
    self.assertEqual(actual,expected)
    self.assertNotIn(':ok',actual)
    self.assertEqual(len(callees),6)
    mutant=[x.replace('(mv :more fn2-cns-sources', '(mv :ok fn2-cns-sources',1) for x in fixture['texts']]
    changed,_=status_closure(mutant)
    self.assertIn(':ok',changed)
    self.assertNotEqual(changed,expected)
 def test_missing_why_detected(self):
  src='(defcost fn2-ctl-stream-hash :answers (:ok :more :bounds)) (defmachine-arms fn2-ctl :declare :arms ((:stream (:do (c n) (fn2-ctl-stream-hash 1) :accept (:ok :more :bounds)) (:charge))))'
  self.assertTrue(any('why' in problem for _,problem in r.issues(src)))
 def test_missing_normal_routes_detected(self):
  src='(defcost fn2-cns-stream-source-issue :answers (:ok :wait :bad)) (defmachine-arms fn2-cns :declare :arms ((:source (:do (c o g) (fn2-cns-stream-source-issue 1)) (:charge))))'
  self.assertTrue(any(':wait' in problem and ':bad' in problem for _,problem in r.issues(src)))
if __name__=='__main__':unittest.main()
