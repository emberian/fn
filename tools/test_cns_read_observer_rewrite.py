#!/usr/bin/env python3
"""Frozen actual callback projection controls; no ACL2 world or runtime claim."""
import json
from pathlib import Path
import unittest
import lisp_rewrite as lr
import cns_read_observer_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
FIX=ROOT/'tests/fixtures/cns_read_observer_targets.json'
R=(ROOT/'tools/cns_read_observer_refresh.lisp').read_text()
M=(ROOT/'tools/cns_read_observer_mid.lisp').read_text()
def nodes(source,head,name):
 p=lr.parse(source)
 return [n for f in p.forms for n in rw.walk(f) if rw.head(n)==head and len(n.items)>1 and rw.sym(n.items[1])==name]
def calls(node,name):return [n for n in rw.walk(node) if rw.head(n)==name]
def arms(source,key):
 p=lr.parse(source);body=rw.named(p.forms,'defmachine-arms','fn2-cns');return {rw.head(n):n for n in rw.value(body,key).items}
class Projection(unittest.TestCase):
 def test_actual_root_and_streamed(self):
  for case in json.loads(FIX.read_text()):
   with self.subTest(source=case['source']):
    before=case['callbacks'];kind=case['kind'];after=rw.transform_callbacks(before,R,M);k=rw.transform_kind(kind)
    lr.parse(after);lr.parse(k)
    # Every CTL form and the old CNS draining branch are exactly untouched.
    b=lr.parse(before);a=lr.parse(after)
    ctlb=[rw.text(b,n) for n in nodes(before,'defmachine-arms','fn2-ctl')]
    ctla=[rw.text(a,n) for n in nodes(after,'defmachine-arms','fn2-ctl')]
    self.assertEqual(ctlb,ctla)
    self.assertEqual(rw.text(b,arms(before,':arms')[':draining']),rw.text(a,arms(after,':arms')[':draining']))
    new=arms(after,':arms');subs=arms(after,':subarms')
    for phase in (':decode',':check',':lookup',':read',':page',':refresh'):
     self.assertEqual(len(calls(new[phase],'fn2-cns-request-acquire')),1)
    for phase in (':commit',':committed',':append',':park'):
     self.assertEqual(rw.head(new[phase].items[3]),':do')
     self.assertEqual(rw.head(new[phase].items[3].items[2]),'fn2-cns-request-release')
    for name in ('hand','cancel','page-end','page-fail','page-cancel'):
     self.assertEqual(rw.head(subs[name].items[3].items[2]),'fn2-cns-request-release')
    self.assertFalse(calls(new[':commit'],'fn2-cns-lookup-cursor'))
    self.assertFalse(calls(new[':committed'],'fn2-cns-lookup-cursor'))
    self.assertEqual(len(calls(new[':refresh'],'fn2-cns-lookup-cursor')),1)
    for cost in [n for n in a.forms if rw.head(n)=='defcost' and rw.sym(n.items[1]).startswith('fn2-cns-')]:
     try:tables=rw.value(cost,':tables')
     except ValueError:continue
     if any(rw.sym(x)=='fn2-core-reads' for x in tables.items):
      self.assertIn('fn2-core-c-source-control',[rw.sym(x) for x in tables.items])
      self.assertIn('fn2-core-c-source-readers',[rw.sym(x) for x in tables.items])
    if case['streamed']:
     opened=nodes(after,'defun','fn2-cns-stream-source-open')[0]
     self.assertFalse(calls(opened,'fn2-cns-entry-mid'))
     self.assertTrue(calls(opened,'fn2-cns-row-mid-checked'))
     self.assertEqual(len(calls(subs['item'],'fn2-cns-stream-source-check-mid')),1)
    # Inserted call-result names are globally fresh. A PAGE end can
    # drop metadata, then reach HAND in the same generated arm path.
    oldvars={rw.sym(v) for n in rw.walk(rw.named(b.forms,'defmachine-arms','fn2-cns'))
             if rw.head(n)==':do' for v in n.items[1].items}
    added=[rw.sym(v) for n in rw.walk(rw.named(a.forms,'defmachine-arms','fn2-cns'))
           if rw.head(n)==':do' and rw.head(n.items[2]) in
             ('fn2-cns-request-acquire','fn2-cns-request-release','fn2-cns-stream-source-check-mid')
           for v in n.items[1].items]
    self.assertEqual(len(added),len(set(added)))
    self.assertFalse(oldvars.intersection(added))
    # PAGE's actual record BREAD branch remains covered by its metadata
    # parent; unlike pool admission, it must not drop before this issue.
    if case['streamed']:
     item=next(n for n in rw.walk(subs['item']) if rw.head(n)==':cond')
     record=next(n for n in item.items[1:] if rw.head(n.items[0])=='equal' and
                 any(rw.sym(x)=='*fn2-fnct-item-record*' for x in n.items[0].items))
    else:record=subs['item']
    self.assertFalse(calls(record,'fn2-cns-request-release'))
    self.assertTrue(calls(record,'fn2-block-read'))
    page=rw.text(a,new[':page'])
    self.assertLess(page.index('fn2-cns-request-release'),page.index('fn2-cns-lease-reserve'))
    self.assertEqual(rw.transform_callbacks(after,R,M),after)
    self.assertEqual(rw.transform_kind(k),k)
 def test_missing_protocol_refuses(self):
  case=json.loads(FIX.read_text())[0]
  broken=case['callbacks'].replace('(:committed :on-refusal','(:missing-committed :on-refusal',1)
  with self.assertRaises((ValueError,KeyError)):rw.transform_callbacks(broken,R,M)
 def test_partial_join_refuses(self):
  case=json.loads(FIX.read_text())[0]
  joined=rw.transform_callbacks(case['callbacks'],R,M)
  partial=joined.replace('fn2-cns-request-release id row-generation','fn2-missing-release id row-generation',1)
  with self.assertRaises(ValueError):rw.transform_callbacks(partial,R,M)
  kind=rw.transform_kind(case['kind']).replace('(mid-checked :bool)','')
  with self.assertRaises(ValueError):rw.transform_kind(kind)
if __name__=='__main__':unittest.main()
