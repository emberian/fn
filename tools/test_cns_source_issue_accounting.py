#!/usr/bin/env python3
"""Actual-source effect/report controls. ACL2 fixtures remain unexecuted."""
from pathlib import Path
import copy
import unittest
import lisp_rewrite as lr
import cns_read_observer_rewrite as rw
from lisp_source import read_all
ROOT=Path(__file__).resolve().parents[1]
def issue(source):
 p=lr.parse(source)
 return next(n for f in p.forms for n in rw.walk(f)
  if rw.head(n)==':do' and len(n.items)>2 and rw.head(n.items[2])=='fn2-cns-stream-source-issue')
def sexp(n):
 if isinstance(n,lr.Lst):return [sexp(x) for x in n.items]
 if isinstance(n,lr.Pre):return [n.prefix,sexp(n.node)]
 return n.low
def reports(node):
 n=sexp(node);cases=n[n.index(':case')+1]
 return {branch[0][0] if isinstance(branch[0],list) else branch[0]:
    next(x for x in reversed(branch[1:]) if x[0]==':charge') for branch in cases}
def set_descriptors(node,label,value):
 node=copy.deepcopy(node)
 cases=node[node.index(':case')+1]
 for b in cases:
  key=b[0][0] if isinstance(b[0],list) else b[0]
  if key==label:
   c=next(x for x in reversed(b[1:]) if x[0]==':charge')
   c[c.index(':descriptors')+1]=str(value)
 return node
def effect_reports_valid(node):
 cases=node[node.index(':case')+1]
 expected={':ok':'1',':wait':'0',':otherwise':'0'}
 for b in cases:
  key=b[0][0] if isinstance(b[0],list) else b[0]
  c=next(x for x in reversed(b[1:]) if x[0]==':charge')
  if c[c.index(':descriptors')+1]!=expected[key]:return False
 return True
class SourceIssueAccounting(unittest.TestCase):
 def test_exact_descriptor_report_and_only_two_charge_fields_change(self):
  before=sexp(issue((ROOT/'tests/fixtures/cns_source_issue_descriptor_before.lisp').read_text()))
  after=sexp(issue((ROOT/'books/cns.lisp').read_text()))
  self.assertEqual(after,set_descriptors(set_descriptors(before,':wait',0),':otherwise',0))
  self.assertTrue(effect_reports_valid(after))
  self.assertFalse(effect_reports_valid(before))
  for label in (':wait',':otherwise'):
   self.assertFalse(effect_reports_valid(set_descriptors(after,label,1)))
  self.assertFalse(effect_reports_valid(set_descriptors(after,':ok',0)))
 def test_shared_typed_ops_facts_cover_child_and_actual_core_face(self):
  proof=(ROOT/'books/cns-source-issue-accounting.lisp').read_text()
  self.assertIn("(fn2-issue-wrapper-effect-events '(fn2-cns-source-issue-children)",proof)
  self.assertIn("(fn2-issued-wrapper-events '(fn2-cns-source-issue-children)",proof)
  core=(ROOT/'books/cns-source-core.lisp').read_text()
  for fn in ('fn2-cns-source-issue-core','fn2-cns-stream-source-issue'):
   for producer in ('fn2-issue-core-effect-event','fn2-issue-core-issued-event'):
    self.assertIn(f"({producer} '{fn}",core)
 def test_actual_fixture_whole_guard_images_and_independent_oracle(self):
  src=(ROOT/'tests/cns-source-issue-unit.lisp').read_text()
  read_all(src,strict=True)
  p=lr.parse(src)
  defs={rw.sym(n.items[1]):n for n in p.forms if rw.head(n)=='defun'}
  model=defs['fn2-csi-positive-model']
  calls=[rw.head(n) for n in rw.walk(model)]
  self.assertFalse(any(x.startswith('fn2-') and not x.startswith('fn2-csi-') for x in calls))
  body=defs['fn2-csi-unit-body'];used=[rw.head(n) for n in rw.walk(body)]
  self.assertEqual(used.count('fn2-cns-source-issue-children'),3)
  for fn in ('fn2-cns-source-root-hold-children','fn2-pool-query-acquire','fn2-pool-query-release','fn2-op-reserve','fn2-op-enqueue'):
   self.assertIn(fn,used)
  self.assertEqual(used.count('fn2-csi-domainp'),4)
  for exact in ('(equal after expected)','(equal before positive-before)',
                '(equal before (fn2-csi-snapshot','(equal wait-before (fn2-csi-snapshot'):
   self.assertIn(exact,src)
 def test_fixture_actual_call_arities_and_schema_names(self):
  definitions={};schemas={}
  for path in (ROOT/'books').glob('*.lisp'):
   try:p=lr.parse(path)
   except lr.ReadError:continue
   for f in p.forms:
    for n in rw.walk(f):
     if rw.head(n)=='defun' and len(n.items)>2 and isinstance(n.items[2],lr.Lst):
      definitions.setdefault(rw.sym(n.items[1]),set()).add(len(n.items[2].items))
    if rw.head(f)=='defcolumns' and isinstance(f.items[2],lr.Lst):
     name=rw.sym(f.items[1]);schemas[name]={name+'-'+rw.sym(c.items[0])+'$a' for c in f.items[2].items}
  source=(ROOT/'tests/cns-source-issue-unit.lisp').read_text();p=lr.parse(source)
  checked=0
  for f in p.forms:
   if rw.head(f)!='defun':continue
   for n in rw.walk(f.items[-1]):
    if isinstance(n,lr.Lst) and rw.head(n) and rw.head(n) in definitions:
     self.assertIn(len(n.items)-1,definitions[rw.head(n)],rw.head(n));checked+=1
  self.assertEqual(checked,23)
  # Every independent row update addresses an actual declared schema column.
  for f in p.forms:
   for n in rw.walk(f):
    if rw.head(n)=='cons' and len(n.items)>1 and isinstance(n.items[1],lr.Pre):
     field=rw.sym(n.items[1].node)
     if field.endswith('$a'):
      owner=max((name for name in schemas if field.startswith(name+'-')),key=len)
      self.assertIn(field,schemas[owner])
if __name__=='__main__':unittest.main()
