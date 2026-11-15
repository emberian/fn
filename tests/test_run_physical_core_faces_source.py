#!/usr/bin/env python3
"""Derive face shapes from actual source carriers; no ACL2 admission claim."""
import re,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_source as ls
BOOKS={'reserve':'resources','bind':'source','step':'step','read':'io','release':'release'}
SCALARS={'reserve':['c','kind','owner','generation'],'bind':['c','kind','owner','generation'],'release':['c','kind','owner','generation'],'step':['c','budget'],'read':['c','budget']}
OUTPUTS={'reserve':['fn2-run-loads','fn2-pool'],'bind':['fn2-run-loads','fn2-checkpoint-summary','fn2-checkpoint-summary-leases','fn2-pool'],'step':['fn2-run-loads','fn2-run-cursors','fn2-fc','fn2-fc-context','fn2-b3','fn2-fields','fn2-pool','fn2-digests'],'read':['fn2-run-loads','fn2-run-load-ops','fn2-pool','fn2-ops','fn2-control','fn2-extents','fn2-alloc-edges'],'release':['fn2-run-loads','fn2-run-cursors','fn2-checkpoint-summary','fn2-checkpoint-summary-leases','fn2-pool']}
def forms(p):return [ls.read_sexp(x) for x in ls.forms((ROOT/p).read_text())]
def pick(fs,head,name):
 found=[x for x in fs if isinstance(x,list) and x[:2]==[head,name]]
 if len(found)!=1:raise AssertionError((head,name,len(found)))
 return found[0]
class PhysicalFaces(unittest.TestCase):
 def test_five_costs_bind_actual_source_abis_and_frames(self):
  costs=forms('books/machines-c.lisp')
  for op,book in BOOKS.items():
   child='fn2-run-load-'+('issue' if op=='read' else op)
   fs=forms('books/run-physical-'+book+'.lisp');f=pick(fs,'defun',child)
   self.assertEqual([x for x in f[2] if not x.startswith('fn2-')],SCALARS[op])
   cost=pick(costs,'defcost','fn2-run-page-'+op)
   self.assertEqual(cost[cost.index(':child')+1],child)
   fr=pick(fs,'fn2-run-load-frames',child);outs=fr[4]
   self.assertEqual([x[0] for x in outs],OUTPUTS[op])
   scalars=3 if op=='read' else 1
   self.assertEqual([int(x[1]) for x in outs],list(range(scalars,scalars+len(outs))))
   self.assertLessEqual(scalars+len(outs),32)
   self.assertEqual(fr[2],f[2])
   self.assertEqual(fr[3],[x for x in f[2] if x.startswith('fn2-')])
 def test_compiler_projects_only_actual_stobjs_out_and_frames(self):
  s=(ROOT/'books/machine-arms.lisp').read_text();a=s.index('(defun fn2-arms-op-face-events');b=s.index('(defun fn2-arms-book-op-faces-1',a);s=s[a:b]
  for x in ("'stobjs-in","'stobjs-out",'fn2-arms-nonstobj-formals','fn2-arms-binders outs','fn2-arms-op','fn2-core-preserves'):
   self.assertIn(x,s)
  s=(ROOT/'books/run-physical-core-faces.lisp').read_text()
  self.assertIn('(fn2-arms-op-face-events op child world)',s)
  self.assertIn('(not (function-symbolp op world))',s)
  self.assertIn('(and row child (function-symbolp child world))',s)
  for op in BOOKS:self.assertNotIn('(defun fn2-run-page-'+op,s)
 def test_explicit_read_issue_effect_and_identity_events(self):
  fs=forms('books/machines-c.lisp');c=pick(fs,'defcost','fn2-run-page-read')
  self.assertEqual(int(c[c.index(':descriptors')+1]),1)
  self.assertEqual(c[c.index(':effects')+1],[[":acquire",[":operation"]]])
  s=(ROOT/'books/machines-c.lisp').read_text()
  for name in ('fn2-issue-wrapper-effect-events','fn2-issued-wrapper-events'):self.assertIn("("+name+" '(fn2-run-load-issue)",s)
 def test_materialization_precedes_actual_c_consumers(self):
  s=(ROOT/'books/assembly-callbacks-c-prepare.lisp').read_text()
  self.assertLess(s.index('(fn2-run-page-core-faces)'),s.index('(fn2-successor-prepare-events)'))
 def test_actual_prepare_local_include_dag(self):
  done=set()
  def visit(p,stack):
   self.assertNotIn(p,stack)
   if p in done:return
   self.assertTrue(p.exists(),p)
   for line in p.read_text().splitlines():
    m=re.match(r'\s*\(include-book "([^"]+)"',line)
    if m and ':dir' not in line:visit((p.parent/(m[1]+'.lisp')).resolve(),stack+[p])
   done.add(p)
  visit(ROOT/'books/assembly-callbacks-c-prepare.lisp',[])
if __name__=='__main__':unittest.main()
