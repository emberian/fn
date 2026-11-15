"""Actual frozen producer source and mutation controls, no ACL2 execution."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk

def tree(name):return [read_sexp(f) for f in forms((ROOT/'books'/name).read_text())]
def function(name,fn):return next(n for f in tree(name) for n in walk(f) if n[:2]==['defun',fn])
def pending_only(code):
 return all(x in str(code) for x in ('*fn2-release-evidence-phase-persisted*','*fn2-release-evidence-phase-settled*','fn2-release-evidence-row-owned-p'))
class Producer(unittest.TestCase):
 def test_pending_and_settled_have_different_target_semantics(self):
  row=function('release-inventory-source.lisp','fn2-release-inventory-row-code')
  self.assertTrue(pending_only(row))
  self.assertFalse(pending_only(str(row).replace('*fn2-release-evidence-phase-settled*','MUTATION')))
  calls=list(walk(row))
  settled=next(i for i,n in enumerate(calls) if n==['when',['=','phase','*fn2-release-evidence-phase-settled*']])
  target=next(i for i,n in enumerate(calls) if n[:2]==['e',['fn2-release-evidence-extent','journal','fn2-release-evidence']])
  self.assertLess(settled,target)
  self.assertIn('fn2-alloc-handle-code',str(row))
 def test_real_cut_and_complete_E_scan_dominate_source(self):
  s=(ROOT/'books/release-inventory-source.lisp').read_text()
  owner=[function('release-inventory-source.lisp','fn2-release-inventory-owner-p'),function('release-inventory-source.lisp','fn2-release-inventory-subject-p')]
  for name in ('fn2-csnapshot-ownerp','fn2-checkpoint-builder-ownerp','fn2-alloc-freeze-token','fn2-alloc-freeze-owner-gen'):
   self.assertIn(name,str(owner))
  done=[function('release-inventory-source.lisp','fn2-release-inventory-complete-p'),function('release-inventory-source.lisp','fn2-release-inventory-source-terminal-p')]
  for name in ('fn2-release-inventory-build-scan','fn2-release-inventory-build-rows-count','fn2-release-inventory-build-cursor','fn2-release-inventory-build-remaining','fn2-release-inventory-build-completed-pages','fn2-checkpoint-page-completed-extent-p'):
   self.assertIn(name,str(done))
  self.assertNotIn('(defcost fn2-release-inventory-complete-p',s)
  self.assertNotIn('(:ready',s)
 def test_real_reserve_header_and_handback_pipeline(self):
  s=(ROOT/'books/release-inventory-source.lisp').read_text()
  for name in ('fn2-checkpoint-construction-reserve','fn2-checkpoint-linked-header-pack','fn2-checkpoint-page-pack-header','fn2-checkpoint-page-begin','fn2-checkpoint-page-complete-p'):
   self.assertIn(name,s)
  consume=next(n for f in tree('release-inventory-source.lisp') for n in walk(f) if n[:2]==['fn2-release-inventory-operation','fn2-release-inventory-consume'])
  self.assertIn('fn2-pool-workspace-code',str(consume))
  self.assertIn('fn2-checkpoint-page-transferred',str(consume))
  self.assertNotIn('(fn2-alloc-commit',s);self.assertNotIn('(fn2-alloc-release',s)
 def test_pending_inventory_claims_only_the_three_actual_proof_resources(self):
  forms_=tree('release-inventory-source.lisp')
  helper=next(n for f in forms_ for n in walk(f) if n[:2]==['fn2-release-inventory-operation','fn2-release-inventory-claim-pending'])
  claims=[n for n in walk(helper) if n and n[0]=='fn2-checkpoint-source-claim']
  self.assertEqual(len(claims),3)
  self.assertEqual([n[3] for n in claims],['descriptor','installation','journal'])
  self.assertNotIn('fn2-release-evidence-extent',str(helper))
  for target in ('descriptor','installation','journal'):
   self.assertIn(['=',['fn2-extents-state',target,'fn2-extents'],'*fn2-extent-state-allocated*'],list(walk(helper)))
  outputs=next(f[2][1] for f in forms_ if f[:2]==['defconst','*fn2-release-inventory-source-outputs*'])
  self.assertIn('fn2-alloc-edges',outputs)
 def test_one_generated_numeric_source_has_no_catalog_indices(self):
  forms_=tree('release-inventory-source.lisp')
  mapping=next(f[2][1] for f in forms_ if f[:2]==['defconst','*fn2-release-inventory-numeric-bindings*'])
  self.assertEqual(len(mapping),29)
  self.assertEqual(len({r[0] for r in mapping}),29)
  self.assertNotIn('candidate',[r[0] for r in mapping])
  self.assertEqual(dict(mapping)['journal-extent'],':row')
  self.assertEqual(dict(mapping)['journal-history'],'journal-history')
  self.assertEqual(dict(mapping)['installation-history'],'installation-history')
  self.assertEqual(dict(mapping)['history'],'history')
if __name__=='__main__':unittest.main()
