"""Actual event-source integration controls; no ACL2 execution claim."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import rewrite_release_inventory_event_abi as abi
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk

def text(name):return (ROOT/'books'/(name+'.lisp')).read_text()
class EventInventory(unittest.TestCase):
 def test_structural_signature_return_and_typed_domain_class(self):
  src='(defun fn2-event-producer-step (budget a) (declare (xargs :stobjs (a) :guard (and (ap a)))) (mv :more '+' '.join(abi.OLDOUTS['fn2-event-producer-step'])+'))'
  out,n=abi.rewrite(src);self.assertGreater(n,0);self.assertEqual(abi.rewrite(out),(out,0))
  for table in abi.ADDS['fn2-event-producer-step']:
   self.assertIn('('+table+'p '+table+')',out)
   self.assertIn('('+table+'-wfp '+table+')',out)
  self.assertTrue(out.endswith('fn2-release-inventory-build))'))
  for name in abi.FILES:self.assertEqual(abi.rewrite(text(name)),(text(name),0),name)
 def test_actual_writer_uses_inventory_between_directory_and_frontier(self):
  build=text('event-build');producer=text('event-producer')
  self.assertIn('(phase *fn2-event-build-phase-inventory-begin*) (role 4)',build)
  for name in ('fn2-release-inventory-begin','fn2-release-inventory-source-step','fn2-release-inventory-source-terminal-p'):
   self.assertIn('('+name,producer)
  self.assertIn('(fn2-event-frontier-put-ref "INVENTORY-" base inventory-head 32 scratch sgen)',build)
  self.assertIn('(fn2-release-inventory-complete-p fn2-release-inventory-build',build)
  self.assertIn('(fn2-checkpoint-linked-hash-buffer 32 0 32 inventory-head',build)
  self.assertIn('(* frontier-pages *fn2-format-page-size*)',build)
  self.assertIn('(+ 1 (fn2-release-inventory-build-pages 0 fn2-release-inventory-build))',producer)
 def test_actual_bind_consume_share_page_worker_and_distinct_owner(self):
  source=text('event-inventory-pages');kind=text('event-build-kind')
  for name in ('fn2-event-inventory-subject-p','fn2-release-inventory-bind','fn2-release-inventory-consume','fn2-event-build-bind-page','fn2-event-build-consume-page'):
   self.assertIn('('+name,source)
  self.assertNotIn('(fn2-issue-write',source);self.assertNotIn('(fn2-alloc-free',source)
  self.assertIn(':child fn2-event-producer-bind-page',kind)
  self.assertIn(':child fn2-event-producer-consume-page',kind)
  self.assertEqual(kind.count('(defcorechild fn2-core-release-inventory-build '),1)
 def test_actual_changed_lower_call_arities(self):
  sources=[text(n) for n in abi.FILES]+[(ROOT/'tests'/(n+'.lisp')).read_text() for n in ('event-build-unit','event-producer-unit')]
  parsed=[lr.parse(s).forms for s in sources];counts={}
  for tree in parsed:
   for m in lr.match('(defun ?name ?args ?*body)',tree):
    name=m.captures['name'].low
    if name in abi.ADDS:counts[name]=len(m.captures['args'].items)
  self.assertEqual(set(counts),set(abi.ADDS))
  for tree in parsed:
   for name,count in counts.items():
    for m in lr.match('('+name+' ?*args)',tree):self.assertEqual(len(m.node.items)-1,count,name)
if __name__=='__main__':unittest.main()
