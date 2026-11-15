"""Retained catalog lifetime controls; this does not execute ACL2."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def fn(source,name):
 m=lr.match('(defun ?name ?*body)',lr.parse(source).forms,name=name)
 if len(m)!=1:raise ValueError(name)
 return m[0].node
def need(n,p):
 if not lr.match(p,[n]):raise ValueError(p)
def cold_step(source):
 n=fn(source,'fn2-event-catalog-cold-step')
 for p in ['(fn2-directory-cold-source-p ?*args)',
 '(= (fn2-checkpoint-restore-events-generation 1 fn2-checkpoint-restore-events) (fn2-checkpoint-restore-events-generation 0 fn2-checkpoint-restore-events))',
 '(fn2-event-catalog-descriptor-p 0 ?*args)',
 '(dst (+ n ordinal))','(< src n)',
 '(fn2-checkpoint-restore-events-work-put dst ?*args (extent src) ?*rest)',
 '(fn2-event-catalog-copy-seal 0 src dst ?*args)']:
  need(n,p)
class Source(unittest.TestCase):
 def test_exact_selected_source_and_disjoint_transfer(self):
  cold_step((ROOT/'books/event-catalog-cold.lisp').read_text())
 def test_candidate_generation_change_refuses(self):
  s=(ROOT/'books/event-catalog-cold.lisp').read_text().replace('(= (fn2-checkpoint-restore-events-generation 1 fn2-checkpoint-restore-events) (fn2-checkpoint-restore-events-generation 0 fn2-checkpoint-restore-events))','t')
  with self.assertRaises(ValueError):cold_step(s)
 def test_transfer_cannot_alias_scratch(self):
  s=(ROOT/'books/event-catalog-cold.lisp').read_text().replace('(dst (+ n ordinal))','(dst ordinal)')
  with self.assertRaises(ValueError):cold_step(s)
 def test_every_actual_scratch_loop_stays_in_first_stripe(self):
  for p in ['checkpoint-restore-events','checkpoint-restore-events-source']:
   s=(ROOT/('books/'+p+'.lisp')).read_text()
   self.assertFalse(lr.match('(fn2-checkpoint-restore-events-work-rows ?*args)',lr.parse(s).forms))
 def test_both_startup_modes_reserve_the_same_two_lifetimes(self):
  s=(ROOT/'books/boot-kind.lisp').read_text()
  self.assertIn('(fn2-checkpoint-restore-events-init 2 fn2-checkpoint-restore-events)',s)
  self.assertIn('(fn2-checkpoint-restore-events-work-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-events-work)',s)
 def test_live_append_copies_actual_resident_source(self):
  n=fn((ROOT/'books/event-catalog-live.lisp').read_text(),'fn2-event-catalog-live-step')
  for p in ['(fn2-commit-directory-lookup batch ?*args)', '(fn2-commit-directory-seal-slot batch ?*args)',
            '(fn2-checkpoint-source-claimedp c ?*args)', '(dst (+ n count))',
            '(= (fn2-checkpoint-restore-events-work-generation dst fn2-checkpoint-restore-events-work) 0)',
            '(fn2-event-catalog-copy-descriptor-from-row 1 0 ?*args)',
            '(fn2-event-catalog-copy-resident-seal 0 seal dst ?*args)']:
   need(n,p)
 def test_source_requires_actual_exact_owned_protection(self):
  n=fn((ROOT/'books/event-catalog.lisp').read_text(),'fn2-event-catalog-held-p')
  need(n,'(member (fn2-extents-state e fn2-extents) (list *fn2-extent-state-allocated* *fn2-extent-state-retire-pending*))')
  for kind in [':installed-root',':recovery-base',':selectable-checkpoint']:
   need(n,'(fn2-alloc-edge-matchesp ?*args '+kind+' fn2-alloc-edges)')
if __name__=='__main__':unittest.main()
