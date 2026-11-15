#!/usr/bin/env python3
"""Concrete raw-source wiring controls; source only, no ACL2 evaluation."""
import copy
from pathlib import Path
import unittest
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def defs(path):return {n[1]:n for t in forms((ROOT/path).read_text()) for n in walk(read_sexp(t)) if len(n)>2 and n[0]=='defun'}
def calls(n):return [x[0] for x in walk(n) if x and isinstance(x[0],str)]
class RawSource(unittest.TestCase):
 def setUp(self):
  self.raw=defs('books/cns-source-raw.lisp');self.cap=defs('books/cns-source-capture.lisp')
 def test_same_live_read_copies_all_commitments_after_real_prefix_initialization(self):
  d=self.cap['fn2-cns-source-capture-read-children'];used=calls(d)
  self.assertLess(used.index('fn2-pool-reset'),used.index('fn2-run-zero'))
  self.assertLess(used.index('fn2-run-zero'),used.index('fn2-read-octets-children'))
  for name in ['*fn2-article-entry-field-source*','*fn2-article-entry-field-stored-source*','*fn2-article-entry-field-location-hashes*']:
   self.assertIn(name,str(d))
  self.assertNotIn('fn2-pool-set-fill',used)
 def test_external_capture_claims_root_atomically_and_never_releases_read(self):
  d=self.cap['fn2-cns-source-capture-children'];used=calls(d)
  self.assertLess(used.index('fn2-cns-source-capture-read-children'),used.index('fn2-cns-source-root-hold-children'))
  self.assertNotIn('fn2-read-release-children',used)
  self.assertNotIn('ready',d[2])
 def test_issue_requires_exact_current_hold_before_actual_pinned_read(self):
  d=self.raw['fn2-cns-source-issue-children'];used=calls(d)
  self.assertLess(used.index('fn2-cns-source-heldp'),used.index('fn2-block-read-children'))
  self.assertLess(used.index('fn2-pool-truncate'),used.index('fn2-block-read-children'))
  self.assertIn('fn2-cns-sources-uncertain',used)
  self.assertNotIn('fn2-issue-read-children',used)
 def test_harvest_binds_actual_slot_generation_cell_and_read_event(self):
  d=self.raw['fn2-cns-source-harvest'];nodes=list(walk(d))
  for expected in [['equal','cell','0'],['equal','event','*fn2-event-read-result*'],['equal','opgen',['fn2-cns-source-operations-generation','op','fn2-cns-source-operations']]]:
   self.assertIn(expected,nodes)
  self.assertIn('fn2-cns-sources-op-gen',calls(d))
  self.assertNotIn('fn2-pool-write',calls(d))
 def test_next_is_copy_only_append_exact_and_eof_rechecks_source(self):
  d=self.raw['fn2-cns-source-next-children'];used=calls(d);nodes=list(walk(d))
  for forbidden in ['fn2-block-read-children','fn2-block-read-commitment-children','fn2-cns-source-hash-update','fn2-cns-source-hash-finish']:
   self.assertNotIn(forbidden,used)
  self.assertIn(['equal','off',['fn2-pool-fill','slot','fn2-pool']],nodes)
  self.assertIn('fn2-cns-sources-hash-offset',used);self.assertIn('fn2-cns-sources-total',used)
  self.assertIn('fn2-pool-workspace-code',used)
  for n in nodes:
   if n and n[0]=='mv' and n[1]==':ok' and n[2]=='0':self.assertEqual(n[3],'t')
 def test_actor_uses_existing_unit_verifier_and_incremental_stored_hash(self):
  d=self.raw['fn2-cns-source-raw-step-children'];used=calls(d)
  for name in ['fn2-block-read-commitment-children','fn2-cns-source-hash-begin','fn2-cns-source-hash-update','fn2-cns-source-hash-finish','fn2-cns-sources-unit-hashed','fn2-cns-sources-hash-offset']:
   self.assertIn(name,used)
  self.assertIn('*fn2-cns-source-stored-offset*',str(d))
  self.assertIn(['min','1024','budget',['-','len','hashed']],list(walk(d)))
 def test_small_raw_check_budget_retains_all_mutable_carriers(self):
  d=self.raw['fn2-cns-source-raw-step-children']
  branches=[n for n in walk(d) if len(n)==2 and isinstance(n[0],list) and n[0] and n[0][0]=='when' and '*fn2-cns-source-phase-raw-check*' in str(n[0])]
  self.assertEqual(len(branches),1)
  first=branches[0][1][1][0]
  self.assertEqual(first,[['unless',['<=','*fn2-commit-unit-bytes*','budget']],['mv',':wait','fn2-cns-sources','fn2-b3','fn2-digests']])
  self.assertNotIn('fn2-block-read-commitment-children',calls(first))
 def test_prepared_six_kib_control_uses_actual_copy_claim_and_gap_refusal(self):
  text=(ROOT/'tests/cns-source-capture-unit.lisp').read_text()
  for name in ['UNEXECUTED','SYNTHETIC','fn2-cns-source-capture-children','fn2-cns-source-heldp','(equal total 6144)','(eq old1 :bounds)','(equal v1 0)']:
   self.assertIn(name,text)
  self.assertNotIn('fn2-pool-set-fill',text)
if __name__=='__main__':unittest.main()
