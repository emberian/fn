"""Source-only controls; actual canonical rebase and runtime remain unexecuted."""
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class Finish(unittest.TestCase):
 def test_single_authority_transfer_owner(self):
  s=(ROOT/'books/checkpoint-live-finish.lisp').read_text()
  self.assertNotIn('update-fn2-checkpoint-summary-authority-',s)
  self.assertNotIn('(fn2-checkpoint-summary-authority-put 0',s)
  self.assertNotIn('fn2-directory-rebase-transfer-bytes',s)
  self.assertIn('(fn2-checkpoint-summary-authority-set-catalog-tag 1',s)
  self.assertIn('*fn2-directory-rebase-phase-committed*',s)
  self.assertIn('*fn2-checkpoint-summary-authority-phase-idle*',s)
 def test_one_actual_cell_no_recursive_copy(self):
  s=(ROOT/'books/checkpoint-live-finish.lisp').read_text()
  helper=s[s.index('(defun fn2-checkpoint-live-copy-query-cell'):s.index('; A terminal read-only comparison')]
  self.assertEqual(helper.count('update-fn2-checkpoint-summary-descriptori'),1)
  self.assertEqual(helper.count('(fn2-checkpoint-summary-descriptori '),1)
  self.assertEqual(helper.count('fn2-checkpoint-live-copy-query-cell'),1)
  self.assertNotIn('(fn2-checkpoint-live-query-descriptor-p',helper)
  self.assertIn('(cursor 0)',s)
  self.assertIn('((unless (= i *fn2-commit-digest-bytes*))',s)
  self.assertNotIn('520',s)
 def test_partial_query_never_applied_and_pending_survives(self):
  s=(ROOT/'books/checkpoint-live-finish.lisp').read_text()
  pre=s[s.index('(defun fn2-checkpoint-live-replace-finish'):s.index('(defun fn2-checkpoint-live-replace-reopen')]
  self.assertNotIn('*fn2-checkpoint-summary-phase-applied*',pre)
  self.assertIn('*fn2-checkpoint-summary-phase-promoting*',pre)
  self.assertNotIn('*fn2-checkpoint-summary-phase-idle*',pre)
  post=s[s.index('(defun fn2-checkpoint-live-replace-reopen'):]
  self.assertLess(post.index('*fn2-directory-rebase-phase-committed*'),post.index('*fn2-checkpoint-summary-phase-applied*'))
 def test_no_new_resources_or_namespace_reset(self):
  s=(ROOT/'books/checkpoint-live-finish.lisp').read_text()
  for forbidden in ('pool-reserve','block-read','run-installed-put','run-installed-set-wire-run','writer-end'):
   self.assertNotIn(forbidden,s)
  clear=s[s.index('(fn2-c-source-control (fn2-c-source-control-put 0'):]
  self.assertNotIn('(next-receipt ',clear);self.assertNotIn('(readers ',clear)
  self.assertNotIn('fn2-c-source-readers-put',s)
 def test_actual_controls_and_invariant_not_wfp_surrogate(self):
  s=(ROOT/'tests/checkpoint-live-finish-unit.lisp').read_text()
  self.assertIn('(fn2-clf-promote 40 0 fn2-core)',s)
  self.assertIn('(= copied 33)',s)
  self.assertIn('(eq early :source)',s)
  self.assertIn('(equal before-consume (fn2-clf-snapshot fn2-core))',s)
  c=(ROOT/'tests/checkpoint-live-catalog-unit.lisp').read_text()
  self.assertIn('(fn2-c-source-count-invariant-p fn2-c-source-control fn2-c-source-readers)',c)
  self.assertIn('((unless (fn2-clc-observers-consistent fn2-core))',c)
 def test_payload_charge_counts_read_and_write(self):
  s=(ROOT/'books/checkpoint-live-finish.lisp').read_text()
  self.assertIn('(+ *fn2-checkpoint-live-promotion-preflight-bytes* 2)',s)
  self.assertIn('(* 2 *fn2-commit-digest-bytes*)',s)
  self.assertIn('not a proved physical-work refinement',s)
if __name__=='__main__':unittest.main()
