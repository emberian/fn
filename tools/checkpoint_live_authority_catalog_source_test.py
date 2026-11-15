"""Actual pending catalog/publication join and master close route."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import checkpoint_live_authority_catalog_rewrite as bind
import checkpoint_live_close_phase_rewrite as phase
ROOT=Path(__file__).resolve().parents[1];B=ROOT/'books';F=ROOT/'tools/fixtures'
def fn(s,name):return lr.match(f'(defun {name} ?*body)',lr.parse(s).forms)[0].node
class Join(unittest.TestCase):
 def test_existing_authority_class_replay(self):
  self.assertEqual((B/'checkpoint-summary-authority-live.lisp').read_text(),bind.rewrite((F/'checkpoint-live-catalog-authority-before.lisp').read_text()))
 def test_master_uses_actual_close_operation(self):
  a,b=phase.rewrite((F/'checkpoint-live-close-checkpoint-master-state.lisp').read_text(),(F/'checkpoint-live-close-checkpoint-master-arms.lisp').read_text())
  self.assertEqual(a,(B/'checkpoint-master-state.lisp').read_text());self.assertEqual(b,(B/'checkpoint-master-arms.lisp').read_text())
  self.assertIn('(fn2-checkpoint-summary-live-close-op) :accept (:captured)',b)
 def test_close_requires_full_actual_authority(self):
  s=(B/'checkpoint-summary-live-close.lisp').read_text();n=fn(s,'fn2-checkpoint-summary-live-close-source-p')
  self.assertTrue(lr.match('(fn2-checkpoint-summary-authority-row-complete-p 1 ?*args)',[n]))
  for field in ['candidate','checkpoint','cut-commit','cut-event','history','incarnation','owner-kind','owner-slot','owner-gen']:
   self.assertTrue(lr.match(f'(= (fn2-checkpoint-summary-{field} 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-authority-{field} 1 fn2-checkpoint-summary-authority))',[n]))
  self.assertTrue(lr.match('(= (fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-authority-catalog-tag 1 fn2-checkpoint-summary-authority))',[n]))
 def test_no_mutable_source_scratch_in_close(self):
  s=(B/'checkpoint-summary-live-close.lisp').read_text()
  for forbidden in ['fn2-checkpoint-metadata','fn2-run-builds','fn2-pool']:
   self.assertNotIn(forbidden,s)
  n=fn(s,'fn2-checkpoint-summary-live-copy-descriptor')
  self.assertTrue(lr.match('(fn2-checkpoint-summary-authority-descriptori (+ 32 i) fn2-checkpoint-summary-authority)',[n]))
 def test_actual_producer_binds_catalog_tag_and_count(self):
  s=(B/'checkpoint-summary-authority-live.lisp').read_text();n=fn(s,'fn2-checkpoint-summary-authority-live-source-p')
  self.assertTrue(lr.match('(fn2-checkpoint-summary-live-current-p ?*args)',[n]))
  self.assertTrue(lr.match('(= (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary) (fn2-checkpoint-source-rank 0 fn2-checkpoint-source))',[n]))
  n=fn(s,'fn2-checkpoint-summary-authority-live-begin')
  self.assertTrue(lr.match('(catalog-tag (fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary))',[n]))
if __name__=='__main__':unittest.main()
