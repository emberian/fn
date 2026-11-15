from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class LiveHold(unittest.TestCase):
 def setUp(self):self.s=(ROOT/'books/checkpoint-live-cbase.lisp').read_text()
 def test_source_is_real_live_producer_not_cold_premise(self):
  self.assertIn('(fn2-checkpoint-live-catalog-current-p ',self.s)
  self.assertNotIn('fn2-checkpoint-restore-',self.s)
  self.assertNotIn('verified',self.s.replace('caller verified flags',''))
 def test_exact_promoted_source_before_canonical_mutation(self):
  check=self.s.index('(fn2-alloc-edge-matchesp source ')
  add=self.s.index('(fn2-alloc-edge-add target tag e epoch allocation :promised-read')
  self.assertLess(check,add)
  self.assertIn(':selectable-checkpoint fn2-alloc-edges)',self.s)
  self.assertIn('(= (fn2-extents-release-pending e fn2-extents) 0)',self.s)
  self.assertNotIn('fn2-extents-put',self.s)
 def test_one_edge_and_no_authority_on_refusal(self):
  self.assertEqual(self.s.count('(fn2-alloc-edge-add '),1)
  self.assertIn('(fn2-checkpoint-cbase-row-identity-p 1 ',self.s)
  self.assertIn('(mv :protected-source fn2-checkpoint-cbase-holds fn2-extents fn2-alloc-edges)',self.s)
  self.assertIn('(cursor (+ 1 e))',self.s)
 def test_no_visibility_or_eviction(self):
  for x in ['fn2-run-install','fn2-run-retire','fn2-pool-release','fn2-alloc-free']:
   self.assertNotIn('('+x+' ',self.s)
 def test_fixed_hash_leaf_guard_mentions_only_actual_carriers(self):
  s=(ROOT/'books/checkpoint-summary-authority-live.lisp').read_text()
  leaf=s[s.index('(defun fn2-checkpoint-summary-live-published-hash-p '):s.index('; The actual writer machine type')]
  for x in ['fn2-checkpoint-writer-wfp','fn2-machines-wfp','fn2-checkpoint-lifecycle-wfp']:
   self.assertNotIn(x,leaf)
if __name__=='__main__':unittest.main()
