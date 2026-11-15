from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class LiveCatalog(unittest.TestCase):
 def setUp(self): self.s=(ROOT/'books/checkpoint-live-catalog.lisp').read_text()
 def test_actual_post_fence_gate(self):
  self.assertIn('(fn2-checkpoint-summary-authority-live-source-p ',self.s)
  self.assertIn('(fn2-checkpoint-live-catalog-current-p ',self.s)
  self.assertIn('(fn2-checkpoint-live-catalog-descriptor-p 0 ',self.s)
 def test_no_serving_publication(self):
  self.assertNotIn('fn2-run-install',self.s)
  self.assertNotIn('phase-applied*',self.s)
  self.assertNotIn('update-fn2-checkpoint-summary-descriptori i',self.s)
 def test_one_cell_per_step_with_exact_terminal_count(self):
  self.assertIn('(fn2-checkpoint-summary-cursor 1 ',self.s)
  self.assertIn('(fn2-checkpoint-summary-count 1 fn2-checkpoint-summary) (fn2-checkpoint-source-rank 0 fn2-checkpoint-source)',self.s)
  self.assertIn('(mv :occupied fn2-checkpoint-summary fn2-checkpoint-summary-sources)',self.s)
 def test_active_tag_never_overwritten(self):
  gate=self.s.index('(mv :occupied ');put=self.s.index('(fn2-checkpoint-summary-sources-put e')
  self.assertLess(gate,put)
  self.assertIn('(fn2-checkpoint-summary-sources-tag e fn2-checkpoint-summary-sources) (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary)',self.s)
if __name__=='__main__':unittest.main()
