"""Discriminating fixtures for the owned actual scheduler continuation class."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import lisp_rewrite as lr
from rewrite_checkpoint_teardown_arms import rewrite

class RetainedContinuationSourceTests(unittest.TestCase):
    def test_exact_actor_seams_and_refusal(self):
        # Each original named seam is present; unrelated bodies remain exact.
        src = '''(defmachine-arms fn2-checkpoint-master :declare :arms
 ((:idle (:park :checkpoint-needed))
  (:snapshot-release (:next :teardown-begin))
  (:teardown-begin (:set (scan 0)))
  (:teardown-source (:do (code) (fn2-checkpoint-teardown-inspect-op row-token k i g s)))
  (:teardown-submit (:do (code) (fn2-checkpoint-teardown-submit row-token k i g e p a)) ((:busy :exhausted) (:yield)))
  (:teardown-wait (:do (code) (fn2-checkpoint-teardown-poll *fn2-checkpoint-master-kind* id row-generation)))
  (:teardown-drop (:do (code) (fn2-checkpoint-teardown-drop-op row-token k i g e p a b)))
  (:teardown-retained (:set (stopped 1)) (:stop :checkpoint))
  (:catalog (:marker preserved))))'''
        out, count = rewrite(src)
        self.assertEqual(count, 9)
        lr.parse(out)
        self.assertIn('(:catalog (:marker preserved))', out)
        self.assertIn('((:busy :exhausted) (:park :checkpoint-needed))', out)
        self.assertIn('(fn2-checkpoint-teardown-poll row-debt-scan row-token', out)
        self.assertIn('(:next :teardown-transfer-begin)', out)
        self.assertIn('(:next :teardown-select)', out)
        self.assertEqual(rewrite(out), (out, 0))

    def test_actual_tree_is_idempotent(self):
        root = Path(__file__).resolve().parents[1]
        src = (root / 'books/checkpoint-master-arms.lisp').read_text()
        self.assertEqual(rewrite(src), (src, 0))
        self.assertIn('(:teardown-holding-uncertain (:set (stopped 1)) (:stop :checkpoint))', src)
        self.assertNotIn('(:teardown-retained (:set (stopped 1))', src)

if __name__ == '__main__':
    unittest.main()
