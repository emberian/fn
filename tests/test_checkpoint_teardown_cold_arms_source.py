"""Source controls for actual physical-anchor transfer/ACK continuations."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import lisp_rewrite as lr
from rewrite_checkpoint_teardown_cold_arms import PHASES, kind, arms
class ColdContinuationSourceTests(unittest.TestCase):
    def test_exact_terminal_class_and_no_new_holds(self):
        src = '(defmachine fn2-checkpoint-master :states (:idle) :holds ((:work :storage-window)) :arms ((:idle)))'
        out, n = kind(src)
        self.assertEqual(n, 2)
        self.assertIn(':holds ((:work :storage-window))', out)
        for p in PHASES:
            self.assertEqual(out.count(p), 2)
        self.assertEqual(kind(out), (out, 0))

    def test_pending_before_done_and_exact_ack(self):
        src = '''(include-book "checkpoint-teardown-sweep")
(defmachine-arms fn2-checkpoint-master :declare :arms
 ((:teardown-transfer-begin :on-refusal ((:stop :checkpoint)) ((:none) (:next :done)))
  (:teardown-transfer-copy :on-refusal ((:stop :checkpoint)) ((:transferred) (:next :done)))
  (:foreign (:marker unchanged))))'''
        out, n = arms(src)
        self.assertEqual(n, 4)
        lr.parse(out)
        self.assertIn('(:foreign (:marker unchanged))', out)
        self.assertIn('((:none) (:set (scan 0)) (:next :teardown-cold-next))', out)
        self.assertIn('(fn2-checkpoint-teardown-cold-ack-op row-source) :accept (:transferred)', out)
        self.assertEqual(arms(out), (out, 0))

    def test_ambiguous_old_terminal_refused(self):
        src = '(:teardown-transfer-begin :on-refusal nil (:next :done) (:next :done))'
        with self.assertRaises(ValueError):
            arms(src)

    def test_actual_actor_matches_phase_class(self):
        root = Path(__file__).resolve().parents[1]
        state = (root / 'books/checkpoint-master-state.lisp').read_text()
        actor = (root / 'books/checkpoint-master-arms.lisp').read_text()
        self.assertEqual(kind(state), (state, 0))
        self.assertEqual(arms(actor), (actor, 0))
        for p in PHASES:
            self.assertEqual(len(lr.match('(' + p + ' :on-refusal ?*body)', lr.parse(actor).forms, deep=True)), 1)
        self.assertIn('(:teardown-holding-uncertain (:set (stopped 1)) (:stop :checkpoint))', actor)
if __name__ == '__main__':
    unittest.main()
