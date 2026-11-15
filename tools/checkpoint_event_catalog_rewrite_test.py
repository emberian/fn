from pathlib import Path
import unittest
from checkpoint_event_catalog_rewrite import scratch_capacity,undo_capacity
class Rewrite(unittest.TestCase):
 def test_first_stripe_specialization_preserves_source(self):
  s='(defun cold (e s) (and (< e (fn2-checkpoint-restore-events-work-rows fn2-checkpoint-restore-events-work)) (preserves fn2-checkpoint-restore-events-work-rows)))'
  out=scratch_capacity(s,1)
  self.assertEqual(undo_capacity(out),s)
  self.assertIn('(preserves fn2-checkpoint-restore-events-work-rows)',out)
 def test_unknown_subject_refuses(self):
  with self.assertRaises(ValueError):scratch_capacity('(fn2-checkpoint-restore-events-work-rows other)',1)
 def test_count_drift_refuses(self):
  with self.assertRaises(ValueError):scratch_capacity('(fn2-checkpoint-restore-events-work-rows fn2-checkpoint-restore-events-work)',2)
if __name__=='__main__':unittest.main()
