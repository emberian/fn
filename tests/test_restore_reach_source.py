"""Structural controls; these never evaluate ACL2 restore decisions."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from restore_reach_source import rewrite

class ReachSourceTests(unittest.TestCase):
    def test_readonly_carriers_and_idempotency(self):
        src = '(defun fn2-checkpoint-restore-reach-claim (fn2-source fn2-dest) (declare (xargs :stobjs (fn2-source fn2-dest) :verify-guards nil)) fn2-dest)'
        out, count = rewrite(src)
        self.assertEqual(count, 1)
        self.assertIn('(fn2-source-wfp fn2-source)', out)
        self.assertIn('(fn2-dest-wfp fn2-dest)', out)
        self.assertTrue(out.endswith('fn2-dest)'))
        self.assertEqual(rewrite(out), (out, 0))

    def test_explicit_guards_other_classes_comments_preserved(self):
        src = '; :guard\n(defun other (fn2-x) (declare (xargs :stobjs fn2-x)) fn2-x)\n(defun fn2-checkpoint-restore-reach-x (fn2-x) (declare (xargs :stobjs fn2-x :guard (fn2-x-wfp fn2-x))) fn2-x)'
        self.assertEqual(rewrite(src), (src, 0))

    def test_event_source_class_keeps_readonly_domain(self):
        src = '(defun fn2-checkpoint-restore-events-step (fn2-source fn2-work) (declare (xargs :stobjs (fn2-source fn2-work) :verify-guards nil)) fn2-work)'
        out, count = rewrite(src)
        self.assertEqual(count, 1)
        self.assertIn('(fn2-source-wfp fn2-source)', out)
        self.assertEqual(rewrite(out), (out, 0))

    def test_alias_refused(self):
        with self.assertRaises(ValueError):
            rewrite('(defun fn2-checkpoint-restore-reach-x (table) (declare (xargs :stobjs table)) table)')


class BootReturnClassTests(unittest.TestCase):
    def test_only_own_exact_return_class(self):
        from restore_reach_source import wire_boot_returns
        tail = 'fn2-checkpoint-restore-reader fn2-checkpoint-restore-map-control fn2-checkpoint-restore-arena-control fn2-fc fn2-pool'
        src = '(defun fn2-boot-checkpoint-root-begin (x) (mv :bounds ' + tail + '))\n(defun other (x) (mv :bounds ' + tail + '))'
        out, n = wire_boot_returns(src)
        self.assertEqual(n, 1)
        self.assertIn('fn2-checkpoint-restore-arena-control fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control fn2-fc', out)
        self.assertTrue(out.endswith('(defun other (x) (mv :bounds ' + tail + '))'))
        self.assertEqual(wire_boot_returns(out), (out, 0))

if __name__ == '__main__':
    unittest.main()
