"""Source fixtures discriminate the bounded new-leaf guard transformation."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from event_build_guards import rewrite

class EventBuildGuardTests(unittest.TestCase):
    def test_class_and_idempotency(self):
        src = '; :guard is a comment\n(defun fn2-event-build-step (fn2-a fn2-b) (declare (xargs :stobjs (fn2-a fn2-b) :verify-guards nil)) (mv fn2-a fn2-b))'
        got, count = rewrite(src)
        self.assertEqual(count, 1)
        self.assertIn(':guard (and (fn2-a-wfp fn2-a) (fn2-b-wfp fn2-b))', got)
        self.assertTrue(got.startswith('; :guard is a comment'))
        self.assertTrue(got.endswith('(mv fn2-a fn2-b))'))
        self.assertEqual(rewrite(got), (got, 0))

    def test_existing_guards_are_exact(self):
        src = '(defun fn2-event-build-step (fn2-a) (declare (xargs :stobjs fn2-a :guard (and (fn2-a-wfp fn2-a) (< 0 (fn2-a-rows fn2-a))))) fn2-a)'
        self.assertEqual(rewrite(src), (src, 0))

    def test_other_owner_is_not_the_class(self):
        src = '(defun other (fn2-a) (declare (xargs :stobjs fn2-a :verify-guards nil)) fn2-a)'
        self.assertEqual(rewrite(src), (src, 0))

    def test_undeclared_alias_refuses(self):
        with self.assertRaises(ValueError):
            rewrite('(defun fn2-event-build-step (table) (declare (xargs :stobjs table :verify-guards nil)) table)')

if __name__ == '__main__':
    unittest.main()
