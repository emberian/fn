"""Narrow source transformation controls; never evaluate ACL2 or model decisions."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from rewrite_checkpoint_root_predicate import rewrite

class RootPredicateRewriteTest(unittest.TestCase):
    def test_calls_preserve_comments_strings_and_existing_subject(self):
        text = '; fn2-checkpoint-built-roots-p\n"fn2-checkpoint-built-roots-p"\n(fn2-checkpoint-built-roots-p 0 c token refs)\n(fn2-checkpoint-production-roots-p 1 c token refs)\n'
        changed, n = rewrite("checkpoint-build.lisp", text)
        self.assertEqual(n, 1)
        self.assertEqual(changed, text.replace('(fn2-checkpoint-built-roots-p 0', '(fn2-checkpoint-production-roots-p 0'))
        self.assertEqual(rewrite("checkpoint-build.lisp", changed), (changed, 0))

    def test_state_moves_definition_and_is_idempotent(self):
        text = '(include-book "checkpoint-member")\n(defun fn2-checkpoint-built-roots-p (role c token refs) (fn2-checkpoint-built-roots-p (+ role 1) c token refs))\n(fn2-checkpoint-built-roots-p 0 c token refs)\n'
        changed, n = rewrite("checkpoint-build-state.lisp", text)
        self.assertEqual(n, 3)
        self.assertNotIn('(defun ', changed)
        self.assertEqual(changed.count('(include-book "checkpoint-production")'), 1)
        self.assertIn('(fn2-checkpoint-production-roots-p 0 c token refs)', changed)
        self.assertEqual(rewrite("checkpoint-build-state.lisp", changed), (changed, 0))

if __name__ == "__main__":
    unittest.main()
