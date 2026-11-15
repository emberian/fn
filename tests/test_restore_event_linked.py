"""Discriminating source fixtures for the real linked-reader selector class."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from restore_event_linked import PATTERNS, rewrite

class LinkedEventSourceTests(unittest.TestCase):
    def test_all_metadata_shapes_and_idempotency(self):
        src = '(defun fn2-checkpoint-restore-header (role) (list ' + ' '.join(x for x, _ in PATTERNS) + '))'
        out, count = rewrite(src)
        self.assertEqual(count, len(PATTERNS))
        self.assertIn('(list slots width pagekind bodykind nfields)', out)
        self.assertEqual(rewrite(out), (out, 0))

    def test_other_owner_strings_comments_exact(self):
        pattern = PATTERNS[0][0]
        src = '; ' + pattern + '\n(defun other (role) ' + pattern + ')\n(defun fn2-checkpoint-restore-entry (role) "' + pattern + '")'
        self.assertEqual(rewrite(src), (src, 0))

    def test_unrelated_role_selector_preserved(self):
        src = '(defun fn2-checkpoint-restore-reader-page-step (role) (if (equal role 2) marker other))'
        self.assertEqual(rewrite(src), (src, 0))

if __name__ == '__main__':
    unittest.main()
