#!/usr/bin/env python3
"""Source seam controls; these do not execute ACL2 or establish admission."""
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[1]
TEXT = (ROOT / 'books/cns-source-retention.lisp').read_text()
def body(name):
    text = TEXT.split('(defun ' + name + ' ', 1)[1]
    return text.split('\n(defun ', 1)[0].split('\n(fn2-', 1)[0]
def replay_closed(text):
    exact = text.find('((fn2-alloc-edge-matchesp')
    coverage = text.find('(mv :coverage')
    add = text.find('(t (fn2-alloc-edge-add')
    return -1 < exact < coverage < add and '*fn2-cns-source-retention-ready*' in text[:coverage]
class RetentionSourceControls(unittest.TestCase):
    def test_replay_uses_only_existing_coverage(self):
        claim = body('fn2-cns-source-claim-identity')
        self.assertTrue(replay_closed(claim))
        self.assertFalse(replay_closed(claim.replace('(mv :coverage', '(mv :ok')))
    def test_dedicated_extent_index(self):
        self.assertIn('(* (nfix s) (fn2-extents-rows fn2-extents)) (nfix e)', body('fn2-cns-source-edge'))
        self.assertNotIn('free', body('fn2-cns-source-edge'))
    def test_root_claim_precedes_ready(self):
        root = body('fn2-cns-source-root-hold-children')
        self.assertLess(root.index('(fn2-cns-source-claim-identity'), root.index('(retention-phase (if raw'))
        self.assertIn('((unless (eq code :ok))', root)
    def test_release_requires_handback_not_eof(self):
        release = body('fn2-cns-source-release-step')
        for field in ['pending', 'uncertain', 'borrow-count']:
            self.assertIn('(equal (fn2-cns-sources-' + field + ' s fn2-cns-sources) 0)', release)
        self.assertIn('*fn2-cns-source-phase-releasing*', release)
        self.assertNotIn('*fn2-cns-source-phase-complete*', release)
        self.assertIn('fn2-pool-workspace-code', release)
        self.assertIn('*fn2-cns-source-phase-released*', release)
    def test_release_one_row_and_exact_owner(self):
        release = body('fn2-cns-source-release-step')
        self.assertEqual(release.count('(fn2-alloc-edge-drop '), 1)
        self.assertIn('(release-row (+ 1 e))', release)
        self.assertIn('(fn2-alloc-edge-matchesp edge cnsgen e epoch allocation :promised-read', release)
        self.assertIn('(mv :edge-owner fn2-cns-sources fn2-extents fn2-alloc-edges)', release)
if __name__ == '__main__':
    unittest.main()
