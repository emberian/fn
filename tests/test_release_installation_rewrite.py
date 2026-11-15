"""Discriminating source controls for the readonly directory frame class."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import release_installation_rewrite as rw

class Thread(unittest.TestCase):
    def test_exact_boundary(self):
        before = '(f fn2-ops fn2-allocation-release fn2-release-evidence)'
        self.assertEqual(rw.thread(before, 1), '(f fn2-ops fn2-commit-root fn2-allocation-release fn2-release-evidence)')

    def test_count_refuses_stale_or_duplicate(self):
        with self.assertRaises(ValueError):
            rw.thread('(unrelated)', 1)
        with self.assertRaises(ValueError):
            rw.thread('(f fn2-ops fn2-allocation-release fn2-release-evidence)', 2)

    def test_actual_guard_hypotheses_preserved(self):
        before = '(and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (fn2-allocation-releasep x))'
        result = rw.frame_hyps(before, 1)
        self.assertIn('(fn2-commit-rootp fn2-commit-root) (fn2-commit-root-wfp fn2-commit-root)', result)
        self.assertIn('(fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)', result)

if __name__ == '__main__':
    unittest.main()
