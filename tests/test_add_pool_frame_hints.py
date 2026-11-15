"""Narrow controls for the pool-frame source transformation."""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from add_pool_frame_hints import add_pool_frame_hints
from lisp_source import forms, read_sexp


class PoolFrameHintsTest(unittest.TestCase):
    def test_preserves_explicit_hints_and_other_forms(self):
        source = '''; comment survives
(fn2-pool-preserves a (x fn2-pool) :hints nil)
(fn2-pool-preserves b (x fn2-pool) :hints (("Goal" :use exact)))
(defun c (x) x)
'''
        self.assertEqual(add_pool_frame_hints(source), source)

    def test_adds_only_hint_and_is_idempotent(self):
        source = '''(fn2-pool-preserves a (x fn2-pool)
 ; keep local comment
 :position 1 :hyps ((valid x)) :prefix "-POOL")'''
        result = add_pool_frame_hints(source)
        old = read_sexp(forms(source)[0])
        new = read_sexp(forms(result)[0])
        self.assertEqual(new[:-2], old)
        self.assertEqual(new[-2:], read_sexp('(:hints (("Goal" :in-theory (disable fn2-pool-rows))))'))
        self.assertIn(':hints (("Goal" :in-theory (disable fn2-pool-rows)))', result)
        self.assertIn('; keep local comment', result)
        self.assertEqual(add_pool_frame_hints(result), result)


if __name__ == '__main__':
    unittest.main()
