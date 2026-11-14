import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from allocator_freeze_rewrite import rewrite, REFUSALS

class FreezeRewrite(unittest.TestCase):
    def test_each_real_entry_preserves_body_and_guard(self):
        for name, refusal in REFUSALS.items():
            source = f'(defun {name} (fn2-extents) (declare (xargs :stobjs fn2-extents)) (original fn2-extents))'
            result = rewrite(source)
            self.assertIn('(declare (xargs :stobjs fn2-extents))', result)
            self.assertIn(refusal, result)
            self.assertIn('(original fn2-extents)', result)
            self.assertEqual(rewrite(result), result)
    def test_comments_calls_and_pins_untouched(self):
        source = '; (defun fn2-alloc-reserve (x) x)\n(fn2-alloc-reserve x)\n(defun fn2-alloc-edge-add (x) (original x))'
        self.assertEqual(rewrite(source), source)
