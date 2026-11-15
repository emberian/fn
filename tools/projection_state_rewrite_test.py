import unittest
from alloc_identity_state_rewrite import rewrite_projection
class ProjectionState(unittest.TestCase):
    def test_formals_locals_values_but_not_schema_keys(self):
        source='(defun fn2-checkpoint-projection-step (state p) (let ((state state)) (fn2-extents-put 0 (state state) (owner-id state))))'
        expected='(defun fn2-checkpoint-projection-step (row-state p) (let ((row-state row-state)) (fn2-extents-put 0 (state row-state) (owner-id row-state))))'
        self.assertEqual(rewrite_projection(source),expected)
        self.assertEqual(rewrite_projection(expected),expected)
    def test_unrelated_function_untouched(self):
        source='(defun untouched (state) state)'
        self.assertEqual(rewrite_projection(source),source)
    def test_changed_put_shape_refuses(self):
        with self.assertRaises(ValueError):
            rewrite_projection('(defun fn2-checkpoint-projection-step (state) (fn2-extents-put 0 state))')
if __name__=='__main__':unittest.main()
