"""Source controls only: no ACL2 evaluation or allocator reference model."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class Source(unittest.TestCase):
    def setUp(self):
        self.forms=lr.parse((ROOT/'books/alloc-identity-index.lisp').read_text()).forms
    def test_executable_prefix_does_not_call_logical_scan(self):
        for form in self.forms:
            flat=lr.flat(form).lower()
            if flat.startswith('(defun fn2-alloc-identity-model-') or flat.startswith('(defun fn2-alloc-identity-refines-p'):
                break
            self.assertNotIn('(fn2-alloc-identity-model-',flat)
            self.assertNotIn('(fn2-alloc-identity-refines-p ',flat)
    def test_generated_shape_package_keeps_type_domain(self):
        shape=lr.match('(defun fn2-alloc-identity-shape-events ?*body)',self.forms)[0].node
        self.assertTrue(lr.match('(fn2-extentsp fn2-extents)',[shape]))
        self.assertTrue(lr.match('(fn2-extents-wfp fn2-extents)',[shape]))
        self.assertTrue(lr.match('(fn2-alloc-identity-publishable-p kind owner ogen source fn2-extents)',[shape]))
    def test_atomic_mutators_use_existing_allocator(self):
        for name,transition in [('commit-adopt','adopt-transition'),('commit-free','free')]:
            form=lr.match(f'(defun fn2-alloc-identity-{name} ?*body)',self.forms)[0].node
            self.assertTrue(lr.match(f'(fn2-alloc-{transition} ?*args)',[form]))
        free=lr.match('(defun fn2-alloc-identity-commit-free ?*body)',self.forms)[0].node
        self.assertTrue(lr.match('(fn2-alloc-release-under-cut-code ?*args)',[free]))
    def test_actual_control_roots_present(self):
        forms=lr.parse((ROOT/'tests/alloc-identity-index-unit.lisp').read_text()).forms
        for call in ('(fn2-aiu-run t)','(fn2-aiu-run nil)','(fn2-aiu-progress-run)','(fn2-aiu-insert-run)'):
            self.assertTrue(lr.match(f'(assert-event {call})',forms))
if __name__=='__main__': unittest.main()
