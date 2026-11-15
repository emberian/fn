import importlib.util
from pathlib import Path
import sys
import unittest

TOOLS = Path(__file__).resolve().parents[1] / 'tools'
sys.path.insert(0, str(TOOLS))
import pool_proof_event_overlay as overlay

class OverlayTests(unittest.TestCase):
    def build(self, text):
        return overlay.make_overlay(text, form_index=1, expected_sha=None)
    def test_scope_and_exact_theorem_guard_bytes(self):
        text = "(encapsulate () (local (progn (defthm local-proof (equal x '(defthm literal y))) (defun f (x) (declare (xargs :guard (natp x))) x))) (defthm outside (equal (f x) x)))"
        out, manifest = self.build(text)
        self.assertEqual(overlay.strip_overlay(out), text)
        self.assertEqual(overlay.theorem_bodies(out), overlay.theorem_bodies(text))
        self.assertEqual(manifest['direct'], 3)
        self.assertIn('(local (progn (with-prover-step-limit 2000000 t', out)
    def test_generated_pair_stays_local_global(self):
        text = "(encapsulate () (defun fn2-pool-op-conservation-events (x) `((local (defthm ,x (equal a a))) (defthm other (equal b b)))) (defmacro apply-pair (x) (cons 'progn (fn2-pool-op-conservation-events x))) (apply-pair p))"
        out, manifest = self.build(text)
        self.assertEqual(manifest['templates'], {'fn2-pool-op-conservation-events': 2})
        self.assertEqual(overlay.strip_overlay(out), text)
        self.assertEqual(overlay.theorem_bodies(out), overlay.theorem_bodies(text))
    def test_unreviewed_emitter_fails_closed(self):
        with self.assertRaises(overlay.OverlayError):
            self.build('(encapsulate () (defun other-events (x) `(defthm ,x (equal a a))))')
    def test_changed_source_rejected(self):
        with self.assertRaises(overlay.OverlayError):
            overlay.make_overlay('(encapsulate () (defthm x (equal a a)))')
    def test_budget_increase_rejected(self):
        with self.assertRaises(overlay.OverlayError):
            overlay.make_overlay('(encapsulate () (defthm x (equal a a)))', form_index=1, expected_sha=None, steps=2_000_001)
    def test_nested_existing_budget_rejected(self):
        with self.assertRaises(overlay.OverlayError):
            self.build('(encapsulate () (with-prover-step-limit 9 (defthm x (equal a a))))')

if __name__ == '__main__':
    unittest.main()
