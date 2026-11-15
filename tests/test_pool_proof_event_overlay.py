from pathlib import Path
import sys
import hashlib
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
        text = "(encapsulate () (defun fn2-pool-op-conservation-events (x) `((local (defthm ,x (equal a a))) (defthm other (equal b b)))) (defmacro fn2-pool-op-conservation (x) (cons 'progn (fn2-pool-op-conservation-events x))) (fn2-pool-op-conservation p))"
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
    def test_lower_time_budget_preserves_event(self):
        text = '(encapsulate () (defthm x (equal a a)))'
        out, manifest = overlay.make_overlay(text, form_index=1, expected_sha=None, seconds=20)
        self.assertEqual(manifest['seconds'], 20)
        self.assertIn("with-prover-time-limit '(20)", out)
        self.assertEqual(overlay.strip_overlay(out), text)
        for seconds in (0, 61, True, 20.5):
            with self.assertRaises(overlay.OverlayError):
                overlay.make_overlay(text, form_index=1, expected_sha=None, seconds=seconds)
    def test_nested_existing_budget_rejected(self):
        with self.assertRaises(overlay.OverlayError):
            self.build('(encapsulate () (with-prover-step-limit 9 (defthm x (equal a a))))')

    def test_reviewed_future_sha_and_generator_selector(self):
        text = "(defconst prefix 1) (encapsulate () (defun fn2-pool-op-conservation-events (x) `((local (defthm ,x (equal a a))) (defthm other (equal b b)))))"
        digest = hashlib.sha256(text.encode()).hexdigest()
        out, manifest = overlay.make_overlay(text, generator='fn2-pool-op-conservation-events', expected_sha=digest)
        self.assertEqual(manifest['form_index'], 2)
        self.assertEqual(manifest['source_sha256'], digest)
        self.assertEqual(overlay.strip_overlay(out), text[text.index('(encapsulate'):])
    def test_generator_selection_rejects_ambiguous_and_unknown(self):
        event = "(encapsulate () (defun fn2-pool-op-conservation-events (x) `((local (defthm ,x (equal a a))) (defthm other (equal b b)))))"
        for text, name in ((event + event, 'fn2-pool-op-conservation-events'), (event, 'unreviewed-events')):
            with self.assertRaises(overlay.OverlayError):
                overlay.make_overlay(text, generator=name, expected_sha=None)
    def test_unreviewed_event_macro_rejected(self):
        with self.assertRaises(overlay.OverlayError):
            self.build('(encapsulate () (unreviewed-proof-factory x))')
    def test_unreviewed_make_event_rejected(self):
        with self.assertRaises(overlay.OverlayError):
            self.build("(encapsulate () (make-event '(defthm hidden (equal x x))))")

if __name__ == '__main__':
    unittest.main()
