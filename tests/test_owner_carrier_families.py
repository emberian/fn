import unittest
from pathlib import Path
from tools.owner_carrier.families import publication, GLOBALS, composition_events


class FamilyTransformationTests(unittest.TestCase):
    def test_all_ten_reads_and_writes_move_together(self):
        for old, field in GLOBALS.items():
            with self.subTest(global_name=old):
                source = f"(f-put-global '{old} (fn-owner-sco-global '{old} state) state)"
                result = publication(source)
                self.assertNotIn(old, result)
                self.assertIn(f'(fn-opub-get {field} (fn-ost-publication state))', result)
                self.assertIn(f'(fn-opub-put {field}', result)
                self.assertEqual(publication(result), result)

    def test_quotes_comments_strings_and_unrelated_calls_are_unchanged(self):
        source = '''; (f-get-global 'fn-owner-sco-base state)
'(f-put-global 'fn-owner-sco-base nil state)
(defun f () "(f-get-global 'fn-owner-sco-base state)")
(f-put-global 'fn-owner-other nil state)'''
        self.assertEqual(publication(source), source)

    def test_nested_effect_refuses_instead_of_evaluating_state_twice(self):
        source = "(f-put-global 'fn-owner-sco-base x (f-put-global 'fn-owner-sco-inflight y state))"
        with self.assertRaises(ValueError):
            publication(source)

    def test_layout_outside_calls_is_preserved(self):
        source = "(let ((state (f-put-global 'fn-owner-sco-base x state))) ; retained\n state)"
        self.assertIn('; retained\n state)', publication(source))

    def test_composition_equations_are_generated_and_cover_all_ten_fields(self):
        root = Path(__file__).resolve().parents[1]
        generated = composition_events()
        self.assertTrue((root / "books/owner-publication-composition.lisp").read_text().endswith(generated))
        for field in GLOBALS.values():
            self.assertIn(f"(fn-opub-get {field} r)", generated)

    def test_served_wrappers_use_the_carried_transitions(self):
        from tools import lisp_rewrite as lr
        root = Path(__file__).resolve().parents[1]
        text = (root / "host/owner-host.lisp").read_text()
        forms = lr.parse(text).forms
        for host, pure in [
            ("catalog-root-reserve", "fn-ocr-reserve"),
            ("catalog-root-current", "fn-ocr-current"),
            ("sco-due", "fn-opub-due"), ("sco-request", "fn-opub-request"),
            ("sco-capture", "fn-opub-capture-context"),
            ("sco-publication-done", "fn-opub-done"),
            ("sco-publication-abandoned", "fn-opub-abandoned")]:
            match = lr.match(None, forms, head="defun", name="fn-owner-" + host, deep=False)[0]
            self.assertIn("(" + pure + " ", text[match.start:match.end].replace("\n", " "))
        from tools.owner_globals_check import globals_of
        self.assertEqual(set(GLOBALS).intersection(globals_of(text)), set())
