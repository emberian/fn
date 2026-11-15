"""Source contracts for registry/export plumbing; ACL2 controls are separate."""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).parents[1]
sys.path.insert(0, str(ROOT / 'meta/emit'))
from emit_lean import read_all

class RefutationPlumbing(unittest.TestCase):
    def test_registry_uses_live_theorem_closed_exact_subject(self):
        text = (ROOT / 'books/owed.lisp').read_text()
        forms = read_all(text)
        check = next(x for x in forms if x[:2] == ['defun', 'fn2-square-refutedp'])
        rendered = str(check)
        for token in ['all-vars', 'statement', 'replacement', 'getpropc', ':refuted']:
            self.assertIn(token, rendered)
        self.assertIn('(not (eq (car (fn2-decl-get :proof (cdar rows))) :proved))', text)
    def test_proved_count_and_completion_do_not_accept_refuted(self):
        text = (ROOT / 'books/owed.lisp').read_text()
        self.assertIn('(if (eq (car (fn2-decl-get :proof r)) :proved) 1 0)', text)
        complete = (ROOT / 'books/assurance-completion.lisp').read_text()
        self.assertIn(':refuted-original', complete)
        self.assertIn(':candidate-replacement-link-unverified', complete)
        self.assertIn('(not (eq (car (fn2-decl-get :proof row)) :proved))', complete)
    def test_identity_survives_table_clear_without_naming_statement(self):
        declaration = (ROOT / 'books/declare.lisp').read_text()
        guard = (ROOT / 'books/owed.lisp').read_text()
        self.assertIn('(defconst ,(fn2-decl-claim-anchor (cadr id))', declaration)
        self.assertIn('(fn2-decl-get :formula row) (fn2-decl-get :translated row)', declaration)
        self.assertIn("'const :missing world", guard)
        self.assertIn('(fn2-square-identity-boundp name row world)', guard)
        controls = (ROOT / 'tests/owed-refutation-unit.lisp').read_text()
        self.assertIn('(table fn2-squares nil nil :clear)', controls)
        self.assertIn('fn2-custom-claim-statement', controls)
        export = (ROOT / 'tests/owed-refutation-export.lsp').read_text()
        self.assertIn('| `FN2-REFUTATION-ORIGINAL` | :REFUTED', export)
        self.assertNotIn('(not (search ":PROVED" text))', export)

    def test_adversarial_actual_events_parse(self):
        for path in ['tests/owed-refutation-unit.lisp', 'tests/owed-refutation-export.lsp']:
            self.assertTrue(read_all((ROOT / path).read_text()))
        text = (ROOT / 'tests/owed-refutation-unit.lisp').read_text()
        self.assertGreaterEqual(text.count('(must-fail'), 5)
        self.assertIn("'(x y)", text)
        self.assertIn("'(1 1 0 0)", text)

if __name__ == '__main__':
    unittest.main()
