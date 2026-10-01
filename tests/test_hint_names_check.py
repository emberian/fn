"""Report-only hint-name lint: synthetic worlds require no ACL2 process."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import hint_names_check as check


class HintNamesCheckTests(unittest.TestCase):
    def audit(self, files):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, text in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            return check.audit(root)

    def names(self, report):
        return {ref.name for ref in report.findings}

    def test_dangling_name(self):
        report = self.audit({'books/a.lisp': '''(defthm ok t
 :hints (("Goal" :in-theory (disable vanished))))'''})
        self.assertEqual(self.names(report), {'vanished'})
        self.assertEqual(report.findings[0].line, 2)
        self.assertEqual(report.findings[0].event, 'ok')

    def test_included_definition(self):
        report = self.audit({'books/a.lisp': '(include-book "b") (defthm ok t :hints (("Goal" :by lemma)))',
                             'books/b.lisp': '(defthm lemma t)'})
        self.assertEqual(report.findings, [])

    def test_unincluded_definition(self):
        report = self.audit({'books/a.lisp': '(defthm ok t :hints (("Goal" :by lemma)))',
                             'books/b.lisp': '(defthm lemma t)'})
        self.assertEqual(self.names(report), {'lemma'})

    def test_system_is_unchecked(self):
        report = self.audit({'books/a.lisp': '(include-book "external" :dir :system) (defthm ok t :hints (("Goal" :by external-lemma)))'})
        self.assertEqual(report.findings, [])
        self.assertEqual([r.name for r in report.unchecked], ['external-lemma'])

    def test_macro_body_definition(self):
        report = self.audit({'books/a.lisp': '''(defmacro make-it () `(defthm generated t))
(make-it)
(defthm ok t :hints (("Goal" :by generated)))'''})
        self.assertEqual(report.findings, [])

    def test_local_definition(self):
        report = self.audit({'books/a.lisp': '(local (defthm lemma t)) (defthm ok t :hints (("Goal" :by lemma)))'})
        self.assertEqual(report.findings, [])

    def test_local_does_not_export(self):
        report = self.audit({'books/a.lisp': '(include-book "b") (defthm ok t :hints (("Goal" :by lemma)))',
                             'books/b.lisp': '(local (defthm lemma t)) (local (include-book "external" :dir :system))'})
        self.assertEqual(self.names(report), {'lemma'})
        self.assertEqual(report.unchecked, [])

    def test_hint_grammar(self):
        report = self.audit({'books/a.lisp': '''
(defun f (x) (declare (xargs :guard-hints (("Goal" :use (:instance guard-lemma (x ignored)))))) x)
(defthm ok t :hints (("Goal"
 :in-theory (union-theories (e/d (enabled (:rewrite rewritten . 1)) (disabled)) (current-theory :here))
 :use (used (:instance instanced (x not-a-name)))
 :by (:functional-instance functional (f g))
 :expand ((expanded x) (:free (x) (free-expanded x)) (:with with-lemma (with-expanded x)))
 :induct (induction x))))'''})
        self.assertEqual(self.names(report), {'guard-lemma', 'enabled', 'rewritten', 'disabled', 'used', 'instanced', 'functional', 'expanded', 'free-expanded', 'with-lemma', 'with-expanded', 'induction'})
        self.assertEqual(len(report.skipped), 1)

    def test_comments_strings_and_named_theory(self):
        report = self.audit({'books/a.lisp': '''; (in-theory (enable fake))
(deftheory rules '(car (:definition cdr)))
(defthm ok t :hints (("Goal" :in-theory (theory 'rules))))'''})
        self.assertEqual(report.findings, [])

    def test_generated_names(self):
        report = self.audit({'books/a.lisp': """
(defstobj pool (cells :type (array integer (2))) (table :type (hash-table equal)))
(defun-inline fast (x) x)
(defun-sk predicate (x) (forall y (equal x y)))
(in-theory (disable poolp cellsi update-cellsi cells-length table-get table-put table-boundp fast$inline predicate-necc))
"""})
        self.assertEqual(report.findings, [])

    def test_parameterized_template(self):
        report = self.audit({'books/a.lisp': """
(defmacro emit (name)
 `(local (defthm ,(intern-in-package-of-symbol
     (concatenate 'string (symbol-name name) "-LEMMA") name) t)))
(emit useful)
(defthm ok t :hints (("Goal" :by useful-lemma)))
"""})
        self.assertEqual(report.findings, [])

    def test_unused_macro_is_not_definition(self):
        report = self.audit({'books/a.lisp': """
(defmacro emit () `(defthm absent t))
(defthm ok t :hints (("Goal" :by absent)))
"""})
        self.assertEqual(self.names(report), {'absent'})

    def test_external_provenance_is_not_a_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'books').mkdir()
            (root / 'books/a.lisp').write_text(
                '(include-book "library" :dir :system) '
                '(in-theory (disable external-lemma missing core-lemma))')
            source = root / 'install'
            (source / 'books').mkdir(parents=True)
            (source / 'books/library.lisp').write_text('(defthm external-lemma t)')
            (source / 'axioms.lisp').write_text('(defaxiom core-lemma t)')
            report = check.audit(root, source=source)
            self.assertEqual(self.names(report), {'missing'})
            self.assertEqual({r.name for r in report.unchecked}, {'external-lemma', 'core-lemma'})

    def test_local_system_include_does_not_leak(self):
        report = self.audit({'books/a.lisp': '(include-book "b") (in-theory (disable missing))',
                             'books/b.lisp': '(local (include-book "external" :dir :system))'})
        self.assertEqual(self.names(report), {'missing'})

    def test_suppressed_macro_not_expanded(self):
        report = self.audit({'tests/acl2/a.lisp': '(must-fail (def-loop rejected (xs) :shape :invalid))'})
        self.assertEqual(report.findings, [])
        self.assertEqual(len(report.skipped), 1)

    def test_local_macro_and_declared_skolem(self):
        report = self.audit({'books/a.lisp': """
(local (defmacro emit (name) `(defthm ,name t)))
(local (emit lemma))
(defun-sk predicate (x) (declare (xargs :guard t)) (forall y (equal x y)))
(defthm ok t :hints (("Goal" :use (lemma predicate-necc))))
"""})
        self.assertEqual(report.findings, [])

    def test_event_codes_and_stobj_table(self):
        report = self.audit({'books/a.lisp': """
(defstobj node (children :type (stobj-table 16)))
(defevent kind :encode encode-kind :decode decode-kind :recognizer kindp)
(in-theory (disable children-get children-put children-boundp encode-kind decode-kind kindp))
"""})
        self.assertEqual(report.findings, [])

    def test_literal_make_event(self):
        report = self.audit({'books/a.lisp': """
(make-event `(defthm generated ,(computed-statement)))
(defthm ok t :hints (("Goal" :by generated)))
"""})
        self.assertEqual(report.findings, [])
        self.assertEqual(len(report.skipped), 1)

    def test_summary_and_table_do_not_run_git_or_gate(self):
        from contextlib import redirect_stdout
        from io import StringIO
        from unittest.mock import patch
        report = check.Report(findings=[check.Reference('books/a.lisp', 2, 'ok', 'missing')])
        with patch.object(check, 'audit', return_value=report), patch.object(check, 'acl2_source', return_value=None), patch.object(check.subprocess, 'run') as git:
            with redirect_stdout(StringIO()) as output:
                self.assertEqual(check.main(['--summary', '--table']), 0)
            git.assert_not_called()
            self.assertIn('1 findings / 0 unchecked / 0 skipped', output.getvalue())
            self.assertIn('books/a.lisp:2 ok MISSING', output.getvalue())


if __name__ == '__main__':
    unittest.main()
