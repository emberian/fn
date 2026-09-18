"""Regression checks for evidence that must fail closed."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location(
    "certify_books", Path(__file__).resolve().parents[1] / "tools" / "certify_books.py"
)
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


class CertificationEvidenceTests(unittest.TestCase):
    def test_markers_reject_echo_spoof_and_previous_run(self):
        marker = runner.success_token("books/example", "current")
        output = '\n'.join([
            f'(cw "{marker}~%")',
            runner.success_token("books/example", "previous"),
            f'arbitrary prefix {marker}',
            f'ACL2 !>>{marker} extra',
            f'ACL2 !>>{marker}',
        ])
        self.assertEqual(runner.success_markers(output, "current"),
                         [marker])

    def test_source_audit_distinguishes_comments_and_escaped_symbols(self):
        source = '''; (skip-proofs ...)
        #| (defaxiom x) #| nested |# (defttag x) |#
        (defconst *help* "skip-proofs \\" defaxiom")
        (ACL2::|SKIP-PROOFS| (defthm unsound nil))
        (defaxiom unsound2 nil)
        '''
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "source.lisp").write_text(source)
            with mock.patch.object(runner, "ROOT", root):
                self.assertEqual(runner.audit_sources({"source.lisp": "unused"}),
                                 {"source.lisp": ["defaxiom", "skip-proofs"]})

    def test_dependency_closure_excludes_unrelated_work(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "books").mkdir()
            (root / "books/root.lisp").write_text('(include-book "dep")\n')
            (root / "books/dep.lisp").write_text('(in-package "ACL2")\n')
            with mock.patch.object(runner, "ROOT", root):
                before = runner.collect_book_sources(["books/root"])
                (root / "books/unrelated.lisp").write_text('(defun work () nil)')
                self.assertEqual(before, runner.collect_book_sources(["books/root"]))
                (root / "books/dep.lisp").write_text('(in-package "ACL2")\n; changed')
                self.assertNotEqual(before, runner.collect_book_sources(["books/root"]))

    def test_system_book_reference_is_not_resolved_as_local(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.lisp"
            source.write_text('(include-book "ihs/quotient-remainder-lemmas" :dir :system)')
            self.assertEqual(runner.local_include_books("source", source), [])


if __name__ == "__main__":
    unittest.main()
