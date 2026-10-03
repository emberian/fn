import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from native_source_world import generate, selected_defthms, bounded_body


class CurrentSourceWorldTests(unittest.TestCase):
    def tree(self, directory):
        root = Path(directory)
        (root / 'books').mkdir(parents=True)
        books = {
            'codec-attach': '(in-package "ACL2")\n',
            'records-attach-concrete': '(in-package "ACL2")\n',
            'payload-arena-extent': '(in-package "ACL2")\n(defun arena-physical (x) x)\n',
            'payload-arena': '(in-package "ACL2")\n(defun arena-generic (x) x)\n',
            'catalog-record': '(in-package "ACL2")\n',
            'payload-arena-attach': '(in-package "ACL2")\n(include-book "payload-arena-extent")\n(attach-stobj fn-arena fn-arena-extent)\n(include-book "payload-arena")\n(include-book "catalog-record")\n(assert-event t)\n',
            'history-paged': '(in-package "ACL2")\n(defun physical (x) x)\n',
            'history-columns': '(in-package "ACL2")\n(defun generic (x) x)\n',
            'history-paged-attach': '(in-package "ACL2")\n(include-book "history-paged")\n(attach-stobj fn-hist fn-hist-paged)\n(include-book "history-columns")\n',
            'child': '(in-package "ACL2")\n(defun child (x) x)\n',
            'parent': '(in-package "ACL2")\n(include-book "child")\n(defthm optional (equal x x) :rule-classes nil)\n',
            'image-world': '(in-package "ACL2")\n(include-book "parent")\n(include-book "history-paged-attach")\n',
        }
        for name, text in books.items(): (root / 'books' / (name + '.lisp')).write_text(text)
        return root

    def test_attachment_precedes_generic_and_all_inputs_are_named(self):
        with tempfile.TemporaryDirectory() as d:
            root = self.tree(d)
            output = root / 'prefix.lisp'
            manifest = generate(root, [], output, revision='immutable-test')
            text = output.read_text()
            self.assertLess(text.index('(defun arena-physical'), text.index('(attach-stobj fn-arena fn-arena-extent)'))
            self.assertLess(text.index('(attach-stobj fn-arena fn-arena-extent)'), text.index('(defun arena-generic'))
            self.assertLess(text.index('(defun arena-generic'), text.index('(assert-event t)'))
            self.assertLess(text.index('(attach-stobj fn-hist fn-hist-paged)'), text.index('(defun generic'))
            data = json.loads(manifest.read_text())
            self.assertEqual(data['source_revision'], 'immutable-test')
            self.assertEqual(set(data['repository_books']), set(data['repository_sha256']))
            self.assertTrue(output.with_name('prefix.early.lisp').is_file())

    def test_dtn_umbrella_adds_transport_without_losing_early_attachment(self):
        with tempfile.TemporaryDirectory() as d:
            root = self.tree(d)
            (root / 'books/transport.lisp').write_text('(defun actual-transport (x) x)')
            (root / 'books/image-world-dtn.lisp').write_text(
                '(include-book "image-world")\n(include-book "transport")')
            out = root / 'dtn.lisp'
            data = json.loads(generate(root, [], out, world_book='books/image-world-dtn').read_text())
            self.assertEqual(data['world_book'], 'books/image-world-dtn')
            self.assertIn('books/transport.lisp', data['repository_books'])
            text = out.read_text()
            self.assertIn('(defun actual-transport', text)
            self.assertLess(text.index('(attach-stobj fn-hist fn-hist-paged)'), text.index('(defun generic'))

    def test_changed_child_refuses_cached_parent(self):
        with tempfile.TemporaryDirectory() as d:
            root = self.tree(Path(d) / 'source')
            cache = self.tree(Path(d) / 'cache')
            for name in ('parent', 'child'):
                for suffix in ('.cert', '.port'):
                    (cache / 'books' / (name + suffix)).write_text('test inventory only')
            (cache / 'books/child.lisp').write_text('(in-package "ACL2")\n(defun child (x) (cons x nil))\n')
            manifest = generate(root, [cache], root / 'prefix.lisp')
            rows = {r['book']: r for r in json.loads(manifest.read_text())['books']}
            self.assertEqual(rows['books/parent']['kind'], 'source-admission')

    def test_explicit_deferral_removes_only_named_theorem(self):
        removed = set()
        text = selected_defthms('(local (defthm optional (equal x x)))\n(defun actual (x) x)', {'optional'}, removed)
        self.assertEqual(removed, {'optional'})
        self.assertNotIn('defthm', text)
        self.assertIn('(defun actual', text)
        with self.assertRaisesRegex(ValueError, 'required guard'):
            selected_defthms('(defthm f{correspondence} (equal x x))', {'f{correspondence}'}, set())

    def test_omitted_rules_leave_literal_theory_catalog_only(self):
        pruned = {}
        text = selected_defthms(
            "(deftheory catalog '(keep omitted (:rewrite omitted)))\n"
            "(defun actual (x) (omitted x))", set(), set(), {'omitted'}, pruned)
        self.assertIn("(deftheory catalog '(keep))", text)
        self.assertIn('(defun actual (x) (omitted x))', text)
        self.assertEqual(pruned, {'catalog': ['omitted']})

    def test_deferral_and_budget_are_explicit_in_manifest(self):
        with tempfile.TemporaryDirectory() as d:
            root = self.tree(d)
            output = root / 'prefix.lisp'
            data = json.loads(generate(root, [], output, deferred={'books/parent': {'optional'}}).read_text())
            self.assertEqual(data['deferred_defthms'], {'books/parent': ['optional']})
            self.assertNotIn('(defthm optional', output.read_text())
            self.assertIn('(with-prover-step-limit 200000', output.read_text())
            self.assertNotIn('with-prover-step-limit!', bounded_body('(encapsulate () (defun x (y) y))', 12))


if __name__ == '__main__': unittest.main()
