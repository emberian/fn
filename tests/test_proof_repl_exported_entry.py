"""Keep certification reachability separate from exported ACL2 world presence."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import proof_repl as repl


class ExportedEntry(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='fn-export-entry-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.books = self.root / 'books'
        self.books.mkdir()

    def book(self, name, text='(in-package "ACL2")\n'):
        (self.books / f'{name}.lisp').write_text(text)
        return 'books/' + name

    def test_local_edge_cannot_cover_its_child_or_child_exports(self):
        self.book('pool-read-contracts', '(include-book "public-base")')
        self.book('public-base')
        self.book('ribbon', '(local (include-book "pool-read-contracts"))')
        # Populate the certification graph first: exported planning must not
        # reuse that graph's cached LOCAL edges under the same source digest.
        self.assertEqual(set(repl.include_graph(self.root, 'books/ribbon')),
                         {'books/ribbon', 'books/pool-read-contracts', 'books/public-base'})
        self.assertEqual(repl.exported_include_graph(self.root, 'books/ribbon'),
                         {'books/ribbon': []})
        entry, exports = repl.warm_entry_books(self.root,
            ['books/ribbon', 'books/pool-read-contracts', 'books/public-base'])
        self.assertEqual(entry, ['books/ribbon', 'books/pool-read-contracts'])
        self.assertEqual(exports, {'books/ribbon', 'books/pool-read-contracts', 'books/public-base'})
        warm = {'books/ribbon', 'books/pool-read-contracts', 'books/public-base'}
        old_covered = set().union(*(set(repl.include_graph(self.root, n)) - {n} for n in warm))
        old_entry = warm - old_covered
        self.assertEqual(old_entry, {'books/ribbon'})
        self.assertNotIn('books/pool-read-contracts',
                         repl.exported_include_graph(self.root, next(iter(old_entry))))
        # Cache availability alone does not force private books into the world.
        self.assertEqual(repl.warm_entry_books(self.root, ['books/ribbon']),
                         (['books/ribbon'], {'books/ribbon'}))

    def test_nonlocal_transitive_path_covers_even_a_separately_local_child(self):
        self.book('leaf')
        self.book('public', '(include-book "leaf")')
        self.book('root', '(local (include-book "leaf"))\n(include-book "public")')
        self.assertEqual(repl.warm_entry_books(self.root,
            ['books/root', 'books/public', 'books/leaf']),
            (['books/root'], {'books/root', 'books/public', 'books/leaf'}))

    def test_nested_local_containers_and_non_event_templates(self):
        self.book('private', '(include-book "deep")')
        self.book('deep')
        self.book('public')
        self.book('root', '''(encapsulate ()
          (local (progn (include-book "private")))
          (defthm visible (equal x x)))
        (progn (include-book "public"))
        (defun quoted () '(include-book "not-a-book"))
        (make-event (value '(local (include-book "private"))))
        (must-fail (include-book "not-a-book"))
        (include-book "arithmetic/top" :dir :system)''')
        self.assertEqual(repl.exported_include_graph(self.root, 'books/root'),
                         {'books/root': ['books/public'], 'books/public': []})
        self.assertIn('books/deep', repl.include_graph(self.root, 'books/root'))

    def test_cli_emits_entry_and_conditional_presence_without_acl2(self):
        self.book('leaf')
        self.book('ribbon', '(local (include-book "leaf"))')
        output = self.root / 'build' / 'entry.lisp'
        captured = io.StringIO()
        with patch.object(repl, 'ROOT', self.root), \
             patch.object(repl, 'apply_box_defaults') as box, \
             patch.object(repl, 'apply_local_defaults') as local, \
             patch.object(repl.subprocess, 'Popen') as launch, \
             redirect_stdout(captured):
            self.assertEqual(repl.main(['warm-entry', 'books/ribbon', 'books/leaf',
                                        '--output', str(output)]), 0)
        launch.assert_not_called()
        box.assert_not_called()
        local.assert_not_called()
        self.assertEqual(output.read_text(), '(in-package "ACL2")\n'
                         '(include-book "../books/ribbon")\n(include-book "../books/leaf")\n')
        plan = json.loads(captured.getvalue())
        self.assertEqual(plan['exported_books_after_success'], ['books/leaf', 'books/ribbon'])
        # The generated entry actually has both nonlocal paths; the historical
        # full-closure pruning would have emitted only Ribbon and lost LEAF.
        self.assertEqual(set(repl.exported_include_graph(self.root, 'build/entry')),
                         {'build/entry', 'books/ribbon', 'books/leaf'})

    def test_output_cannot_overwrite_a_local_dependency(self):
        self.book('leaf')
        self.book('root', '(local (include-book "leaf"))')
        path = self.books / 'leaf.lisp'
        original = path.read_text()
        with patch.object(repl, 'ROOT', self.root):
            self.assertEqual(repl.warm_entry(type('Args', (), {
                'books': ['books/root'], 'output': str(path)})()), 2)
        self.assertEqual(path.read_text(), original)

    def test_exported_cycle_refuses_instead_of_claiming_presence(self):
        self.book('a', '(include-book "b")')
        self.book('b', '(include-book "a")')
        with self.assertRaisesRegex(ValueError, 'include cycle'):
            repl.warm_entry_books(self.root, ['books/a', 'books/b'])


if __name__ == '__main__':
    unittest.main()
