"""Source identity/projection controls; no ACL2 execution or admission."""
import copy
from pathlib import Path
import subprocess
import unittest
import lisp_rewrite as lr
import run_bound_cursor_projection as p
ROOT = Path(__file__).resolve().parents[1]
FIX = ROOT / 'tools/fixtures/run-bound-cursor'
BASE = '4c16b9e51'


def tree(n):
    if isinstance(n, lr.Lst):
        return [tree(x) for x in n.items]
    if isinstance(n, lr.Pre):
        return [n.prefix, tree(n.node)]
    return n.text if isinstance(n, lr.Str) else n.low


def undo_only_added_state(n):
    if not isinstance(n, list):
        return n
    if len(n) > 2 and n[:2] == ['defcolumns', 'fn2-run-cursors']:
        n[2] = [field for field in n[2] if field[0] not in p.REQUIRED]
    if n and n[0] == 'fn2-run-cursors-put':
        n = n[:2] + [field for field in n[2:] if field[0] not in p.REQUIRED]
    return [undo_only_added_state(x) for x in n]


class CursorProjection(unittest.TestCase):
    def setUp(self):
        self.base = subprocess.check_output(['git', 'show', BASE + ':books/runs.lisp'], cwd=ROOT, text=True)
        self.actual = (ROOT / 'books/runs.lisp').read_text()
        self.frozen = (FIX / 'frozen.lisp').read_text()

    def test_every_root_definition_api_and_guard_is_preserved(self):
        before = [tree(n) for n in lr.parse(self.base).forms]
        after = [tree(n) for n in lr.parse(self.actual).forms]
        after = [n for n in after if n[:2] != ['defun', p.HASH]]
        self.assertEqual(before, undo_only_added_state(copy.deepcopy(after)))
        self.assertNotIn('fn2-run-cursor-start-installed', self.actual)
        self.assertNotIn('(physical :bool)', self.actual[self.actual.index('(defcolumns fn2-run-installed'):])

    def test_accessor_and_columns_are_exact_actual_source_projection(self):
        self.assertEqual(tree(p.one(self.actual, '(defun '+p.HASH+' ?*args)')),
                         tree(p.one(self.frozen, '(defun '+p.HASH+' ?*args)')))
        old = tree(p.one(self.base, '(defcolumns fn2-run-cursors ?*args)'))[2]
        actual = tree(p.one(self.actual, '(defcolumns fn2-run-cursors ?*args)'))[2]
        real = {field[0]: field for field in tree(p.one(self.frozen, '(defcolumns fn2-run-cursors ?*args)'))[2]}
        self.assertEqual(actual, old + [real[name] for name in p.REQUIRED])
        self.assertNotIn('priority', [f[0] for f in actual])

    def test_resident_reuse_clears_every_new_authority_and_hash_column(self):
        start = p.one(self.actual, '(defun fn2-run-cursor-start ?*args)')
        put = lr.match('(fn2-run-cursors-put c ?*fields)', [start])[0].node
        fields = {n.items[0].low: tree(n.items[1]) for n in put.items[2:]}
        for name in p.REQUIRED:
            self.assertEqual(fields[name], '*fn2-none*' if name == 'source-row' else '0')
        self.assertEqual(tree(start.items[2]), tree(p.one(self.base, '(defun fn2-run-cursor-start ?*args)').items[2]))

    def test_transformation_fixture_and_actual_output_agree(self):
        mini = (FIX / 'root.lisp').read_text()
        result = p.project(mini, self.frozen)
        for pattern in ['(defcolumns fn2-run-cursors ?*args)', '(defun fn2-run-cursor-start ?*args)', '(defun '+p.HASH+' ?*args)']:
            self.assertEqual(tree(p.one(result, pattern)), tree(p.one(self.actual, pattern)))
        self.assertEqual(p.project(self.base, self.frozen), self.actual)

    def test_reject_duplicate_projection_or_missing_frozen_field(self):
        with self.assertRaisesRegex(ValueError, 'already contains'):
            p.project(self.actual, self.frozen)
        with self.assertRaisesRegex(ValueError, 'lacks required'):
            p.project(self.base, self.frozen.replace('(epoch :u60)', ''))


if __name__ == '__main__':
    unittest.main()
