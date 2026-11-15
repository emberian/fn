"""Physical cursor source-boundary controls; no ACL2 or I/O execution claim."""
import copy
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from lisp_source import forms, read_sexp
ROOT = Path(__file__).resolve().parents[1]


def walk(node):
    if isinstance(node, list):
        yield node
        for child in node:
            yield from walk(child)


def definitions(file):
    return {n[1]: n for text in forms((ROOT / file).read_text())
            for n in walk(read_sexp(text)) if len(n) > 2 and n[0] == 'defun'}


def calls(node):
    return [n[0] for n in walk(node) if n and isinstance(n[0], str)]


def full_parent_identity(node):
    used = calls(node)
    return all('fn2-run-paths-' + f in used for f in ['epoch'] + [f'hash-{i}' for i in range(8)])


class PhysicalCursorSource(unittest.TestCase):
    def setUp(self):
        self.runs = definitions('books/runs.lisp')
        self.steps = definitions('books/runs-assemble.lisp')

    def test_installed_physical_root_copies_exact_reference_and_waits(self):
        root = self.runs['fn2-run-cursor-start-installed']
        used = calls(root)
        for field in ['epoch', 'catalog-tag', 'run', 'wire-run'] + [f'hash-{i}' for i in range(8)]:
            self.assertIn('fn2-run-installed-' + field, used)
        self.assertIn('*fn2-run-cursor-phase-miss*', str(root))
        self.assertIn('*fn2-none*', str(root))
        self.assertNotIn('fn2-run-cache-install', used)
        self.assertNotIn('fn2-block-read-children', used)
        self.assertIn(['run', ['fn2-run-installed-wire-run', 'r', 'fn2-run-installed']], list(walk(root)))
        self.assertIn(['priority', ['fn2-run-installed-run', 'r', 'fn2-run-installed']], list(walk(root)))

    def test_parent_reread_preserves_all_hash_words_and_epoch(self):
        parent = self.runs['fn2-run-cursor-parent-ref']
        self.assertTrue(full_parent_identity(parent))
        damaged = copy.deepcopy(parent)
        for n in walk(damaged):
            if n and n[0] == 'fn2-run-paths-epoch':
                n[0] = 'missing-epoch'
        self.assertFalse(full_parent_identity(damaged))
        up = self.steps['fn2-run-step-up']
        bstar = next(n for n in walk(up) if n and n[0] == 'b*')
        bindings = bstar[1]
        physical = next(i for i, n in enumerate(bindings) if 'fn2-run-cursor-parent-ref' in calls(n))
        cache = next(i for i, n in enumerate(bindings) if 'fn2-run-cache-lookup' in calls(n))
        self.assertLess(physical, cache)
        self.assertIn('*fn2-run-cursor-phase-miss*', str(bindings[physical]))

    def test_child_ref_uses_actual_parent_hash_window_before_cache(self):
        childref = self.runs['fn2-run-cursor-child-ref']
        used = calls(childref)
        for field in ['storage-domain', 'page-kind', 'encoded-length', 'writer-epoch', 'expected-hash']:
            self.assertIn('*fn2-format-ref-field-' + field + '*', str(childref))
        for getter in ['fn2-fields-ref-slot', 'fn2-fields-ref-gen', 'fn2-run-cursors-slot', 'fn2-run-cursors-gen']:
            self.assertIn(getter, used)
        child = self.steps['fn2-run-step-child']
        bstar = next(n for n in walk(child) if n and n[0] == 'b*')
        physical = next(i for i, n in enumerate(bstar[1]) if 'fn2-run-cursor-child-ref' in calls(n))
        cache = next(i for i, n in enumerate(bstar[1]) if 'fn2-run-cache-lookup' in calls(n))
        self.assertLess(physical, cache)
        self.assertNotIn('fn2-run-cache-install', calls(child))

    def test_miss_does_not_decode_and_header_rechecks_semantic_identity(self):
        cursor = self.steps['fn2-run-cursor-step']
        cond = next(n for n in walk(cursor) if n and n[0] == 'cond')
        miss = next(n for n in cond[1:] if '*fn2-run-cursor-phase-miss*' in str(n[0]) and 'physical' in str(n[0]))
        self.assertNotIn('fn2-run-phase-child', calls(miss))
        self.assertIn(':miss', str(miss))
        header = self.steps['fn2-run-step-header']
        for getter in ['fn2-run-read-header', 'fn2-run-cursors-run', 'fn2-run-cursors-schema', 'fn2-run-cursors-resume-child']:
            self.assertIn(getter, calls(header))
        self.assertIn('*fn2-run-cursor-phase-child*', str(header))

    def test_successor_threads_actor_owner_separately_from_key_owner(self):
        successor = definitions('books/machines-c-successor.lisp')
        for name in ['fn2-succ-resolve', 'fn2-succ-resolve-step', 'fn2-succ-resolve-next']:
            self.assertIn('qk', successor[name][2])
            self.assertIn('qs', successor[name][2])
            self.assertIn('qg', successor[name][2])
        root = next(n for n in walk(successor['fn2-succ-resolve-next'])
                    if n and n[0] == 'fn2-run-cursor-start-installed')
        self.assertEqual(root[4:7], ['qk', 'qs', 'qg'])
        for file, kind in [('books/txn.lisp', '*fn2-txn-kind*'), ('books/authority.lisp', '*fn2-auth-kind*'), ('books/cns.lisp', '*fn2-cns-kind*')]:
            source = (ROOT / file).read_text()
            self.assertIn('4096 ' + kind + ' id row-generation)', source)


if __name__ == '__main__':
    unittest.main()
