#!/usr/bin/env python3
"""Connect the resource footprint to existing production writer families."""
from pathlib import Path
import hashlib
import json
import unittest
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[1]
def atom(n):
    return n.text.lower() if isinstance(n, lr.Atom) else ''
def walk(n):
    yield n
    if isinstance(n, lr.Lst):
        for x in n.items:
            yield from walk(x)
    elif isinstance(n, lr.Pre):
        yield from walk(n.node)
class ServiceGeometry(unittest.TestCase):
    def test_post_families_are_actual_producer_footprint(self):
        g = lr.parse(ROOT/'books/checkpoint-service-geometry.lisp')
        hit = lr.match('_', g.forms, deep=False, name='*fn2-checkpoint-post-schema-families*')
        self.assertEqual(len(hit), 1)
        declared = {atom(n) for n in hit[0].node.items[2].node.items}
        txn = lr.parse(ROOT/'books/txn.lisp')
        actual = set()
        for name in ('fn2-txn-put-identity-core', 'fn2-txn-put-identity',
                     'fn2-txn-put-article', 'fn2-txn-add-group'):
            forms = lr.match('_', txn.forms, deep=True, head='defun', name=name)
            self.assertEqual(len(forms), 1)
            for node in walk(forms[0].node):
                if isinstance(node, lr.Lst) and node.items:
                    head = atom(node.items[0])
                    for family in declared:
                        if head.startswith(family+'-'):
                            actual.add(family)
        self.assertEqual(actual, declared)
        # Independently collect every typed schema writer prefix in the same
        # source bodies, so a newly added family cannot escape the budget list.
        schema_names = set()
        for book in ('identity', 'ordered', 'folds'):
            for hit in lr.match('_', lr.parse(ROOT/f'books/{book}.lisp').forms,
                                deep=True, head='defrunschema'):
                schema_names.add(atom(hit.node.items[1]))
        discovered = set()
        for name in ('fn2-txn-put-identity-core', 'fn2-txn-put-identity',
                     'fn2-txn-put-article', 'fn2-txn-add-group'):
            form = lr.match('_', txn.forms, deep=True, head='defun', name=name)[0].node
            for node in walk(form):
                if isinstance(node, lr.Lst) and node.items:
                    head = atom(node.items[0])
                    discovered.update(s for s in schema_names if head.startswith(s+'-'))
        self.assertEqual(discovered, declared)

    def test_boot_windows_are_separate_generic_claims(self):
        for book, name, count in (
            ('executor', 'fn2-boot-start', 2),
            ('recovery-machine', 'fn2-recovery-prepare', 2),
            ('checkpoint-restore-boot', 'fn2-boot-checkpoint-root-reserve', 1)):
            source = lr.parse(ROOT/f'books/{book}.lisp')
            found = lr.match('_', source.forms, deep=True, head='defun', name=name)
            self.assertEqual(len(found), 1)
            calls = [n for n in walk(found[0].node) if isinstance(n, lr.Lst)
                     and n.items and atom(n.items[0]) == 'fn2-core-reserve']
            self.assertEqual(len(calls), count)
        boot = lr.parse(ROOT/'books/boot.lisp')
        released = lr.match('_', boot.forms, deep=True, head='defun', name='fn2-boot-release-windows')
        self.assertEqual(len(released), 1)
        # Pack/rx and root remain distinct leases; actual epoch-result joins
        # root release before finalization opens the epoch or releases listeners.
        text = boot.text[released[0].start:released[0].end]
        self.assertNotIn('root-slot', text)

    def check_ready_join(self, source):
        boot = lr.parse(source)
        arms = [n for f in boot.forms for n in walk(f)
                if isinstance(n, lr.Lst) and n.items]
        epoch = [n for n in arms if atom(n.items[0]) == ':epoch-result']
        release = [n for n in arms if len(n.items) > 1
                   and atom(n.items[0]) == ':release' and atom(n.items[1]) == ':on-refusal']
        self.assertEqual(len(epoch), 1)
        self.assertEqual(len(release), 1)
        text = boot.text[epoch[0].start:epoch[0].end]
        calls = ['fn2-boot-finish-bank-obligations',
                 'fn2-boot-release-root-window', 'fn2-boot-finalize-recovery',
                 'fn2-boot-release-windows', '(:next :release)']
        positions = [text.index(name) for name in calls]
        self.assertEqual(positions, sorted(positions))
        self.assertIn('(not (equal row-outcome *fn2-outcome-done*)) (:stop :io)', text)
        self.assertIn('(fn2-boot-release-root-window id row-generation) :accept (:ok :retired)', text)
        transitions = [n for n in arms if len(n.items) == 2
                       and atom(n.items[0]) == ':next' and atom(n.items[1]) == ':ready']
        self.assertEqual(len(transitions), 2)
        self.assertTrue(all(release[0].start < n.start < n.end < release[0].end
                            for n in transitions))
        helper = lr.parse(ROOT/'books/boot-root-release.lisp')
        found = lr.match('_', helper.forms, deep=True, head='defun',
                         name='fn2-boot-release-root-window')
        self.assertEqual(len(found), 1)
        text = helper.text[found[0].start:found[0].end]
        returned = text.index('(fn2-core-release slot gen *fn2-boot-kind* id ogen fn2-core)')
        accepted = text.index("((unless (member-eq code '(:ok :retired)))", returned)
        cleared = text.index('(root-slot 0) (root-gen 0)', accepted)
        self.assertLess(returned, accepted)
        self.assertLess(accepted, cleared)
        bank = lr.parse(ROOT/'books/checkpoint-bank-boot.lisp')
        finalize = lr.match('_', bank.forms, deep=True, head='defun',
                            name='fn2-boot-finalize-recovery')
        self.assertEqual(len(finalize), 1)
        text = bank.text[finalize[0].start:finalize[0].end]
        self.assertIn('(= (fn2-machine-root-gen id fn2-core) 0)', text)
        geometry = (ROOT/'books/checkpoint-service-geometry.lisp').read_text()
        self.assertIn('(cold (+ startup root))', geometry)
        self.assertIn('(cold-post post)', geometry)
        self.assertNotIn('(cold-post (+ post root))', geometry)

    def test_actual_ready_join_releases_root_before_service(self):
        source = (ROOT/'books/boot.lisp').read_text()
        self.check_ready_join(source)
        with self.assertRaises((AssertionError, ValueError)):
            self.check_ready_join(source.replace(
                '(fn2-boot-release-root-window id row-generation)',
                '(fn2-boot-missing-release id row-generation)', 1))
        with self.assertRaises(AssertionError):
            self.check_ready_join(source.replace(
                '(fn2-boot-release-root-window id row-generation) :accept (:ok :retired)',
                '(fn2-boot-release-root-window id row-generation) :accept (:ok :retired :busy)', 1))

    def test_actual_engine_uses_shared_workspace_geometry(self):
        receipt = json.loads((ROOT/'tools/fixtures/identity-workspace-geometry-extraction.json').read_text())
        geometry = (ROOT/'books/identity-workspace-geometry.lisp').read_text()
        old = (ROOT/receipt['original_book']).read_text()
        self.assertEqual(hashlib.sha256(receipt['scratch_form'].encode()).hexdigest(), receipt['scratch_form_sha256'])
        self.assertEqual(geometry.count(receipt['scratch_form']), 1)
        self.assertNotIn(receipt['scratch_form'], old)
        self.assertNotIn(receipt['old_initializer'], old)
        self.assertEqual(old.count(receipt['new_initializer']), 1)

if __name__ == '__main__':
    unittest.main()
