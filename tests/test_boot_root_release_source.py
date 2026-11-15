"""Narrow source controls; no Lisp evaluation or physical boot claim."""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr


def release_order(source):
    fn = lr.match('(defun fn2-boot-release-root-window ?*body)', lr.parse(source).forms)[0].node
    patterns = ['(fn2-pool-workspace-code slot gen *fn2-boot-kind* id ogen fn2-pool)',
                '(fn2-pool-release-countp slot fn2-pool)',
                '((unless (eq preflight :ok)) (mv preflight fn2-core))',
                '(fn2-core-release slot gen *fn2-boot-kind* id ogen fn2-core)',
                "((unless (member-eq code '(:ok :retired))) (mv code fn2-core))",
                '(fn2-boot-put-core id (root-slot 0) (root-gen 0) (root-cursor 0) (root-role 0))']
    nodes = []
    for pattern in patterns:
        found = lr.match(pattern, [fn])
        if len(found) != 1:
            raise ValueError('missing/duplicated release boundary: '+pattern)
        nodes.append(found[0].node)
    if [n.start for n in nodes] != sorted(n.start for n in nodes):
        raise ValueError('preflight, accepted release, root reset order changed')


class Source(unittest.TestCase):
    def setUp(self):
        self.src = (ROOT/'books/boot-root-release.lisp').read_text()
        self.forms = lr.parse(self.src).forms

    def test_shared_release_preflight_before_mutation(self):
        release_order(self.src)
        self.assertNotIn('(fn2-pool-release ', self.src)
        self.assertNotIn('(update-fn2-pool-', self.src)
        self.assertNotIn('(fn2-pool-put ', self.src)
        with self.assertRaises(ValueError):
            release_order(self.src.replace('((unless (eq preflight :ok)) (mv preflight fn2-core))', '', 1))

    def test_actual_completed_boot_actor_and_recovery(self):
        fn = lr.match('(defun fn2-boot-release-root-window ?*body)', self.forms)[0].node
        for p in ['(= (fn2-machine-generation id fn2-core) ogen)',
                  '(= (fn2-machine-phase id fn2-core) *fn2-boot-state-epoch-result*)',
                  '(= (fn2-machine-event-ready id fn2-core) 1)',
                  '(= (fn2-machine-outcome id fn2-core) *fn2-outcome-done*)',
                  '(= (fn2-machine-pending id fn2-core) 0)',
                  '(= (fn2-machine-phase recovery fn2-core) *fn2-recovery-machine-state-done*)',
                  '(= (fn2-machine-stopped recovery fn2-core) 1)',
                  '(= (fn2-machine-pending recovery fn2-core) 0)']:
            self.assertTrue(lr.match(p, [fn]), p)

    def test_terminal_consumers_and_owned_capture(self):
        fn = lr.match('(defun fn2-boot-root-consumers-settled-p ?*body)', self.forms)[0].node
        for p in ['(fn2-checkpoint-payload-rebindablep fn2-checkpoint-payload)',
                  '(= (fn2-event-read-pending 0 fn2-event-read) 0)',
                  '(= (fn2-checkpoint-restore-semantic-depth 0 fn2-checkpoint-restore-semantic) 0)',
                  '(fn2-checkpoint-summary-authority-complete-p fn2-checkpoint-summary-authority fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)',
                  '(fn2-checkpoint-cbase-held-p fn2-checkpoint-summary fn2-checkpoint-cbase-holds)',
                  '(= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-applied*)']:
            self.assertTrue(lr.match(p, [fn]), p)

    def test_genuinely_absent_fresh_root_only(self):
        for p in ['(= slot 0)', '(= cursor 0)', '(= role 0)', '(= create 1)',
                  '(= (fn2-boot-config-anchor-checked-mask fn2-boot-config) 0)',
                  '(= (fn2-boot-config-anchor-empty-mask fn2-boot-config) 15)',
                  '(= (fn2-boot-config-anchor-invalid-mask fn2-boot-config) 0)']:
            self.assertTrue(lr.match(p, self.forms), p)

    def test_fixture_uses_actual_release_loans_and_read_issue(self):
        src = (ROOT/'tests/boot-root-release-unit.lisp').read_text()
        forms = lr.parse(src).forms
        for p in ['(fn2-pool-release ?*args)', '(fn2-pool-lease-out ?*args)', '(fn2-issue-read ?*args)']:
            self.assertTrue(lr.match(p, forms), p)
        self.assertNotIn('(fn2-pool-set-state ', src)
        self.assertNotIn('(fn2-pool-set-out-count ', src)
        self.assertEqual(len(lr.match('(assert-event ?test)', forms)), 14)

    def test_query_repeat_and_unrelated_owner_use_actual_pool(self):
        src = (ROOT/'tests/boot-root-release-unit.lisp').read_text()
        for p in ['(fn2-pool-query-acquire root gen 0 1 *fn2-boot-kind* id ogen fn2-pool)',
                  '(fn2-pool-query-release root gen fn2-pool)',
                  '(fn2-pool-reserve 0 199 29 5 fn2-pool)',
                  '(fn2-test-table-snapshot-fn2-pool fn2-pool)',
                  '(whole-antecedent (fn2-boot-root-consumers-settled-p id ogen root claimed-gen fn2-core))',
                  '(assert-event (fn2-brru-test :query))',
                  '(assert-event (fn2-brru-test :repeat))']:
            self.assertIn(p, src)
        self.assertIn('(eq code :held) (equal before after)', src)
        self.assertIn('(eq repeated :state)', src)

    def test_connected_cold_completion_checks_once_and_failed_retention(self):
        src = (ROOT/'tests/checkpoint-cold-path-unit.lisp').read_text()
        self.assertLess(src.index('(root-gen (fn2-machine-root-gen boot fn2-core))'),
                        src.index('(fn2-ccp-complete-epoch fault'))
        self.assertLess(src.index('(fn2-ccp-drive 200000 nil', src.index('(fn2-ccp-complete-epoch fault')),
                        src.index('(fn2-boot-release-root-window boot owner-generation fn2-core)'))
        for p in ['(eq repeat :state) repeat-unchanged',
                  '(fn2-test-table-snapshot-fn2-pool fn2-pool)',
                  '(posp (nth 1 resource)) (not (nth 2 resource))',
                  '(nth 5 resource) (nth 6 resource)']:
            self.assertIn(p, src)


class FinalizeSource(unittest.TestCase):
    def check_gate(self, source):
        fn = lr.match('(defun fn2-boot-finalize-recovery (id ogen fn2-core) ?*body)', lr.parse(source).forms)[0].node
        patterns = [
            '(= (fn2-machine-root-gen id fn2-core) 0)',
            '(= (fn2-machine-outcome id fn2-core) *fn2-outcome-done*)',
            '(fn2-recovery-selected-current-p rid fn2-core)',
            '(> epoch (fn2-machine-rc-epoch rid fn2-core))',
            '(fn2-checkpoint-bank-protection-complete-p ?*args)',
            '(fn2-checkpoint-bank-promote-selected ?*args)',
            '((unless (eq code :installed)) (mv code fn2-checkpoints fn2-extents))',
            '(update-fn2-alloc-freeze-phase 0 fn2-extents)',
            '(fn2-alloc-begin-epoch epoch fn2-extents)',
        ]
        positions = []
        for pattern in patterns:
            matches = lr.match(pattern, [fn])
            self.assertEqual(len(matches), 1, pattern)
            positions.append(matches[0].node.start)
        self.assertEqual(positions, sorted(positions))
        self.assertFalse(lr.match('(update-fn2-alloc-epoch-begun ?*args)', [fn]))

    def test_actual_final_gate_and_removed_premises(self):
        source = (ROOT / 'books/checkpoint-bank-boot.lisp').read_text()
        self.check_gate(source)
        for old in [
            '(> epoch (fn2-machine-rc-epoch rid fn2-core))',
            '(fn2-recovery-selected-current-p rid fn2-core)',
            '(= (fn2-machine-root-gen id fn2-core) 0)',
        ]:
            fn = lr.match('(defun fn2-boot-finalize-recovery (id ogen fn2-core) ?*body)', lr.parse(source).forms)[0].node
            original = source[fn.start:fn.end]
            self.assertIn(old, original)
            with self.assertRaises(AssertionError):
                self.check_gate(source[:fn.start] + original.replace(old, 't', 1) + source[fn.end:])


if __name__ == '__main__': unittest.main()
