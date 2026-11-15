import json
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_accumulator_rewrite as rw
import event_archive_test_accumulator_rewrite as tests
import event_archive_batch_rewrite as batch
import event_archive_seal_rewrite as seal

ROOT=Path(__file__).resolve().parents[1]


def form(source,pattern):
    n=lr.match(pattern,lr.parse(source).forms)[0].node
    return source[n.start:n.end]


class Accumulator(unittest.TestCase):
    def test_actual_three_book_projection_and_idempotence(self):
        before=json.loads((ROOT/'tools/fixtures/event-archive-accumulator-before.json').read_text())
        for name,recipe in [('event-archive-state.lisp',rw.state),
                            ('event-archive-cold-cursor.lisp',rw.cursor),
                            ('event-archive-cold-boot.lisp',rw.boot)]:
            after=recipe(before[name])
            after=seal.state(batch.state(after)) if name=='event-archive-state.lisp' else after
            after=batch.project_cursor(after) if name=='event-archive-cold-cursor.lisp' else after
            self.assertEqual(after,(ROOT/'books'/name).read_text())
            self.assertEqual(after,recipe(after))
        self.assertEqual(form(before['event-archive-state.lisp'],'(defun fn2-event-archive-candidate-held-p ?*body)'),
                         form((ROOT/'books/event-archive-state.lisp').read_text(),'(defun fn2-event-archive-candidate-held-p ?*body)'))

    def test_real_boot_handles_role_and_preflight_before_borrow_mutation(self):
        cursor=(ROOT/'books/event-archive-cold-cursor.lisp').read_text()
        boot=(ROOT/'books/event-archive-cold-boot.lisp').read_text()
        self.assertIn('(accumulator (fn2-machine-pool-slot id fn2-core))',boot)
        self.assertIn('(agen (fn2-machine-pool-gen id fn2-core))',boot)
        self.assertIn('(equal (fn2-machine-root-role id fn2-core) 3)',form(boot,'(defun fn2-boot-checkpoint-archive-owner-p ?*body)'))
        begin=form(cursor,'(fn2-event-archive-operation (fn2-event-archive-cold-cursor-begin ?*args) ?*body)')
        for term in ['(not (equal accumulator scratch))','(not (equal accumulator page))',
                     '(eq (fn2-pool-workspace-code accumulator agen kind owner gen fn2-pool) :ok)']:
            self.assertLess(begin.index(term),begin.index('(fn2-run-load-admission-begin'))
        self.assertNotIn('fn2-pool-reset',begin)
        self.assertNotIn('fn2-pool-zero',begin)

    def test_every_cursor_visit_rebinds_the_same_distinct_owned_accumulator(self):
        current=form((ROOT/'books/event-archive-cold-cursor.lisp').read_text(),
                     '(defun fn2-event-archive-cold-cursor-source-p ?*body)')
        for getter in ['fn2-event-archive-accumulator-slot','fn2-event-archive-accumulator-gen']:
            self.assertIn(getter,current)
        self.assertIn('(fn2-run-loads-page c fn2-run-loads)',current)
        self.assertIn('(fn2-run-loads-scratch c fn2-run-loads)',current)
        self.assertIn('(fn2-pool-workspace-code (fn2-event-archive-accumulator-slot',current)

    def test_exact_replay_and_actual_fixture_classes_compose(self):
        before=json.loads((ROOT/'tools/fixtures/event-archive-accumulator-tests-before.json').read_text())
        for name,source in before.items():
            after=tests.rewrite(source,name)
            after=batch.source_test(after,name)
            self.assertEqual(after,(ROOT/'tools'/name).read_text())
            self.assertEqual(after,tests.rewrite(after,name))
        before=json.loads((ROOT/'tools/fixtures/event-archive-accumulator-units-before.json').read_text())
        for name,source in before.items():
            after=rw.fixture(source)
            after=batch.copy_fixture(batch.fixture(after)) if name=='event-archive-cold-member-unit.lisp' else after
            self.assertEqual(after,(ROOT/'tests'/name).read_text())
            self.assertEqual(after,rw.fixture(after))
            self.assertIn('(fn2-pool-reserve 1 1 2 3 fn2-pool)',after)
            self.assertIn(':accumulator-alias',after)
            self.assertIn(':accumulator-generation',after)


if __name__=='__main__':unittest.main()
