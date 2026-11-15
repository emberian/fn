"""Current-root actual initialization and shared resource geometry controls."""
from pathlib import Path
import hashlib
import json
import unittest
import lisp_rewrite as lr
import checkpoint_worker_totalize as totalize


def defs(text):
    return {getattr(n.items[1], 'text', ''): text[n.start:n.end]
            for n in lr.parse(text).forms if isinstance(n, lr.Lst) and len(n.items)>1
            and getattr(n.items[0], 'text', '') in ['defun','defconst']}


class RootCreditInit(unittest.TestCase):
    def test_actual_image_boundary_before_genesis(self):
        s = Path('books/executor.lisp').read_text()
        f = defs(s)['fn2-init-executor']
        self.assertLess(f.index('(fn2-core-init profile fn2-core)'), f.index('(fn2-init-credit-boundary profile fn2-core)'))
        self.assertLess(f.index('(fn2-init-credit-boundary profile fn2-core)'), f.index('(fn2-init-engine profile fn2-core)', f.index('  (b*')))
        self.assertIn('((unless (eq credit :ok)) (fn2-core-stop *fn2-stop-reason-engine-genesis* fn2-core))', f)
        boundary = defs(s)['fn2-init-credit-boundary']
        self.assertIn('(not (fn2-profile-get :image-boot profile)) (mv :ok fn2-core)', boundary)
        self.assertIn('(fn2-checkpoint-working-credit-init profile fn2-core)', boundary)
        init = Path('books/checkpoint-working-credit-init.lisp').read_text()
        self.assertIn('profile (fn2-commit-rows fn2-commit) (fn2-commit-io-rows fn2-commit-io)', init)
        self.assertIn('(fn2-checkpoint-service-protocol-classes fn2-pool)', init)
        self.assertIn('(fn2-checkpoint-service-upload-classes fn2-pool) fn2-pool', init)

    def test_one_actual_p_formula_and_capacity(self):
        s = Path('books/checkpoint-working-credit.lisp').read_text()
        self.assertEqual(s.count('(fn2-pool-credit-configure groups fn2-pool)'),1)
        for actual in ['(fn2-checkpoint-working-credit-vector 0 fn2-pool)',
                       '(fn2-checkpoint-drain-credit-vector 0 journal-class windows fn2-pool)',
                       '(fn2-allocation-release-credit-vector 0 fn2-pool)',
                       '(fn2-checkpoint-service-demand-vector profile paths uploads fn2-pool)',
                       '(fn2-checkpoint-working-profile-fitp 0 groups service fn2-pool)',
                       '(equal commit-io-rows (* *fn2-commit-write-resources* commitrows))']:
            self.assertIn(actual,s)
        self.assertLess(s.index('(fn2-checkpoint-working-profile-fitp 0 groups service fn2-pool)'),s.index('(fn2-pool-credit-configure groups fn2-pool)'))
        capacity = defs(Path('books/allocation-release-geometry.lisp').read_text())['fn2-allocation-release-member-capacity']
        self.assertIn('(+ 32 *fn2-format-txn-record-max-size* *fn2-format-release-allocation-max-size*)',capacity)

    def test_actual_boot_recovery_inventory_without_phantom_root(self):
        s = Path('books/checkpoint-service-geometry.lisp').read_text()
        self.assertNotIn('*fn2-checkpoint-cold-root-windows*',s)
        inventory = defs(s)['*fn2-checkpoint-startup-window-requests*']
        for role in ['boot-pack','boot-rx','recovery-window','recovery-workspace']:
            self.assertIn(role+' . ,*fn2-format-sector-bytes*',inventory)
        executor = defs(Path('books/executor.lisp').read_text())['fn2-boot-start']
        self.assertEqual(executor.count('(fn2-core-reserve class *fn2-boot-kind*'),2)
        self.assertIn('(fn2-pool-class-for 4096 fn2-pool)',executor)
        recovery = Path('books/recovery-machine.lisp').read_text()
        self.assertEqual(recovery.count('(fn2-core-reserve (fn2-scribe-window-class fn2-core) *fn2-recovery-machine-kind*'),2)
        for root in ['root-slot','root-gen','root-reserve']:
            self.assertNotIn(root,Path('books/boot-kind.lisp').read_text())

    def test_same_actual_arena_and_o_providers(self):
        for book in ['books/machines-c.lisp','books/machines-c-successor.lisp']:
            s=Path(book).read_text()
            self.assertIn('(fn2-idc-profile-arena profile)',s)
            self.assertNotIn('(fn2-b-capacity :identity-arena-bytes 65536 profile)',s)
        service=Path('books/checkpoint-service-geometry.lisp').read_text()
        self.assertIn('(include-book "successor-schema-geometry")',service)
        self.assertIn('(fn2-pool-class-for *fn2-idc-scratch-bytes* fn2-pool)',service)
        self.assertNotIn('idc-scratch-bytes',Path('books/identity-workspace-geometry.lisp').read_text())

    def test_root_old_worker_api_preserved_under_declared_guard(self):
        r=json.loads(Path('tools/fixtures/checkpoint-worker-totalization.json').read_text())
        self.assertEqual(len(r['functions']),6)
        s=Path('books/checkpoint-future-working.lisp').read_text()
        for row in r['functions']:
            n=totalize.definition(s,row['name'])
            self.assertEqual(totalize.restored(s[n.start:n.end],row),row['original_form'])
        self.assertIn('(defun fn2-checkpoint-future-reserve-loop (i kind owner gen ',s)
        self.assertNotIn('(i nonce kind owner gen ',s)

    def test_actual_node_positive_and_shared_p_only_negative(self):
        s=Path('tests/root-working-credit-init-unit.lisp').read_text();lr.parse(s)
        for actual in ['*fn2-node-profile*','(fn2-init-executor profile :null nil fn2-core)',
                       '(fn2-checkpoint-working-credit-configure *fn2-node-profile*',
                       '(fn2-pool-credit-protectedi i fn2-pool)',
                       '(assert-event (fn2-rwciu-node-run t))','(assert-event (fn2-rwciu-node-run nil))',
                       '(assert-event (fn2-rwciu-short-run))']:
            self.assertIn(actual,s)
        self.assertNotIn('(:pool-classes .',s)

    def test_protocol_projection_uses_actual_registry_and_resolver(self):
        init=Path('books/checkpoint-working-credit-init.lisp').read_text()
        self.assertIn('(fn2-machine-class-form (fn2-arm-get :class (cdar specs))',init)
        for kind,face in [('fn2-conn',':admission'),('fn2-ctl',':admission'),('fn2-cns',':taken'),('fn2-upload',':taken')]:
            self.assertIn("(fn2-checkpoint-service-kind-form '"+kind+' '+face+' world)',init)
        service=Path('books/checkpoint-service-geometry.lisp').read_text()
        self.assertIn('(fn2-checkpoint-service-path-demand class paths)',service)
        self.assertIn('(fn2-checkpoint-service-class-count class uploads)',service)
        self.assertNotIn('(equal class *fn2-upload-chunk-class*)',service)
        fixture=Path('tests/root-working-credit-init-unit.lisp').read_text()
        self.assertIn('(assert-event (fn2-rwciu-alias-run))',fixture)
        self.assertIn('(assert-event (fn2-rwciu-protocol-short-run))',fixture)

if __name__=='__main__':
    unittest.main()
