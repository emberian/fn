"""Source controls for INSTALL once and two retryable sealer cleanup phases."""

from pathlib import Path
import subprocess
import unittest

import lisp_rewrite as lr
import seal_cleanup_phase_rewrite as rw

ROOT = Path(__file__).resolve().parents[1]
BASE = '44d549172'


def one(pattern, source):
    found = lr.match(pattern, lr.parse(source).forms, deep=False)
    if len(found) != 1:
        raise AssertionError(f'expected one {pattern}')
    return found[0].node


def check(source):
    enum = one('(defcolumns fn2-seals ?*body)', source)
    expected = ('(:enum fn2-seal-phase (:idle :build :filter :install '
                ':overlay-return :hash-return :failed :release))')
    if not lr.match(expected, [enum]):
        raise ValueError('cleanup phases missing from actual enum')
    pending = one('(defun fn2-seal-pending-p ?*body)', source)
    install = one('(defun fn2-seal-install ?*body)', source)
    overlay = one('(defun fn2-seal-overlay-return ?*body)', source)
    hash_return = one('(defun fn2-seal-hash-return ?*body)', source)
    step = one('(defun fn2-seal-step ?*body)', source)
    for phase in ('overlay-return', 'hash-return'):
        if not lr.match(f'(equal phase *fn2-seal-phase-{phase}*)', [pending]):
            raise ValueError(f'pending omits {phase}')
        dispatch = lr.match(f'((equal phase *fn2-seal-phase-{phase}*) ?*body)', [step])
        if len(dispatch) != 1 or not lr.match(f'(fn2-seal-{phase} ?*args)', [dispatch[0].node]):
            raise ValueError(f'step omits {phase} dispatch')
    install_run = lr.match('(fn2-seal-install-run fn2-seals fn2-run-installed)', [install])
    phase_write = lr.match('(fn2-seals-set-phase 0 *fn2-seal-phase-overlay-return* fn2-seals)', [install])
    if len(install_run) != 1 or len(phase_write) != 1 or install_run[0].start >= phase_write[0].start:
        raise ValueError('INSTALL once transition lost')
    if not lr.match('((unless (equal (fn2-seals-phase 0 fn2-seals) '
                    '*fn2-seal-phase-install*)) '
                    '(mv :state fn2-seals fn2-overlays fn2-run-installed fn2-pool))', [install]):
        raise ValueError('direct INSTALL re-entry not refused')
    for op in ('fn2-seal-retire', 'fn2-pool-release'):
        if lr.match(f'({op} ?*args)', [install]):
            raise ValueError('INSTALL still performs cleanup')
    if not lr.match('(mv :more fn2-seals fn2-overlays fn2-run-installed fn2-pool)', [install]):
        raise ValueError('INSTALL must yield before cleanup')
    if lr.match('(fn2-seal-install ?*args)', [overlay, hash_return]):
        raise ValueError('cleanup may re-enter INSTALL')
    release_overlay = lr.match('(fn2-seal-retire o fn2-overlays fn2-pool)', [overlay])
    advance_hash = lr.match('(fn2-seals-set-phase 0 *fn2-seal-phase-hash-return* fn2-seals)', [overlay])
    if len(release_overlay) != 1 or len(advance_hash) != 1 or release_overlay[0].start >= advance_hash[0].start:
        raise ValueError('overlay return advances before accepted release')
    if not lr.match('((unless (or (eq code :ok) (eq code :retired))) '
                    '(mv code fn2-seals fn2-overlays fn2-pool))', [overlay]):
        raise ValueError('overlay held/credit must preserve phase and handle')
    release_hash = lr.match('(fn2-pool-release hslot ?*args)', [hash_return])
    final = lr.match('(fn2-seals-put 0 ?*args)', [hash_return])
    if len(release_hash) != 1 or len(final) != 1 or release_hash[0].start >= final[0].start:
        raise ValueError('hash return advances before accepted release')
    if not lr.match('((unless (or (eq code :ok) (eq code :retired))) '
                    '(mv code fn2-seals fn2-pool))', [hash_return]):
        raise ValueError('hash held/credit must preserve phase and handle')
    if not lr.match('(mv :done fn2-seals fn2-pool)', [hash_return]):
        raise ValueError('hash cleanup completion lost')


class Source(unittest.TestCase):
    def test_fixed_original_and_exact_whole_file_transform(self):
        original = subprocess.check_output(
            ['git', 'show', f'{BASE}:books/sealer.lisp'], cwd=ROOT, text=True)
        for pattern, old in rw.BEFORE.items():
            node = one(pattern, original)
            self.assertEqual(original[node.start:node.end], old, pattern)
        transformed, count = rw.transform(original)
        self.assertEqual(count, 6)
        self.assertEqual(transformed, rw.PATH.read_text())
        self.assertEqual(rw.transform(transformed), (transformed, 0))

    def test_phase_and_retry_controls(self):
        check(rw.PATH.read_text())

    def test_mutations_refused(self):
        source = rw.PATH.read_text()
        for old, new in (
                ('(fn2-seals-set-phase 0 *fn2-seal-phase-overlay-return* fn2-seals)',
                 '(fn2-seals-set-phase 0 *fn2-seal-phase-install* fn2-seals)'),
                ('(fn2-seal-hash-return fn2-seals fn2-pool)',
                 '(fn2-seal-install fn2-seals fn2-overlays fn2-run-installed fn2-pool)')):
            self.assertIn(old, source)
            with self.assertRaises(ValueError):
                check(source.replace(old, new, 1))
        overlay = one('(defun fn2-seal-overlay-return ?*body)', source)
        gate = lr.match('((unless (or (eq code :ok) (eq code :retired))) '
                        '(mv code fn2-seals fn2-overlays fn2-pool))', [overlay])[0].node
        condition = gate.items[0].items[1]
        with self.assertRaises(ValueError):
            check(lr.write(source, [(condition.start, condition.end, '(eq code :ok)')]))

    def test_actual_provider_staged_fixture_keeps_all_handles(self):
        source = (ROOT / 'tests/seal-release-row-held-unit.lisp').read_text()
        body = one('(defun fn2-srh-staged-cleanup-body ?*body)', source)
        columns = one('(defcolumns fn2-seals ?*body)', rw.PATH.read_text()).items[2].items
        seal_snapshot = one('(defun fn2-srh-seals-rows ?*body)', source)
        for column in columns:
            field = column.items[0].low
            self.assertTrue(lr.match(f'(fn2-seals-{field} i fn2-seals)', [seal_snapshot]),
                            field)
        for pattern in (
                '(fn2-pool-query-acquire held-slot held-gen 0 1 1 10 3 fn2-pool)',
                '(fn2-seal-install fn2-seals fn2-overlays fn2-run-installed fn2-pool)',
                '(fn2-seal-overlay-return fn2-seals fn2-overlays fn2-pool)',
                '(fn2-seal-hash-return fn2-seals fn2-pool)',
                '(fn2-pool-query-release held-slot held-gen fn2-pool)',
                '(eq duplicate :state)', '(eq hash-first :held)', '(eq arena :held)',
                '(equal after-install-seals (fn2-srh-seals-rows 0 fn2-seals))',
                '(equal after-install-pool (fn2-srh-pool-snapshot fn2-pool))',
                '(equal (if hold-hash after-arena-seals after-install-seals) '
                '(fn2-srh-seals-rows 0 fn2-seals))',
                '(equal (if hold-hash after-arena-pool after-install-pool) '
                '(fn2-srh-pool-snapshot fn2-pool))'):
            self.assertTrue(lr.match(pattern, [body]), pattern)
        self.assertEqual(len(lr.match('(assert-event ?*body)', lr.parse(source).forms,
                                      deep=False)), 7)


if __name__ == '__main__':
    unittest.main()
