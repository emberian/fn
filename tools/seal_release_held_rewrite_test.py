"""Source controls for query-held resident and overlay release ordering.

The ACL2 operation fixture is prepared against the real pool provider but
is not executed by this Python test.
"""

from pathlib import Path
import subprocess
import unittest

import lisp_rewrite as lr
import seal_release_held_rewrite as rw
import seal_cleanup_phase_rewrite as phases

ROOT = Path(__file__).resolve().parents[1]
BASE = 'cfe47d373'
PROVIDER = '826e44b7fd086f13cee9344aa6a4dacef74c144b'


def at(ref, file):
    return subprocess.check_output(['git', 'show', f'{ref}:{file}'],
                                   cwd=ROOT, text=True)


def one(pattern, source):
    found = lr.match(pattern, lr.parse(source).forms, deep=False)
    if len(found) != 1:
        raise AssertionError(f'expected one {pattern}, found {len(found)}')
    return found[0].node


def check_order(sealer):
    row = one('(defun fn2-seal-release-row ?*body)', sealer)
    overlay = one('(defun fn2-seal-retire ?*body)', sealer)
    row_patterns = [
        '(= (fn2-run-installed-physical r fn2-run-installed) 1)',
        '(fn2-run-cache-peek (nfix u) fn2-run-cache)',
        '(fn2-pool-release-countp slot fn2-pool)',
        '(fn2-pool-release slot gen (fn2-run-installed-okind r fn2-run-installed) '
        '(fn2-run-installed-oslot r fn2-run-installed) '
        '(fn2-run-installed-ogen r fn2-run-installed) fn2-pool)',
        '(or (eq released :ok) (eq released :retired))',
        '(fn2-run-cache-drop (nfix u) fn2-run-cache)',
        '(fn2-run-retired-next r fn2-run-installed)',
    ]
    positions = []
    for pattern in row_patterns:
        found = lr.match(pattern, [row])
        if len(found) != 1:
            raise ValueError('resident release lost ' + pattern)
        positions.append(found[0].start)
    if positions != sorted(positions):
        raise ValueError('resident release consumes handle before pool acceptance')
    if not lr.match('((unless (or (eq released :ok) (eq released :retired))) '
                    '(mv released fn2-run-cache fn2-pool))', [row]):
        raise ValueError('resident refusal does not retain cache')
    overlay_patterns = [
        '(equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-frozen*)',
        '(fn2-pool-release-countp slot fn2-pool)',
        '(fn2-pool-release slot gen okind oslot ogen fn2-pool)',
        '(or (eq released :ok) (eq released :retired))',
        '(fn2-ov-advance o *fn2-overlay-phase-frozen* *fn2-overlay-phase-free* fn2-overlays)',
    ]
    positions = []
    for pattern in overlay_patterns:
        found = lr.match(pattern, [overlay])
        if len(found) != 1:
            raise ValueError('overlay release lost ' + pattern)
        positions.append(found[0].start)
    if positions != sorted(positions):
        raise ValueError('overlay advances before pool acceptance')
    if not lr.match('((unless (or (eq released :ok) (eq released :retired))) '
                    '(mv released fn2-overlays fn2-pool))', [overlay]):
        raise ValueError('overlay refusal does not retain row')
    if not lr.match('(mv (if (eq code :ok) released code) fn2-overlays fn2-pool)', [overlay]):
        raise ValueError('overlay loses accepted :retired code')


class Source(unittest.TestCase):
    def test_fixed_original_forms_and_exact_current_transformation(self):
        for file, patterns in rw.REPLACEMENTS.items():
            baseline = at(BASE, file)
            for pattern, old in rw.BEFORE[file].items():
                node = one(pattern, baseline)
                self.assertEqual(baseline[node.start:node.end], old, pattern)
            expected, count = rw.transform(file, baseline)
            self.assertEqual(count, len(patterns) + (2 if file == 'books/sealer.lisp' else 0), file)
            if file == 'books/sealer.lisp':
                expected, phase_count = phases.transform(expected)
                self.assertEqual(phase_count, 6)
            self.assertEqual(expected, (ROOT / file).read_text(), file)
            if file == 'books/sealer.lisp':
                self.assertEqual(phases.transform(expected), (expected, 0))
            else:
                self.assertEqual(rw.transform(file, expected), (expected, 0))

    def test_both_effect_orders_and_refusals(self):
        sealer = (ROOT / 'books/sealer.lisp').read_text()
        check_order(sealer)
        start = one('(defun fn2-seal-start ?*body)', sealer)
        overlay_return = one('(defun fn2-seal-overlay-return ?*body)', sealer)
        hash_return = one('(defun fn2-seal-hash-return ?*body)', sealer)
        self.assertTrue(lr.match('(if (or (eq code :ok) (eq code :retired)) :retired code)', [start]))
        self.assertTrue(lr.match('((unless (or (eq code :ok) (eq code :retired))) '
                                 '(mv code fn2-seals fn2-overlays fn2-pool))', [overlay_return]))
        self.assertTrue(lr.match('((unless (or (eq code :ok) (eq code :retired))) '
                                 '(mv code fn2-seals fn2-pool))', [hash_return]))

    def test_order_mutations_are_refused(self):
        actual = (ROOT / 'books/sealer.lisp').read_text()
        row = one('(defun fn2-seal-release-row ?*body)', actual)
        release = lr.match('(fn2-pool-release slot gen ?*args)', [row])[0]
        drop = lr.match('(fn2-run-cache-drop (nfix u) fn2-run-cache)', [row])[0]
        self.assertLess(release.start, drop.start)
        mutated = actual.replace('(fn2-run-cache-drop (nfix u) fn2-run-cache)',
                                 '(fn2-run-cache-peek (nfix u) fn2-run-cache)', 1)
        with self.assertRaises(ValueError):
            check_order(mutated)
        overlay = one('(defun fn2-seal-retire ?*body)', actual)
        advance = lr.match('(fn2-ov-advance o ?*args)', [overlay])[0]
        self.assertTrue(advance.start > overlay.start)
        mutated = actual.replace('(or (eq released :ok) (eq released :retired))',
                                 '(eq released :ok)', 2)
        with self.assertRaises(ValueError):
            check_order(mutated)

    def test_peek_is_pure_and_drop_uses_same_lookup(self):
        runs = (ROOT / 'books/runs.lisp').read_text()
        peek = one('(defun fn2-run-cache-peek ?*body)', runs)
        drop = one('(defun fn2-run-cache-drop ?*body)', runs)
        self.assertFalse(lr.match('(fn2-run-cache-put ?*args)', [peek]))
        self.assertEqual(len(lr.match('(fn2-run-cache-peek unit fn2-run-cache)', [drop])), 1)
        self.assertEqual(len(lr.match('(fn2-run-cache-put i '
                                      '(state *fn2-run-cache-state-empty*))', [drop])), 1)

    def test_actual_provider_and_acquired_reference_fixture(self):
        pool = at(PROVIDER, 'books/pool.lisp')
        acquire = one('(defun fn2-pool-query-acquire ?*body)', pool)
        close = one('(defun fn2-pool-query-release ?*body)', pool)
        release = one('(defun fn2-pool-release ?*body)', pool)
        workspace = one('(defun fn2-pool-workspace-code ?*body)', pool)
        self.assertTrue(lr.match('(fn2-pool-set-query-ref-count slot ?*args)', [acquire]))
        self.assertTrue(lr.match('(fn2-pool-set-query-ref-count slot ?*args)', [close]))
        self.assertTrue(lr.match('(mv :ok (= count 1) fn2-pool)', [close]))
        self.assertTrue(lr.match('(if (fn2-pool-ownerp slot okind oslot ogen fn2-pool) :held :owner)', [workspace]))
        self.assertTrue(lr.match('(mv :credit fn2-pool)', [release]))
        fixture = (ROOT / 'tests/seal-release-row-held-unit.lisp').read_text()
        lr.parse(fixture)
        for name in ('fn2-srh-resident-held-body', 'fn2-srh-overlay-held-body'):
            body = one(f'(defun {name} ?*body)', fixture)
            self.assertEqual(len(lr.match('(fn2-pool-query-acquire slot gen 0 1 1 10 3 fn2-pool)', [body])), 1)
            self.assertEqual(len(lr.match('(fn2-pool-query-release slot gen fn2-pool)', [body])), 1)
        for name in ('fn2-srh-resident-held-body', 'fn2-srh-resident-retired-body',
                     'fn2-srh-resident-credit-body'):
            body = one(f'(defun {name} ?*body)', fixture)
            self.assertTrue(lr.match('(fn2-run-install 0 1 1 0 slot gen 0 1 1 1 10 3 '
                                     'fn2-run-installed)', [body]))
            self.assertTrue(lr.match('(fn2-run-install-units 0 0 0 fn2-run-installed)',
                                     [body]))
            self.assertTrue(lr.match('(fn2-run-retire 0 fn2-run-installed)', [body]))
        overlay = one('(defun fn2-srh-overlay-held-body ?*body)', fixture)
        self.assertTrue(lr.match('(fn2-ov-start 0 1 slot gen 0 1 1 10 3 0 '
                                 'fn2-overlays fn2-overlay-index fn2-pool)', [overlay]))
        self.assertTrue(lr.match('(fn2-ov-freeze 0 fn2-overlays)', [overlay]))
        self.assertEqual(len(lr.match('(assert-event ?*body)', lr.parse(fixture).forms, deep=False)), 7)
        overlay_retired = one('(defun fn2-srh-overlay-retired-body ?*body)', fixture)
        self.assertTrue(lr.match('(eq released :retired)', [overlay_retired]))
        self.assertTrue(lr.match('(eq twice :state)', [overlay_retired]))
        credit = one('(defun fn2-srh-resident-credit-body ?*body)', fixture)
        for pattern in ('(fn2-pool-credit-configure ?*args)',
                        '(fn2-pool-credit-begin ?*args)',
                        '(fn2-pool-reserve-credit ?*args)',
                        '(eq refused :credit)'):
            self.assertTrue(lr.match(pattern, [credit]), pattern)

    def test_refusal_snapshots_cover_actual_row_and_pool_fields(self):
        fixture = (ROOT / 'tests/seal-release-row-held-unit.lisp').read_text()
        for table, file, ref in (
                ('fn2-run-installed', 'books/runs.lisp', None),
                ('fn2-run-cache', 'books/runs.lisp', None),
                ('fn2-overlays', 'books/overlay.lisp', None),
                ('fn2-pool', 'books/pool.lisp', PROVIDER)):
            source = at(ref, file) if ref else (ROOT / file).read_text()
            columns = one(f'(defcolumns {table} ?*body)', source).items[2].items
            snapshot = one(f'(defun fn2-srh-{table.removeprefix("fn2-")}-rows ?*body)',
                           fixture)
            for column in columns:
                name = column.items[0].low
                self.assertTrue(lr.match(f'({table}-{name} i {table})', [snapshot]),
                                f'{table}.{name}')
        pool_snapshot = one('(defun fn2-srh-pool-snapshot ?*body)', fixture)
        pool_arrays = one('(defun fn2-srh-pool-arrays ?*body)', fixture)
        for field in ('data', 'class-heads', 'class-counts', 'class-sizes',
                      'credit-protected', 'credit-purpose', 'credit-phase',
                      'credit-group-nonce', 'credit-group-owner-kind',
                      'credit-group-owner-slot', 'credit-group-owner-gen',
                      'credit-demand', 'credit-available'):
            self.assertTrue(lr.match(f'(fn2-pool-{field}-length fn2-pool)', [pool_snapshot]))
            self.assertTrue(lr.match(f'(fn2-pool-{field}i i fn2-pool)', [pool_arrays]))
        for field in ('nclasses', 'gen-limit', 'credit-configured',
                      'credit-group-count', 'retired-count'):
            self.assertTrue(lr.match(f'(fn2-pool-{field} fn2-pool)', [pool_snapshot]))


if __name__ == '__main__':
    unittest.main()
