"""Actual cold loader-readiness source controls; these do not execute ACL2."""
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


def calls(node):
    return [n[0] for n in walk(node) if n and isinstance(n[0], str)]


def definitions(path):
    return {n[1]: n for t in forms((ROOT / path).read_text()) for n in walk(read_sexp(t))
            if len(n) > 2 and n[0] == 'defun' and isinstance(n[1], str)}


def current_bound(node):
    used = calls(node)
    return all(name in used for name in ['fn2-run-loads-admissions', 'fn2-run-load-readiness-admissions',
        'fn2-run-load-readiness-cursor-end', 'fn2-run-loads-rows', 'fn2-run-load-readiness-row',
        'fn2-run-load-ops-rows', 'fn2-run-load-geometry-current-p', 'fn2-run-load-readiness-ownerp',
        'fn2-run-load-readiness-roomp'])


class RunPhysicalReadinessSource(unittest.TestCase):
    def setUp(self):
        self.ready = definitions('books/run-physical-readiness.lisp')
        self.geometry = definitions('books/run-physical-geometry.lisp')

    def test_profile_geometry_is_real_initializer_data_and_readonly_to_scan(self):
        init = self.geometry['fn2-run-load-geometry-profile-init']
        for name in ['fn2-b-run-cursor-rows', 'fn2-profile-t', 'fn2-b-read-rows', 'fn2-profile-o',
                     'fn2-b-upload-windows', 'fn2-b-ctl-rows', 'fn2-b-format-slots',
                     'fn2-b-field-rows', 'fn2-b-digest-minimum']:
            self.assertIn(name, calls(init))
        for source in self.ready.values():
            self.assertNotIn('fn2-run-load-geometry-put', calls(source))
            self.assertNotIn('fn2-run-load-geometry-profile-init', calls(source))
        current = self.ready['fn2-run-load-geometry-current-p']
        for actual in ['fn2-id-decides-rows', 'fn2-reads-rows', 'fn2-run-cursors-rows',
                       'fn2-checkpoint-summary-leases-rows', 'fn2-ops-rows', 'fn2-run-load-ops-rows',
                       'fn2-fc-rows', 'fn2-fc-context-rows', 'fn2-b3-rows', 'fn2-fields-rows', 'fn2-digests-rows']:
            self.assertIn(actual, calls(current))
        self.assertIn('*fn2-b-range-source-cursors*', str(current))
        self.assertIn('*fn2-b-seal-source-cursors*', str(current))
        self.assertIn('fn2-run-loads-admissions', calls(current))

    def test_row_checks_private_checker_stripes_and_initialized_jobs(self):
        row = self.ready['fn2-run-load-readiness-one-row-p']
        for name in ['fn2-run-loads-phase', 'fn2-run-loads-windows', 'fn2-run-loads-pending',
                     'fn2-run-loads-checker', 'fn2-run-load-geometry-prefix',
                     'fn2-run-cursors-phase', 'fn2-run-cursors-physical',
                     'fn2-checkpoint-summary-leases-live', 'fn2-fc-phase', 'fn2-b3-ready',
                     'fn2-run-readerp', 'fn2-digest-rowp']:
            self.assertIn(name, calls(row))
        geometry = self.ready['fn2-run-load-geometry-current-p']
        self.assertIn('fn2-run-load-geometry-controls', calls(geometry))
        self.assertIn('5', str(geometry))
        op = self.ready['fn2-run-load-readiness-op-row-p']
        for name in ['fn2-run-load-ops-live', 'fn2-run-load-ops-generation', 'fn2-run-load-ops-cursor', 'fn2-ops-rows']:
            self.assertIn(name, calls(op))

    def test_completion_is_two_actual_eofs_and_admission_serial_not_caller_flag(self):
        done = self.ready['fn2-run-load-readiness-complete-current-p']
        self.assertTrue(current_bound(done))
        damaged = copy.deepcopy(done)
        for n in walk(damaged):
            if n and n[0] == 'fn2-run-loads-admissions':
                n[0] = 'unchecked-admissions'
        self.assertFalse(current_bound(damaged))
        self.assertNotIn('fn2-run-load-readiness-one-row-p', calls(done))
        self.assertNotIn('fn2-run-load-readiness-op-row-p', calls(done))
        step = self.ready['fn2-run-load-readiness-step']
        self.assertIn('fn2-run-loads-admissions', calls(step))
        self.assertIn('fn2-run-load-readiness-one-row-p', calls(step))
        self.assertIn('fn2-run-load-readiness-op-row-p', calls(step))
        self.assertNotIn('fn2-run-load-readiness-step', calls(step[3:]))
        self.assertNotIn('fn2-block-read-children', calls(step))

    def test_only_private_scan_carrier_mutates_and_result_width_is_two(self):
        for name in ['fn2-run-load-readiness-begin', 'fn2-run-load-readiness-step']:
            for node in walk(self.ready[name]):
                if node and node[0] == 'mv':
                    self.assertEqual(len(node) - 1, 2)
                    self.assertEqual(node[-1], 'fn2-run-load-readiness')
            writes = [n for n in calls(self.ready[name]) if '-set-' in n or n.endswith('-put')]
            self.assertTrue(all(n.startswith('fn2-run-load-readiness-') for n in writes), writes)
        begin = self.ready['fn2-run-load-readiness-begin']
        self.assertIn('fn2-run-loads-admissions', calls(begin))
        self.assertNotIn('ready', begin[2])
        self.assertNotIn('complete', begin[2])

    def test_room_is_actual_class_capacity_and_free_count_not_a_future_promise(self):
        room = self.ready['fn2-run-load-readiness-roomp']
        for name in ['fn2-pool-class-for', 'fn2-pool-class-sizesi', 'fn2-run-load-roomp',
                     'fn2-ops-free-head', 'fn2-ops-outbox-credits']:
            self.assertIn(name, calls(room))
        self.assertIn('*fn2-b-query-loader-jobs*', str(room))
        self.assertIn('fn2-run-load-readiness-roomp', calls(self.ready['fn2-run-load-readiness-begin']))
        self.assertIn('fn2-run-load-readiness-roomp', calls(self.ready['fn2-run-load-readiness-complete-current-p']))

    def test_prepared_initializer_fixture_uses_real_reserve_for_serial_control(self):
        unit = definitions('tests/run-physical-readiness-unit.lisp')
        self.assertIn('fn2-core-init', calls(unit['fn2-rly-body']))
        self.assertIn('fn2-run-load-reserve', calls(unit['fn2-rly-reserve']))
        self.assertNotIn('update-fn2-run-loads-admissions', calls(unit['fn2-rly-body']))
        self.assertIn('fn2-rly-roomp', calls(unit['fn2-rly-body']))
        self.assertIn('fn2-rly-stamp', calls(unit['fn2-rly-body']))
        self.assertIn('fn2-rly-current', calls(unit['fn2-rly-body']))
        fuel = unit['fn2-rly-scan-fuel']
        self.assertIn('fn2-run-loads-rows', calls(fuel))
        self.assertIn('fn2-run-load-ops-rows', calls(fuel))
        text = (ROOT / 'tests/run-physical-readiness-unit.lisp').read_text()
        for mode in ['complete', 'partial', 'row', 'foreign', 'serial']:
            self.assertIn('(assert-event (fn2-rly-test :' + mode + '))', text)
        production = definitions('books/run-physical-resources.lisp')['fn2-run-load-reserve']
        bstar = next(n for n in walk(production) if n and n[0] == 'b*')
        serial = next(i for i, n in enumerate(bstar[1]) if 'update-fn2-run-loads-admissions' in calls(n))
        allocation = next(i for i, n in enumerate(bstar[1]) if 'fn2-pool-reserve' in calls(n))
        self.assertLess(serial, allocation)


if __name__ == '__main__':
    unittest.main()
