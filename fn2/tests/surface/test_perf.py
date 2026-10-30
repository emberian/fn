"""Unit tests for the R perf driver's row map and result shaping (no node; the cells run on hbox)."""
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from fn2.tests.surface import FAMILIES, perf


class PerfDriverUnit(unittest.TestCase):
    def test_every_manifest_row_is_mapped_or_named_unmeasured(self):
        rows = {row for family in FAMILIES.values() for row in family['performance_rows']}
        self.assertEqual(rows - set(perf.ROWS) - set(perf.UNMEASURED), set())
        self.assertFalse(set(perf.ROWS) & set(perf.UNMEASURED))
        from tools.load import result, workloads
        bars = {b['id']: b for b in result.load_bars()}
        cells = set(workloads.load()['cells'])
        for row, (cell, ids) in perf.ROWS.items():
            self.assertIn(cell, cells, row)
            for bar in ids:
                self.assertEqual(bars[bar]['cell'], cell, (row, bar))

    def fake(self, metrics, not_measured=None):
        directory = tempfile.mkdtemp()
        cell = dict(cell='W1@small', workload='post-rate', preset='small', target='image', status='complete',
                    metrics=metrics, not_measured=not_measured or {}, box={'loadavg_start': [1.0], 'loadavg_end': [1.0], 'fs': 'zfs', 'busy_cores_start': 0, 'busy_cores_end': 0, 'pinned': True})
        return mock.patch.object(perf, 'run_cell', return_value=(cell, Path(directory)))

    def test_headline_metric_unit_and_published_verdicts_without_a_gate(self):
        metrics = {'post.p50_ms.c1': 999.0, 'post.p99_ms.c1': 5000.0, 'post.cpu_ms_per_op.c1': 1.0,
                   'post.rate_c1': 3.0, 'post.rate_c8': 4.0}
        with self.fake(metrics):
            got = perf.perf(case=None, target='fn1', family='nntp', out='/x', row='T-POST')
        self.assertEqual((got['metric'], got['value'], got['unit']), ('post.p50_ms.c1', 999.0, 'ms'))
        self.assertEqual(got['profile']['preset'], 'small')
        verdict = {v['bar']: v['verdict'] for v in got['verdicts']}
        self.assertEqual(verdict['T-POST'], 'FAIL')      # published, and the driver still returns
        self.assertIn('post.rate_c8', got['metrics'])

    def test_nothing_measured_is_a_skip_with_the_load_reason(self):
        with self.fake({}, {'alloc.article.exponent': 'no prof hook'}):
            with self.assertRaisesRegex(unittest.SkipTest, 'no prof hook'):
                perf.perf(case=None, target='fn1', family='nntp', out='/x', row='T-ALLOC')

    def test_unmeasured_row_is_a_named_skip(self):
        with self.assertRaisesRegex(unittest.SkipTest, 'tls_handshake_budget native'):
            perf.perf(case=None, target='fn1', family='tls_auth', out='/x', row='tls_handshake_budget')


if __name__ == '__main__':
    unittest.main()
