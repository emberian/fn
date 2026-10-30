"""R performance drivers: each published row measured by the carried load matrix (`tools/load`, RELEASE-PLAN §2.2 R).

One hook for every family: `FN2_SURFACE_PERF_<FAMILY>=fn2.tests.surface.perf:perf`. A row names the
tools/load cell whose run measures it and the bars (tools/load/bars.json) that read it. The driver runs the
cell once per surface run (cached under OUT/perf/cells/<cell>/; several rows share W1, W6a, W15), and returns
the headline metric with its unit and the cell's profile, every bar metric beside it, and tools/load's own
verdict rows (PASS / FAIL / REPORTED / NOT-MEASURED) as published data. Nothing here compares a number to a
bar: the verdicts are tools/load's, printed, never asserted (README: performance is published, never a gate).

A row no cell measures is a named skip. A cell that measured none of the row's metrics is a skip carrying
tools/load's own NOT-MEASURED reason, never an estimate.
"""
import json
import os
from pathlib import Path
import sys
import unittest

from fn2.tests.surface import ROOT, driver

# row -> (cell, [bar ids]); the first bar's first metric is the headline.
ROWS = {
    'T-CMD': ('T-CMD', ['T-CMD']),
    'T-READ': ('W2', ['T-READ', 'L-READ']),
    'T-LIN': ('W14', ['T-LIN', 'L-LIN']),
    'T-POST': ('W1', ['T-POST', 'L-POST']),
    'T-RATE': ('W1', ['T-RATE']),
    'T-PUB-STALL': ('W8S', ['T-PUB-STALL']),
    'T-ALLOC': ('T-OPS', ['T-ALLOC', 'T-CALLS', 'T-SYNC']),
    'T-OPEN': ('W15', ['T-OPEN']),
    'T-PUB': ('W15', ['T-PUB']),
    'W15': ('W15', ['T-OPEN', 'T-PUB']),
    'L-CATCHUP': ('W6a', ['L-CATCHUP', 'T-CATCH']),
    'W6a': ('W6a', ['L-CATCHUP', 'L-DIVERGE-CATCHUP']),
    'W6q': ('W6q', []),
    'L-DIVERGE-*': ('W6b', ['L-DIVERGE-FEED']),
    'F8 custody/receipt figures': ('F8', ['P1-DURABLE-F8', 'P2-IDENTITY-F8', 'P5-RECOVERY-F8']),
    'conn-capacity': ('conn-capacity', []),
    'L-FRESH': ('L-FRESH', ['L-FRESH']),
    'W13 VmHWM': ('W13', ['L-HWM', 'L-RSS']),
}
# Rows the carried matrix does not measure, with what does or will.
UNMEASURED = {
    'W7': 'W7 runs through tools.load.w7_extent, not the cell driver; its adapter is owed',
    'wake p50/p95 (30 waiters, 3-7k rows/day)': 'no tools/load cell; the remote waiter workload is E3\'s (RELEASE-PLAN §1 consumer row)',
    'M5 bytes per isolated ack': 'no tools/load cell; owed with E3\'s consumer wire',
    'per-page p99': 'no tools/load cell for the web face; owed with E7',
    'tls_handshake_budget': 'measured by the tls_handshake_budget native (E), not a tools/load cell',
    'W3': 'no tools/load cell (the hostile connection-flood workload is owed)',
    'W4': 'no tools/load cell (the hostile auth-failure workload is owed)',
    'W5': 'no tools/load cell (the hostile slow-sender workload is owed)',
}
CELL_SECONDS = int(os.environ.get('FN2_SURFACE_PERF_CELL_SECONDS', '2300'))


def unit(metric, bar):
    if bar.get('unit'):
        return bar['unit']
    # The metric's last word names what it is (`publish.write_octets.exponent` is an exponent, H7 run).
    for suffix, name in (('exponent', 'exponent'), ('ratio', 'ratio'), ('violations', 'count'), ('_ms', 'ms'),
                         ('_s', 's'), ('kib', 'KiB'), ('rate', 'per s'), ('octets', 'octets')):
        if suffix in metric.rsplit('.', 1)[-1] or suffix in metric:
            return name
    return 'value'


def run_cell(cell, out):
    """result.json's cell row for CELL, running tools/load once per surface run."""
    directory = Path(out) / 'perf' / 'cells' / cell
    result = directory / 'result.json'
    if not result.exists():
        from tests.native_harness import native_image
        image = native_image('FN_NATIVE_HOST')
        argv = [sys.executable, '-m', 'tools.load.driver', 'run', '--cell', cell, '--image', str(image),
                '--label', 'fn2-h-' + cell.replace('/', '-'), '--out', str(directory),
                # The output's filesystem (ZFS on hbox), not /dev/shm: the disk rows' checks name zfs.
                '--work', str(directory / 'work')]
        status = driver(argv, directory / 'run', CELL_SECONDS, env=dict(os.environ))
        if not result.exists():
            raise AssertionError(f'tools/load {cell}: no result.json (exit {status}); see {directory}/run/driver.log')
    data = json.loads(result.read_text())
    rows = [c for c in data['cells'] if c.get('cell', '').split('@')[0].split('/')[0] == cell and not c.get('sub')]
    if not rows:
        raise AssertionError(f'tools/load {cell}: result.json holds no {cell} row (status {data.get("status")})')
    return rows[-1], directory


def perf(*, case, target, family, out, row):
    if row in UNMEASURED:
        raise unittest.SkipTest(f'perf row {row}: {UNMEASURED[row]}')
    if row not in ROWS:
        raise ValueError(f'perf row {row} ({family}) maps to no tools/load cell')
    from tools.load import result as load_result
    cell, bar_ids = ROWS[row]
    measured, directory = run_cell(cell, out)
    by_id = {b['id']: b for b in load_result.load_bars()}
    bars = [by_id[i] for i in bar_ids]
    verdicts = [v for v in load_result.judge_cell(measured, bars)]
    metrics = measured.get('metrics') or {}
    wanted = [c['metric'] for b in bars for c in b['checks']] or sorted(metrics)
    published = {m: metrics.get(m) for m in wanted}
    headline = next((m for m in wanted if metrics.get(m) is not None), None)
    if headline is None:
        reasons = sorted({(measured.get('not_measured') or {}).get(m) or 'metric absent' for m in wanted})
        raise unittest.SkipTest(f'perf row {row}: tools/load {cell} measured none of {wanted}: ' + '; '.join(reasons))
    bar = next((b for b in bars for c in b['checks'] if c['metric'] == headline), {})
    box = measured.get('box') or {}
    return dict(value=metrics[headline], unit=unit(headline, bar), metric=headline,
                profile=dict(cell=measured.get('cell'), workload=measured.get('workload'),
                             preset=measured.get('preset'), target=measured.get('target'), status=measured.get('status'),
                             loadavg_start=box.get('loadavg_start'), fs=box.get('fs')),
                metrics=published, verdicts=verdicts, evidence=str(directory))
