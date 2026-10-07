"""Per-request cost columns of the shared native span (program section 2b, AT-1).

The raw SBCL file drives the DEPLOYED span macro and the deployed I/O leaves;
this file asserts the numbers, and runs it again over mutated copies of the
sources, which must turn the matching tooth red.
"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import native_trace

MIB = 1 << 20
COLUMNS = ('cpu_us', 'gc_us', 'gc_count', 'read_octets', 'write_octets', 'syscalls')


def run_raw(env=None):
    full = dict(os.environ, **(env or {}))
    return subprocess.run([shutil.which('sbcl') or 'sbcl', '--noinform', '--script',
                           'tests/native_request_cost_raw.lisp'], cwd=ROOT, env=full,
                          capture_output=True, text=True, timeout=120)


def rows_of(stdout):
    spans = [json.loads(s[len(native_trace.PREFIX):]) for s in stdout.splitlines()
             if s.startswith(native_trace.PREFIX)]
    return {r['phase']: r for r in spans if r.get('type') == 'span'}


def fixture_of(stdout):
    m = re.search(r'COST_FIXTURE article=(\d+) header=(\d+) stuffing=(\d+) reply=(\d+)', stdout)
    return dict(zip(('article', 'header', 'stuffing', 'reply'), map(int, m.groups())))


def at1_failures(stdout):
    """The AT-1 teeth over one raw run; the names of the teeth that failed."""
    rows, fixture, failed = rows_of(stdout), fixture_of(stdout), []

    def tooth(name, ok):
        if not ok:
            failed.append(name)
    alloc = rows['alloc-8mib']
    tooth('i-allocation', alloc['allocation_scope'] == 'isolated-process'
          and 8 * MIB <= alloc['allocated_bytes'] <= 8 * MIB + 64 * 1024)
    for path in ('plain', 'tls'):
        row = rows['article-' + path]
        tooth('ii-' + path, fixture['article'] <= row['write_octets'] <= fixture['reply']
              and row['syscalls'] >= 1 and row['read_octets'] == 0)
    gc = rows['forced-gc']
    tooth('iii-gc', gc['gc_count'] >= 1 and gc['gc_us'] >= 0)
    return failed


class RequestCostTests(unittest.TestCase):
    def test_at1_teeth_hold_on_the_deployed_span_and_leaves(self):
        result = run_raw()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('NATIVE_REQUEST_COST_PASS', result.stdout)
        self.assertEqual(at1_failures(result.stdout), [])
        rows = rows_of(result.stdout)
        for row in rows.values():
            self.assertEqual(row['v'], 2)
            for column in COLUMNS:
                self.assertIsInstance(row[column], int, column)
                self.assertGreaterEqual(row[column], 0)
            self.assertEqual((row['cpu_scope'], row['gc_scope'], row['io_scope']),
                            (row['cpu_scope'], 'process', 'thread'))
            self.assertIn(row['cpu_scope'], ('thread', 'process'))
            self.assertIsNone(row['rss_kib'])  # rss_every 0: never sampled

    def test_thread_scope_cpu_and_io(self):
        rows = rows_of(run_raw().stdout)
        # A spinning thread's CPU is its own span's; a sleeping span waiting for
        # another thread's spin and writes is charged neither.
        self.assertGreaterEqual(rows['busy']['cpu_us'], 5000)
        self.assertLess(rows['other-thread']['cpu_us'], 30000)
        self.assertEqual(rows['other-thread']['write_octets'], 0)
        self.assertEqual(rows['other-thread']['syscalls'], 0)
        self.assertEqual(rows['quiet']['write_octets'], 0)

    def test_nested_spans_report_their_own_deltas(self):
        rows = rows_of(run_raw().stdout)
        reply = fixture_of(run_raw().stdout)['reply']
        self.assertEqual(rows['inner']['write_octets'], reply)
        self.assertEqual(rows['outer']['write_octets'], 2 * reply)
        self.assertEqual(rows['inner']['parent_id'], rows['outer']['span_id'])

    def mutated(self, source, old, new, variable):
        text = (ROOT / source).read_text()
        self.assertEqual(text.count(old), 1, f'{source} no longer has exactly one {old!r}')
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / Path(source).name
        path.write_text(text.replace(old, new))
        return run_raw({variable: str(path)})

    def test_mutation_tls_leaf_not_counted_turns_the_tls_tooth_red(self):
        result = self.mutated('host/native/tls.lisp',
                              '(progn (fnn-io-count :write result)\n                   result)', 'result',
                              'FN_COST_TLS_SOURCE')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(at1_failures(result.stdout), ['ii-tls'])

    def test_mutation_plain_leaf_not_counted_turns_the_plain_tooth_red(self):
        result = self.mutated('host/native/io.lisp', '(fnn-io-count :write count)', 'nil',
                              'FN_COST_IO_SOURCE')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(at1_failures(result.stdout), ['ii-plain'])

    def test_parser_reads_v2_rows_and_refuses_malformed_columns(self):
        rows = rows_of(run_raw().stdout)
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'v2.log'
            log.write_text(''.join(native_trace.PREFIX + json.dumps(r) + '\n' for r in rows.values()))
            report = native_trace.analyze(log)
            tls = next(r for r in report['phases'] if r['phase'] == 'article-tls')
            self.assertEqual(tls['write_octets_inclusive'], rows['article-tls']['write_octets'])
            self.assertEqual(report['requests'][0]['connection_id'], 9)
            bad = dict(rows['quiet'], cpu_us=-1)
            log.write_text(native_trace.PREFIX + json.dumps(bad) + '\n')
            with self.assertRaisesRegex(ValueError, 'invalid span measurement'):
                native_trace.analyze(log)
