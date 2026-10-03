"""Shared native trace lifetimes, scope and analysis using actual SBCL source."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import native_trace


class NativeTraceTests(unittest.TestCase):
    def test_actual_macro_values_unwind_nested_scope_and_disabled_observation(self):
        result = subprocess.run([shutil.which('sbcl') or 'sbcl', '--noinform', '--script',
                                 'tests/native_trace_raw.lisp'], cwd=ROOT,
                                capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('NATIVE_TRACE_PASS', result.stdout)
        self.assertNotIn('SECRET MUST NOT LOG', result.stdout)
        rows = [json.loads(s[len(native_trace.PREFIX):]) for s in result.stdout.splitlines()
                if s.startswith(native_trace.PREFIX)]
        outer = next(r for r in rows if r.get('phase') == 'outer')
        inner = next(r for r in rows if r.get('phase') == 'inner')
        self.assertEqual(inner['parent_id'], outer['span_id'])
        self.assertEqual((outer['connection_id'], inner['operation_id'], inner['connection_generation']),
                         (9, 71, 4))
        mux = next(r for r in rows if r.get('phase') == 'mux-render')
        self.assertEqual((mux['connection_id'], mux['operation_id'], mux['connection_generation']), (9, 88, 4))
        self.assertEqual(next(r for r in rows if r.get('phase') == 'throw')['outcome'], 'nonlocal-exit')
        self.assertEqual(next(r for r in rows if r.get('phase') == 'error')['outcome'], 'condition')
        concurrent = next(r for r in rows if r.get('phase') == 'concurrent-process')
        self.assertEqual(concurrent['allocation_scope'], 'process')
        self.assertGreater(concurrent['allocated_bytes'], 0)
        self.assertIn('TRACE_DISABLED plain=0 disabled=0', result.stdout)
        self.assertTrue(any(r.get('dropped') == 2 and r.get('sample_every') == 2 for r in rows))
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'actual.log'
            log.write_text(result.stdout)
            report = native_trace.analyze(log)
            self.assertEqual(report['phases'][0]['phase'], 'concurrent-process')
            self.assertIn('not unique allocation', report['scope'])

    def test_trace_only_owner_hook_does_not_sample_allocation(self):
        script = '''(load "tests/native_section_envelope_raw.lisp")
(in-package "ACL2")
(fnn-trace-start)
(let ((original (symbol-function 'sb-ext:get-bytes-consed)))
  (unwind-protect
       (progn (setf (symbol-function 'sb-ext:get-bytes-consed)
                    (lambda () (error "allocation sampling not opted in")))
              (assert (eq (fnn-owner-measured (:clock-only 3) :ok) :ok)))
    (setf (symbol-function 'sb-ext:get-bytes-consed) original)))
(fnn-trace-report *standard-output*)'''
        # SBCL's package lock intentionally protects its API; the fixture
        # explicitly unlocks it only to detect any accidental counter call.
        script = '(sb-ext:unlock-package "SB-EXT")\n' + script
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'trace-only.lisp'
            path.write_text(script)
            result = subprocess.run([shutil.which('sbcl') or 'sbcl', '--noinform', '--script', str(path)],
                                    cwd=ROOT, capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        rows = [json.loads(s[len(native_trace.PREFIX):]) for s in result.stdout.splitlines()
                if s.startswith(native_trace.PREFIX)]
        row = next(r for r in rows if r.get('phase') == 'clock-only')
        self.assertIsNone(row['allocated_bytes'])
        self.assertEqual(row['allocation_scope'], 'disabled')

    def test_analysis_keeps_scopes_and_reports_inclusive_comparison(self):
        def span(scope, allocated):
            return native_trace.PREFIX + json.dumps(dict(type='span', phase='render', allocation_scope=scope,
                duration_us=10, allocated_bytes=allocated, outcome='returned')) + '\n'
        with tempfile.TemporaryDirectory() as directory:
            baseline, current = (Path(directory) / p for p in ('old.log', 'new.log'))
            baseline.write_text(span('process', 100) + span('isolated-process', 20))
            current.write_text(span('process', 40) + span('isolated-process', 10) + span('disabled', None))
            report = native_trace.analyze(current)
            self.assertEqual(len(report['phases']), 3)
            changes = native_trace.compare(report, native_trace.analyze(baseline))
            self.assertEqual({r['allocation_scope']: r['mean_allocated_bytes_delta'] for r in changes},
                             {'process': -60, 'isolated-process': -10})
            result = subprocess.run([sys.executable, 'tools/native_trace.py', str(current), '--compare', str(baseline), '--json'],
                                    cwd=ROOT, capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(len(json.loads(result.stdout)['comparisons']), 2)

    def test_malformed_trace_measurement_refuses_instead_of_claiming_zero(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'bad.log'
            log.write_text(native_trace.PREFIX + '{"type":"span","phase":"render","allocation_scope":"process",'
                           '"duration_us":-1,"allocated_bytes":0}\n')
            with self.assertRaisesRegex(ValueError, 'invalid span measurement'):
                native_trace.analyze(log)
