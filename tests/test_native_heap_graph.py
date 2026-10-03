"""Actual SBCL object identity/size accounting, independent of matcher admission."""
from pathlib import Path
import json
import shutil
import subprocess
import tempfile
import unittest
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import native_matcher_probe


class NativeHeapGraphTests(unittest.TestCase):
    def test_aliasing_borrowed_static_leaves_and_actual_object_sizes(self):
        script = '''(defpackage "ACL2" (:use "COMMON-LISP"))
(load "tools/native_heap_graph.lisp")
(in-package "ACL2")
(let* ((text (copy-seq "borrowed")) (tail (list text 3))
       (big (expt 2 150)) (private (list big tail tail nil t :tag #\\A))
       (borrowed (fnmg-graph (list tail)))
       (owned (fnmg-owned (fnmg-graph (list private)) borrowed))
       (summary (fnmg-summary owned)))
  (assert (= (getf summary :conses) 7))
  (assert (= (getf summary :bignums) 1))
  (assert (= (getf summary :strings) 0))
  (assert (= (getf summary :direct-bytes)
             (+ (* 7 (sb-ext:primitive-object-size (cons 0 0)))
                (sb-ext:primitive-object-size big))))
  (assert (= (getf (fnmg-summary (fnmg-union owned owned)) :direct-bytes)
             (getf summary :direct-bytes)))
  (let* ((next (cons :next private))
         (next-owned (fnmg-owned (fnmg-graph (list next)) borrowed))
         (union (fnmg-union owned next-owned)))
    (assert (= (getf (fnmg-summary union) :conses) 8)))
  (format t "GRAPH ~a~%" (fnmg-json-summary owned)))
(assert (= (hash-table-count (fnmg-graph (list nil t :keyword 1 #\\Z))) 0))
(assert (handler-case (progn (fnmg-graph (list (make-hash-table))) nil)
          (error () t)))
(let* ((constant (copy-seq "constant")) (private (list constant))
       (owned (fnmg-owned (fnmg-graph (list private)) (fnmg-graph nil)
                          (fnmg-graph (list constant)))))
  (assert (= (getf (fnmg-summary owned) :strings) 0)))
'''
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'graph.lisp'
            path.write_text(script)
            result = subprocess.run([shutil.which('sbcl') or 'sbcl', '--noinform', '--script', str(path)],
                                    cwd=ROOT, capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        row = json.loads(next(line[6:] for line in result.stdout.splitlines() if line.startswith('GRAPH ')))
        self.assertEqual((row['conses'], row['bignums'], row['objects']), (7, 1, 8))
        self.assertGreater(row['direct-bytes'], 7 * 16)

    def test_report_preserves_counterexamples_and_refuses_missing_states_or_samples(self):
        rows = []
        for case_id in range(1, 12):
            rows.append(native_matcher_probe.PREFIX + json.dumps(dict(type='case', case_id=case_id,
                patterns=1, tokens=1, input_octets=1, owned_cons_bound=55, allocation_replays=32)))
            rows.append(native_matcher_probe.PREFIX + json.dumps(dict(type='state', case_id=case_id,
                step=0, owned={'conses': 56, 'direct-bytes': 896}, over_bound=True)))
            rows.append(native_matcher_probe.PREFIX + json.dumps(dict(type='done', case_id=case_id,
                steps=0, matched=False)))
            rows.append('FN_TRACE ' + json.dumps(dict(type='span', operation_id=case_id,
                phase='matcher-round', allocation_scope='isolated-process', allocated_bytes=1024,
                duration_us=1, outcome='returned')))
        rows.append('FN_TRACE ' + json.dumps(dict(type='summary', dropped=0, incomplete=0)))
        rows.append('NATIVE_MATCHER_HEAP_PASS')
        result = native_matcher_probe.report('\n'.join(rows))
        self.assertEqual(result['cases'][0]['over_bound_steps'], [0])
        self.assertEqual(result['cases'][0]['allocation_sample']['allocated_bytes'], 1024)
        with self.assertRaisesRegex(ValueError, 'incomplete retained state'):
            native_matcher_probe.report('\n'.join(rows[:1] + rows[2:]))
        with self.assertRaisesRegex(ValueError, 'missing matched allocation'):
            native_matcher_probe.report('\n'.join(rows[:3] + rows[4:]))
        with self.assertRaisesRegex(ValueError, 'incomplete allocation'):
            native_matcher_probe.report('\n'.join(rows[:-2] + rows[-1:]))
