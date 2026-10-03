"""Actual SBCL object identity/size accounting, independent of matcher admission."""
from pathlib import Path
import json
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


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
