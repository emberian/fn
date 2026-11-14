"""Execute the actual shared run close policy in a small SBCL carrier.

Source-only: this does not admit ACL2 events or run a storage/native pipeline.
"""
import shutil
import subprocess
import unittest
from pathlib import Path

from tools import lisp_source
from tests.test_checkpoint_capacity_source import emit

ROOT = Path(__file__).resolve().parents[1]


def function(name, book):
    for source in lisp_source.forms((ROOT / 'books' / book).read_text()):
        form = lisp_source.read_sexp(source)
        if isinstance(form, list) and form[:2] == ['defun', name]:
            return emit(form[:3] + [f for f in form[3:] if f[:1] != ['declare']])
    raise AssertionError(name)


@unittest.skipUnless(shutil.which('sbcl'), 'source policy control requires SBCL')
class CloseFullSourceTests(unittest.TestCase):
    def run_policy(self, policy):
        script = '''
(defmacro mv (&rest xs) `(values ,@xs))
(defmacro mv-let (names expr &rest body) `(multiple-value-bind ,names ,expr ,@body))
(defun zp (x) (not (and (integerp x) (< 0 x))))
(defparameter *fn2-run-writer-phase-open* 1)
(defparameter *fn2-run-writer-phase-closing* 2)
(defun fn2-run-writers-entries (w rows) (second (nth w rows)))
(defun fn2-run-writers-phase (w rows) (first (nth w rows)))
(defun fn2-run-writers-set-pos (w pos rows)
 (let ((rows (copy-tree rows))) (setf (third (nth w rows)) pos) rows))
(defun fn2-run-writers-set-phase (w phase rows)
 (let ((rows (copy-tree rows))) (setf (first (nth w rows)) phase) rows))
''' + function('fn2-run-close', 'runs-page.lisp') + '\n' + policy + '''
(let ((before '((1 0 19) (1 3 29) (2 4 39))))
 (multiple-value-bind (code rows) (fn2-run-close-full 0 before)
  (assert (eq code :length)) (assert (equal rows before)))
 (multiple-value-bind (code rows) (fn2-run-close-full 1 before)
  (assert (eq code :more)) (assert (equal rows '((1 0 19) (2 3 0) (2 4 39)))))
 (multiple-value-bind (code rows) (fn2-run-close-full 2 before)
  (assert (eq code :state)) (assert (equal rows before)))
 (assert (equal before '((1 0 19) (1 3 29) (2 4 39)))))
'''
        return subprocess.run(['sbcl', '--noinform', '--disable-debugger', '--script', '/dev/stdin'],
                              input=script, text=True, capture_output=True, timeout=30)

    def test_empty_refuses_and_nonempty_closes(self):
        result = self.run_policy(function('fn2-run-close-full', 'runs-page.lisp'))
        self.assertEqual(result.returncode, 0, result.stderr[-2000:])

    def test_empty_guard_removal_is_detected(self):
        policy = function('fn2-run-close-full', 'runs-page.lisp')
        mutant = policy.replace('(zp (fn2-run-writers-entries w fn2-run-writers))', 'nil')
        self.assertNotEqual(policy, mutant)
        self.assertNotEqual(self.run_policy(mutant).returncode, 0)

    def test_leaf_and_parent_use_shared_policy(self):
        assemble = (ROOT / 'books/runs-assemble.lisp').read_text()
        parent = function('fn2-run-promote-commit', 'runs.lisp')
        self.assertIn('(fn2-run-close-full w fn2-run-writers)', assemble)
        self.assertIn('(fn2-run-close-full (+ 1 w) fn2-run-writers)', parent)
        self.assertNotIn('(fn2-run-close ', parent)
