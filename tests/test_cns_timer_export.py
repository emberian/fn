"""Exercise the actual raw printer with a small synthetic world (no ACL2 proof claim)."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

PRINTER = Path(__file__).parents[1] / 'meta/emit/print-world.lisp'


@unittest.skipUnless(shutil.which('sbcl'), 'raw printer control needs SBCL')
class ScopedTimerExport(unittest.TestCase):
    def test_scope_keeps_body_guard_measure_closure_and_default_context(self):
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / 'control.lisp'
            script.write_text('''
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *meta-w* nil)
(defvar *meta-natives* nil)
(defvar *fn2-machine-directory-fields* nil)
(defun meta-body (name) (case name (helper '(body-helper)) (otherwise '(quote 0))))
(defun meta-measure (name) (and (eq name 'helper) '(measure-helper)))
(defun getpropc (name prop default world)
  (declare (ignore world))
  (if (and (eq name 'helper) (eq prop 'guard)) '(guard-helper) default))
(defun meta-kind (kind) (list kind :table nil))
(defun meta-kw (key row) (getf row key))
(defun meta-column-fns (kind columns) (declare (ignore columns)) (list kind))
(defun fn2-columns-sym (kind suffix) (declare (ignore kind suffix)) 'snapshot-reader)
(defun fn2-tv-object (object) object)
(defun fn2-tv-function (name world) (declare (ignore world)) name)
(defun fn2-tv-manifest (world) (declare (ignore world)) nil)
(defun meta-constants (prefixes) (declare (ignore prefixes)) nil)
(defun meta-arm-constants (kind acc) (declare (ignore kind)) acc)
(defun acl2-version+ () "synthetic-printer-control")
(with-open-file (input "''' + str(PRINTER) + '''")
  (loop for form = (read input nil :eof) until (eq form :eof) do
    (when (and (consp form) (eq (car form) 'defun)
               (member (cadr form) '(meta-fns-of meta-fns-of-list meta-closure meta-print-certificate)))
      (eval form))))
(meta-print-certificate "scoped.sexp" '(helper) 'fn2-cns nil nil)
(meta-print-certificate "context.sexp" '(helper) 'fn2-cns)
(flet ((packet (path) (with-open-file (input path) (cdr (read input)))))
  (let ((scoped (packet "scoped.sexp")) (context (packet "context.sexp")))
    (assert (equal (getf scoped :roots) '(helper)))
    (assert (null (set-exclusive-or (getf scoped :functions)
                                  '(helper body-helper guard-helper measure-helper))))
    (assert (null (getf scoped :refused)))
    (assert (member 'snapshot-reader (getf context :roots)))
    (assert (member 'fn2-machine-slot (getf context :roots)))
    (assert (member 'fn2-cns (getf context :roots)))))
(format t "SCOPED-TIMER-PRINTER-CONTROL PASS~%")
''')
            result = subprocess.run(['sbcl', '--noinform', '--script', str(script)],
                                    cwd=directory, text=True, capture_output=True, timeout=15)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('SCOPED-TIMER-PRINTER-CONTROL PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()
