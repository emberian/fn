"""Fixed native bridge result/error semantics; actual controller proof is separate."""
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import proof_repl
sys.path.insert(0, str(ROOT / "tests"))
import test_native_raw_dispatch_trap as trap_test

SCALAR_DRIVER = r"""
(fnn-raw-dispatch-set-hooks (lambda (name args) (declare (ignore name args)) nil)
                            (lambda () t))
(defun expect-fault (function)
  (assert (handler-case (progn (funcall function) nil) (fnn-store-fault () t))))
(expect-fault (lambda () (fnn-fixed-raw-callback 'missing)))
;; a declared target with no definition: the installation itself refuses
(setq *test-interfaces* '((missing-function :raw-with (thm))))
(assert (handler-case (progn (fnn-install-raw-dispatch :report nil) nil) (error () t)))
(expect-fault (lambda () (fnn-fixed-raw-callback 'missing-function)))
(setf (symbol-function 'raw-input-next)
      (compile nil '(lambda (token controller pool)
        (values :range 3 5 8 controller pool token))))
(setf (symbol-function 'not-compiled)
      (let ((sb-ext:*evaluator-mode* :interpret)) (eval '(lambda () :unprepared))))
(assert (not (compiled-function-p (symbol-function 'not-compiled))))
(setq *test-interfaces* '((input-next :raw-guarded t) (not-compiled :raw-with (thm)))
      *test-targets* '((input-next . raw-input-next)))
(assert (= (fnn-install-raw-dispatch :report nil) 2))
(let ((callback (fnn-fixed-raw-callback 'input-next))
      (controller (vector 0)) (pool (vector nil :uninitialized nil)))
  (multiple-value-bind (word start count end new-controller new-pool token)
      (fnn-core-mv 'input-next (funcall callback 17 controller pool))
    (assert (and (eq word :range) (= start 3) (= count 5) (= end 8)
                 (eq new-controller controller) (eq new-pool pool) (= token 17)))))
(let ((*fnn-dispatch-counterpart* t))
  (expect-fault (lambda () (fnn-fixed-raw-callback 'input-next))))
(expect-fault (lambda () (fnn-fixed-raw-callback 'not-compiled)))
(assert (zerop (length (multiple-value-list (fnn-core-mv 'zero (values))))))
(assert (eq (fnn-core-mv 'one (values :refused)) :refused))
(multiple-value-bind (word reason)
    (fnn-core-mv 'uncertain (values :uncertain :persistence))
  (assert (and (eq word :uncertain) (eq reason :persistence))))
(assert (eq (fnn-core-mv 'semantic-thrown (values :thrown)) :thrown))
(expect-fault (lambda () (fnn-core-mv 'escape (throw 'raw-ev-fncall :escaped))))
(expect-fault (lambda () (fnn-core-mv 'exception (error "raw failure"))))
(format t "PASS fixed scalar-MV values, identity, semantic status and faults~%")
"""


class ScalarMVTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_bridge_preserves_scalar_values_and_fails_closed(self):
        selected = []
        for form in proof_repl.forms((ROOT / "host/native/io.lisp").read_text()):
            if proof_repl.head_and_name(form)[1] in {
                    "fnn-fixed-raw-callback", "fnn-core-mv",
                    "fnn-fixed-callback-fault", "fnn-fixed-callback-fail"}:
                selected.append(form)
        self.assertEqual(len(selected), 4)
        driver = trap_test.PRELUDE + '(load "' + str(ROOT / "host/native/raw-trap.lisp") + '")\n' + \
            "\n\n".join(selected) + SCALAR_DRIVER
        # The test collects results solely to inspect a zero-value return;
        # the actual bridge source above contains no result-list operation.
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "scalar-mv.lisp"
            path.write_text(driver)
            run = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                                  "--script", str(path)], capture_output=True, text=True, timeout=30)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn("PASS fixed scalar-MV", run.stdout)


if __name__ == "__main__":
    unittest.main()
