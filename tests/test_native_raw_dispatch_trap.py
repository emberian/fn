"""D40 raw dispatch: the image-level trap (host/native/io.lisp, THE TRAP).

The shipped definitions are read out of io.lisp and run in a bare SBCL: a
raw-dispatched function's binding is replaced by a trap at installation, so
every host call outside the dispatcher faults however it is spelled -- each
of the Codex r34 bypasses of the source scan (tools/raw_dispatch_rule.py) is
a case here -- while a dispatcher call returns exactly what the captured
function returns, on the raw path and on the counterpart path, and ACL2 code
inside the dispatcher's extent (a raw body compiled before installation, a
*1* counterpart) reaches it unchanged.
"""
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import proof_repl

SHIPPED = {
    "*fnn-raw-dispatch*", "*fnn-dispatch-counterpart*", "fnn-raw-dispatch-trap",
    "*fnn-in-core*", "*fnn-raw-captured*", "*fnn-raw-traps*", "fnn-raw-trap-for",
    "fnn-raw-trap-install", "fnn-raw-dispatch-traps-intact", "fnn-raw-captured",
    "fnn-dispatch-function", "fnn-counterpart", "fnn-call", "fnn-fixed-raw-callback",
}

DRIVER = r'''
(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_*1*_ACL2" (:use))
(in-package "ACL2")
(define-condition fnn-store-error (error) ((message :initarg :message :reader msg)))
(define-condition fnn-store-fault (fnn-store-error) ())
(defun fnn-fault (control &rest args)
  (error 'fnn-store-fault :message (apply #'format nil control args)))
(defun fnn-entry-guard (name args) (declare (ignore name args)) nil)
%SHIPPED%

(defvar *checks* 0)
(defmacro check (form) `(progn (assert ,form () "failed: ~s" ',form) (incf *checks*)))
(defun trapped-p (thunk)
  (handler-case (progn (funcall thunk) nil)
    (fnn-raw-dispatch-trap (c) (search "called outside the dispatcher" (msg c)))))

;; An ACL2 entry FN-SUB (guard-verified, compiled), a raw body FN-USES compiled
;; BEFORE installation that calls it (as another guard-verified function's raw
;; body does), and FN-SUB's *1* counterpart, which checks a guard and calls
;; the raw symbol.
(defun fn-sub (x y) (values (- x y) (list x y)))
(defun fn-uses (x) (multiple-value-list (fn-sub x 1)))
(setf (symbol-function (intern "FN-SUB" "ACL2_*1*_ACL2"))
      (lambda (x y) (assert (and (integerp x) (integerp y))) (fn-sub x y)))
(compile 'fn-sub) (compile 'fn-uses)
(defvar *before* (list (multiple-value-list (fn-sub 7 2)) (multiple-value-list (fn-sub -3 9))))

;; Installation, as fnn-install-raw-dispatch does for each accepted entry.
(setf (gethash 'fn-sub *fnn-raw-dispatch*) 'fn-sub)
(fnn-raw-trap-install 'fn-sub)
(check (eq (fnn-raw-trap-install 'fn-sub) 'fn-sub))          ; idempotent
(check (eq (gethash 'fn-sub *fnn-raw-captured*)
           (fnn-raw-captured 'fn-sub)))
(check (not (eq (symbol-function 'fn-sub) (fnn-raw-captured 'fn-sub))))
(check (= (fnn-raw-dispatch-traps-intact) 1))

;; Dispatcher calls are unchanged: the raw path applies the captured object.
(check (equal (list (fnn-call 'fn-sub 7 2) (fnn-call 'fn-sub -3 9)) *before*))
(check (eq (fnn-dispatch-function 'fn-sub) (fnn-raw-captured 'fn-sub)))
;; ... and the counterpart path (*1* then the trapped symbol, inside the extent).
(let ((*fnn-dispatch-counterpart* t))
  (check (equal (list (fnn-call 'fn-sub 7 2) (fnn-call 'fn-sub -3 9)) *before*)))
;; ACL2 code inside the extent reaches the captured function.
(check (equal (let ((*fnn-in-core* t)) (fn-uses 5)) '(4 (5 1))))
;; A callback the dispatcher hands out runs inside the extent.
(check (equal (multiple-value-list (funcall (fnn-fixed-raw-callback 'fn-sub) 7 2))
              (first *before*)))

;; Every host call outside the dispatcher faults, however spelled.
(check (trapped-p (lambda () (fn-sub 7 2))))                                 ; literal call
(check (trapped-p (lambda () (fn-uses 5))))                                  ; compiled before install
(check (trapped-p (lambda () (funcall 'fn-sub 7 2))))
(check (trapped-p (lambda () (apply #'fn-sub '(7 2)))))
(check (trapped-p (lambda () (funcall (symbol-function 'fn-sub) 7 2))))
(check (trapped-p (lambda () (mapcar #'fn-sub '(7) '(2)))))
;; r34-F2: package-qualified names built at run time
(check (trapped-p (lambda () (cl:funcall (cl:intern "FN-SUB" "ACL2") 7 2))))
(check (trapped-p (lambda () (funcall (find-symbol "FN-SUB" "ACL2") 7 2))))
;; r34-F3: a defconstant initializer evaluated after installation
(check (trapped-p (lambda () (eval '(defconstant +fn-sub-const+ (fn-sub 7 2))))))
;; r34-F5: a macro arm whose expansion calls it
(defmacro via-macro (x) `(fn-sub ,x 1))
(check (trapped-p (lambda () (eval '(via-macro 3)))))
;; r34-F7: a form read with the reader
(check (trapped-p (lambda () (eval (read-from-string "(fn-sub 7 2)")))))
;; r34-F1: a file the scanner never sees, loaded after installation
(check (trapped-p (lambda () (load "%UNSCANNED%"))))
;; a hand-built thread outside the extent
(check (trapped-p (lambda ()
                    (let ((result nil))
                      (sb-thread:join-thread
                       (sb-thread:make-thread
                        (lambda () (setq result (handler-case (progn (fn-sub 1 1) :ran)
                                                  (fnn-raw-dispatch-trap () :trapped))))))
                      (when (eq result :trapped)
                        (error 'fnn-raw-dispatch-trap :message "called outside the dispatcher"))))))

;; r34-F4: a redefinition after installation replaces the trap; the intact
;; check (end of build, every start) refuses it.
(defun fn-sub (x y) (values (+ x y) nil))
(check (handler-case (progn (fnn-raw-dispatch-traps-intact) nil)
         (fnn-store-fault (c) (search "no longer trapped" (msg c)))))
(format t "PASS raw-dispatch trap: ~d checks~%" *checks*)
'''


class RawDispatchTrapTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_trap_faults_outside_and_serves_inside(self):
        selected = {}
        for form in proof_repl.forms((ROOT / "host/native/io.lisp").read_text()):
            name = proof_repl.head_and_name(form)[1]
            if name in SHIPPED:
                selected[name] = form
        self.assertEqual(set(selected), SHIPPED)
        with tempfile.TemporaryDirectory() as directory:
            unscanned = Path(directory) / "unscanned.lisp"
            unscanned.write_text('(in-package "ACL2")\n(fn-sub 7 2)\n')
            path = Path(directory) / "trap.lisp"
            path.write_text(DRIVER.replace("%SHIPPED%", "\n\n".join(selected.values()))
                            .replace("%UNSCANNED%", str(unscanned)))
            run = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                                  "--script", str(path)], capture_output=True, text=True, timeout=60)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn("PASS raw-dispatch trap", run.stdout)


if __name__ == "__main__":
    unittest.main()
