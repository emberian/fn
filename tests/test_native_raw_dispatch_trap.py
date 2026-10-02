"""D40 raw dispatch: the image-level trap (host/native/raw-trap.lisp, THE TRAP).

raw-trap.lisp and io.lisp's dispatcher forms run in a bare SBCL: a
raw-dispatched function's binding is replaced by a trap at installation, so
every host call outside the dispatcher faults however it is spelled -- each
of the Codex r34 bypasses of the source scan (tools/raw_dispatch_rule.py) is
a case here -- while a dispatcher call returns exactly what the captured
function returns, on the raw path and on the counterpart path, and ACL2 code
inside a dispatcher call's extent (a raw body compiled before installation, a
*1* counterpart) reaches it unchanged.  The Codex r63 findings are cases too:
no accessor hands out a captured object (F1), the traps install before every
other raw host file in each build script (F2), the extent is a per-call
token, not a flag (F3), a reinstall over a redefinition is refused (F4), and
the self-probe cleans up (F5).
"""
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import proof_repl

# io.lisp's half of the dispatcher; raw-trap.lisp is loaded whole.
SHIPPED = {"fnn-call", "fnn-fixed-raw-callback"}

# The ACL2 world functions fnn-install-raw-dispatch reads, stubbed: the
# fn-interfaces table is *test-interfaces*, a :raw-guarded entry's target is
# looked up in *test-targets*, and every declaration is accepted.
PRELUDE = r"""
(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_*1*_ACL2" (:use))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defvar *test-interfaces* nil)
(defvar *test-targets* nil)
(defun w (state) state)
(defun table-alist (name wrld) (declare (ignore name wrld)) *test-interfaces*)
(defun assoc-keyword (key l) (member key l))
(defun fn-di-raw-guarded-problem (&rest r) (declare (ignore r)) nil)
(defun fn-di-raw-with-problem (&rest r) (declare (ignore r)) nil)
(defun fn-di-raw-guarded-target (name entry wrld)
  (declare (ignore entry wrld)) (values nil (cdr (assoc name *test-targets*))))
(defun symbol-class (name wrld) (declare (ignore name wrld)) :common-lisp-compliant)
(defun getpropc (&rest r) (declare (ignore r)) nil)
(defun fnn-fault (control &rest args)
  (error 'fnn-store-fault :message (apply #'format nil control args)))
"""

DRIVER = r"""
%PRELUDE%
(load "%RAWTRAP%")
%SHIPPED%
(fnn-raw-dispatch-set-hooks (lambda (name args) (declare (ignore name args)) nil)
                            (lambda () t))

(defvar *checks* 0)
(defmacro check (form) `(progn (assert ,form () "failed: ~s" ',form) (incf *checks*)))
(defun msg (c) (fnn-message c))
(defun trapped-p (thunk)
  (handler-case (progn (funcall thunk) nil)
    (fnn-raw-dispatch-trap (c) (search "called outside the dispatcher" (msg c)))))

;; An ACL2 entry FN-SUB (guard-verified, compiled), a raw body FN-USES compiled
;; BEFORE installation that calls it (as another guard-verified function's raw
;; body does), FN-SUB's *1* counterpart, which checks a guard and calls the
;; raw symbol, and an entry FN-OUTER that is not raw-dispatched, whose *1*
;; runs FN-USES (and keeps its call's token, for the F3 cases).
(defun fn-sub (x y) (values (- x y) (list x y)))
(defun fn-uses (x) (multiple-value-list (fn-sub x 1)))
(setf (symbol-function (intern "FN-SUB" "ACL2_*1*_ACL2"))
      (lambda (x y) (assert (and (integerp x) (integerp y))) (fn-sub x y)))
(defvar *stolen* nil)
(setf (symbol-function (intern "FN-OUTER" "ACL2_*1*_ACL2"))
      (lambda (x) (setq *stolen* *fnn-core-token*) (fn-uses x)))
(compile 'fn-sub) (compile 'fn-uses)
(defvar *before* (list (multiple-value-list (fn-sub 7 2)) (multiple-value-list (fn-sub -3 9))))

;; Installation, from the (stubbed) fn-interfaces table.
(setq *test-interfaces* '((fn-sub :raw-with (fn-sub-carries))))
(check (= (fnn-install-raw-dispatch :report nil) 1))
(check (eq (fnn-raw-trap-install 'fn-sub) 'fn-sub))          ; idempotent
(check (= (fnn-raw-dispatch-traps-intact) 1))
(check (equal (fnn-raw-dispatch-names) '(fn-sub)))
(check (eq (fnn-raw-dispatch-target 'fn-sub) 'fn-sub))
(check (eq (fnn-dispatch-symbol 'fn-sub) 'fn-sub))
;; r63-F1: no accessor hands out the captured object.
(check (not (fboundp 'fnn-raw-captured)))
(check (not (boundp '*fnn-raw-captured*)))
(check (not (fboundp 'fnn-dispatch-function)))
(check (not (boundp '*fnn-raw-dispatch*)))
(check (not (boundp '*fnn-in-core*)))

;; Dispatcher calls are unchanged: the raw path applies the captured object.
(check (equal (list (fnn-call 'fn-sub 7 2) (fnn-call 'fn-sub -3 9)) *before*))
(check (fnn-raw-dispatch-captured-p 'fn-sub))
;; ... and the counterpart path (*1* then the trapped symbol, inside the extent).
(let ((*fnn-dispatch-counterpart* t))
  (check (equal (list (fnn-call 'fn-sub 7 2) (fnn-call 'fn-sub -3 9)) *before*))
  (check (not (fnn-raw-dispatch-captured-p 'fn-sub))))
;; ACL2 code inside a dispatcher call's extent reaches the captured function.
(check (equal (fnn-call 'fn-outer 5) '((4 (5 1)))))
(check (equal (fnn-raw-session-extent (lambda () (fn-uses 5))) '(4 (5 1))))
;; A callback the dispatcher hands out runs inside a fresh extent per call.
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
;; r63-F3: the extent is a per-call capability, not a flag.  A token bound by
;; hand grants nothing; a dispatcher's token kept past its call is dead; a
;; live token carried to another thread grants nothing there.
(check (trapped-p (lambda () (let ((*fnn-core-token* (list :fnn-core-token))) (fn-sub 7 2)))))
(check (trapped-p (lambda () (let ((*fnn-core-token* t)) (fn-sub 7 2)))))
(check (consp *stolen*))
(check (trapped-p (lambda () (let ((*fnn-core-token* *stolen*)) (fn-sub 7 2)))))
(setf (symbol-function (intern "FN-THIEF" "ACL2_*1*_ACL2"))
      (lambda ()
        (let ((token *fnn-core-token*) (result nil))
          (sb-thread:join-thread
           (sb-thread:make-thread
            (lambda ()
              (setq result (handler-case (let ((*fnn-core-token* token)) (fn-sub 1 1) :ran)
                             (fnn-raw-dispatch-trap () :trapped))))))
          result)))
(check (equal (fnn-call 'fn-thief) '(:trapped)))
;; r63-F5: the self-probe serves, traps, and leaves nothing behind.
(check (equal (multiple-value-list (fnn-raw-trap-self-probe)) '("served" "trapped" "trapped")))
(check (equal (fnn-raw-dispatch-names) '(fn-sub)))
(check (equal (multiple-value-list (fnn-raw-trap-probe-target 7 2)) '(5 (7 2))))
;; the hooks are set once
(check (handler-case (progn (fnn-raw-dispatch-set-hooks nil nil) nil)
         (fnn-store-fault () t)))

;; r34-F4 / r63-F4: a redefinition after installation replaces the trap; a
;; reinstall refuses to capture the new body, and the intact check (end of
;; build, every start) refuses it.
(defun fn-sub (x y) (values (+ x y) nil))
(check (handler-case (progn (fnn-raw-trap-install 'fn-sub) nil)
         (fnn-store-fault (c) (search "redefined after its trap" (msg c)))))
(check (handler-case (progn (fnn-raw-dispatch-traps-intact) nil)
         (fnn-store-fault (c) (search "no longer trapped" (msg c)))))
(check (handler-case (progn (fnn-install-raw-dispatch :report nil) nil)
         (fnn-store-fault (c) (search "redefined after its trap" (msg c)))))
(format t "PASS raw-dispatch trap: ~d checks~%" *checks*)
"""


def shipped_forms(names):
    selected = {}
    for form in proof_repl.forms((ROOT / "host/native/io.lisp").read_text()):
        name = proof_repl.head_and_name(form)[1]
        if name in names:
            selected[name] = form
    return selected


def run_sbcl(text, name):
    with tempfile.TemporaryDirectory() as directory:
        unscanned = Path(directory) / "unscanned.lisp"
        unscanned.write_text('(in-package "ACL2")\n(fn-sub 7 2)\n')
        path = Path(directory) / name
        path.write_text(text.replace("%UNSCANNED%", str(unscanned)))
        return subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                               "--script", str(path)], capture_output=True, text=True,
                              timeout=60)


class RawDispatchTrapTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_trap_faults_outside_and_serves_inside(self):
        selected = shipped_forms(SHIPPED)
        self.assertEqual(set(selected), SHIPPED)
        run = run_sbcl(DRIVER.replace("%PRELUDE%", PRELUDE)
                       .replace("%RAWTRAP%", str(ROOT / "host/native/raw-trap.lisp"))
                       .replace("%SHIPPED%", "\n\n".join(selected.values())), "trap.lisp")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("PASS raw-dispatch trap", run.stdout)

    def test_traps_install_before_every_other_raw_host_file(self):
        """r63-F2: each build script loads raw-trap.lisp and installs the
        traps before it loads any other raw host file."""
        for script in ("build.lisp", "build-dtn.lisp", "build-store-test.lisp"):
            text = (ROOT / "host/native" / script).read_text()
            loads = re.findall(r'\(load "host/native/([^"]+)"\)', text)
            self.assertEqual(loads[0], "raw-trap.lisp", script)
            first = text.index('(load "host/native/raw-trap.lisp")')
            install = text.index("(fnn-install-raw-dispatch)")
            second = text.index('(load "host/native/' + loads[1] + '")')
            self.assertLess(first, install, script)
            self.assertLess(install, second, script)
            self.assertEqual(text.count("(fnn-install-raw-dispatch)"), 1, script)


if __name__ == "__main__":
    unittest.main()
