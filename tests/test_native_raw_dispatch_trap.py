"""D40 raw dispatch: the image-level trap (host/native/raw-trap.lisp).

raw-trap.lisp and io.lisp's dispatcher forms run in a bare SBCL.  A
raw-dispatched function's binding is replaced by a trap at installation, so
every host call outside a dispatcher extent faults however it is spelled --
each Codex r34 bypass of the source scan (tools/raw_dispatch_rule.py) is a
case here -- while a dispatcher call returns exactly what the captured
function returns, on the raw path and the counterpart path, and ACL2 code
inside an extent (a raw body compiled before installation, a *1*
counterpart) reaches it unchanged.

The extent is a per-thread slot (an uninterned special bound by the
dispatcher), so the cases also pin what replaced the 10-02 token table: a
same-named symbol bound by hand grants nothing, nothing kept past a call
grants anything, a thread started inside an extent is outside it, and a
dispatcher call and a callback call allocate nothing beyond what the entry
itself allocates (Codex r69 L1: the token table cost a synchronized
hash-table write and remhash per fnn-call).  The Codex r63/r69 findings are
cases too: no accessor hands out a captured object (r63 F1), the traps
install before every other raw host file in each build script (r63 F2), a
reinstall over a redefinition is refused (r63 F4), the self-probe cleans up
(r63 F5), the entry guard's fault keeps its class through fnn-call (r69
F1), io.lisp's conditions stay in io.lisp (r69 F2), the session extent is
decided by the seal and not by a rebindable variable (r69 F4), and each
escape the claim names has a case (r69 F5).
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

# io.lisp's half of the dispatcher and the conditions it signals.
SHIPPED = {"fnn-store-error", "fnn-store-fault", "fnn-entry-guard-fault", "fnn-fault",
           "fnn-counterpart", "fnn-call", "fnn-fixed-raw-callback"}

# The ACL2 world functions fnn-install-raw-dispatch reads, stubbed: the
# fn-interfaces table is *test-interfaces*, formals come from *test-formals*,
# a :raw-guarded entry's target from *test-targets*, and every declaration is
# accepted.  fnn-entry-guard refuses the one name FN-REFUSED.
PRELUDE = r"""
(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_*1*_ACL2" (:use))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defvar *test-interfaces* nil)
(defvar *test-targets* nil)
(defvar *test-formals* nil)
(defun w (state) state)
(defun table-alist (name wrld) (declare (ignore name wrld)) *test-interfaces*)
(defun assoc-keyword (key l) (member key l))
(defun fn-di-raw-guarded-problem (&rest r) (declare (ignore r)) nil)
(defun fn-di-raw-with-problem (&rest r) (declare (ignore r)) nil)
(defun fn-di-raw-creatorp (name entry wrld)
  (declare (ignore entry wrld)) (assoc name *test-targets*))
(defun fn-di-raw-guarded-target (name entry wrld)
  (declare (ignore entry wrld)) (values nil (cdr (assoc name *test-targets*))))
(defun symbol-class (name wrld) (declare (ignore name wrld)) :common-lisp-compliant)
(defun getpropc (name key default wrld)
  (declare (ignore wrld))
  (if (eq key 'formals)
      (let ((hit (assoc name *test-formals*))) (if hit (cdr hit) default))
    default))
"""

DRIVER = r"""
%PRELUDE%
(load "%RAWTRAP%")
%SHIPPED%
(defun fnn-entry-guard (name args)
  (declare (ignore args))
  (when (eq name 'fn-refused)
    (error 'fnn-entry-guard-fault :message "host-entry-guard: fn-refused argument 1")))

(defvar *checks* 0)
(defmacro check (form) `(progn (assert ,form () "failed: ~s" ',form) (incf *checks*)))
(defun trapped-p (thunk)
  (handler-case (progn (funcall thunk) nil)
    (fnn-raw-dispatch-trap (c) (search "called outside the dispatcher" (princ-to-string c)))))

;; An ACL2 entry FN-SUB (guard-verified, compiled), a raw body FN-USES
;; compiled BEFORE installation that calls it (as another guard-verified
;; function's raw body does), FN-SUB's *1* counterpart, which checks a guard
;; and calls the raw symbol, an entry FN-OUTER that is not raw-dispatched,
;; whose *1* runs FN-USES, a creator, and an entry with more formals than the
;; fixed-arity bound.
(defun fn-sub (x y) (values (- x y) (list x y)))
(defun fn-uses (x) (multiple-value-list (fn-sub x 1)))
(defun create-fn-thing () (vector :thing))
(defun fn-wide (a b c d e f g h i j k l m n o p q) (list a b c d e f g h i j k l m n o p q))
(defun fn-refused (x) x)
(setf (symbol-function (intern "FN-SUB" "ACL2_*1*_ACL2"))
      (lambda (x y) (assert (and (integerp x) (integerp y))) (fn-sub x y)))
(defvar *kept* nil)
(setf (symbol-function (intern "FN-OUTER" "ACL2_*1*_ACL2"))
      (lambda (x) (setq *kept* (lambda () (fn-sub 7 2))) (fn-uses x)))
(compile 'fn-sub) (compile 'fn-uses) (compile 'create-fn-thing) (compile 'fn-wide)
(compile 'fn-refused)
(defvar *before* (list (multiple-value-list (fn-sub 7 2)) (multiple-value-list (fn-sub -3 9))))

;; Installation, from the (stubbed) fn-interfaces table.
(setq *test-formals* '((fn-sub x y) (create-fn-thing)
                       (fn-wide a b c d e f g h i j k l m n o p q) (fn-refused x)))
(setq *test-targets* '((create-fn-thing . create-fn-thing)))
(setq *test-interfaces* '((fn-sub :raw-with (fn-sub-carries))
                          (create-fn-thing :raw-guarded (0 nil (fn-thing)))
                          (fn-wide :raw-with (fn-wide-carries))
                          (fn-refused :raw-with (fn-refused-carries))))
(check (= (fnn-install-raw-dispatch :report nil) 4))
(check (= (fnn-install-raw-dispatch :report nil) 4))                ; idempotent before the seal
(check (equal (fnn-raw-dispatch-names) '(create-fn-thing fn-refused fn-sub fn-wide)))
(check (eq (fnn-raw-dispatch-target 'fn-sub) 'fn-sub))
(check (eq (fnn-dispatch-symbol 'fn-sub) 'fn-sub))
(check (= (fnn-raw-dispatch-arity 'fn-sub) 2))
(check (= (fnn-raw-dispatch-arity 'fn-wide) 17))
(check (fnn-raw-dispatch-creator-p 'create-fn-thing))
;; never sealed: the intact check refuses
(check (handler-case (progn (fnn-raw-dispatch-traps-intact) nil)
         (fnn-raw-dispatch-trap (c) (search "never sealed" (princ-to-string c)))))
;; before the seal no ACL2 session extent exists
(check (handler-case (progn (fnn-raw-session-extent (lambda () t)) nil)
         (fnn-raw-dispatch-trap (c) (search "developer-only" (princ-to-string c)))))
(check (= (fnn-raw-trap-seal :developer t) 4))
(check (= (fnn-raw-dispatch-traps-intact) 4))
(check (handler-case (progn (fnn-raw-trap-seal) nil) (fnn-raw-dispatch-trap () t)))
(check (handler-case (progn (fnn-install-raw-dispatch :report nil) nil)
         (fnn-raw-dispatch-trap (c) (search "sealed" (princ-to-string c)))))
(check (handler-case (progn (fnn-raw-trap-install 'fn-x 'fn-uses) nil)
         (fnn-raw-dispatch-trap (c) (search "sealed" (princ-to-string c)))))
;; r63-F1: no accessor hands out a captured object, and the old tables are gone.
(dolist (name '(fnn-raw-captured fnn-dispatch-function fnn-raw-dispatch-set-hooks))
  (check (not (fboundp name))))
(dolist (name '(*fnn-raw-captured* *fnn-raw-dispatch* *fnn-startup-creators*
                *fnn-core-token* *fnn-in-core*))
  (check (not (boundp name))))
(check (null (find-symbol "FNN-RAW-EXTENT" "ACL2")))

;; Dispatcher calls are unchanged: the raw path applies the captured object.
(check (equal (list (fnn-call 'fn-sub 7 2) (fnn-call 'fn-sub -3 9)) *before*))
(check (fnn-raw-dispatch-captured-p 'fn-sub))
(check (equalp (fnn-call 'create-fn-thing) '(#(:thing))))
(check (equal (fnn-call 'fn-wide 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17)
              '((1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17))))
;; ... and the counterpart path (*1* then the trapped symbol, inside the
;; extent); a startup creator stays raw in either mode.
(let ((*fnn-dispatch-counterpart* t))
  (check (equal (list (fnn-call 'fn-sub 7 2) (fnn-call 'fn-sub -3 9)) *before*))
  (check (not (fnn-raw-dispatch-captured-p 'fn-sub)))
  (check (fnn-raw-dispatch-captured-p 'create-fn-thing))
  (check (handler-case (progn (fnn-fixed-raw-callback 'fn-sub) nil) (fnn-store-fault () t))))
;; ACL2 code inside a dispatcher call's extent reaches the captured function.
(check (equal (fnn-call 'fn-outer 5) '((4 (5 1)))))
(check (equal (fnn-raw-session-extent (lambda () (fn-uses 5))) '(4 (5 1))))
;; A fixed callback enters an extent itself, keeps the values, and is the
;; same object every time (selected once at startup, compared by identity).
(let ((callback (fnn-fixed-raw-callback 'fn-sub)))
  (check (compiled-function-p callback))
  (check (eq callback (fnn-fixed-raw-callback 'fn-sub)))
  (check (equal (multiple-value-list (funcall callback 7 2)) (first *before*))))
(check (handler-case (progn (fnn-fixed-raw-callback 'fn-not-raw) nil) (fnn-store-fault () t)))
;; r69-F1: the entry guard's fault reaches the caller as itself, unwrapped.
(check (handler-case (progn (fnn-call 'fn-refused 1) nil)
         (fnn-entry-guard-fault (c) (search "host-entry-guard" (fnn-message c)))))

;; r69-L1: no allocation per call beyond the entry's own.  A callback call
;; and a trapped inner call cons what the same body conses called plainly.
(defun consed (thunk)
  (funcall thunk)
  (let ((before (sb-ext:get-bytes-consed)))
    (funcall thunk)
    (- (sb-ext:get-bytes-consed) before)))
(defun fn-sub-plain (x y) (values (- x y) (list x y)))
(compile 'fn-sub-plain)
(let* ((sub (fnn-fixed-raw-callback 'fn-sub))
       (plain (consed (lambda () (dotimes (i 100000) (fn-sub-plain 7 2)))))
       (via-callback (consed (lambda () (dotimes (i 100000) (funcall sub 7 2)))))
       (trapped-inner (consed (lambda ()
                                (fnn-raw-session-extent
                                 (lambda () (dotimes (i 100000) (fn-sub 7 2))))))))
  (format t "consed per 100k: plain ~d callback ~d trapped-inner ~d~%"
          plain via-callback trapped-inner)
  (check (> plain 0))
  (check (<= via-callback (+ plain 4096)))
  (check (<= trapped-inner (+ plain 4096))))

;; Every host call outside an extent faults, however spelled.
(check (trapped-p (lambda () (fn-sub 7 2))))                                 ; literal call
(check (trapped-p (lambda () (fn-uses 5))))                                  ; compiled before install
(check (trapped-p (lambda () (funcall 'fn-sub 7 2))))
(check (trapped-p (lambda () (apply #'fn-sub '(7 2)))))
(check (trapped-p (lambda () (funcall (symbol-function 'fn-sub) 7 2))))
(check (trapped-p (lambda () (funcall (fdefinition 'fn-sub) 7 2))))
(check (trapped-p (lambda () (mapcar #'fn-sub '(7) '(2)))))
(check (trapped-p (lambda () (create-fn-thing))))
(check (trapped-p (lambda () (fn-wide 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17))))
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
;; The per-thread slot.  A same-named symbol bound by hand grants nothing;
;; a closure made inside an extent and called after it is outside; a thread
;; started inside an extent is outside it.
(check (trapped-p (lambda () (progv (list (make-symbol "FNN-RAW-EXTENT")) (list t) (fn-sub 7 2)))))
(check (functionp *kept*))
(check (trapped-p *kept*))
(setf (symbol-function (intern "FN-THIEF" "ACL2_*1*_ACL2"))
      (lambda ()
        (let ((result nil))
          (sb-thread:join-thread
           (sb-thread:make-thread
            (lambda ()
              (setq result (handler-case (progn (fn-sub 1 1) :ran)
                             (fnn-raw-dispatch-trap () :trapped))))))
          result)))
(check (equal (fnn-call 'fn-thief) '(:trapped)))
;; Two threads in and out of extents at once: each sees only its own.
(let* ((stop nil) (outside-ran 0) (inside-trapped 0)
       (inside (sb-thread:make-thread
                (lambda () (loop until stop
                                 do (handler-case (fnn-call 'fn-sub 7 2)
                                      (serious-condition () (incf inside-trapped)))))))
       (outside (sb-thread:make-thread
                 (lambda () (loop until stop
                                  do (handler-case (progn (fn-sub 7 2) (incf outside-ran))
                                       (fnn-raw-dispatch-trap () nil)))))))
  (sleep 0.3)
  (setq stop t)
  (sb-thread:join-thread inside) (sb-thread:join-thread outside)
  (check (= outside-ran 0))
  (check (= inside-trapped 0)))
;; r63-F5: the self-probe serves, traps, and leaves nothing behind.
(check (equal (multiple-value-list (fnn-raw-trap-self-probe))
              '("served" "served" "trapped" "trapped" "trapped" "trapped")))
(check (equal (fnn-raw-dispatch-names) '(create-fn-thing fn-refused fn-sub fn-wide)))
(check (equal (multiple-value-list (fnn-raw-trap-probe-target 7 2)) '(5 (7 2))))
(check (null (fnn-raw-dispatch-callback 'fnn-raw-trap-probe)))

;; r34-F4 / r63-F4: a redefinition after installation replaces the trap; the
;; intact check (end of build, every start) refuses it.
(defun fn-sub (x y) (values (+ x y) nil))
(check (handler-case (progn (fnn-raw-dispatch-traps-intact) nil)
         (fnn-raw-dispatch-trap (c) (search "no longer trapped" (princ-to-string c)))))
(format t "PASS raw-dispatch trap: ~d checks~%" *checks*)
"""

# Before the seal: a reinstall over a redefinition is refused (r63 F4), and a
# production seal gives no session extent however the profile variable is
# bound afterwards (r69 F4).
DRIVER_UNSEALED = r"""
%PRELUDE%
(load "%RAWTRAP%")
%SHIPPED%
(defun fnn-entry-guard (name args) (declare (ignore name args)) nil)
(defvar *checks* 0)
(defmacro check (form) `(progn (assert ,form () "failed: ~s" ',form) (incf *checks*)))
(defun fn-sub (x y) (- x y))
(compile 'fn-sub)
(setq *test-formals* '((fn-sub x y)))
(setq *test-interfaces* '((fn-sub :raw-with (fn-sub-carries))))
(check (= (fnn-install-raw-dispatch :report nil) 1))
(defun fn-sub (x y) (+ x y))
(check (handler-case (progn (fnn-install-raw-dispatch :report nil) nil)
         (fnn-raw-dispatch-trap (c) (search "redefined after its trap" (princ-to-string c)))))
(check (handler-case (progn (fnn-raw-trap-install 'fn-sub 'fn-sub) nil)
         (fnn-raw-dispatch-trap (c) (search "redefined after its trap" (princ-to-string c)))))
(defvar *fnn-image-profile* :production)
(check (integerp (fnn-raw-trap-seal :developer nil)))   ; the refused install left the table empty
(let ((*fnn-image-profile* :developer))
  (check (handler-case (progn (fnn-raw-session-extent (lambda () t)) nil)
           (fnn-raw-dispatch-trap (c) (search "developer-only" (princ-to-string c))))))
(format t "PASS raw-dispatch unsealed: ~d checks~%" *checks*)
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
                              timeout=120)


def driver(template):
    selected = shipped_forms(SHIPPED)
    assert set(selected) == SHIPPED, SHIPPED - set(selected)
    return (template.replace("%PRELUDE%", PRELUDE)
            .replace("%RAWTRAP%", str(ROOT / "host/native/raw-trap.lisp"))
            .replace("%SHIPPED%", "\n\n".join(selected.values())))


class RawDispatchTrapTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_trap_faults_outside_and_serves_inside(self):
        run = run_sbcl(driver(DRIVER), "trap.lisp")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("PASS raw-dispatch trap", run.stdout)

    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_redefinition_and_production_seal(self):
        run = run_sbcl(driver(DRIVER_UNSEALED), "unsealed.lisp")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("PASS raw-dispatch unsealed", run.stdout)

    def test_traps_install_before_every_other_raw_host_file(self):
        """r63-F2: each build script loads raw-trap.lisp and installs the
        traps before it loads any other raw host file, seals after the
        profile is selected, and checks the traps at the end of its raw
        block."""
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
            profile = text.index("(fnn-select-image-profile")
            seal = text.index("(fnn-raw-trap-seal :developer (fnn-developer-image-p))")
            self.assertLess(profile, seal, script)
            intact = text.index("(fnn-raw-dispatch-traps-intact)")
            banner = text.index("(setq *print-startup-banner* nil))")
            block = text[first:banner]
            last = block.rindex('(load "host/native/') + first
            self.assertLess(last, intact, script)
            self.assertLess(intact, banner, script)

    def test_io_keeps_its_conditions(self):
        """r69-F2: raw-trap.lisp defines only its own condition."""
        text = (ROOT / "host/native/raw-trap.lisp").read_text()
        self.assertEqual(re.findall(r"\(define-condition (\S+)", text),
                         ["fnn-raw-dispatch-trap"])


if __name__ == "__main__":
    unittest.main()
