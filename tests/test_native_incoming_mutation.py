"""Actual incoming mutation gates with core decisions and recording storage.

The pool's slot accessor and physical reserve are test doubles. The holder
decision and native mutation/dispatch bodies are extracted from source.
This does not qualify allocation costs or the scheduler that catches busy.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import proof_repl


def selected(path, names):
    forms = {proof_repl.head_and_name(f)[1]: f for f in proof_repl.forms(path.read_text())}
    return [forms[name] for name in names]


class IncomingMutationTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_gate_ownership_failure_and_atomic_interleaving(self):
        core = Path(os.environ.get("FN_INCOMING_CORE_TREE", ROOT))
        core_forms = []
        for relative, names in [
            ("books/page-read-ledger.lisp", ["fn-prl-nth"]),
            ("books/incoming-octet-holder.lisp", ["fn-ioh-tokenp", "fn-ioh-matches", "fn-ioh-access"]),
            ("books/incoming-buffer-carrier-shape.lisp", ["fn-ibc-carrier-row"]),
            ("host/page-read-host.lisp", ["fn-owner-incoming-row", "fn-owner-incoming-mutation-allowedp"]),
        ]:
            core_forms.extend(selected(core / relative, names))
        # Only top-level XARGS declarations are removed; bodies are literal.
        pure = []
        for form in core_forms:
            start = form.index("(declare")
            declaration = proof_repl.forms(form[start:])[0]
            pure.append(form[:start] + form[start + len(declaration):])
        names = ["fnn-fixed-raw-callback", "fnn-core-mv", "fnn-incoming-buffer-busy",
                 "fnn-with-incoming-mutation", "fnn-live-octets", "fnn-octets-fill",
                 "fnn-octets-clear", "fnn-octets-reserve", "fnn-octets-append-vector",
                 "fnn-octets-release", "fnn-incoming-mutation-start",
                 "fnn-incoming-generic-mutation-allowedp"]
        native = selected(ROOT / "host/native/io.lisp", names)
        header = r'''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(deftype fnn-octets () '(simple-array (unsigned-byte 8) (*)))
(defun natp (x) (and (integerp x) (>= x 0)))
(defun zp (x) (not (and (integerp x) (> x 0))))
(defun member-eq (x xs) (member x xs :test #'eq))
(defun member-equal (x xs) (member x xs :test #'equal))
(define-condition fnn-store-fault (error) ((message :initarg :message)))
(defun fnn-fault (fmt &rest args)
 (error 'fnn-store-fault :message (apply #'format nil fmt args)))
(defvar *fnn-raw-dispatch* (make-hash-table :test #'eq))
(defvar *fnn-dispatch-counterpart* nil)
(defvar *fnn-incoming-mutation-callback* nil)
(defvar *fnn-extent-lock* (sb-thread:make-mutex))
(defvar *fnn-octets* nil)
(defvar *the-live-state* nil)
(defun user-stobj-alist (state) (declare (ignore state)) (error "unexpected uncached buffer"))
(defvar *pool* (vector nil nil (list '(:input-backing 7 8) nil)))
(defun fnn-live-page-read-pool () *pool*)
(defun fn-prp-incoming-slot (pool) (svref pool 2))
(defun set-row (row) (setf (second (svref *pool* 2)) row))
(defvar *reserve-count* 0)
(defvar *mutation-lock-seen* nil)
(defun fn-octets$c-reserve (n st)
 (assert (sb-thread:holding-mutex-p *fnn-extent-lock*))
 (setf *mutation-lock-seen* t)
 (incf *reserve-count*)
 (when (> n (length (svref st 0)))
  (let ((v (make-array n :element-type '(unsigned-byte 8) :initial-element 0)))
   (replace v (svref st 0)) (setf (svref st 0) v)))
 st)
(defun bytes (&rest xs)
 (make-array (length xs) :element-type '(unsigned-byte 8) :initial-contents xs))
(defun fresh () (setf *fnn-octets* (vector (bytes 10 11 12 13 14 15 16 17) 3)
                     *reserve-count* 0 *mutation-lock-seen* nil))
'''
        driver = r'''
(setf (gethash 'fn-owner-incoming-mutation-allowedp *fnn-raw-dispatch*)
      'fn-owner-incoming-mutation-allowedp)
(fnn-incoming-mutation-start)
(defvar *cases* 0)
(defun busy (thunk operation)
 (let ((backing (svref *fnn-octets* 0)) (old (copy-seq (svref *fnn-octets* 0)))
       (fill (svref *fnn-octets* 1)) (reserve *reserve-count*) (continued nil))
  (assert (handler-case (progn (funcall thunk) (setf continued t) nil)
            (fnn-incoming-buffer-busy (c)
             (assert (not (typep c 'error)))
             (assert (not (typep c 'fnn-store-fault)))
             (eq (fnn-incoming-buffer-busy-operation c) operation))))
  (assert (not continued))
  (assert (and (eq backing (svref *fnn-octets* 0))
               (equalp old (svref *fnn-octets* 0)) (= fill (svref *fnn-octets* 1))
               (= reserve *reserve-count*)))
  (incf *cases*)))
(defun mutations (token)
 (list (cons :fill (lambda () (fnn-octets-fill (bytes 1 2) token)))
       (cons :clear (lambda () (fnn-octets-clear token)))
       (cons :reserve (lambda () (fnn-octets-reserve 32 token)))
       (cons :append (lambda () (fnn-octets-append-vector (bytes 4 5) token)))
       (cons :release (lambda () (fnn-octets-release token)))))
; Actual core decisions: absent token, stale token, sealed/cancelled, copy
; job and backing job. Even the correct token cannot bypass a held job.
(dolist (row '(((:incoming 1) :setup (16 0 0 0 1))
               ((:incoming 1) :readonly (16 0 0 0 1))
               ((:incoming 1) :cancelled (16 0 0 0 1))
               ((:incoming 1) :setup (16 0 0 0 1) (:incoming-copy :job))
               ((:incoming 1) :setup (16 0 0 0 1) (:input-backing :job))))
 (set-row row)
 (dolist (token '(nil (:incoming 2)))
  (dolist (op (mutations token)) (fresh) (busy (cdr op) (car op)))))
(dolist (row '(((:incoming 1) :readonly (16 0 0 0 1))
               ((:incoming 1) :cancelled (16 0 0 0 1))
               ((:incoming 1) :setup (16 0 0 0 1) (:incoming-copy :job))
               ((:incoming 1) :setup (16 0 0 0 1) (:input-backing :job))))
 (set-row row)
 (dolist (op (mutations '(:incoming 1))) (fresh) (busy (cdr op) (car op))))
(set-row nil)
(dolist (op (mutations '(:incoming 1))) (fresh) (busy (cdr op) (car op)))
; Both allowed cases preserve the preexisting return conventions and effects.
(dolist (token '(nil (:incoming 1)))
 (set-row (and token (list token :setup '(16 0 0 0 1))))
 (fresh)
 (assert (eq (fnn-octets-fill (bytes 1 2) token) *fnn-octets*))
 (assert (= (svref *fnn-octets* 1) 2))
 (assert (= (fnn-octets-append-vector (bytes 3 4) token) 2))
 (assert (equalp (subseq (svref *fnn-octets* 0) 0 4) (bytes 1 2 3 4)))
 (assert (eq (fnn-octets-reserve 32 token) *fnn-octets*))
 (assert (= (svref *fnn-octets* 1) 4))
 (assert (zerop (fnn-octets-clear token)))
 (assert (eq (fnn-octets-release token) *fnn-octets*))
 (assert (zerop (length (svref *fnn-octets* 0)))) (incf *cases*))
; Missing callback, thrown raw evaluation and execution error remain faults,
; before any physical mutation; they never become semantic busy.
(dolist (callback (list nil (compile nil '(lambda (token pool)
                  (declare (ignore token pool)) (throw 'raw-ev-fncall :escaped)))
                       (compile nil '(lambda (token pool)
                  (declare (ignore token pool)) (error "callback failure")))))
 (fresh)
 (let ((*fnn-incoming-mutation-callback* callback))
  (assert (handler-case (progn (fnn-octets-fill (bytes 1)) nil)
            (fnn-store-fault () t)))
  (assert (= *reserve-count* 0))
  (assert (equalp (svref *fnn-octets* 0) (bytes 10 11 12 13 14 15 16 17))))
 (incf *cases*))
; Recursive entry is necessary when the caller already owns the pool mutex.
(set-row nil) (fresh)
(sb-thread:with-mutex (*fnn-extent-lock*) (fnn-octets-fill (bytes 21)))
(assert *mutation-lock-seen*) (incf *cases*)
; A new live pool is read at the mutation, not cached with the callback.
(fresh)
(let ((*pool* (vector nil nil
                (list '(:input-backing 8 8) '((:incoming 8) :readonly (16 0 0 0 1))))))
 (busy (lambda () (fnn-octets-clear)) :clear))
; Failed startup selection clears the earlier callback before refusing.
(let ((*fnn-dispatch-counterpart* t))
 (assert (handler-case (progn (fnn-incoming-mutation-start) nil)
           (fnn-store-fault () t))))
(assert (null *fnn-incoming-mutation-callback*))
(fnn-incoming-mutation-start) (incf *cases*)
; Real thread schedule: another holder cannot be installed between the core
; permission and the actual write. No owner mutex is acquired by this gate.
(set-row nil) (fresh)
(let* ((checked (sb-thread:make-semaphore)) (proceed (sb-thread:make-semaphore))
       (attempted (sb-thread:make-semaphore)) (installed (sb-thread:make-semaphore))
       (result nil) (worker-error nil)
       (callback *fnn-incoming-mutation-callback*)
       (worker (sb-thread:make-thread
        (lambda ()
         (handler-case
          (let ((*fnn-incoming-mutation-callback*
                  (lambda (token pool)
                   (multiple-value-prog1 (funcall callback token pool)
                    (sb-thread:signal-semaphore checked)
                    (assert (sb-thread:wait-on-semaphore proceed :timeout 5))))))
           (setf result (fnn-octets-fill (bytes 41 42))))
          (serious-condition (c) (setf worker-error c)))))))
 (assert (sb-thread:wait-on-semaphore checked :timeout 5))
 (let ((holder (sb-thread:make-thread
        (lambda () (sb-thread:signal-semaphore attempted)
         (sb-thread:with-mutex (*fnn-extent-lock*)
          (assert (equalp (subseq (svref *fnn-octets* 0) 0 2) (bytes 41 42)))
          (set-row '((:incoming 9) :readonly (16 0 0 0 1)))
          (sb-thread:signal-semaphore installed))))))
  (assert (sb-thread:wait-on-semaphore attempted :timeout 5))
  (assert (not (sb-thread:wait-on-semaphore installed :timeout .05)))
  (sb-thread:signal-semaphore proceed)
  (sb-thread:join-thread worker) (sb-thread:join-thread holder)
  (assert (null worker-error)) (assert (eq result *fnn-octets*))
  (busy (lambda () (fnn-octets-fill (bytes 99))) :fill)
  (incf *cases*)))
(format t "PASS ~d incoming mutation scenarios~%" *cases*)
'''
        source = header + "\n".join(pure + native) + driver
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / "mutation.lisp"
            script.write_text(source)
            run = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                                  "--script", str(script)], capture_output=True, text=True, timeout=30)
        evidence = os.environ.get("FN_INCOMING_GATE_EVIDENCE")
        if evidence:
            out = Path(evidence)
            out.mkdir(parents=True, exist_ok=True)
            (out / "actual-gate.lisp").write_text(source)
            (out / "result.log").write_text(run.stdout + run.stderr)
            (out / "coordinate.json").write_text(json.dumps({
                "native_forms_sha256": hashlib.sha256("\n".join(native).encode()).hexdigest(),
                "core_forms_sha256": hashlib.sha256("\n".join(core_forms).encode()).hexdigest(),
                "returncode": run.returncode, "core_tree": str(core),
                "scope": __doc__,
            }, indent=2) + "\n")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("PASS 85 incoming mutation scenarios", run.stdout)


if __name__ == "__main__":
    unittest.main()
