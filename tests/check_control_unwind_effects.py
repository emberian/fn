"""Actual issued-turn macro plus actual account retainer on callback escape.

The parent entry/fault and returned values are synthetic transport fixtures,
not funded stobj admission or a native qualification.
"""
import argparse
import sys
import runpy
import subprocess
import tempfile
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--tree', type=Path, required=True)
p.add_argument('--owner-control', type=Path)
p.add_argument('--owner', type=Path)
a = p.parse_args()
sys.path.insert(0, str(a.tree))
ns = runpy.run_path(str(a.tree / 'tests/test_native_account_adoption_transport.py'))
program = '''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defvar *fnn-extent-lock* (sb-thread:make-mutex))
(defvar *the-live-state* :original-state)
(defvar *fault-effects* nil)
(defvar *finish-effects* nil)
(defstruct fnn-owner-control-binding slots pool slot)
(defvar *binding* (make-fnn-owner-control-binding :slots :old-slots :pool :old-pool :slot 2))
(defun fnn-owner-service-control-binding (service) (declare (ignore service)) *binding*)
(defun fnn-owner-control-enter (binding) (declare (ignore binding)) (values :gate-owned 17))
(defun fnn-owner-control-finish (binding nonce)
 (assert (= nonce 17))
 (setf *finish-effects* (list (fnn-owner-control-binding-slots binding)
                            (fnn-owner-control-binding-pool binding))))
(defun fnn-owner-control-fault (binding)
 (setf *fault-effects* (list (fnn-owner-control-binding-slots binding)
                           (fnn-owner-control-binding-pool binding))))
(defun fnn-fixed-callback-fail (&rest args) (declare (ignore args)) (error "intentional missing STATE fault"))
(defmacro fnn-owner-gated ((service class) &body body)
 (declare (ignore service class)) `(progn ,@body))
(defun fnn-owner-service-stopping (service) (declare (ignore service)) nil)
(defun fnn-owner-shared-action-locked (service cid callback)
 (declare (ignore service cid)) (funcall callback))
'''
def named(path, prefix, override=None):
    if not override:
        return ns['named'](path, prefix)
    text = override.read_text()
    return next(text[x:y] for x, y in ns['spans'](text) if text[x:y].startswith(prefix))

program += named('host/native/owner-control-turn.lisp', '(defmacro fnn-with-owner-control-issued-turn\n', a.owner_control)
program += ns['named']('host/native/account-adoption.lisp', '(defun fnn-account-retain-control-effects ')
program += named('host/native/owner.lisp', '(defun fnn-owner-serialized-with-control-turn\n', a.owner)
program += '''
;; Both escapes occur inside the actual macro's sole actual caller. The first
;; retainer deliberately fails after retaining partial effects; the second
;; retains complete effects then parsing throws before callback return.
(dolist (which '(:missing-state :post-retain-parse))
 (setf *binding* (make-fnn-owner-control-binding :slots :old-slots :pool :old-pool :slot 2)
       *the-live-state* :original-state *fault-effects* nil *finish-effects* nil)
 (assert (handler-case
  (progn
   (fnn-owner-serialized-with-control-turn :service nil
    (lambda (slot nonce slots pool)
     (declare (ignore slot nonce slots pool))
     (fnn-account-retain-control-effects
      :service (list :unavailable nil :fresh-slots :fresh-pool
                     (if (eq which :missing-state) nil :fresh-state)))
     (error "intentional post-retain parse escape")))
   nil)
  (error () t)))
 (format t "~s fault observer received ~s~%" which *fault-effects*)
 (assert (equal *fault-effects* '(:fresh-slots :fresh-pool)))
 (assert (null *finish-effects*))
 (assert (eq *the-live-state* (if (eq which :missing-state) :original-state :fresh-state))))
;; A generic normal callback need not use the account retainer. The actual
;; caller must publish all returned effects before a missing-STATE fault.
(setf *binding* (make-fnn-owner-control-binding :slots :old-slots :pool :old-pool :slot 2)
      *fault-effects* nil *finish-effects* nil)
(assert (handler-case
 (progn
  (fnn-owner-serialized-with-control-turn :service nil
   (lambda (slot nonce slots pool)
    (declare (ignore slot nonce slots pool))
    (values :unavailable nil :returned-slots :returned-pool nil)))
  nil)
 (error () t)))
(assert (equal *fault-effects* '(:returned-slots :returned-pool)))
(assert (null *finish-effects*))
;; Success and cleanup retain legitimate outputs and finish that same receipt.
(setf *binding* (make-fnn-owner-control-binding :slots :old-slots :pool :old-pool :slot 2)
      *fault-effects* nil *finish-effects* nil)
(multiple-value-bind (word answer)
 (fnn-owner-serialized-with-control-turn :service nil
  (lambda (slot nonce slots pool)
   (declare (ignore slot nonce slots pool))
   (values :yield :answer :returned-slots :returned-pool :returned-state))
  :control
  (lambda (slot nonce slots pool)
   (assert (and (= slot 2) (= nonce 17) (eq slots :returned-slots) (eq pool :returned-pool)))
   (values :account-turn-retained :epilogue-pool :epilogue-state)))
 (assert (and (eq word :yield) (eq answer :answer))))
(assert (equal *finish-effects* '(:returned-slots :epilogue-pool)))
(assert (null *fault-effects*))
(assert (eq *the-live-state* :epilogue-state))
(format t "ACTUAL_CONTROL_UNWIND_EFFECTS_PASS; synthetic UNFUNDED entry.~%")
'''
with tempfile.TemporaryDirectory(prefix='fn-closeout-unwind-') as d:
    path = Path(d) / 'regression.lisp'
    path.write_text(program)
    r = subprocess.run(['sbcl', '--noinform', '--script', str(path)], text=True, capture_output=True, timeout=30)
    print(r.stdout + r.stderr)
    raise SystemExit(r.returncode)
