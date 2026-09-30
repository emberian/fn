"""Exact native caller transport fixture, not image/funding qualification.

The fixture loads the changed native forms and the unchanged unavailable core
source bodies. Synthetic callbacks test control/effect retention; they confer
no authority and do not model the parser, provider or all-alias retirement.
"""
import subprocess
from pathlib import Path
from tools.proof_repl import spans

ROOT = Path(__file__).resolve().parents[1]


def _named(text, prefix):
    return next(text[a:b] for a, b in spans(text) if text[a:b].startswith(prefix))


def _without_declarations(form):
    # CL fixture only: ACL2 guards/stobj translation remain a separate gate.
    while "(declare " in form:
        start = form.index("(declare ")
        depth = 0
        for end in range(start, len(form)):
            depth += (form[end] == "(") - (form[end] == ")")
            if depth == 0:
                form = form[:start] + form[end + 1:]
                break
    return form


def test_actual_attempt_closed_source_and_retained_callbacks(tmp_path):
    native = (ROOT / "host/native/owner.lisp").read_text()
    core = (ROOT / "host/post-identity-captured-host.lisp").read_text()
    # Frozen source readout is used as a fixture prerequisite, not an invented
    # qualified flag. Its exact body is also present in the modern owner cohort.
    runtime_source = (ROOT / "books/runtime-operation-source.lisp").read_text()
    unavailable = "\n".join(_without_declarations(_named(runtime_source, f"(defun {name} "))
                             for name in ("fn-owner-runtime-operation-source",
                                          "fn-owner-runtime-operation-role-table"))
    chosen = []
    for a, b in spans(native):
        f = native[a:b]
        if any(f.startswith(p) for p in (
            "(defstruct (fnn-owner-pic-runtime", "(defun fnn-owner-pic-runtime-",
            "(defun fnn-owner-pic-call-locked", "(defun fnn-owner-captured-precheck-locked",
            "(defun fnn-owner-attempt (")):
            chosen.append(f)
    program = r'''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defmacro mv (&rest x) `(values ,@x))
(defmacro mv-let (names call &body body) `(multiple-value-bind ,names ,call ,@body))
(defmacro fnn-core-mv (name call) (declare (ignore name)) call)
(defmacro fnn-owner-attempt-handlers (store &body body) (declare (ignore store)) `(progn ,@body))
(defstruct fnn-owner-service store captured-runtime)
(defvar *fnn-extent-lock* (sb-thread:make-mutex))
(defvar *the-live-state* nil)
(defvar *calls* nil)
(defvar *fuel-inputs* nil)
(defvar *copies* 0)
(defvar *legacy* 0)
(defvar *frontier* 0)
(defun fnn-live-page-read-pool () :pool)
(defun fnn-fixed-callback-fail (&rest x) (error "core fault ~s" x))
(defun fnn-core-mv-unused (&rest x) (declare (ignore x)))
(defun fnn-owner-core (name &rest args)
  (declare (ignore args))
  (case name (fn-owner-group-codes '(1)) (fn-owner-post-boundary :admissible)
    (otherwise (error "unexpected owner core call ~s" name))))
(defun fnn-charge (x) x)
(defun fnn-octet-list (x) (coerce x 'list))
(defun fnn-validate-post-boundary (x) (assert (eq x :admissible)))
(defun fnn-octets-fill (&rest x) (declare (ignore x)) (incf *copies*))
(defun fnn-owner-buffer-arena-action (&rest x) (declare (ignore x)) (incf *legacy*))
(defun fnn-advance-frontier (&rest x) (declare (ignore x)) (incf *frontier*))
(defun fnn-refuse (&rest x) (error "unexpected refusal ~s" x))
(defun fn-owner-pic-begin (&rest x) (declare (ignore x)) (error "not installed"))
(defun fn-owner-pic-next (&rest x) (declare (ignore x)) (error "not installed"))
(defun fn-owner-pic-confirm (&rest x) (declare (ignore x)) (error "not installed"))
(defun fn-owner-pic-retire (&rest x) (declare (ignore x)) (error "not installed"))
'''
    program += unavailable
    for name in ("fn-owner-pic-demand", "fn-owner-pic-runtime-issue"):
        program += _without_declarations(_named(core, f"(defun {name} ")) + "\n"
    program += "\n".join(chosen)
    program += r'''
(defun fixture-result (word &optional erp)
  (values erp word 0 :mio-returned :pool-returned :digest-returned *the-live-state*))
(defun fixture-next (&rest x)
  (push (car x) *fuel-inputs*) (push :next *calls*) (fixture-result :yield))
(defun fixture-confirm (&rest x)
  (push (car x) *fuel-inputs*) (push :confirm *calls*) (fixture-result :confirmed))
(defun fixture-retire (&rest x)
  (push (car x) *fuel-inputs*) (push :retire *calls*) (fixture-result :retire-unavailable))
(let ((service (make-fnn-owner-service :store :store)))
  ;; Actual changed attempt refuses from core source before payload fill,
  ;; materializing comparator or frontier. This is a real executed call site.
  (assert (eq (fnn-owner-attempt service #(1) #(2) '(#(3)) #(4))
              :runtime-operation-unavailable))
  (assert (and (zerop *copies*) (zerop *legacy*) (zerop *frontier*)))
  (assert (eq (fnn-owner-pic-runtime-install-locked service :original-copy
                  :mio :arena :octets :pool :digest 2) :runtime-operation-unavailable))
  (assert (null (fnn-owner-service-captured-runtime service)))
  ;; Synthetic UNFUNDED transport fixture: no installed runtime claim.
  (let ((runtime (%make-fnn-owner-pic-runtime :input-copy :original-copy
                  :mio :mio :arena :arena :octets :octets :pool :pool :digest :digest
                  :quantum 2 :next #'fixture-next :confirm #'fixture-confirm
                  :retire #'fixture-retire)))
    (setf (fnn-owner-service-captured-runtime service) runtime)
    (assert (eq (fnn-owner-attempt service #(1) #(2) '(#(3)) #(4)) :yield))
    (assert (equal (reverse *calls*) '(:next)))
    (assert (eq (fnn-owner-pic-runtime-input-copy runtime) :original-copy))
    (assert (eq (fnn-owner-pic-runtime-mio runtime) :mio-returned))
    (setf *calls* nil *fuel-inputs* nil
          (fnn-owner-pic-runtime-next runtime)
          (lambda (&rest x) (push (car x) *fuel-inputs*) (push :next *calls*)
             (fixture-result :confirmation-required)))
    (assert (eq (fnn-owner-attempt service #(1) #(2) '(#(3)) #(4)) :retire-unavailable))
    (assert (equal (reverse *calls*) '(:next :confirm :retire)))
    (assert (equal (reverse *fuel-inputs*) '(2 0 0)))
    (assert (and (zerop *copies*) (zerop *legacy*) (zerop *frontier*)))
    ;; Returned effects are retained BEFORE the actual native fault escapes.
    (setf (fnn-owner-pic-runtime-next runtime)
      (lambda (&rest x) (declare (ignore x)) (fixture-result :yield :fault)))
    (let ((faulted nil))
      (handler-case (fnn-owner-captured-precheck-locked service)
        (error () (setf faulted t)))
      (assert faulted))
    (assert (eq (fnn-owner-service-captured-runtime service) runtime))
    (assert (eq (fnn-owner-pic-runtime-input-copy runtime) :original-copy))
    (assert (eq (fnn-owner-pic-runtime-pool runtime) :pool-returned))
    (assert (eq (fnn-owner-pic-runtime-digest runtime) :digest-returned))))
(format t "CAPTURED_NATIVE_TRANSPORT_PASS~%")
'''
    path = tmp_path / "captured-transport.lisp"
    path.write_text(program)
    result = subprocess.run(["sbcl", "--noinform", "--script", str(path)],
                            text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "CAPTURED_NATIVE_TRANSPORT_PASS" in result.stdout
