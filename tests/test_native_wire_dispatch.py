"""Actual native missing-source cut; no image or positive allowance claim."""
import subprocess
from pathlib import Path
from tools.proof_repl import spans

ROOT = Path(__file__).resolve().parents[1]


def _named(text, prefix):
    return next(text[a:b] for a, b in spans(text) if text[a:b].startswith(prefix))


def _cl_form(form):
    # Trusted source fixture only. Stobj/guard translation is a separate gate.
    while "(declare " in form:
        a = form.index("(declare ")
        depth = 0
        for b in range(a, len(form)):
            depth += (form[b] == "(") - (form[b] == ")")
            if depth == 0:
                form = form[:a] + form[b + 1:]
                break
    return form


def test_actual_queue_render_flush_refuse_before_work(tmp_path):
    native = (ROOT / "host/native/mux.lisp").read_text()
    owner = (ROOT / "host/native/owner.lisp").read_text()
    source = (ROOT / "books/runtime-operation-source.lisp").read_text()
    selected = "\n".join(_named(native, p) for p in (
        "(defstruct (fnn-mux-conn ", "(defun fnn-mux-wire-source ",
        "(defun fnn-mux-queue ", "(defun fnn-mux-queue-plan ",
        "(defun fnn-mux-flush "))
    selected += _named(owner, "(defun fnn-owner-response-unpin ")
    program = r'''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defmacro mv (&rest xs) `(values ,@xs))
(defmacro fnn-core-mv (name call) (declare (ignore name)) call)
(defvar *fnn-extent-lock* (sb-thread:make-mutex))
(defvar *the-live-state* nil)
(defvar *work* nil)
(defun fnn-live-page-read-pool () :same-pool)
(defun fnn-mux-service (&rest x) (declare (ignore x)) (push :service *work*) :service)
(defun fnn-mux-render-next (&rest x) (declare (ignore x)) (push :render *work*) (error "unfunded render"))
(defun fnn-owner-connection-call (&rest x) (declare (ignore x)) (push :write *work*) (error "unfunded write"))
(defun fnn-mux-z-out (&rest x) (declare (ignore x)) (push :copy *work*) (error "unfunded copy"))
(defun fnn-mux-after (&rest x) (declare (ignore x)) (push :return *work*) (error "unsettled return"))
(defun fnn-owner-response-pin-step (&rest x)
  (declare (ignore x)) (push :pin-release *work*) (error "unsettled pin release"))
'''
    program += _cl_form(_named(source, "(defun fn-owner-runtime-operation-source "))
    program += selected
    program += r'''
(let* ((out (vector 1 2 3)) (plan (list :retained-plan))
       (custody (list :retained-custody))
       (conn (%make-fnn-mux-conn :out out :out-at 1 :plan plan
               :after :close :input custody :want :output)))
  ;; These are the actual native call sites; their old versions render/copy/write.
  (assert (eq (fnn-mux-queue :loop conn '(8 9) :send :close)
              :runtime-operation-unavailable))
  (assert (eq (fnn-mux-queue-plan :loop conn plan :close)
              :runtime-operation-unavailable))
  (assert (eq (fnn-mux-flush :loop conn) :runtime-operation-unavailable))
  (assert (eq (fnn-owner-response-unpin :service 7) :runtime-operation-unavailable))
  (assert (null *work*))
  (assert (and (eq (fnn-mux-conn-out conn) out)
               (= (fnn-mux-conn-out-at conn) 1)
               (eq (fnn-mux-conn-plan conn) plan)
               (eq (fnn-mux-conn-input conn) custody)
               (eq (fnn-mux-conn-after conn) :close)
               (eq (fnn-mux-conn-want conn) :output)
               (null (fnn-mux-conn-wire-runtime conn)))))
;; Synthetic UNFUNDED family readout: availability alone cannot authorize I/O.
(setf (symbol-function 'fn-owner-runtime-operation-source)
  (lambda (kind pool state) (declare (ignore pool state))
    (assert (eq kind :outgoing-window)) (values :ready :unqualified-shape)))
(let ((conn (%make-fnn-mux-conn)))
  (assert (eq (fnn-mux-queue :loop conn '(1) :send nil) :output-issuer-unavailable))
  (assert (eq (fnn-mux-queue-plan :loop conn '(1) nil) :output-issuer-unavailable))
  (assert (eq (fnn-mux-flush :loop conn) :output-issuer-unavailable))
  (assert (eq (fnn-owner-response-unpin :service 7) :output-terminal-unavailable))
  (assert (null *work*)))
(format t "NATIVE_WIRE_MISSING_SOURCE_PASS~%")
'''
    path = tmp_path / "wire-cut.lisp"
    path.write_text(program)
    result = subprocess.run(["sbcl", "--noinform", "--script", str(path)],
                            text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "NATIVE_WIRE_MISSING_SOURCE_PASS" in result.stdout
