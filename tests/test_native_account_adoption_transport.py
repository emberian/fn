"""Literal pooled native lifecycle transport; synthetic core is NOT a grant."""
from pathlib import Path
import subprocess
from tools.proof_repl import spans

ROOT = Path(__file__).resolve().parents[1]


def named(path, prefix):
    text = (ROOT / path).read_text()
    return next(text[a:b] for a, b in spans(text) if text[a:b].startswith(prefix))


def cl_form(form):
    while '(declare ' in form:
        a = form.index('(declare ')
        depth = 0
        for b in range(a, len(form)):
            depth += (form[b] == '(') - (form[b] == ')')
            if depth == 0:
                form = form[:a] + form[b + 1:]
                break
    return form


def test_actual_native_five_mv_lifecycle_transport(tmp_path):
    program = '''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defun zp (x) (or (not (integerp x)) (<= x 0)))
(defvar *fnn-extent-lock* (sb-thread:make-mutex))
(defvar *the-live-state* (list :actual-state-ref))
(defvar *pool* (list :actual-pool-ref))
(defvar *calls* nil)
(defvar *slots* (list :actual-slots-ref))
(defvar *mode* :refused)
(defun fnn-live-page-read-pool () *pool*)
(defun fnn-fault (format &rest args) (error (apply #'format nil format args)))
(defun fnn-indeterminate (text) (error text))
(defun fnn-owner-consumer-entropy-observation () :observed-entropy)
(defun fnn-owner-serialized-with-control-turn (service cid thunk &optional (class :control) epilogue)
  (declare (ignore service cid class))
  (when (eq *mode* :no-ticket)
    (return-from fnn-owner-serialized-with-control-turn
      (values :owner-control-unavailable :refused)))
  (let ((result (multiple-value-list (funcall thunk 2 17 *slots* *pool*))))
    (assert (and (= (length result) 5) (eq (third result) *slots*)
                 (eq (fourth result) *pool*) (eq (fifth result) *the-live-state*)))
    ;; Actual callback references dropped before the synthetic scheduler
    ;; cleanup edge. This fixture tests transport, NOT alias retirement.
    (setf thunk nil)
    (when epilogue
      (multiple-value-bind (word next-pool next-state)
          (funcall epilogue 2 17 *slots* *pool*)
        (declare (ignore word))
        (assert (and (eq next-pool *pool*) (eq next-state *the-live-state*)))))
    (values (first result) (second result))))
(defun fnn-core (name &rest args) (apply (symbol-function name) args))
(defun fnn-call (name &rest args)
  ;; Explicit synthetic UNFUNDED core script: records real transport only.
  (push (cons name args) *calls*)
  (case name
    (fn-owner-account-adoption-begin
      (assert (and (= (fourth args) 2) (= (fifth args) 17)
                   (eq (sixth args) *slots*) (eq (seventh args) *pool*)
                   (eq (eighth args) *the-live-state*)))
      (list (case *mode* (:fault :recovery-required) (:refused :refused) (t :yield))
            :unavailable *slots* *pool* *the-live-state*))
    (fn-owner-account-adoption-tick
      (assert (and (= (first args) 2) (= (second args) 17)
                   (eq (third args) *slots*) (eq (fourth args) *pool*)
                   (eq (fifth args) *the-live-state*)))
      (list (if (eq *mode* :publish) :publish :refused)
            :opaque-operation *slots* *pool* *the-live-state*))
    (fn-owner-account-turn-return-current
      (assert (and (= (first args) 2) (= (second args) 17)
                   (eq (third args) *slots*) (eq (fourth args) *pool*)
                   (eq (fifth args) *the-live-state*)))
      (list :account-return-pending *pool* *the-live-state*))
    (fn-owner-account-adoption-collect
      (assert (and (= (first args) 2) (= (second args) 17)
                   (eq (third args) *slots*) (eq (fourth args) *pool*)
                   (eq (fifth args) *the-live-state*)))
      (list :accepted nil *slots* *pool* *the-live-state*))
    (fn-owner-account-adoption-status
      (assert (eq (first args) *the-live-state*)) (list '(:accepted)))
    (otherwise (error "unexpected native endpoint ~s" name))))
(defun fnn-owner-account-publication-locked (service)
  (declare (ignore service)) (push '(:synthetic-durable-callback) *calls*) :durable)
(defun fnn-owner-account-configuration-publication-locked (service)
  (declare (ignore service)) (error "wrong publication callback"))
'''
    for prefix in ('(defun fn-cp-nth ',):
        program += cl_form(named('books/consumer-position-fields.lisp', prefix))
    for prefix in ('(defun fn-cado-result-action ', '(defun fn-cado-result-after-status ',
                   '(defun fn-cado-status-result-action '):
        program += cl_form(named('books/account-adoption-result.lisp', prefix))
    program += cl_form(named('books/consumer-account-candidate.lisp',
                             '(defun fn-cad-action-kind '))
    for prefix in ('(defun fnn-account-adoption-begin ',
                   '(defun fnn-account-adoption-tick ',
                   '(defun fnn-account-adoption-status ', '(defun fnn-account-adoption-epilogue ',
                   '(defun fnn-account-adoption-collect '):
        program += named('host/native/account-adoption.lisp', prefix)
    program += named('host/native/auth.lisp', '(defun fnn-native-auth-adopt-config ')
    program += '''
(let ((config (list :original-config)) (bindings (list :original-bindings)))
  (assert (eq (fnn-native-auth-adopt-config :service config bindings) :refused))
  (assert (= (length *calls*) 2))
  (assert (and (eq (second (find 'fn-owner-account-adoption-begin *calls* :key #'car)) config)
               (eq (third (find 'fn-owner-account-adoption-begin *calls* :key #'car)) bindings))))
(setf *calls* nil *mode* :no-ticket)
(assert (eq (fnn-native-auth-adopt-config :service nil nil) :refused))
(assert (null *calls*))
(setf *calls* nil *mode* :tick-refused)
(assert (eq (fnn-native-auth-adopt-config :service nil nil) :refused))
(assert (= (length *calls*) 4))
(setf *calls* nil *mode* :publish)
(assert (eq (fnn-native-auth-adopt-config :service nil nil) :accepted))
(assert (= (length *calls*) 6))
(assert (eq (car (find 'fn-owner-account-adoption-collect *calls* :key #'car)) 'fn-owner-account-adoption-collect))
(setf *calls* nil *mode* :fault)
(assert (handler-case
          (progn (fnn-native-auth-adopt-config :service nil nil) nil)
          (error () t)))
(assert (= (length *calls*) 2))
(format t "ACCOUNT_NATIVE_LITERAL_TRANSPORT_PASS~%")
'''
    path = tmp_path / 'account-transport.lisp'
    path.write_text(program)
    out = subprocess.run(['sbcl', '--noinform', '--script', str(path)],
                         capture_output=True, text=True, timeout=30)
    assert out.returncode == 0, out.stdout + out.stderr
    assert 'ACCOUNT_NATIVE_LITERAL_TRANSPORT_PASS' in out.stdout


def test_actual_return_recovery_cut_keeps_debt(tmp_path):
    """Actual return-current branch; synthetic state is not a lifetime grant."""
    program = '''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defmacro mv (&rest x) `(values ,@x))
(defmacro mv-let (names form &body body) `(multiple-value-bind ,names ,form ,@body))
(defun member-eq (x xs) (member x xs :test #'eq))
(defun fn-owner-account-turn-current (state) (declare (ignore state)) nil)
(defun fn-prp-mode (pool) (first pool))
(defun fn-prp-alloc-mode (pool) (second pool))
(defun fn-owner-account-turn-epilogue-token (&rest x)
 (declare (ignore x)) (error "unexpected authority lookup"))
(defun fn-owner-account-turn-return (&rest x)
 (declare (ignore x)) (error "unexpected settlement"))
'''
    program += cl_form(named('host/account-adoption-return-host.lisp',
                             '(defun fn-owner-account-turn-return-current\n'))
    program += '''
(dolist (case '((:served :active :account-turn-not-owned)
               (:served :draining :account-turn-not-owned)
               ((:counter-publishing :retained-roots) :recovery :account-return-pending)
               (:served :recovery :account-return-pending)))
 (let ((pool (list (first case) (second case))) (state (list :original-state)))
  (multiple-value-bind (word next-pool next-state)
    (fn-owner-account-turn-return-current 2 17 :actual-slots pool state)
   (assert (eq word (third case)))
   (assert (and (eq pool next-pool) (eq state next-state))))))
(format t "ACCOUNT_RETURN_RECOVERY_CUT_PASS~%")
'''
    path = tmp_path / 'account-return-cut.lisp'
    path.write_text(program)
    out = subprocess.run(['sbcl', '--noinform', '--script', str(path)],
                         capture_output=True, text=True, timeout=30)
    assert out.returncode == 0, out.stdout + out.stderr
    assert 'ACCOUNT_RETURN_RECOVERY_CUT_PASS' in out.stdout
