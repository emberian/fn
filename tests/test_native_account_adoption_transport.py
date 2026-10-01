"""Literal pooled native lifecycle transport; synthetic core is NOT a grant."""
from pathlib import Path
import subprocess
import hashlib
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
(defstruct fnn-owner-control-binding slots pool)
(defvar *binding* (make-fnn-owner-control-binding :slots *slots* :pool *pool*))
(defun fnn-owner-service-control-binding (service) (declare (ignore service)) *binding*)
(defun fnn-fixed-callback-fail (&rest x) (declare (ignore x)) (error "missing returned effects"))
(defun fnn-live-page-read-pool () *pool*)
(defun fnn-fault (format &rest args) (error (apply #'format nil format args)))
(defun fnn-indeterminate (text) (error text))
(defun fnn-owner-consumer-entropy-observation () (error "unexpected pre-issuer entropy"))
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
      (assert (and (null (third args)) (= (fourth args) 2) (= (fifth args) 17)
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
    (fn-owner-account-adoption-publication-step
      (assert (and (= (first args) 2) (= (second args) 17)
                   (eq (third args) *slots*) (eq (fourth args) *pool*)
                   (eq (fifth args) *the-live-state*)))
      (list :durable nil *slots* *pool* *the-live-state*))
    (fn-owner-account-adoption-status
      (assert (eq (first args) *the-live-state*)) (list '(:accepted)))
    (otherwise (error "unexpected native endpoint ~s" name))))
'''
    for prefix in ('(defun fn-cp-nth ',):
        program += cl_form(named('books/consumer-position-fields.lisp', prefix))
    for prefix in ('(defun fn-cado-result-action ', '(defun fn-cado-result-after-status ',
                   '(defun fn-cado-status-result-action '):
        program += cl_form(named('books/account-adoption-result.lisp', prefix))
    program += cl_form(named('books/consumer-account-candidate.lisp',
                             '(defun fn-cad-action-kind '))
    for prefix in ('(defun fnn-account-retain-control-effects ',
                   '(defun fnn-account-adoption-begin ',
                   '(defun fnn-account-adoption-tick ',
                   '(defun fnn-account-adoption-status ', '(defun fnn-account-adoption-epilogue ',
                   '(defun fnn-account-adoption-collect ',
                   '(defun fnn-owner-account-publication-locked ',
                   '(defun fnn-owner-account-configuration-publication-locked '):
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
;; Actual transport helper retains every available returned object BEFORE
;; faulting on a missing STATE; original STATE remains available to fencing.
(fnn-account-retain-control-effects
 :service (list :yield nil :fresh-slots :fresh-pool :fresh-state))
(assert (and (eq (fnn-owner-control-binding-slots *binding*) :fresh-slots)
             (eq (fnn-owner-control-binding-pool *binding*) :fresh-pool)
             (eq *the-live-state* :fresh-state)))
(let ((original-state *the-live-state*))
 (assert (handler-case
          (progn (fnn-account-retain-control-effects
                   :service (list :unavailable nil :next-slots :next-pool nil)) nil)
          (error () t)))
 (assert (and (eq (fnn-owner-control-binding-slots *binding*) :next-slots)
              (eq (fnn-owner-control-binding-pool *binding*) :next-pool)
              (eq *the-live-state* original-state))))
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


def test_actual_publication_missing_producer_retains_turn(tmp_path):
    """Actual gate refuses before I/O even with synthetic available families."""
    program = '''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defmacro mv (&rest x) `(values ,@x))
(defmacro mv-let (names form &body body) `(multiple-value-bind ,names ,form ,@body))
(defun zp (x) (or (not (integerp x)) (<= x 0)))
(defun natp (x) (and (integerp x) (>= x 0)))
(defun member-eq (x xs) (member x xs :test #'eq))
(defvar *kind* :publish)
(defvar *stage* :none)
(defvar *token* '(:account-preparation-turn 7 3 4))
(defvar *issued* *token*)
(defun fn-owner-account-adoption-operation (state)
 (declare (ignore state))
 (list :account-adoption-operation :opaque-id :source
       (list *kind* :original-selection) :original-job
       3 4 9 10 11 :namespace 12 :original-request *token*))
(defun fn-owner-account-turn-receipt (state)
 (declare (ignore state)) (values :account-turn-reserved *issued*))
(defun fn-owner-account-turn-current-bodyp (op source slot nonce slots pool state)
 (declare (ignore source slots pool state))
 (and (eq op :operation-select) (= slot 2) (= nonce 17)))
(defun fn-owner-runtime-operation-source (kind pool state)
 (declare (ignore kind pool state))
 (values (if (eq *stage* :none) :runtime-operation-unavailable :runtime-operation-available)
         :synthetic-unfunded-family))
(defun fn-owner-runtime-operation-role-table (kind pool state)
 (declare (ignore kind pool state))
 (values (if (member *stage* '(:resources :complete)) :runtime-operation-available
          :runtime-operation-unavailable) :synthetic-roles))
(defun fn-owner-runtime-operation-resources (kind pool state)
 (declare (ignore kind pool state))
 (values (if (eq *stage* :complete) :runtime-operation-available :runtime-operation-unavailable)
         :synthetic-original-resource-result))
'''
    for file, prefix in (
        ('books/consumer-position-fields.lisp', '(defun fn-cp-nth '),
        ('books/account-adoption-input-source.lisp', '(defun fn-cado-widthp '),
        ('books/account-adoption-input-source.lisp', '(defun fn-cado-receipt-coordinatep '),
        ('host/account-adoption-publication-host.lisp', '(defun fn-owner-account-adoption-publication-step\n'),
    ):
        program += cl_form(named(file, prefix))
    program += '''
(dolist (case '((:none :publish :account-publication-operation-unavailable)
               (:family :publish :account-publication-role-unavailable)
               (:resources :publish :account-publication-resources-unavailable)
               (:complete :publish :account-publication-executor-missing)
               (:complete :configure :account-configuration-destination-missing)))
 (setf *stage* (first case) *kind* (second case))
 (let ((slots (list :actual-slots)) (pool (list :retained-pool)) (state (list :retained-state)))
  (multiple-value-bind (word answer ns np nstate)
    (fn-owner-account-adoption-publication-step 2 17 slots pool state)
   (assert (and (eq word :unavailable) (eq answer (third case))
                (eq ns slots) (eq np pool) (eq nstate state))))))
;; Corrupted-state removal: all other scripted gate conditions remain true.
(setf *issued* '(:account-preparation-turn 6 3 4) *stage* :complete *kind* :publish)
(let ((slots (list :actual-slots)) (pool (list :retained-pool)) (state (list :retained-state)))
 (multiple-value-bind (word answer ns np nstate)
   (fn-owner-account-adoption-publication-step 2 17 slots pool state)
  (assert (and (eq word :refused) (eq answer :account-publication-source-changed)
               (eq ns slots) (eq np pool) (eq nstate state)))))
(format t "ACCOUNT_PUBLICATION_MISSING_PRODUCER_PASS~%")
'''
    path = tmp_path / 'account-publication-source.lisp'
    path.write_text(program)
    out = subprocess.run(['sbcl', '--noinform', '--script', str(path)],
                         capture_output=True, text=True, timeout=30)
    assert out.returncode == 0, out.stdout + out.stderr
    assert 'ACCOUNT_PUBLICATION_MISSING_PRODUCER_PASS' in out.stdout


def test_real_owner_nil_binding_refuses_before_account_creator(tmp_path):
    """Real frozen owner wrapper + actual auth; missing binding invokes no body."""
    owner_path = ROOT / 'tests/fixtures/account-control-turn-2a5b8df51.lisp'
    assert hashlib.sha256(owner_path.read_bytes()).hexdigest() == '2f6527cf15f9afdf5cbb5bcffa585227433bdd8db2bece4b6caeefd5a8238dd6'
    actual_owner = owner_path.read_text()
    program = '''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defstruct fnn-owner-service control-binding)
(defvar *calls* 0)
(defvar *the-live-state* nil)
(defmacro fnn-with-owner-control-issued-turn ((binding slot nonce slots pool) &body body)
 (declare (ignore binding))
 `(let ((,slot nil) (,nonce nil) (,slots nil) (,pool nil))
    (error "missing binding incorrectly entered issuer") ,@body))
(defmacro fnn-owner-gated ((service class) &body body)
 (declare (ignore service class)) `(progn ,@body))
(defun fnn-owner-service-stopping (service) (declare (ignore service)) nil)
(defun fnn-refuse (&rest x) (declare (ignore x)) (error "unexpected scheduler"))
(defun fnn-owner-shared-action-locked (&rest x) (declare (ignore x)) (error "unexpected scheduler"))
(defun fnn-fixed-callback-fail (&rest x) (declare (ignore x)) (error "unexpected callback"))
(defun fnn-owner-consumer-entropy-observation () (error "unexpected entropy allocation or file I/O"))
(defun fnn-account-adoption-begin (&rest x) (declare (ignore x)) (incf *calls*) (error "unexpected creator"))
(defun fnn-account-adoption-epilogue (&rest x) (declare (ignore x)) (incf *calls*) (error "unexpected epilogue"))
(defun fnn-account-adoption-tick (&rest x) (declare (ignore x)) (incf *calls*) (error "unexpected tick"))
(defun fnn-core (&rest x) (declare (ignore x)) (incf *calls*) (error "unexpected core"))
(defun fnn-account-retain-control-effects (&rest x) (declare (ignore x)) (error "unexpected effects"))
(defun fnn-fault (&rest x) (declare (ignore x)) (error "unexpected fault"))
(defun fnn-indeterminate (&rest x) (declare (ignore x)) (error "unexpected uncertainty"))
'''
    program += actual_owner
    program += named('host/native/auth.lisp', '(defun fnn-native-auth-adopt-config ')
    program += '''
(let ((service (make-fnn-owner-service :control-binding nil))
      (config (list :original-parsed-config)) (bindings (list :original-bindings)))
 (assert (null (fnn-owner-service-control-binding service)))
 (assert (eq (fnn-native-auth-adopt-config service config bindings) :refused))
 (assert (zerop *calls*)))
(format t "REAL_OWNER_NIL_BINDING_BEFORE_CREATOR_PASS~%")
'''
    path = tmp_path / 'account-real-owner-refusal.lisp'
    path.write_text(program)
    out = subprocess.run(['sbcl', '--noinform', '--script', str(path)],
                         capture_output=True, text=True, timeout=30)
    assert out.returncode == 0, out.stdout + out.stderr
    assert 'REAL_OWNER_NIL_BINDING_BEFORE_CREATOR_PASS' in out.stdout
