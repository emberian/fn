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
    program += named('host/native/auth-adoption-parked.lisp', '(defun fnn-native-auth-adopt-config ')
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
(defun fn-owner-account-adoption-configuration-step (slot nonce slots pool state)
 (declare (ignore slot nonce))
 (values :unavailable :configuration-semantic-pending slots pool state))
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
               (:complete :configure :configuration-semantic-pending)))
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
    program += named('host/native/auth-adoption-parked.lisp', '(defun fnn-native-auth-adopt-config ')
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


def test_actual_semantic_lease_refuses_before_account_reservation(tmp_path):
    """Actual CURRENT fixed-tag check precedes PRS issue; no shape grant."""
    program = '''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defmacro mv (&rest x) `(values ,@x))
(defmacro mv-let (names form &body body) `(multiple-value-bind ,names ,form ,@body))
(defun zp (n) (or (not (integerp n)) (<= n 0)))
(defun boundp-global (key state) (not (null (assoc key state))))
(defun f-get-global (key state) (cdr (assoc key state)))
(defun fn-ats-role-bodyp (&rest args) (declare (ignore args)) t)
(defun fn-owner-account-turn-current (state) (declare (ignore state)) nil)
(defun fn-act-reserve (&rest args) (declare (ignore args)) (error "unexpected account PRS issue"))
'''
    for path, prefix in [
        ('books/snapshot-source-token.lisp', '(defun fn-omk-at '),
        ('books/snapshot-source-token.lisp', '(defun fn-omk-widthp '),
        ('books/admission-semantic-exclusion.lisp', '(defun fn-owner-admission-semantic-busy-p '),
        ('host/account-adoption-turn-host.lisp', '(defun fn-owner-account-turn-admit-resources-internal\n'),
    ]:
        program += cl_form(named(path, prefix))
    program += '''
(dolist (source '((:history-config-acquiring :original-owner :original-turn)
                 (:history-config-source :token :base :generation :incarnation
                     :count :cursor :wire :output :receipt)))
 (let* ((state (list (cons 'fn-owner-history-semantic-source source)))
        (pool (list :original-pool))
        (resources '(:account-adoption-resources :operation-select
                     :demand :rescue :retained :body :coordinate :contract)))
  (assert (fn-owner-admission-semantic-busy-p state))
  (multiple-value-bind (word next-pool next-state)
    (fn-owner-account-turn-admit-resources-internal :operation-select
        :original-source resources 2 17 :actual-slots pool state)
   (assert (eq word :account-semantic-source-busy))
   (assert (and (eq pool next-pool) (eq state next-state))))))
(dolist (source '(nil (:history-config-acquiring :short)
                  (:history-config-source :short)
                  (:other-source :a :b)))
 (assert (not (fn-owner-admission-semantic-busy-p
               (list (cons 'fn-owner-history-semantic-source source))))))
(format t "ACCOUNT_SEMANTIC_BUSY_BEFORE_RESERVATION_PASS~%")
'''
    path = tmp_path / 'account-semantic-reservation-refusal.lisp'
    path.write_text(program)
    out = subprocess.run(['sbcl', '--noinform', '--script', str(path)],
                         capture_output=True, text=True, timeout=30)
    assert out.returncode == 0, out.stdout + out.stderr
    assert 'ACCOUNT_SEMANTIC_BUSY_BEFORE_RESERVATION_PASS' in out.stdout


def test_actual_configuration_caller_retains_each_returned_effect(tmp_path):
    """Actual caller transport; scripted C producers are UNFUNDED, not receipts."""
    program = '''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defmacro mv (&rest x) `(values ,@x))
(defmacro mv-let (names form &body body) `(multiple-value-bind ,names ,form ,@body))
(defvar *acquires* 0)
(defvar *prepares* 0)
(defvar *acquire-word* :account-config-source-retained)
(defvar *prepare-word* :yield)
(defvar *acquired-slots* (list :returned-slots))
(defvar *acquired-pool* (list :returned-pool))
(defvar *acquired-state* (list :actual-c-source))
(defvar *prepared-state* (list :retained-full8-c-cursors))
(defun fn-owner-account-config-source (state) (and (eq state *acquired-state*) :retained))
(defun fn-owner-history-config-begin (slot nonce slots pool state)
 (declare (ignore slot nonce slots pool state))
 (incf *acquires*)
 (values *acquire-word* :core-derived-id *acquired-slots* *acquired-pool* *acquired-state*))
(defun fn-owner-account-config-preparation-step (state)
 (assert (eq state *acquired-state*))
 (incf *prepares*)
 (values *prepare-word* *prepared-state*))
'''
    program += cl_form(named('host/account-adoption-publication-host.lisp',
                             '(defun fn-owner-account-adoption-configuration-step\n'))
    program += '''
;; First acquire: every literal returned effect is retained before preparation.
(multiple-value-bind (word answer slots pool state)
 (fn-owner-account-adoption-configuration-step 2 17 :old-slots :old-pool :old-state)
 (assert (and (eq word :yield) (eq answer :yield)
              (eq slots *acquired-slots*) (eq pool *acquired-pool*)
              (eq state *prepared-state*) (= *acquires* 1) (= *prepares* 1))))
;; SAME retained source resumes without acquiring or reserving another identity.
(setf *prepare-word* :configuration-semantic-pending)
(multiple-value-bind (word answer slots pool state)
 (fn-owner-account-adoption-configuration-step 2 17 *acquired-slots* *acquired-pool* *acquired-state*)
 (assert (and (eq word :unavailable) (eq answer :configuration-semantic-pending)
              (eq slots *acquired-slots*) (eq pool *acquired-pool*)
              (eq state *prepared-state*) (= *acquires* 1) (= *prepares* 2))))
;; Unknown acquisition/refusal retains actual effects and invokes no prep.
(setf *acquire-word* :account-config-source-unavailable)
(multiple-value-bind (word answer slots pool state)
 (fn-owner-account-adoption-configuration-step 2 17 :old-slots :old-pool :old-state)
 (assert (and (eq word :unavailable) (eq answer :account-config-source-unavailable)
              (eq slots *acquired-slots*) (eq pool *acquired-pool*)
              (eq state *acquired-state*) (= *acquires* 2) (= *prepares* 2))))
;; An acquiring/ambiguous preparation result cannot become durable or accepted.
(setf *prepare-word* :recovery-required)
(multiple-value-bind (word answer slots pool state)
 (fn-owner-account-adoption-configuration-step 2 17 *acquired-slots* *acquired-pool* *acquired-state*)
 (assert (and (eq word :recovery-required) (eq answer :recovery-required)
              (eq slots *acquired-slots*) (eq pool *acquired-pool*)
              (eq state *prepared-state*) (= *acquires* 2) (= *prepares* 3))))
(format t "ACCOUNT_C_CALLER_RETAINED_EFFECTS_PASS~%")
'''
    path = tmp_path / 'account-c-caller-effects.lisp'
    path.write_text(program)
    out = subprocess.run(['sbcl', '--noinform', '--script', str(path)],
                         capture_output=True, text=True, timeout=30)
    assert out.returncode == 0, out.stdout + out.stderr
    assert 'ACCOUNT_C_CALLER_RETAINED_EFFECTS_PASS' in out.stdout


def test_actual_configuration_claim_parks_and_rebinds_without_issue(tmp_path):
    """Actual CURRENT transforms/host calls; synthetic UNFUNDED ATS/source parents."""
    program = '''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defmacro mv (&rest x) `(values ,@x))
(defmacro mv-let (names form &body body) `(multiple-value-bind ,names ,form ,@body))
(defun zp (x) (or (not (integerp x)) (<= x 0)))
(defun natp (x) (and (integerp x) (>= x 0)))
(defun member-eq (x xs) (member x xs :test #'eq))
(defun update-nth (n val xs)
 (if (zerop n) (cons val (cdr xs)) (cons (car xs) (update-nth (1- n) val (cdr xs)))))
(defun boundp-global (key state) (not (null (assoc key state))))
(defun f-get-global (key state) (cdr (assoc key state)))
(defun f-put-global (key val state) (acons key val (remove key state :key #'car :test #'eq)))
(defun fn-cbor-octet-listp (xs) (every (lambda (n) (and (natp n) (< n 256))) xs))
(defun fn-cp-uintp (n) (and (natp n) (< n (expt 2 64))))
(defun fn-owner-account-turn-current (state) (f-get-global 'current state))
(defun fn-owner-account-turn-keep (row state) (f-put-global 'current row state))
(defun fn-owner-account-adoption-operation (state) (f-get-global 'holder state))
(defun fn-owner-account-adoption-job (state) (nth 7 (fn-owner-account-turn-current state)))
(defun fn-owner-account-adoption-source (state) (declare (ignore state)) (values :source-current nil nil nil))
(defun fn-owner-account-turn-epilogue-token (&rest x) (declare (ignore x)) (error "C incorrectly entered E return"))
(defun fn-owner-account-turn-return (&rest x) (declare (ignore x)) (error "C incorrectly settled E aliases"))
(defun fn-owner-account-config-source (state) (f-get-global 'lease state))
(defun fn-owner-account-config-preparation-state (state) (f-get-global 'prep state))
(defun fn-owner-history-config-writer-gate (state) (declare (ignore state)) :config-writer-current)
(defvar *phase* 3)
(defvar *resources-available* nil)
(defvar *resources-word* nil)
(defvar *prepay-word* :prepaid)
(defvar *prepay-count* 0)
(defun fn-ats-matchingp (slot nonce slots pool)
 (declare (ignore slots pool)) (and (= slot 2) (member nonce '(17 18 19 20 21))))
(defun fn-ats-kindsi (slot slots) (declare (ignore slot slots)) :owner-control)
(defun fn-ats-phasesi (slot slots) (declare (ignore slot slots)) *phase*)
(defun fn-ats-role-bodyp (slot nonce role slots pool)
 (and (eq role :owner-control) (= *phase* 3) (fn-ats-matchingp slot nonce slots pool)))
(defun fn-owner-runtime-operation-resources (kind pool state)
 (declare (ignore pool state)) (assert (eq kind :account-config-resume))
 (values (or *resources-word* (if *resources-available* :runtime-operation-available :runtime-operation-unavailable))
         '(:account-adoption-resources :account-config-resume (4 0 0 0 0) nil nil 100 :source :return)))
(defun fn-ats-prepay-body-internal (slot nonce body slots pool)
 (declare (ignore slot nonce pool)) (assert (= body 100))
 (incf *prepay-count*) (when (eq *prepay-word* :prepaid) (setf *phase* 3))
 (values *prepay-word* slots :actual-fresh-Q-pool))
(defun fn-act-reserve (&rest x) (declare (ignore x)) (error "second account claim issue"))
(defun fn-prs-issue (&rest x) (declare (ignore x)) (error "unexpected PRS issue"))
(defun fn-catd-next (&rest x) (declare (ignore x)) (error "unexpected reselection"))
'''
    for file, prefix in (
        ('books/consumer-position-fields.lisp', '(defun fn-cp-nth '),
        ('books/account-adoption-input-source.lisp', '(defun fn-cado-widthp '),
        ('books/account-adoption-input-source.lisp', '(defun fn-cado-receipt-coordinatep '),
        ('books/account-adoption-input-source.lisp', '(defun fn-cado-source-keyp '),
        ('books/account-adoption-turn.lisp', '(defun fn-act-row '),
        ('books/account-adoption-turn.lisp', '(defun fn-act-livep '),
        ('books/account-adoption-turn.lisp', '(defun fn-act-uncertain '),
        ('books/account-adoption-turn-state.lisp', '(defun fn-owner-account-turn-fence '),
        ('books/account-adoption-turn-continuation.lisp', '(defun fn-act-suspend '),
        ('books/account-adoption-turn-continuation.lisp', '(defun fn-act-rebind '),
        ('host/account-adoption-turn-host.lisp', '(defun fn-owner-account-turn-current-bodyp\n'),
        ('books/history-config-journal-state.lisp', '(defun fn-owner-history-config-journal '),
        ('host/account-config-continuation-host.lisp', '(defun fn-owner-account-config-continuation-currentp '),
        ('host/account-config-continuation-host.lisp', '(defun fn-owner-account-config-suspended-currentp '),
        ('host/account-config-continuation-host.lisp', '(defun fn-owner-account-config-suspend-current\n'),
        ('host/account-config-continuation-host.lisp', '(defun fn-owner-account-config-resume\n'),
        ('host/account-adoption-host.lisp', '(defun fn-owner-account-adoption-tick\n'),
        ('host/account-adoption-return-host.lisp', '(defun fn-owner-account-turn-return-current\n'),
    ):
        program += cl_form(named(file, prefix))
    program += '''
(defun fn-prs-vectorp (v) (and (= (length v) 5) (every #'natp v)))
(defun fn-prs-below (a b) (every #'<= a b))
(let* ((token '(:account-preparation-turn 7 3 4))
       (id '(:account-operation :candidate 9 10))
       (key (list :account-adoption-source token 3 4 (make-list 32 :initial-element 0) 10))
       (oldrequest (list :original-input)) (oldjob (list :original-job))
       (intent (list :account-turn-reservation :original-ledger :proposed-ledger
                     :original-complete-resources 2 17))
       (row (list :account-turn token :reserved '(8 0 0 0 1)
                  :operation-select key oldrequest oldjob nil intent))
       (holder (list :account-adoption-operation id key '(:configure :marker)
                     oldjob 3 4 8 9 10 :namespace 12 oldrequest token))
       (base (list :history-config-base id :original-store :original-config
                   :canonical :view :posting :obligation))
       (prep (list :account-config-preparation id token :full8 :record base :metadata
                   :groups :history-cursor :generation-cursor 4 5 :next-node :actual-fields14))
       (lease (list :history-config-source id token :parent 3 8 4 :coordinate :record :acquired))
       (state (list (cons 'current row) (cons 'holder holder) (cons 'lease lease)
                    (cons 'prep prep) (cons 'fn-owner-history-config-base base)))
       (pool (list :original-pool)) (slots (list :actual-slots)))
 (assert (fn-owner-account-config-continuation-currentp state))
 ;; Any actual registered journal intent forbids park; effects unchanged.
 (let ((s (f-put-global 'fn-owner-history-config-journal '(:history-config-journal-intent) state)))
  (multiple-value-bind (word np ns)
    (fn-owner-account-config-suspend-current 2 17 slots pool s)
   (assert (and (eq word :account-return-pending) (eq np pool) (eq ns s)))))
 ;; First park owns actual roots while retaining the original claim/counters.
 (multiple-value-bind (word np parked)
   (fn-owner-account-turn-return-current 2 17 slots pool state)
  (assert (and (eq word :account-turn-retained) (eq np pool)))
  (let ((saved (fn-owner-account-turn-current parked)))
   (assert (eq (third saved) :suspended))
   (dolist (i '(1 3 4 5 6 7 9)) (assert (eq (nth i saved) (nth i row))))
   (assert (equal (nth 8 saved) (list :account-config-suspension id key base prep lease)))
   (assert (fn-owner-account-config-suspended-currentp parked))
   (setf *phase* 2)
   ;; Missing source/prepay keeps all parked aliases and original counters.
   (multiple-value-bind (w answer sl po st)
     (fn-owner-account-config-resume 2 18 slots pool parked)
    (assert (and (eq w :unavailable) (eq answer :account-config-resume-resources-unavailable)
                 (eq sl slots) (eq po pool) (eq st parked) (zerop *prepay-count*))))
   (multiple-value-bind (w po st)
     (fn-owner-account-config-suspend-current 2 18 slots pool parked)
    (assert (and (eq w :account-turn-retained) (eq po pool) (eq st parked))))
   ;; Corrupted receipt/slot removal cannot rebind or spend another claim.
   (multiple-value-bind (w answer sl po st)
     (fn-owner-account-config-resume 3 18 slots pool parked)
    (assert (and (eq w :refused) (eq answer :account-continuation-changed)
                 (eq sl slots) (eq po pool) (eq st parked) (zerop *prepay-count*))))
   ;; Unknown source outcome fences original aliases, never finishes the turn.
   (setf *resources-word* :unknown-source-outcome)
   (multiple-value-bind (w answer sl po st)
     (fn-owner-account-config-resume 2 20 slots pool parked)
    (assert (and (eq w :recovery-required) (eq answer :unknown-source-outcome)
                 (eq sl slots) (eq po pool) (zerop *prepay-count*)))
    (let ((fenced (fn-owner-account-turn-current st)))
     (assert (eq (third fenced) :uncertain))
     (dolist (i '(1 3 4 5 6 7 8 9)) (assert (eq (nth i fenced) (nth i saved)))))
    (multiple-value-bind (rw rp rs)
      (fn-owner-account-turn-return-current 2 20 slots pool st)
     (assert (and (eq rw :account-return-pending) (eq rp pool) (eq rs st)))))
   (setf *resources-word* nil *resources-available* t *prepay-word* :yield)
   ;; Budget yield retains the parked account claim and all returned Q effects.
   (multiple-value-bind (w answer sl po st)
     (fn-owner-account-config-resume 2 21 slots pool parked)
    (assert (and (eq w :yield) (eq answer :account-config-resume-budget-yield)
                 (eq sl slots) (eq po :actual-fresh-Q-pool) (eq st parked)
                 (= *prepay-count* 1))))
   (setf *prepay-word* :prepaid)
   ;; Synthetic source availability exercises actual prepay/rebind transport.
   (setf *resources-available* t)
   (multiple-value-bind (w answer sl po st)
     (fn-owner-account-adoption-tick 2 19 slots pool parked)
    (assert (and (eq w :configure) (eq answer id) (eq sl slots)
                 (eq po :actual-fresh-Q-pool) (= *prepay-count* 2)))
    (let* ((rebound (fn-owner-account-turn-current st)) (newintent (nth 9 rebound)))
     (assert (eq (third rebound) :reserved))
     (dolist (i '(1 3 4 5 6 7 8)) (assert (eq (nth i rebound) (nth i saved))))
     (dolist (i '(0 1 2 3)) (assert (eq (nth i newintent) (nth i intent))))
     (assert (and (= (nth 4 newintent) 2) (= (nth 5 newintent) 19))))))))
(format t "ACCOUNT_C_RETAINED_CLAIM_REBIND_PASS~%")
'''
    path = tmp_path / 'account-c-retained-claim.lisp'
    path.write_text(program)
    out = subprocess.run(['sbcl', '--noinform', '--script', str(path)],
                         capture_output=True, text=True, timeout=30)
    assert out.returncode == 0, out.stdout + out.stderr
    assert 'ACCOUNT_C_RETAINED_CLAIM_REBIND_PASS' in out.stdout


# The functions above are pytest-shaped; tools/native_source_check.py and the
# native harness run `python3 -m unittest`, which collected nothing here and
# exited 5 (check-lane red CL02, 2026-10-03).  Each runs as a unittest case
# with its own temporary directory.  The host file it reads,
# host/native/account-adoption.lisp, is parked (planning/host-parked.json, F06):
# these are image-free source checks of the parked code, kept green until L3
# deletes or rewires it.  fnn-native-auth-adopt-config moved at stage 0 from
# host/native/auth.lisp to host/native/auth-adoption-parked.lisp; the two
# cases that read it read it there.
import tempfile  # noqa: E402
import unittest  # noqa: E402


class AccountAdoptionTransportTests(unittest.TestCase):
    pass


for _name, _function in list(globals().items()):
    if _name.startswith("test_") and callable(_function):
        def _case(self, _function=_function):
            with tempfile.TemporaryDirectory() as directory:
                _function(Path(directory))
        setattr(AccountAdoptionTransportTests, _name, _case)
        del globals()[_name]  # collected once, as the class's case
del _name, _function
