;;; Durable BP node service for outbound work and received FNBS custody.
;;;
;;; Every decision is fn-bpnf-step.  This adapter observes files, persistence
;;; barriers, sockets and TCPCL outcomes, then reports those observations back
;;; to the step function.  A TCPCL outcome never deletes bundle bytes or emits
;;; an fn archive/application receipt.

(in-package "ACL2")

(defstruct fnn-bps
  root lifecycle tally state spool-lock lock-fd (release-debt nil) (stages nil)
  (next-session 0)
  ;; The last base transfer's reading in the contact being driven, and
  ;; whose outcome it is.  :process (a one-shot verb that was asked for the
  ;; transfer: bp-contact tick, bp-service run) folds a refused or uncertain
  ;; transfer into the exit code.  :connection (bp-node serve and dispatch,
  ;; fnn-bpnode-send-receipts) does not: ACL2 has already requeued the job
  ;; by its own identity (fn-bpn-forward-result-step's :requeued record,
  ;; fn-bpnp-uncertain-receipt-transfer-keeps-the-job-owed), so the reading
  ;; costs only that connection, as spec bp-node-machine 4.3.2 states.
  (transfer nil) (transfer-scope :process)
  ;; The (JOB . LIMIT) the family proposal in flight read (Q4a increment B,
  ;; fnn-bps-fragment-effects), so its kind-18 :persist-result carries the
  ;; same finished job; nil when no proposal is in flight.
  (fragment-job nil)
  ;; Volatile reassembly continuation (ARRIVAL JOB LIMIT FAMILY-KEY). Custody is already
  ;; kind-5 durable before this starts; its loss on process death loses work
  ;; only. Each service turn walks one fn-bpfj-step quantum. RESCAN is a
  ;; scheduling hint raised by new custody or durable family replacement.
  (fragment-pending nil) (fragment-rescan t) (fragment-tried nil)
  ;; Routing of queued base jobs (books/bp-node-contact-driver.lisp): nil
  ;; when the verb has no Store (the job keeps the address it was queued
  ;; with), else (:table TABLE), ACL2's route table (fn-bprt-table).
  ;; EXPECTED is the node ID ACL2 names for the hop of the offer being
  ;; driven, which the TCPCL session machine requires the contact to
  ;; announce (fn-tcl-init-acceptablep); nil outside a routed offer.
  (routing nil) (expected nil)
  ;; ACL2's reading of the generation selection file, and the recovery
  ;; event built from it (spec bp-node-machine 3.6; N16).
  (plan (list :none)) (recovery-event nil)
  ;; ACL2's reading of the node's profile, (ROWS OCTETS ADU BUNDLE): the held
  ;; rows and held octets the machine may hold, the largest ADU it admits and
  ;; the largest bundle it decodes (fn-bpnpf-profile-read,
  ;; books/bp-node-profile; PRF-131, PRF-134).  NODE-PROFILE is the whole
  ;; reading, (ROWS OCTETS ADU BUNDLE ROTATE) (fn-bpnpf-node-profile-read):
  ;; ROTATE is the rotation threshold a node verb's open consults
  ;; (fnn-bps-rotate-when-due); PROFILE is its base, ACL2's
  ;; fn-bpnpf-node-profile-base.
  (profile nil) (node-profile nil)
  ;; Each peer's contact frontier, ACL2's table (fn-bpnjc-contact-close,
  ;; books/bp-node-job-cursor.lisp): carried between contacts, empty at
  ;; open, where every frontier is 0 (fn-bpnjc-frontier-zero).
  (cursors nil))

(defun fnn-bps-max-rows (service) (first (fnn-bps-profile service)))

(defun fnn-bps-read-profile (root)
  "ACL2's reading of ROOT's `bp-node-profile' (fn-bpnpf-node-profile-read):
the default when the file is absent, the operator's (ROWS OCTETS ADU BUNDLE
ROTATE) when it is one valid profile frame (a format-1 or format-2 frame
takes the default ADU and bundle octets and the default rotation threshold);
anything else is refused before the journal is opened."
  (let* ((path (fnn-join root (fnn-core 'fn-bpnpf-file-name)))
         (present (fnn-check-regular path))
         (profile (fnn-core 'fn-bpnpf-node-profile-read (and present t)
                            (and present
                                 (fnn-octet-list
                                  (fnn-read-regular-bounded
                                   path (fnn-core 'fn-bpnpf-read-bound)))))))
    (unless profile
      (fnn-refuse "bp: ACL2 refused the node profile ~a" path))
    profile))

(defun fnn-bps-note (service word)
  "Record WORD, an evidence word ACL2 named, for SERVICE's run."
  (fnn-bp-note (fnn-bps-tally service) word)
  service)

(defun fnn-bps-outcome (service)
  "ACL2's class of SERVICE's run so far (fn-bprc-class): :accepted, :refused,
:uncertain (a connection lost after it existed), :not-connected or :fenced (a
publication whose outcome is unknown; recovery required)."
  (fnn-core 'fn-bprc-class (fnn-bp-run-evidence (fnn-bps-tally service))))

; Bound only during a negotiated outbound TCPCL contact.  The ACL2 effect
; supplies the exact image after immutable kind-8 publication.
(defvar *fnn-bps-forward-send* nil)

(defvar *fnn-bps-lifecycle-enumerations* 0)

(defun fnn-bps-lock (root)
  "Acquire lifecycle ownership with an actual carrier before fallible inspection."
  (let ((carrier (make-fnn-bps :root root)) (transferred nil))
    (fnn-unwind-cleanups
      ((setf (fnn-bps-lock-fd carrier)
             (fnn-open (fnn-join root "lifecycle.lock")
                       (logior sb-posix:o-rdwr sb-posix:o-creat +fnn-o-nofollow+) #o600))
       (unless (fnn-regular-p (fnn-fstat (fnn-bps-lock-fd carrier)))
         (fnn-fault "bp-service: refusing non-regular lifecycle lock"))
       (handler-case
           (fnn-flock (fnn-bps-lock-fd carrier) (logior +fnn-lock-ex+ +fnn-lock-nb+))
         (fnn-os-error (e)
           (if (= (fnn-os-errno e) sb-posix:eagain)
               (fnn-refuse "bp-service: lifecycle queue is already locked")
             (fnn-fault "bp-service: cannot establish lifecycle ownership: ~a" e))))
       (setq transferred t)
       (prog1 (fnn-bps-lock-fd carrier) (setf (fnn-bps-lock-fd carrier) nil)))
      (unless transferred (fnn-bps-release carrier)))))

(defvar *fnn-bps-release-debts* nil
  "Actual service carriers whose lifecycle/spool physical return is unobserved.")

(defun fnn-bps-release-observation ()
  (if (or *fnn-bps-release-debts*
          (not (eq (fnn-tcl-spool-close-observation) :closed))) :uncertain :closed))

(defun fnn-bps-release (service)
  (when (fnn-bps-release-debt service)
    (fnn-indeterminate "bp-service: prior lock return remains unobserved"))
  (let ((fd (fnn-bps-lock-fd service)) (spool (fnn-bps-spool-lock service)))
    ;; The service owns neither consumed descriptor after this point; debt
    ;; retains their identities, never permission to retry a recycled number.
    (setf (fnn-bps-lock-fd service) nil (fnn-bps-spool-lock service) nil)
    (handler-case
        (fnn-unwind-cleanups ()
          (when fd (fnn-flock fd +fnn-lock-un+))
          (when fd (fnn-close fd))
          (fnn-tcl-spool-release spool))
      (serious-condition (condition)
        (setf (fnn-bps-release-debt service) (list fd spool condition))
        (pushnew service *fnn-bps-release-debts* :test #'eq)
        (fnn-indeterminate "bp-service: physical lock return unobserved: ~a" condition)))))

(defun fnn-bps-namespace-plan (service)
  ; Sorting is only observation order.  ACL2 decides which names are bounded
  ; hidden-stage evidence and whether final names form its exact frontier.
  (incf *fnn-bps-lifecycle-enumerations*)
  (when (and (> *fnn-bps-lifecycle-enumerations* 1)
             (string= (or (fnn-developer-selector "FN_BP_SERVICE_TEST_FAIL_SECOND_LIFECYCLE_ENUMERATION") "")
                      "1"))
    (fnn-fault "bp-service: lifecycle namespace was enumerated after recovery"))
  (let* ((limit (fnn-core 'fn-bpnf-namespace-max-entries)))
    (unless (and (integerp limit) (>= limit 0))
      (fnn-fault "bp-service: ACL2 returned an invalid lifecycle namespace bound"))
    (let* ((names
             (sort
              (handler-case
                  (fnn-list-directory-bounded
                   (fnn-bps-lifecycle service) limit
                   "bp lifecycle namespace")
                (fnn-store-fault (e)
                  (fnn-indeterminate
                   "bp-service: lifecycle namespace exceeds its bound: ~a" e))
                (fnn-os-error (e)
                  (fnn-indeterminate
                   "bp-service: lifecycle namespace cannot be enumerated: ~a" e)))
              #'string<))
         (plan (fnn-core 'fn-bpnf-mixed-recovery-plan names)))
      (unless (eq (fnn-core 'fn-bpnf-mixed-recovery-planp plan) t)
        (fnn-indeterminate "bp-service: ACL2 rejected lifecycle namespace"))
      (values names plan))))

(defun fnn-bps-clock-domain-gate (service namespace-plan)
  "Return ACL2's boot-domain decision for this recovery.  An :initialize
decision publishes the domain record first.  The host never classifies the
decision: the recovery event carries it as its seventh field and
fn-bpnp-step admits it or fences (spec bp-node-machine 11.1 N07)."
  (let* ((root (fnn-bps-root service))
         (final (fnn-join root (fnn-core 'fn-bpcd-final-name)))
         (present (fnn-check-regular final))
         (sequence-frontier
           (fnn-check-regular
            (fnn-join (fnn-join root "sequence") "frontier.fnb")))
         (legacy-evidence
           (fnn-core 'fn-bpnr-clock-domain-evidence
                     namespace-plan (and sequence-frontier t)
                     (fnn-bps-plan service)))
         (saved (and present
                     (fnn-octet-list
                      (fnn-read-regular-bounded
                       final (fnn-core 'fn-bpcd-frame-limit)))))
         (observed (fnn-bp-boot-id-observation))
         (plan (fnn-core 'fn-bpnf-clock-domain-plan
                         saved (and present t) observed legacy-evidence
                         (and (fnn-bps-lock-fd service) t) (not present))))
    (case (fnn-core 'fn-bpnf-clock-domain-plan-status plan)
      (:initialize
       (let* ((stage (fnn-join root
                               (format nil ".clock-domain-~d-~a"
                                       (sb-posix:getpid) (fnn-random-hex 12))))
              (outcome
                (fnn-immutable-publish-effect
                 (fnn-core 'fn-bpnf-clock-domain-plan-publication plan)
                 stage final root
                 (fnn-octets (fnn-core 'fn-bpnf-clock-domain-plan-frame plan))
                 :cleanup-directory root :operation-label :clock-domain)))
         (unless (eq outcome :durable)
           (fnn-indeterminate
            "bp-service: clock domain publication is ~a" outcome)))))
    plan))

(defun fnn-bps-read-records (service names)
  (let ((limit (fnn-core 'fn-bpn-host-lifecycle-frame-limit))
        (records nil))
    (dolist (name names (nreverse records))
      (let* ((path (fnn-join (fnn-bps-lifecycle service) name))
             (raw (fnn-read-regular-bounded path limit))
             (record (fnn-core 'fn-bpn-host-lifecycle-record-unframe
                               (fnn-octet-list raw))))
        (unless record
          (fnn-indeterminate "bp-service: lifecycle record ~a is damaged" name))
        (push record records)))))

(defun fnn-bps-read-received-rows (service names)
  ;; Kind 5 and kind 7 share the exact epoch-operation filename and the
  ;; generic FNBS frame payload cap.  ACL2 decodes and orders the row kinds.
  (let ((limit (fnn-core 'fn-bpnf-stored-frame-limit))
        (rows nil))
    (dolist (name names (nreverse rows))
      (let* ((path (fnn-join (fnn-bps-lifecycle service) name))
             (raw (fnn-read-regular-bounded path limit))
             (octets (fnn-octet-list raw))
             (admission (fnn-core 'fn-bprpf-row-admit octets
                                   (fnn-bps-profile service))))
        (unless (eq (first admission) :ready)
          (fnn-indeterminate "bp-service: replay profile refusal ~a: ~a"
                             name (second admission)))
        (push (list name octets) rows)))))

(defun fnn-bps-sequence-ready (service has-records)
  (let* ((dir (fnn-join (fnn-bps-root service) "sequence"))
         (prior (fnn-lstat dir)))
    ;; Do not create a fresh sequence namespace just to inspect it: W12's
    ;; allocator must observe the creation itself so it can accept an absent
    ;; frontier exactly once and barrier the parent before first allocation.
    (if (null prior)
        (if has-records :fault :ready)
      (progn
        (handler-case
            (progn (fnn-safe-directory dir nil)
                   (fnn-fsync-dir (fnn-parent dir)))
          (fnn-os-error (e)
            (fnn-indeterminate
             "bp-service: sequence namespace publication failed: ~a" e)))
        (let* ((frontier (fnn-join dir "frontier.fnb"))
               (present (fnn-check-regular frontier))
               (raw (if present
                        (fnn-read-regular-bounded
                         frontier (fnn-core 'fn-bpn-host-sequence-frame-limit))
                      (fnn-make-octets 0)))
               (answer (fnn-core 'fn-bpn-host-sequence-recover
                                 (fnn-octet-list raw) (and present t) nil)))
          (if (eq (fnn-core 'fn-bpn-host-sequence-ready-p answer) t)
              :ready
            :fault))))))

(defun fnn-bps-base (service)
  (fnn-core 'fn-bpnf-base (fnn-bps-state service)))

(defun fnn-bps-foundation-step (service event)
  ;; The initial base-state invariant is checked once at open.  This checks
  ;; only the bounded event before the exact guarded machine call.
  ;; fn-bpnj-step (books/bp-node-job-offer.lisp) is fn-bpnp-step on every
  ;; event but three (fn-bpnj-step-delegates-every-other-event): a named
  ;; base job offer (:contact-job PEER KEY), a transport result that names
  ;; its attempt (:job-result KEY TOKEN OUTCOME), and an unnamed base
  ;; result, which settles nothing.
  (unless (eq (fnn-core 'fn-bpnj-host-eventp event) t)
    (fnn-indeterminate "bp-service: malformed foundation event"))
  (let ((answer (fnn-core 'fn-bpnj-step
                          (fnn-bps-state service) event)))
    (setf (fnn-bps-state service)
          (fnn-core 'fn-bpnf-answer-state answer))
    (fnn-core 'fn-bpnf-answer-effects answer)))

(defun fnn-bps-step (service event)
  (fnn-bps-foundation-step service (list :base event)))

(defun fnn-bps-record-path (service token)
  (fnn-join (fnn-bps-lifecycle service)
            (fnn-core 'fn-bpn-host-lifecycle-record-name token)))

(defun fnn-bps-persist-record (service token record)
  (let* ((dir (fnn-bps-lifecycle service))
         (final (fnn-bps-record-path service token))
         (frame-list (fnn-core 'fn-bpn-host-lifecycle-record-frame record))
         (frame (and frame-list (fnn-octets frame-list)))
         (stage (fnn-join dir (format nil ".record-~d-~a"
                                      (sb-posix:getpid) (fnn-random-hex 12)))))
    ;; An encoder refusal settles the matching pending operation: ACL2's
    ;; :refused persist result clears the pending proposal and answers its
    ;; refusal effect (fn-bpnj-encoder-refusal-settles-the-pending-record).
    ;; Nothing was written.
    (unless frame
      (fnn-out "BP lifecycle record encoder refused token=~d" token)
      (return-from fnn-bps-persist-record :refused))
    (let* ((final-absent (if (fnn-lstat final) nil t))
           (operation
             (fnn-core 'fn-bpn-host-lifecycle-publication-authorize
                       (fnn-bps-base service) token record
                       (if (fnn-bps-lock-fd service) t nil)
                       final-absent)))
      (unless (eq (fnn-core
                   'fn-bpn-host-lifecycle-publication-operationp operation) t)
        (if final-absent
            (fnn-fault "bp-service: ACL2 rejected pending publication echo")
          (fnn-indeterminate
           "bp-service: canonical next lifecycle name is already occupied")))
      (unless (and
               (equal token
                      (fnn-core
                       'fn-bpn-host-lifecycle-publication-operation-token
                       operation))
               (equal record
                      (fnn-core
                       'fn-bpn-host-lifecycle-publication-operation-record
                       operation)))
        (fnn-fault "bp-service: ACL2 publication operation changed its echo"))
      ; The authority directory barrier makes FINAL durable.  Stage unlink and
      ; its same-directory cleanup barrier are best effort: bounded recovery
      ; retains hidden stages explicitly, so their survival cannot weaken the
      ; durable lifecycle record or require an uncertain application result.
      (fnn-immutable-publish-effect
       (fnn-core
        'fn-bpn-host-lifecycle-publication-operation-publication operation)
       stage final dir frame :cleanup-directory dir))))

(defun fnn-bps-persist-kind-five (service epoch operation-id held)
  (let* ((dir (fnn-bps-lifecycle service))
         (name (fnn-core 'fn-bpnf-stored-record-name epoch operation-id))
         (final (fnn-join dir name))
         (final-absent (if (fnn-lstat final) nil t))
         (operation
           (fnn-core 'fn-bpnf-publication-authorize
                     (fnn-bps-state service) epoch operation-id held
                     (if (fnn-bps-lock-fd service) t nil) final-absent)))
    (when (equal operation '(:fault :fnbs-publication-codec))
      (return-from fnn-bps-persist-kind-five (values :refused nil)))
    (unless (eq (fnn-core 'fn-bpnf-publication-operationp operation) t)
      (fnn-indeterminate
       "bp-service: kind-5 publication authority refused the pending echo"))
    (let* ((authorized-name
             (fnn-core 'fn-bpnf-publication-operation-name operation))
           (stage (fnn-join dir (format nil ".record-~d-~a"
                                         (sb-posix:getpid) (fnn-random-hex 12))))
           (frame (fnn-octets
                   (fnn-core 'fn-bpnf-publication-operation-frame operation)))
           (publisher
             (fnn-core 'fn-bpnf-publication-operation-publisher operation)))
      (unless (equal authorized-name name)
        (fnn-fault "bp-service: ACL2 kind-5 name changed after authorization"))
      (let ((outcome
              (fnn-immutable-publish-effect
               publisher stage final dir frame :cleanup-directory dir)))
        (values outcome (and (eq outcome :durable) final))))))

(defun fnn-bps-persist-kind-seven (service epoch operation-id record)
  (let* ((dir (fnn-bps-lifecycle service))
         (name (fnn-core 'fn-bpnf-stored-record-name epoch operation-id))
         (final (fnn-join dir name))
         (final-absent (if (fnn-lstat final) nil t))
         (operation
           (fnn-core 'fn-bpah-publication-authorize
                     (fnn-bps-state service) epoch operation-id record
                     (if (fnn-bps-lock-fd service) t nil) final-absent)))
    (when (equal operation '(:fault :delivery-codec))
      (return-from fnn-bps-persist-kind-seven :refused))
    (unless (eq (fnn-core 'fn-bpah-publication-operationp operation) t)
      (fnn-indeterminate
       "bp-service: kind-7 publication authority refused pending echo"))
    (let* ((authorized-name
             (fnn-core 'fn-bpah-publication-name operation))
           (stage (fnn-join dir (format nil ".record-~d-~a"
                                         (sb-posix:getpid) (fnn-random-hex 12))))
           (frame (fnn-octets
                   (fnn-core 'fn-bpah-publication-frame operation)))
           (publisher
             (fnn-core 'fn-bpah-publication-publisher operation)))
      (unless (equal authorized-name name)
        (fnn-fault "bp-service: ACL2 kind-7 name changed after authorization"))
      (fnn-immutable-publish-effect
       publisher stage final dir frame :cleanup-directory dir))))

(defun fnn-bps-persist-kind-eighteen (service epoch operation-id record)
  (let* ((dir (fnn-bps-lifecycle service))
         (name (fnn-core 'fn-bpnf-stored-record-name epoch operation-id))
         (final (fnn-join dir name))
         (final-absent (if (fnn-lstat final) nil t))
         (operation
           (fnn-core 'fn-bpnf-family-publication-authorize
                     (fnn-bps-state service) epoch operation-id record
                     (if (fnn-bps-lock-fd service) t nil) final-absent)))
    (when (equal operation '(:fault :family-codec))
      (return-from fnn-bps-persist-kind-eighteen :refused))
    (unless (eq (fnn-core 'fn-bpnf-family-publication-operationp operation) t)
      (fnn-indeterminate
       "bp-service: kind-18 publication authority refused pending echo"))
    (let* ((authorized-name
             (fnn-core 'fn-bpnf-family-publication-name operation))
           (stage (fnn-join dir (format nil ".record-~d-~a"
                                         (sb-posix:getpid) (fnn-random-hex 12))))
           (frame (fnn-octets
                   (fnn-core 'fn-bpnf-family-publication-frame operation)))
           (publisher
             (fnn-core 'fn-bpnf-family-publication-publisher operation)))
      (unless (equal authorized-name name)
        (fnn-fault "bp-service: ACL2 kind-18 name changed after authorization"))
      (fnn-immutable-publish-effect
       publisher stage final dir frame :cleanup-directory dir))))

(defun fnn-bps-persist-dispatch (service epoch operation-id record)
  (let* ((dir (fnn-bps-lifecycle service))
         (name (fnn-core 'fn-bpnf-stored-record-name epoch operation-id))
         (final (fnn-join dir name))
         (final-absent (if (fnn-lstat final) nil t))
         (operation
           (fnn-core 'fn-bpnp-dispatch-publication-authorize
                     (fnn-bps-state service) epoch operation-id record
                     (if (fnn-bps-lock-fd service) t nil) final-absent)))
    (when (equal operation '(:fault :dispatch-codec))
      (return-from fnn-bps-persist-dispatch :refused))
    (unless (eq (fnn-core 'fn-bpnp-dispatch-publication-operationp operation) t)
      (fnn-indeterminate
       "bp-service: dispatch publication authority refused pending echo"))
    (let* ((authorized-name
             (fnn-core 'fn-bpnp-dispatch-publication-name operation))
           (stage (fnn-join dir (format nil ".record-~d-~a"
                                         (sb-posix:getpid) (fnn-random-hex 12))))
           (frame (fnn-octets
                   (fnn-core 'fn-bpnp-dispatch-publication-frame operation)))
           (publisher
             (fnn-core 'fn-bpnp-dispatch-publication-publisher operation)))
      (unless (equal authorized-name name)
        (fnn-fault "bp-service: dispatch name changed after authorization"))
      (fnn-immutable-publish-effect
       publisher stage final dir frame :cleanup-directory dir))))

(defun fnn-bps-persist-forward (service epoch operation-id record)
  (let* ((dir (fnn-bps-lifecycle service))
         (name (fnn-core 'fn-bpnf-stored-record-name epoch operation-id))
         (final (fnn-join dir name))
         (final-absent (if (fnn-lstat final) nil t))
         (operation
           (fnn-core 'fn-bpnp-forward-publication-authorize
                     (fnn-bps-state service) epoch operation-id record
                     (if (fnn-bps-lock-fd service) t nil) final-absent)))
    (when (equal operation '(:fault :forward-codec))
      (return-from fnn-bps-persist-forward :refused))
    (unless (eq (fnn-core 'fn-bpnp-forward-publication-operationp operation) t)
      (fnn-indeterminate
       "bp-service: forward publication authority refused pending echo"))
    (let* ((authorized-name
             (fnn-core 'fn-bpnp-forward-publication-name operation))
           (stage (fnn-join dir (format nil ".record-~d-~a"
                                         (sb-posix:getpid) (fnn-random-hex 12))))
           (frame (fnn-octets
                   (fnn-core 'fn-bpnp-forward-publication-octets operation)))
           (publisher
             (fnn-core 'fn-bpnp-forward-publication-publisher operation)))
      (unless (equal authorized-name name)
        (fnn-fault "bp-service: forward name changed after authorization"))
      (fnn-immutable-publish-effect
       publisher stage final dir frame :cleanup-directory dir))))

(defun fnn-bps-persist-kind-ten (service epoch operation-id record)
  (let* ((dir (fnn-bps-lifecycle service))
         (name (fnn-core 'fn-bpnf-stored-record-name epoch operation-id))
         (final (fnn-join dir name))
         (final-absent (if (fnn-lstat final) nil t))
         (operation
           (fnn-core 'fn-bpnf-delete-publication-authorize
                     (fnn-bps-state service) epoch operation-id record
                     (if (fnn-bps-lock-fd service) t nil) final-absent)))
    (when (equal operation '(:fault :delete-codec))
      (return-from fnn-bps-persist-kind-ten :refused))
    (unless (eq (fnn-core 'fn-bpnf-delete-publication-operationp operation) t)
      (fnn-indeterminate
       "bp-service: kind-10 publication authority refused pending echo"))
    (let* ((authorized-name
             (fnn-core 'fn-bpnf-delete-publication-name operation))
           (stage (fnn-join dir (format nil ".record-~d-~a"
                                         (sb-posix:getpid) (fnn-random-hex 12))))
           (frame (fnn-octets
                   (fnn-core 'fn-bpnf-delete-publication-frame operation)))
           (publisher
             (fnn-core 'fn-bpnf-delete-publication-publisher operation)))
      (unless (equal authorized-name name)
        (fnn-fault "bp-service: ACL2 kind-10 name changed after authorization"))
      (fnn-immutable-publish-effect
       publisher stage final dir frame :cleanup-directory dir))))

(defun fnn-bps-persist-kind-fourteen (service epoch operation-id record)
  ;; The kind-14 conflict record (spec bp-node-machine 3.3, 4.1 step 4).
  ;; ACL2 authorizes the exact name, frame and publisher.
  (let* ((dir (fnn-bps-lifecycle service))
         (name (fnn-core 'fn-bpnf-stored-record-name epoch operation-id))
         (final (fnn-join dir name))
         (final-absent (if (fnn-lstat final) nil t))
         (operation
           (fnn-core 'fn-bpnf-conflict-publication-authorize
                     (fnn-bps-state service) epoch operation-id record
                     (if (fnn-bps-lock-fd service) t nil) final-absent)))
    (when (equal operation '(:fault :conflict-codec))
      (return-from fnn-bps-persist-kind-fourteen :refused))
    (unless (eq (fnn-core 'fn-bpnf-conflict-publication-operationp operation) t)
      (fnn-indeterminate
       "bp-service: kind-14 publication authority refused pending echo"))
    (let* ((authorized-name
             (fnn-core 'fn-bpnf-conflict-publication-name operation))
           (stage (fnn-join dir (format nil ".record-~d-~a"
                                         (sb-posix:getpid) (fnn-random-hex 12))))
           (frame (fnn-octets
                   (fnn-core 'fn-bpnf-conflict-publication-frame operation)))
           (publisher
             (fnn-core 'fn-bpnf-conflict-publication-publisher operation)))
      (unless (equal authorized-name name)
        (fnn-fault "bp-service: ACL2 kind-14 name changed after authorization"))
      (fnn-immutable-publish-effect
       publisher stage final dir frame :cleanup-directory dir))))

(defun fnn-bps-settle-conflict (service effect)
  "Publish one :persist-conflict proposal and return the machine's answer to
its outcome, which is the refusal to the offering ingress."
  (unless (= (length effect) 4)
    (fnn-indeterminate "bp-service: malformed kind-14 publication effect"))
  (let* ((epoch (second effect))
         (operation-id (third effect))
         (outcome (fnn-bps-persist-kind-fourteen
                   service epoch operation-id (fourth effect))))
    (fnn-bps-note service (fnn-core 'fn-bprc-publication-evidence outcome))
    (fnn-bps-foundation-step
     service (list :persist-result epoch operation-id outcome))))

(defun fnn-bps-route-host (route) (fnn-octets-string (fnn-octets (second route))))
(defun fnn-bps-route-port (route) (third route))
(defun fnn-bps-route-node (route) (fnn-octets-string (fnn-octets (fourth route))))
(defun fnn-bps-route-keepalive (route) (fifth route))
(defun fnn-bps-route-segment-mru (route) (sixth route))
(defun fnn-bps-route-transfer-mru (route) (seventh route))

(defmacro fnn-bps-with-send-socket ((socket) &body body)
  "Release send custody without replacing the condition escaping the session."
  (let ((primary (gensym "PRIMARY")))
    `(let ((,primary nil))
       (unwind-protect
            (handler-case (progn ,@body)
              (serious-condition (condition)
                (setq ,primary condition)
                (error condition)))
         (when ,socket
           (handler-case (fnn-socket-shut ,socket)
             (serious-condition (cleanup)
               (error (or ,primary cleanup)))))))))

(defvar *fnn-bps-retained-send* nil
  "Installed BP node retained sender; receives one durable send effect.")
(defun fnn-bps-send-effect-next (service effect)
  (when *fnn-bps-retained-send*
    (funcall *fnn-bps-retained-send* service effect)
    (return-from fnn-bps-send-effect-next nil))
  (let* ((route (second effect))
         (key (fourth effect))
         (wire (fifth effect))
         ;; The attempt this transfer belongs to: ACL2's token of the job's
         ;; durable :attempting record.  The result names it, and a result
         ;; naming another attempt settles nothing
         ;; (fn-bpnj-stale-job-result-settles-nothing).
         (attempt (fnn-core 'fn-bpnj-attempt-token (fnn-bps-state service) key))
         (socket nil)
         (fragments nil)
         (transfer-index 1)
         (plan-refused nil)
         (outcome :uncertain))
    (handler-case
        (fnn-bps-with-send-socket (socket)
             (progn
               ; Test-only exact core/adapter fault.  It is inside the same
               ; handler as real send-path failures so the regression proves
               ; that a fault is never collapsed into transport uncertainty.
               (when (string= (or (fnn-developer-selector "FN_BP_SERVICE_TEST_SEND_FAULT") "") "1")
                 (fnn-fault "bp-service: injected send core fault"))
               (setq socket (fnn-tcl-connect (fnn-bps-route-host route)
                                             (fnn-bps-route-port route)))
               ;; RFC 9174 5.4.1: no transfer exceeds the peer's Transfer
               ;; MRU.  Once SESS_INIT has negotiated it, ACL2's
               ;; fn-bpfs-plan (books/bp-fragment-send.lisp) answers whether
               ;; WIRE goes whole, as RFC 9171 5.8 fragments each at most
               ;; that MRU (fn-bpfs-plan-fragments-fit-mru), or not at all.
               ;; The first transfer rides this session; each further
               ;; fragment gets its own session to the same hop.
               (let* ((params (fnn-tcl-params
                               (fnn-bps-route-node route) (fnn-bps-expected service)
                               (fnn-bps-route-keepalive route)
                               (fnn-bps-route-segment-mru route)
                               (fnn-bps-route-transfer-mru route)))
                      (conn (fnn-tcl-session
                             (fnn-socket-fd socket) :active params
                             "bp-service" (fnn-bps-root service)
                             :expect 0 :refuse-inbound t
                             :on-ready
                             (lambda (connection)
                               (let* ((mtu (fnn-core 'fn-tcl-negotiated-transfer-mtu
                                                     (fnn-core 'fn-tcl-session-negotiated
                                                               (fnn-tclc-session connection))))
                                      (plan (fnn-core 'fn-bpfs-plan wire mtu)))
                                 (case (first plan)
                                   (:whole
                                    (setf (fnn-tclc-pending connection)
                                          (cons "bp-service" wire)))
                                   (:fragments
                                    (fnn-out "BP fragmenting length=~d peer-mru=~d fragments=~d"
                                             (length wire) mtu (length (rest plan)))
                                    (setf (fnn-tclc-pending connection)
                                          (cons "bp-service" (second plan)))
                                    (setq fragments (cddr plan)))
                                   (otherwise
                                    (fnn-out "BP fragmentation refused reason=~(~a~) length=~d peer-mru=~d"
                                             (second plan) (length wire) mtu)
                                    (setq plan-refused t))))))))
                 (setq outcome (if plan-refused
                                   :refused
                                 (or (fnn-tclc-outcome conn) :uncertain)))
                 (fnn-socket-shut socket)
                 (setq socket nil)
                 ;; The job's one attempt covers all of its fragments: ACL2
                 ;; (fn-bpfs-fragment-outcome) reads each further transfer,
                 ;; and after the first fragment has gone a connect that
                 ;; sent nothing is :uncertain, never :failed.
                 (loop for fragment in fragments
                       for index from 2
                       while (eq outcome :accepted)
                       do (setq transfer-index index)
                          (let* ((next nil)
                                 (transfer
                                   (handler-case
                                       (fnn-bps-with-send-socket (next)
                                            (progn
                                              (setq next (fnn-tcl-connect
                                                          (fnn-bps-route-host route)
                                                          (fnn-bps-route-port route)))
                                              (or (fnn-tclc-outcome
                                                   (fnn-tcl-session
                                                    (fnn-socket-fd next) :active params
                                                    "bp-service" (fnn-bps-root service)
                                                    :bundle fragment :expect 0
                                                    :refuse-inbound t))
                                                  :uncertain)))
                                     ((or fnn-os-error sb-bsd-sockets:socket-error) ()
                                       (if next :uncertain :failed)))))
                            (setq outcome (fnn-core 'fn-bpfs-fragment-outcome index transfer))
                            (fnn-out "BP fragment ~d transfer ~(~a~)" index outcome))))))
      (fnn-store-error (e)
        ;; Only the exact named refusal used by the session adapter is a
        ;; transport observation. Store uncertainty/faults and unknown
        ;; subclasses retain their condition for the owner's boundary.
        (unless (eq (type-of e) 'fnn-store-error) (error e))
        (setq outcome (fnn-core 'fn-bpfs-fragment-outcome transfer-index
                                (if socket :uncertain :failed))))
      ((or fnn-os-error sb-bsd-sockets:socket-error) ()
        ;; A connect that never produced a socket sent no octet: the
        ;; transfer certainly did not happen (:failed, requeued by ACL2).
        ;; Any failure after the connection exists stays :uncertain.
        (setq outcome (fnn-core 'fn-bpfs-fragment-outcome transfer-index
                                (if socket :uncertain :failed)))))
    ;; The outcome word is an observation; ACL2 names the run's evidence
    ;; from the durable :requeued record's reason (the :forward-refused
    ;; effect, fn-bpnrc-job-result-class-is-the-transport-class).
    (setf (fnn-bps-transfer service) outcome)
    (fnn-bps-foundation-step service (list :job-result key attempt outcome))))

(defun fnn-bps-drive-effect (service effect)
  "Carry out one ACL2 effect; answer the effects ACL2 returned for it, which
are driven next, before the effects after this one (depth first)."
  (let ((next nil))
    (case (first effect)
      (:persist-dispatch
       (unless (= (length effect) 4)
         (fnn-indeterminate "bp-service: malformed dispatch publication effect"))
       (let* ((epoch (second effect))
              (operation-id (third effect))
              (record (fourth effect))
              (outcome
                (fnn-bps-persist-dispatch
                 service epoch operation-id record)))
         (fnn-bps-note service (fnn-core 'fn-bprc-publication-evidence outcome))
         (setq next
          (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      (:dispatch-ready
       (fnn-out "BP received carrier dispatch durable"))
      (:dispatch-answer
       (case (second effect)
         (:refused
          (fnn-bps-note service :refused)
          (fnn-out "BP received carrier dispatch refused"))
         (otherwise
          (fnn-bps-note service :fenced)
          (fnn-indeterminate "bp-service: dispatch publication uncertain"))))
      (:persist-conflict
       (setq next (fnn-bps-settle-conflict service effect)))
      (:persist-delete
       (unless (= (length effect) 4)
         (fnn-indeterminate "bp-service: malformed kind-10 publication effect"))
       (let* ((epoch (second effect))
              (operation-id (third effect))
              (record (fourth effect))
              (outcome
                (fnn-bps-persist-kind-ten
                 service epoch operation-id record)))
         (fnn-bps-note service (fnn-core 'fn-bprc-publication-evidence outcome))
         (setq next
          (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      (:delete-ready
       (fnn-out "BP held carrier deletion durable arrival=~d" (second effect)))
      (:delete-answer
       (case (second effect)
         (:refused
          (fnn-bps-note service :refused)
          (fnn-out "BP held carrier deletion refused"))
         (otherwise
          (fnn-bps-note service :fenced)
          (fnn-indeterminate "bp-service: held deletion uncertain"))))
      (:report-due
       (fnn-out "BP status report intent durable; outbound queue pending"))
      (:persist-family
       (unless (= (length effect) 4)
         (fnn-indeterminate "bp-service: malformed kind-18 publication effect"))
       (let* ((epoch (second effect))
              (operation-id (third effect))
              (record (fourth effect))
              (outcome
                (fnn-bps-persist-kind-eighteen
                 service epoch operation-id record)))
         (fnn-bps-note service (fnn-core 'fn-bprc-publication-evidence outcome))
         (setq next
          (fnn-bps-foundation-step
                   service
                   ;; Q4a: the result carries the proposal's finished job and
                   ;; limit, so fn-bpfj-persist-step reads the image out of
                   ;; the job it was proposed from (fnn-bps-fragment-effects
                   ;; left it in the service; consumed here, once).
                   (let ((carried (fnn-bps-fragment-job service)))
                     (setf (fnn-bps-fragment-job service) nil)
                     (if carried
                         (list :persist-result epoch operation-id outcome
                               (car carried) (cdr carried))
                       (list :persist-result epoch operation-id outcome)))))))
      (:family-ready
       (fnn-out "BP fragment family durable")
       ;; Another family is next turn's work, never recursive work before
       ;; this transfer's ACK or inside the publication effect driver.
       (setf (fnn-bps-fragment-rescan service) t
             (fnn-bps-fragment-tried service) nil))
      (:family-answer
       (case (second effect)
         (:refused (fnn-out "BP fragment family publication refused"))
         (otherwise
          (fnn-bps-note service :fenced)
          (fnn-indeterminate "bp-service: fragment family uncertain"))))
      (:persist-delivery
       (unless (= (length effect) 4)
         (fnn-indeterminate "bp-service: malformed kind-7 publication effect"))
       (let* ((epoch (second effect))
              (operation-id (third effect))
              (record (fourth effect))
              (outcome
                (fnn-bps-persist-kind-seven
                 service epoch operation-id record)))
         (fnn-bps-note service (fnn-core 'fn-bprc-publication-evidence outcome))
         (setq next
          (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      ((:persist-attempt :persist-forward-result :persist-deferral)
       (unless (= (length effect) 4)
         (fnn-indeterminate "bp-service: malformed forward publication effect"))
       (let* ((epoch (second effect))
              (operation-id (third effect))
              (record (fourth effect))
              (outcome (fnn-bps-persist-forward
                        service epoch operation-id record)))
         (fnn-bps-note service (fnn-core 'fn-bprc-publication-evidence outcome))
         (setq next
          (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      (:deliver
       (fnn-fault "bp-service: application delivery requires the owner caller"))
      (:delivery-answer
       ;; PRF-224: ACL2's report (fn-bpah-handoff-report) names the
       ;; application's disposition the durable kind 7 holds: durable only
       ;; when the application committed, refused by name otherwise.
       (case (fnn-core 'fn-bpah-handoff-report effect)
         (:durable
          (fnn-out "BP application handoff durable disposition=~(~a~)"
                   (third effect)))
         (:refused
          ;; A durable kind 7 recording the application's refusal completes
          ;; the delivery: the run's evidence is unchanged (the transfer was
          ;; accepted and its disposition is durable), as before PRF-224.
          ;; Only a refused publication or callback (no disposition) is the
          ;; run's refusal.
          (if (third effect)
              (fnn-out "BP application handoff refused disposition=~(~a~) (kind 7 durable)"
                       (third effect))
            (progn
              (fnn-bps-note service :refused)
              (fnn-out "BP application handoff refused"))))
         (otherwise
          (fnn-bps-note service :fenced)
          (fnn-indeterminate "bp-service: application handoff uncertain"))))
      (:persist
       (let* ((token (second effect))
              (record (third effect))
              (outcome (fnn-bps-persist-record service token record)))
         (fnn-bps-note service (fnn-core 'fn-bprc-publication-evidence outcome))
         (setq next
          (fnn-bps-step service (list :persist-result token outcome)))))
      (:cl-send
       (if (= (length effect) 7)
           (if *fnn-bps-forward-send*
               (funcall *fnn-bps-forward-send* effect)
             (fnn-indeterminate
              "bp-service: durable forward attempt lacks its session"))
         (setq next (fnn-bps-send-effect-next service effect))))
      (:forward-ready
       (fnn-out "BP forwarding result durable arrival=~d status=~(~a~)"
                (second effect) (third effect)))
      (:forward-answer
       (case (second effect)
         (:refused
          (fnn-bps-note service :refused))
         (:uncertain
          (fnn-bps-note service :fenced)
          (fnn-indeterminate "bp-service: forwarding publication uncertain"))))
      (:forward-stale
       (fnn-out "BP forwarding callback stale"))
      (:job-result-stale
       ;; The result names an attempt that is not the job's current one:
       ;; ACL2 settled nothing.
       (fnn-out "BP job result stale attempt=~a (settles nothing)" (third effect)))
      (:job-result-unnamed
       (fnn-fault "bp-service: a base transport result did not name its attempt"))
      (:forward-stranded
       ;; ACL2 decided the row reached the retry bound (spec 4.3.1); the
       ;; host only reports it.  The row, its attempt and its debt stay held.
       (fnn-out "BP forwarding stranded arrival=~d retries=~d (held; no session or restart re-offers it; bp-node resume re-arms it)"
                (second effect) (fourth effect)))
      (:forward-no-route
       ;; ACL2's routing gate (fn-bpnp-routed-start, spec 4.6) offered
       ;; nothing on this session: the row, its attempt state and its
       ;; obligation stay held.
       (fnn-out "BP forwarding no-route arrival=~d hop=~a decision=~(~a~) (held; the obligation stays)"
                (second effect) (third effect) (fourth effect)))
      (:resume-refused
       ;; ACL2's refusal of an operator resume (fn-bpnp-resume-refusal);
       ;; nothing was written.
       (fnn-bps-note service :refused)
       (fnn-out "BP forwarding resume refused arrival=~d reason=~(~a~)"
                (second effect) (third effect)))
      (:progress-wait
       (fnn-out "BP node progress waiting reason=~(~a~)" (third effect)))
      (:delivery-deferred
       ;; BP-R17: ACL2 kept the row held and :dispatch-pending; class 3
       ;; offers it again once the monotonic reading reaches the fourth field.
       (fnn-out "BP node delivery deferred busy=~d after=~d"
                (third effect) (fourth effect)))
      (:delivery-stranded
       ;; BP-R17 at the configured retry budget: still held, never refused.
       ;; The count is durable (kind 20): a restart does not re-arm it; ACL2
       ;; reports it on every progress event that selects nothing else.
       ;; The arrival an operator names to `bp-node resume' is the held
       ;; row's own (ACL2's lookup of the effect's key).
       (let ((row (fnn-core 'fn-bpnf-find-held (second effect)
                            (fnn-core 'fn-bpnf-held-list
                                      (fnn-bps-state service)))))
         (fnn-out "BP node delivery stranded busy=~d arrival=~a (held; bp-node resume re-arms it)"
                  (third effect) (fnn-core 'fn-bpn-nth 3 row))))
      (:delivery-resumed
       (fnn-out "BP node delivery resumed (busy count cleared)"))
      (:deferral-answer
       (case (second effect)
         (:refused
          (fnn-bps-note service :refused)
          (fnn-out "BP node busy count publication refused"))
         (otherwise
          (fnn-bps-note service :fenced)
          (fnn-indeterminate "bp-service: busy count publication uncertain"))))
      (:bundle-queue-accepted
       (fnn-out "BP queue accepted work=~a attempt=~a generation=~d status=~(~a~)"
                (fnn-octets-string (fnn-octets (second effect)))
                (fnn-octets-string (fnn-octets (third effect)))
                (fourth effect) (sixth effect)))
      (:bundle-queue-refused
       (fnn-bps-note service :refused)
       (fnn-out "BP queue refused reason=~(~a~)" (car (last effect))))
      (:bundle-queue-uncertain
       (fnn-bps-note service :fenced)
       (fnn-out "BP queue uncertain reason=~(~a~)" (car (last effect))))
      (:forward-refused
       ;; A one-shot verb that asked for the transfer (:process scope) takes
       ;; ACL2's word for the requeued record's reason; under :connection
       ;; scope the reading costs only that connection (spec 4.3.2).
       (when (eq (fnn-bps-transfer-scope service) :process)
         (fnn-bps-note service (fnn-core 'fn-bprc-effect-evidence effect)))
       (fnn-out "BP forwarding retained reason=~(~a~)" (car (last effect))))
      (:transport
       (fnn-out "BP transport work=~a status=~(~a~)"
                (fnn-octets-string (fnn-octets (second effect)))
                (fifth effect)))
      (:restart-fault
       (fnn-bps-note service :fenced)
       (if (eq (second effect) :clock-domain)
           (fnn-indeterminate "bp-service: restart fenced: clock domain ~(~a~)"
                              (third effect))
         (fnn-indeterminate "bp-service: restart fenced: ~(~a~)"
                            (second effect))))
      (:restart-ready
       (fnn-out "BP FNBS recovered held=~d" (second effect)))
      (:persist-checkpoint
       ;; (:persist-checkpoint EPOCH OP GENERATION CHECKPOINT): publish
       ;; ACL2's CHECKPOINT (fn-bpnr-rotation-checkpoint, whose operation
       ;; frontier is (EPOCH . OP)) as the selection of GENERATION, then
       ;; answer the machine with the program's outcome.
       (let* ((epoch (second effect))
              (operation-id (third effect))
              (outcome (fnn-bps-publish-generation service (fourth effect)
                                                   (fifth effect))))
         (fnn-bps-note service (fnn-core 'fn-bprc-publication-evidence outcome))
         (setq next
          (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      (:generation-selected
       (fnn-out "BP journal generation selected generation=~d" (second effect))
       ;; The selection is durable: retire what no recovery reads again.
       (fnn-bps-retire-generations service (second effect)))
      (:rotation-refused
       (fnn-bps-note service :refused)
       (fnn-out "BP journal rotation refused generation=~d" (second effect)))
      (:rotation-uncertain
       (fnn-bps-note service :fenced)
       (fnn-out "BP journal rotation uncertain generation=~d" (second effect)))
      (t nil))
    next))

;; Executes by a loop (lane depth-debt, PRF-919): an effect's answer used to be
;; driven by a nested call, one control-stack frame per publication in the
;; chain. Family reassembly itself now advances only on explicit scheduling
;; turns; :family-ready marks another family for a later turn. The
;; order is the recursion's: an effect's answer is driven completely before
;; the next effect of its list (a stack of the lists still to finish).
(defun fnn-bps-drive-effects (service effects)
  (let ((pending (list effects)))
    (loop while pending
          do (let ((current (pop pending)))
               (when (consp current)
                 (push (cdr current) pending)
                 (let ((next (fnn-bps-drive-effect service (car current))))
                   (when next (push next pending)))))))
  service)

(defun fnn-bps-rotation-test-stop (point)
  "Developer cut: stop this process at a named point of the rotation program
so a test can kill it there (N16)."
  (when (string= (or (fnn-developer-selector "FN_BP_ROTATION_TEST_STOP") "")
                 point)
    (fnn-out "BP journal rotation stopped at=~a" point)
    (finish-output)
    (sb-posix:kill (sb-posix:getpid) sb-unix:sigstop)))

(defun fnn-bps-retire-generations (service generation)
  "Remove the names ACL2 retires after GENERATION's selection is durable
(fn-bpnr-retired-names: older generation directories and a killed rotation's
staged selection files) by running ACL2's program fn-bpnr-retire-ops one
step at a time: each retired directory's files, the directory, then one root
barrier.  Every prefix of the program is a crash point of the model
(books/bp-node-retire.lisp fn-bpnr-retirement-cut-keeps-open-view): the
selection file, the selected directory and the other names the open reads
are unchanged at every cut, so a death or a failed step changes no recovery
and the next run (the next `bp-node checkpoint') finishes the removal.  A
failed step stops the program; the selection is already durable."
  (let* ((root (fnn-bps-root service))
         (limit (fnn-core 'fn-bpnf-namespace-max-entries))
         (names (fnn-list-directory-bounded root limit "bp journal root"))
         (retired (fnn-core 'fn-bpnr-retired-names names generation))
         (listings
           (loop for name in retired
                 for path = (fnn-join root name)
                 for st = (fnn-lstat path)
                 when (and st (not (fnn-symlink-p st)) (fnn-directory-p st))
                   collect (cons name (fnn-list-directory-bounded path limit name))))
         (ops (fnn-core 'fn-bpnr-retire-ops names listings generation))
         (step 0))
    (when retired
      (handler-case
          (dolist (op ops)
            (let ((kind (first op)))
              (case kind
                (:unlink-in
                 (let ((file (fnn-join (fnn-join root (second op)) (third op))))
                   (fnn-check-regular file)
                   (fnn-unlink file)))
                (:rmdir
                 (let ((dir (fnn-join root (second op))))
                   (fnn-fsync-dir dir)
                   (fnn-posix (dir) (sb-posix:rmdir dir))
                   (fnn-out "BP journal generation retired name=~a" (second op))))
                (:unlink
                 (let ((file (fnn-join root (second op))))
                   (fnn-check-regular file)
                   (fnn-unlink file)
                   (fnn-out "BP journal generation retired name=~a" (second op))))
                (:barrier (fnn-fsync-dir root))
                (otherwise
                 (fnn-fault "ACL2 returned an invalid retirement step"))))
            (incf step)
            (fnn-bps-rotation-test-stop (format nil "retire-~d" step)))
        (fnn-os-error (e)
          (fnn-out "BP journal generation retirement incomplete step=~d: ~a"
                   (1+ step) e))))))

(defun fnn-bps-publish-generation (service generation ck)
  "Publish CK, the checkpoint fn-bpnp-rotate-step proposed, as GENERATION's
selection file under ACL2's phase driver fn-bpnr-publish-action/-step/-outcome:
the generation directory and its barriers, then the staged selection file and
its barrier, the rename over the final name, and the root barrier.  Every
octet is ACL2's."
  (let* ((root (fnn-bps-root service))
         (jobs (fnn-bps-max-rows service))
         (octet-list (fnn-core 'fn-bpnr-checkpoint-octets
                               ck (fnn-core 'fn-bpnr-depth-budget jobs)))
         (octets (and octet-list (fnn-octets octet-list)))
         (dir (fnn-join root (fnn-core 'fn-bpnr-generation-directory generation)))
         (final (fnn-join root (fnn-core 'fn-bpnr-selection-name)))
         (stage (fnn-join root (format nil ".bp-generation-~d-~a"
                                       (sb-posix:getpid) (fnn-random-hex 12))))
         (phase :directory))
    (unless octets
      (fnn-indeterminate "bp-service: ACL2 refused the checkpoint octets"))
    (flet ((attempt (point thunk fail)
             (setq phase
                   (handler-case
                       (progn (funcall thunk)
                              (let ((next (fnn-core 'fn-bpnr-publish-step phase :ok)))
                                (fnn-bps-rotation-test-stop point)
                                next))
                     (fnn-os-error ()
                       (fnn-core 'fn-bpnr-publish-step phase fail))))))
      (unwind-protect
           (loop
             (case (fnn-core 'fn-bpnr-publish-action phase)
               (:make-directory
                (attempt "directory"
                         (lambda ()
                           (fnn-safe-directory dir t)
                           (fnn-fsync-dir dir)
                           (fnn-fsync-dir root))
                         :error))
               (:stage-and-file-barrier
                (attempt "stage" (lambda () (fnn-write-staged stage octets))
                         :known-fail))
               (:replace
                (attempt "replace" (lambda () (fnn-replace stage final)) :error))
               (:directory-barrier
                (attempt "barrier" (lambda () (fnn-fsync-dir root)) :error))
               (:done (return))
               (otherwise
                (fnn-fault "ACL2 returned an invalid rotation publication action"))))
        (ignore-errors (when (fnn-check-regular stage) (fnn-unlink stage)))))
    (fnn-core 'fn-bpnr-publish-outcome phase)))

(defconstant +fnn-bps-fragment-quantum+ 4096
  "Positions of the reassembly sweep one fn-bpfj-step walks
(books/bp-node-fragment-job fn-bpfj-step-is-bounded): the work of one
scheduling step, whatever the family holds.")

(defun fnn-bps-fragment-effects (service)
  "One resumable reassembly quantum and at most one family proposal.
The final :family event still asks ACL2 to reject a stale job; the host never
installs its reassembled image. A process death restarts from durable rows."
  (let* ((tally (fnn-bps-tally service))
         (observation (fnn-bp-observation
                       (fnn-bp-tally-wall tally)
                       (fnn-bp-tally-wall-error tally)))
         (carried (fnn-bps-fragment-pending service)))
    (unless carried
      (unless (fnn-bps-fragment-rescan service)
        (return-from fnn-bps-fragment-effects nil))
      (setf (fnn-bps-fragment-rescan service) nil)
      (let ((candidate (fnn-core 'fn-bpfj-next-candidate
                                 (fnn-bps-state service) observation
                                 (fnn-bps-fragment-tried service))))
        (unless (and (consp candidate) (eq (first candidate) :ready))
          (return-from fnn-bps-fragment-effects nil))
        (let* ((state (fnn-bps-state service))
               (arrival (second candidate))
               (anchor (fnn-core 'fn-bpnf-find-arrival arrival
                                 (fnn-core 'fn-bpnf-held-list state)))
               (job (fnn-core 'fn-bpfj-start state anchor))
               (limit (fnn-core 'fn-bpnpf-held-octets
                                (fnn-bps-profile service))))
          (setq carried (list arrival job limit (third candidate))))))
    (let* ((arrival (first carried))
           (job (second carried))
           (limit (third carried))
           (family-key (fourth carried)))
      (unless (eq (fnn-core 'fn-bpfj-finishedp job) t)
        (setq job (fnn-core 'fn-bpfj-step job +fnn-bps-fragment-quantum+)))
      (if (eq (fnn-core 'fn-bpfj-finishedp job) t)
          (progn
            (setf (fnn-bps-fragment-pending service) nil)
            (let ((effects (fnn-bps-foundation-step
                            service (list :family arrival observation job limit))))
              (push family-key (fnn-bps-fragment-tried service))
              (if effects
                  (setf (fnn-bps-fragment-job service) (cons job limit))
                ;; Refused/stale families cannot hide the next ready one.
                ;; Try that candidate in another turn, never in this one.
                (setf (fnn-bps-fragment-rescan service) t))
              effects))
        (progn
          (setf (fnn-bps-fragment-pending service) (list arrival job limit family-key))
          nil)))))

(defun fnn-bps-fragment-progress (service)
  (fnn-bps-drive-effects service (fnn-bps-fragment-effects service))
  service)

(defun fnn-bps-fragment-work-p (service)
  "Only a wakeup hint; ACL2 decides whether a family is enabled."
  (or (fnn-bps-fragment-pending service) (fnn-bps-fragment-rescan service)))

(defun fnn-bps-receive (service admission wire)
  "Return the ACL2-selected TCPCL disposition after kind-5 custody settles.
ADMISSION is ACL2's channel admission answer for this transfer
(fnn-bps-tcpcl-admission).  PRF-128: fn-bpaj-admitted-receive-event refuses
a bundle from a refused channel with the admission's reason, and only its
:ready answer reaches fnn-bps-foundation-step, so no custody is taken.
PRF-134: fn-bpnpf-admitted-receive-event applies the node's profile around
it: a wire past the profile's bundle octets is refused before it is decoded
and a bundle whose ADU is past the profile's ADU octets before custody, each
by name (books/bp-node-profile-admission)."
  (let* ((tally (fnn-bps-tally service))
         (observation
           (fnn-bp-observation (fnn-bp-tally-wall tally)
                                (fnn-bp-tally-wall-error tally)))
         (prepared
           (fnn-core 'fn-bpnpf-admitted-receive-event
                     (fnn-bps-profile service)
                     admission (fnn-bp-tally-config tally) wire observation)))
    (unless (eq (fnn-core 'fn-bpnf-receive-wire-readyp prepared) t)
      (return-from fnn-bps-receive (values prepared nil)))
    (let* ((event (fnn-core 'fn-bpnf-receive-wire-event-value prepared))
           ;; The admitted ingress the :ready event carries
           ;; (fn-bpaj-admitted-channel-receives-under-its-ingress).
           (ingress (fourth event))
           (adu (fnn-core 'fn-bpb-payload (second event)))
           (effects (fnn-bps-foundation-step service event))
           (path nil))
      (when (and (consp effects) (consp (car effects))
                 (eq (caar effects) :persist))
        (let* ((proposal (car effects))
               (epoch (second proposal))
               (operation-id (third proposal))
               (held (fourth proposal)))
          (unless (and (null (cdr effects)) (= (length proposal) 4))
            (fnn-indeterminate "bp-service: malformed kind-5 publication effect"))
          (multiple-value-bind (outcome final)
              (fnn-bps-persist-kind-five service epoch operation-id held)
            (setq path final
                  effects (fnn-bps-foundation-step
                           service (list :persist-result epoch operation-id
                                         outcome))))))
      ;; A conflicting reception (N11): the kind-14 record settles before
      ;; the callback takes the machine's final answer, as kind 5 does.
      (when (and (consp effects) (consp (car effects))
                 (eq (caar effects) :persist-conflict))
        (unless (null (cdr effects))
          (fnn-indeterminate "bp-service: malformed kind-14 publication effect"))
        (setq effects (fnn-bps-settle-conflict service (car effects))))
      (let ((result (fnn-core 'fn-bpnf-callback-result effects ingress path)))
        (when (eq (first result) :accepted)
          ;; The callback returns the durable custody disposition now. The
          ;; service advances reassembly only after TCPCL flushes that ACK.
          (setf (fnn-bps-fragment-rescan service) t
                (fnn-bps-fragment-tried service) nil))
        (when (eq (first result) :uncertain)
          (fnn-bps-note service :fenced))
        (when (eq (first result) :refused)
          (fnn-bps-note service :refused))
        (values result adu)))))

(defun fnn-bps-tcpcl-ingress
  (fnbs-state conn session-counter xfer-id owner channel)
  "The CL ingress ACL2 stamps for one transfer (anonymous when the channel
was refused), or NIL: the third element of fnn-bps-tcpcl-admission."
  (third (fnn-bps-tcpcl-admission fnbs-state conn session-counter xfer-id
                                  owner channel)))

(defun fnn-bps-tcpcl-admission
  (fnbs-state conn session-counter xfer-id owner channel)
  "ACL2's channel admission answer for one transfer, or NIL.  FNBS-STATE names
the epoch: bp-node's live FNBS state, or the initial state for bp-app
receive, which runs no FNBS machine."
  (let* ((negotiated
           (fnn-core 'fn-tcl-session-negotiated (fnn-tclc-session conn)))
         (announced
           (fnn-core 'fn-tcl-negotiated-peer-node-id negotiated))
         (answer (and owner channel
                      (fnn-owner-core 'fn-owner-bp-tcpcl-ingress
                                      fnbs-state
                                      session-counter xfer-id channel
                                      announced))))
    (when (and answer (eq (first answer) :refused))
      ;; The reason is ACL2's admission result.  Keep it visible at the
      ;; channel boundary without logging an identity or article octets.
      (fnn-out "BP channel admission refused reason=~(~a~)"
               (second answer)))
    answer))

(defvar *fnn-octets-bp* nil)

(defun fnn-live-octets-bp ()
  "The BP open's own octet buffer (books/bp-node-rotation-buffer.lisp
`fn-octets-bp', congruent to `fn-octets'); never the owner's buffer."
  (or *fnn-octets-bp*
      (setq *fnn-octets-bp*
            (or (cdr (assoc 'fn-octets-bp (user-stobj-alist *the-live-state*)))
                (fnn-fault "the BP octet buffer stobj is not in this image")))))

(defun fnn-bps-selection-plan (root profile)
  "ACL2's reading of the generation selection file: (:none), (:selected CK)
or (:damaged).  The read bound and decode budget are the profile's.  The
file's bytes go into `fn-octets-bp' as they are (one byte per octet) and
ACL2 reads them by index: fn-bpnrb-selection-plan, equal to
fn-bpnr-selection-plan over the buffer's octets
(fn-bpnrb-selection-plan-is-selection-plan)."
  (let* ((path (fnn-join root (fnn-core 'fn-bpnr-selection-name)))
         (jobs (first profile))
         (octets-bound (second profile))
         (present (fnn-check-regular path))
         (bytes (if present
                    (fnn-read-regular-bounded
                     path (fnn-core 'fn-bpnr-read-bound jobs octets-bound))
                    (make-array 0 :element-type '(unsigned-byte 8))))
         (st (fnn-live-octets-bp)))
    (fn-octets$c-reserve (length bytes) st)
    (replace (the fnn-octets (svref st 0)) bytes)
    (setf (svref st 1) (length bytes))
    (unwind-protect
         (fnn-core 'fn-bpnrb-selection-plan (and present t)
                   (fnn-core 'fn-bpnr-depth-budget jobs) st)
      ;; Empty the buffer and drop the file's array: the open reads it once.
      (setf (svref st 1) 0
            (svref st 0) (make-array 0 :element-type '(unsigned-byte 8))))))

(defun fnn-bps-open (journal config wall wall-error &optional held)
  "Open JOURNAL: take its shared journal lock and lifecycle lock, read the
profile and the generation selection, and recover.  HELD, when given, is a
service of this process that already holds both locks on JOURNAL
(fnn-bps-reopen-in-place): the recovery runs under them, takes neither
again and releases neither on a failure (HELD's owner does)."
  (let* ((profile-started (progn
                                 (unless (or held (eq (fnn-bps-release-observation) :closed))
                                   (fnn-indeterminate "bp-service: prior lock return remains unobserved"))
                                 (fnn-bp-profile-points)
                                 (get-internal-real-time)))
         (root (fnn-bp-journal-dir journal))
         ; Shared journal ownership precedes cleanup and the lifecycle lock.
         ; No live bp/tcpcl writer can lose its staging file to recovery.
         (spool-lock (if held
                         (fnn-bps-spool-lock held)
                         (fnn-tcl-spool-acquire root)))
         (service nil) (returned nil))
    (fnn-unwind-cleanups
        ((setq service (make-fnn-bps :root root :spool-lock spool-lock
                                      :lock-fd (and held (fnn-bps-lock-fd held))))
         (let* ((node-profile (fnn-bps-read-profile root))
         (profile (fnn-core 'fn-bpnpf-node-profile-base node-profile))
         (plan (let* ((selected (fnn-bps-selection-plan root profile))
                          (admission (fnn-core 'fn-bprpf-selection-admit
                                               selected profile)))
                     (unless (eq (first admission) :ready)
                       (fnn-indeterminate "bp-service: checkpoint profile refusal: ~a"
                                          (second admission)))
                     selected))
         (life (fnn-join root (fnn-core 'fn-bpnr-plan-directory plan)))
         ;; A reopen in place keeps the run's evidence (its tally).
         (tally (if held
                    (fnn-bps-tally held)
                    (make-fnn-bp-tally :config config :wall wall
                                       :wall-error wall-error
                                       :journal root :spool-lock spool-lock))))
        (progn
          (handler-case
              (progn
                (fnn-safe-directory life t)
                ;; Repeat the namespace-publication barrier on every recovery:
                ;; an earlier mkdir may have returned before its parent barrier
                ;; failed.
                (fnn-fsync-dir (fnn-parent life))
                ;; A prior record link may be visible even though its directory
                ;; barrier failed.  Establish that barrier before the restart
                ;; machine treats any final record as durable evidence.
                (fnn-fsync-dir life))
            (fnn-os-error (e)
              (fnn-indeterminate
               "bp-service: lifecycle namespace publication failed: ~a" e)))
          ;; Retain custody before evaluating the heavy ACL2 initial state.
          (unless held (setf (fnn-bps-lock-fd service) (fnn-bps-lock root)))
          (setf (fnn-bps-lifecycle service) life
                (fnn-bps-tally service) tally
                (fnn-bps-plan service) plan
                (fnn-bps-profile service) profile
                (fnn-bps-node-profile service) node-profile
                (fnn-bps-state service)
                (fnn-core 'fn-bpnf-initial-state
                          config (first profile) (second profile)))
          (unless (eq (fnn-core 'fn-bpn-machine-invariantp
                                (fnn-bps-base service)) t)
            (fnn-indeterminate "bp-service: invalid initial machine state"))
          (setf *fnn-bps-lifecycle-enumerations* 0)
          (multiple-value-bind (observed-names plan)
              (fnn-bps-namespace-plan service)
            (declare (ignore observed-names))
            (handler-case (fnn-fsync-dir root)
              (fnn-os-error (e)
                (fnn-indeterminate
                 "bp-service: clock domain namespace barrier failed: ~a" e)))
            (let* ((domain
                     (handler-case (fnn-bps-clock-domain-gate service plan)
                       (fnn-os-error (e)
                         (fnn-indeterminate
                          "bp-service: clock domain observation failed: ~a" e))))
                   (record-names
                     (fnn-core 'fn-bpnf-mixed-legacy-names plan))
                   (received-names
                     (fnn-core 'fn-bpnf-mixed-received-names plan))
                   (legacy-observed
                     (fnn-core 'fn-bpnf-mixed-legacy-observed plan))
                   (decoded (fnn-bps-read-records service record-names))
                   (recovery (fnn-core 'fn-bpn-host-lifecycle-recovery
                                       legacy-observed decoded)))
              (unless (eq (fnn-core 'fn-bpn-host-lifecycle-recovery-ready-p
                                    recovery) t)
                (fnn-indeterminate
                 "bp-service: lifecycle names do not bind decoded record tokens"))
              (let* ((records
                       (fnn-core 'fn-bpn-host-lifecycle-recovery-records recovery))
                     (rows (fnn-bps-read-received-rows service received-names))
                     (sequence (fnn-bps-sequence-ready service (and records t)))
                     ;; Seventh field: ACL2's boot-domain decision.  The
                     ;; machine fences unless it admits it (N07).
                     (event (append
                             ;; The generation selection plan, not the
                             ;; namespace plan bound above (N16 native run:
                             ;; passing the latter replayed the empty new
                             ;; generation without its checkpoint).
                             ;; The held projection's replay (lane
                             ;; bp-catalog): the octet total carried, not
                             ;; re-summed per row; equal to
                             ;; fn-bpnr-recover-auto-event by
                             ;; fn-bphp-recover-auto-event-is-bpnr.
                             (fnn-core 'fn-bprpf-admit-recovery
                               (fnn-core 'fn-bphp-recover-auto-event
                                         (fnn-bps-state service) records
                                         sequence rows (fnn-bps-plan service))
                               profile)
                             (list domain))))
                (setf (fnn-bps-recovery-event service) event)
                (setf (fnn-bps-stages service)
                      (fnn-core 'fn-bpn-host-lifecycle-recovery-stages recovery))
                (fnn-bps-drive-effects
                 service (fnn-bps-foundation-step service event))
                (fnn-out "BP queue recovered jobs=~d"
                         (fnn-core 'fn-bpnf-base-job-count
                                   (fnn-bps-state service)))
                (unless (eq (fnn-core 'fn-bpn-host-lifecycle-recovery-agrees-p
                                      recovery (fnn-bps-base service)) t)
                  (fnn-indeterminate
                   "bp-service: recovered namespace and machine frontier disagree"))
                (unless (eq (fnn-core 'fn-bpn-machine-invariantp
                                      (fnn-bps-base service)) t)
                  (fnn-indeterminate
                   "bp-service: recovered base machine invariant failed"))
                (fnn-bps-fragment-progress service)
                (fnn-bp-profile-open service profile-started)
                (setq returned t)
                service))))))
      ;; HELD owns both borrowed locks even if this recovery fails.
      ;; Release retains the actual service when physical return is uncertain.
      (when (and (not held) (not returned))
        (if service
            (fnn-bps-release service)
          (fnn-tcl-spool-release spool-lock))))))

(defun fnn-bps-reopen-in-place (service journal config wall wall-error)
  "Recover JOURNAL again into SERVICE, under the locks SERVICE holds (no
other process can take the journal in between): the recovery fnn-bps-open
runs, over whatever is durable (the new selection after a rotation).  The
fields a recovery decides are replaced (state, plan, recovery event,
profile, the lifecycle namespace, the stages; the contact frontiers are
empty, as at every open); the run's evidence, its session counter, its
routing and its transfer scope stay, so the callers that captured SERVICE
(the serve loop's deliver closure) see the reopened journal.  A failure
signals with SERVICE still holding its locks; its owner releases them."
  (let ((fresh (fnn-bps-open journal config wall wall-error service)))
    (setf (fnn-bps-root service) (fnn-bps-root fresh)
          (fnn-bps-lifecycle service) (fnn-bps-lifecycle fresh)
          (fnn-bps-state service) (fnn-bps-state fresh)
          (fnn-bps-stages service) (fnn-bps-stages fresh)
          (fnn-bps-plan service) (fnn-bps-plan fresh)
          (fnn-bps-recovery-event service) (fnn-bps-recovery-event fresh)
          (fnn-bps-profile service) (fnn-bps-profile fresh)
          (fnn-bps-node-profile service) (fnn-bps-node-profile fresh)
          (fnn-bps-fragment-job service) (fnn-bps-fragment-job fresh)
          (fnn-bps-fragment-pending service) (fnn-bps-fragment-pending fresh)
          (fnn-bps-fragment-rescan service) (fnn-bps-fragment-rescan fresh)
          (fnn-bps-fragment-tried service) (fnn-bps-fragment-tried fresh)
          (fnn-bps-cursors service) nil
          (fnn-bps-transfer service) nil
          (fnn-bps-expected service) nil)
    service))

;;; Routing (spec bp-node-machine 4.6; books/bp-route-jobs.lisp and
;;; books/bp-node-contact-driver.lisp).  The Store's table is read once,
;;; under the owner, for a verb that holds no owner of its own.
;;; Served BP commands use the same independently captured DEFAULT pool as
;;; NNTP/HTTP. The BP session bank remains a separate grant for socket/source
;;; contexts; it does not authorize decoded Store reads.
(defstruct fnn-bp-served-owner-custody claimed started stopped)

(defun fnn-bp-served-owner-start (custody root max-connections)
  (let ((root (fnn-absolute root)))
  (fnn-owner-claim-run-authority *fnn-owner-caller-reservation*)
  (setf (fnn-bp-served-owner-custody-claimed custody) t)
  (fnn-owner-page-read-startup
   root max-connections nil nil
   (lambda () (setf (fnn-bp-served-owner-custody-started custody) t)))
  (let ((service (fnn-owner-install root max-connections)))
    ;; Retain the actual Store even if retiring recovery-only borrows escapes.
    (fnn-owner-retain-run-authority service)
    (fnn-extent-end-recovery-cache)
    service)))

(defun fnn-bp-served-owner-stop (custody service)
  (when (fnn-bp-served-owner-custody-claimed custody)
    ;; Mark held BEFORE a join that can escape. Failed installation may have
    ;; retained its actual Store before returning SERVICE to this caller.
    (fnn-owner-store-settlement service :held)
    (when (fnn-bp-served-owner-custody-started custody)
      (let ((actual (or service
                       (and (fnn-owner-service-p *fnn-owner-retained-service*)
                            *fnn-owner-retained-service*))))
        (if actual (fnn-owner-cold-shutdown actual)
          (fnn-extent-executor-stop))))
    ;; Only a normal physical return records termination. Timeout/escape
    ;; cannot turn this bit on or relinquish the retained service carrier.
    (setf (fnn-bp-served-owner-custody-stopped custody) t)))

(defun fnn-bp-served-owner-settle (custody service roots-ready)
  (when (fnn-bp-served-owner-custody-claimed custody)
    (let ((settlement
            (fnn-core 'fn-ort-service-settlement-action
                      (if roots-ready :joined :held)
                      (if (fnn-bp-served-owner-custody-stopped custody)
                          :closed :unobserved))))
      (unless (eq (fnn-owner-store-settlement service settlement) :joined)
        (fnn-indeterminate "BP served owner physical or publication custody remains held")))))

(defun fnn-bps-read-route-table (store-root)
  (let ((owner (fnn-owner-install store-root 1)))
    (fnn-unwind-cleanups ((fnn-owner-core 'fn-owner-bp-route-table))
      (fnn-owner-feed-close-all owner)
      (fnn-store-close (fnn-owner-service-store owner)))))

(defun fnn-bps-use-store-routes (service store-root)
  (when store-root
    (setf (fnn-bps-routing service)
          (list :table (fnn-bps-read-route-table store-root))))
  service)

(defun fnn-bps-queue-route (service peer node-id transfer-mru default-host
                            default-port)
  "Queue time.  With routing in force, ACL2's route to PEER's routed hop
(fn-bprt-job-route), or nil when the table routes PEER nowhere: the job is
not queued and its obligation stays owed where it is.  Without routing, the
address the verb was given."
  (let ((node (fnn-octet-list (fnn-string-octets node-id)))
        (text (fnn-core 'fn-bpaj-eid-text peer)))
    (if (fnn-bps-routing service)
        (let ((route (fnn-core 'fn-bprt-job-route text
                               (second (fnn-bps-routing service))
                               node +fnn-tcl-keepalive+ +fnn-tcl-segment-mru+
                               transfer-mru)))
          (if route
              (fnn-out "BP queue route destination=~a port=~d" text (third route))
            (fnn-out "BP queue route destination=~a decision=~(~a~) (not queued; the obligation stays)"
                     text (first (fnn-core 'fn-bprt-outbound-choice text
                                           (second (fnn-bps-routing service))))))
          route)
      (list :route (fnn-octet-list (fnn-string-octets default-host))
            default-port node +fnn-tcl-keepalive+ +fnn-tcl-segment-mru+
            transfer-mru))))

(defun fnn-bpc-drive-contact (service event)
  "Drive one contact EVENT, (:contact PEER OPEN).  An opening contact asks
ACL2 before every offer (fn-bpnjc-contact-next, books/bp-node-job-cursor.lisp:
the answer of fn-bpnj-contact-next, the first READY queued job, so a held or
already-offered older job never starves a younger one, read from the
contact's cursor instead of the head of the job list,
fn-bpnjc-contact-next-is-the-head-scan): it names the event to drive
through fn-bpnp-step and the hop's node ID, holds a job its routing refuses,
or closes the contact.  ACL2 threads the keys this contact has offered and
the cursor, so a job whose transfer was not accepted (requeued) waits for the
next contact (fn-bpnj-contact-offers-each-job-at-most-once) and the contact
examines each job once (fn-bpnjc-drain-visits-are-linear).  The contact
opens at the peer's frontier (fn-bpnjc-contact-cursor) and its close
advances it (fn-bpnjc-contact-close).  Answers the list of ACL2's answers,
first first."
  (setf (fnn-bps-transfer service) nil)
  (let ((peer (second event)) (offered nil) (answers nil) (cursor nil))
    (when (third event)
      (setq cursor (fnn-core 'fn-bpnjc-contact-cursor (fnn-bps-cursors service) peer))
      (loop repeat (fnn-bps-max-rows service)
            for result = (fnn-core 'fn-bpnjc-contact-next (fnn-bps-state service)
                                   peer (fnn-bps-routing service) offered cursor)
            for answer = (car result)
            do (setq cursor (cdr result))
               (push answer answers)
               (case (first answer)
                 (:offer
                  (setq offered (third answer))
                  (setf (fnn-bps-expected service) (fourth answer))
                  (unwind-protect
                       (fnn-bps-drive-effects
                        service (fnn-bps-foundation-step service (second answer)))
                    (setf (fnn-bps-expected service) nil))
                  (when (fourth answer)
                    (fnn-out "BP queued job routed peer=~a expected=~a"
                             (fnn-core 'fn-bpaj-eid-text peer) (fourth answer))))
                 (:held
                  (fnn-out "BP queued job held destination=~a decision=~(~a~) (the job and its obligation stay)"
                           (fnn-core 'fn-bpaj-eid-text peer) (third answer))
                  (loop-finish))
                 (t (loop-finish))))
      (setf (fnn-bps-cursors service)
            (fnn-core 'fn-bpnjc-contact-close (fnn-bps-cursors service)
                      (fnn-bps-state service) peer cursor)))
    (fnn-bps-drive-effects service (fnn-bps-step service (list :contact peer nil)))
    (reverse answers)))

(defun fnn-bps-attempt-ready (service)
  ;; Expiry changes only the BP job's lifecycle status.  The record retains
  ;; its exact bundle bytes and this layer has no archive-release effect.
  (let ((obs (fnn-bp-observation (fnn-bp-tally-wall (fnn-bps-tally service))
                                 (fnn-bp-tally-wall-error
                                  (fnn-bps-tally service)))))
    (loop repeat (fnn-bps-max-rows service)
          for effects = (fnn-bps-step service (list :clock obs))
          while effects do (fnn-bps-drive-effects service effects)))
  (dolist (peer (fnn-core 'fn-bpn-host-ready-peers (fnn-bps-base service)))
    (fnn-bpc-drive-contact service (list :contact peer t)))
  service)

(defun fnn-bps-exit-code (service)
  "ACL2's code for the run's evidence (fn-bprc-run-exit-code)."
  (fnn-core 'fn-bprc-run-exit-code (fnn-bp-run-evidence (fnn-bps-tally service))))

(defun fnn-command-bp-service-run (host port adu-path journal node-id peer-id
                                   work attempt generation lifetime crc-type
                                   hop-limit transfer-mru wall wall-error)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (peer (fnn-bp-eid peer-id))
         (service (fnn-bps-open journal config wall wall-error)))
    (fnn-unwind-cleanups
        ((let* ((adu (fnn-octet-list (fnn-read-regular-bounded adu-path transfer-mru)))
                (obs (fnn-bp-observation wall wall-error))
                (work-octets (fnn-octet-list (fnn-string-octets work)))
                (attempt-octets (fnn-octet-list (fnn-string-octets attempt)))
                (existing (fnn-core 'fn-bpn-host-existing-sequence
                                    (fnn-bps-base service) work-octets
                                    attempt-octets generation))
                ;; Allocation has crossed W12's file and directory barriers
                ;; before this sequence enters fn-bpn-step.
                (sequence
                 (if (eq (fnn-core 'fn-bpn-host-existing-sequence-p existing) t)
                     (fnn-core 'fn-bpn-host-existing-sequence-value existing)
                   (fnn-bp-reserve-sequence (fnn-bps-tally service))))
                (route (list :route
                             (fnn-octet-list (fnn-string-octets host)) port
                             (fnn-octet-list (fnn-string-octets node-id))
                             +fnn-tcl-keepalive+ +fnn-tcl-segment-mru+ transfer-mru))
                (event (list :enqueue
                             work-octets attempt-octets
                             generation sequence route peer adu obs)))
           (fnn-bps-drive-effects service (fnn-bps-step service event))
           (fnn-bps-attempt-ready service)
           (fnn-bps-exit-code service)))
      (fnn-bps-release service))))

(defun fnn-command-bp-service-resume (journal node-id lifetime crc-type
                                      hop-limit transfer-mru wall wall-error
                                      &optional store-root)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (service (fnn-bps-open journal config wall wall-error)))
    (fnn-unwind-cleanups
        ((progn
           ;; [STORE]: route the queued jobs by that Store's bp-route table.
           (fnn-bps-use-store-routes service store-root)
           (fnn-bps-attempt-ready service)
           (fnn-bps-exit-code service)))
      (fnn-bps-release service))))

(defun fnn-command-bp-service-inspect-received (frame-path adu-out)
  "Read-only, ACL2-decoded evidence projection of a kind-5 FNBS frame."
  (let* ((frame (fnn-octet-list
                 (fnn-read-regular-bounded
                  frame-path (fnn-core 'fn-bpnf-stored-frame-limit))))
         (result (fnn-core 'fn-bpnf-inspect-adu frame)))
    (unless (eq (fnn-core 'fn-bpnf-inspect-readyp result) t)
      (fnn-refuse "bp-service: invalid received FNBS frame"))
    (let ((adu (fnn-core 'fn-bpnf-inspect-value result)))
      (fnn-write-staged adu-out (fnn-octets adu))
      (fnn-out "BP FNBS inspect adu=~d" (length adu))
      +fnn-exit-ok+)))

(defun fnn-dispatch-bp-service (command args)
  (flet ((need (n)
           (when (< (length args) n)
             (error 'fnn-usage-error :message "bp-service: missing arguments")))
         (arg (index &optional default)
           (fnn-tcl-arg args index default))
         (number (index default)
           (fnn-tcl-number (fnn-tcl-arg args index) default))
         (optional-number (index)
           (let ((text (fnn-tcl-arg args index)))
             (and text (parse-integer text)))))
    (cond
      ((string= command "run")
       (need 9)
       (fnn-command-bp-service-run
        (first args) (parse-integer (second args)) (third args) (fourth args)
        (fifth args) (sixth args) (seventh args) (eighth args)
        (parse-integer (ninth args))
        (number 9 +fnn-bp-lifetime+) (number 10 +fnn-bp-crc-type+)
        (number 11 +fnn-bp-hop-limit+) (number 12 +fnn-tcl-transfer-mru+)
        (optional-number 13) (number 14 0)))
      ((string= command "resume")
       (need 2)
       (fnn-command-bp-service-resume
        (first args) (second args)
        (number 2 +fnn-bp-lifetime+) (number 3 +fnn-bp-crc-type+)
        (number 4 +fnn-bp-hop-limit+) (number 5 +fnn-tcl-transfer-mru+)
        (optional-number 6) (number 7 0) (arg 8)))
      ((string= command "inspect-received")
       (need 2)
       (fnn-command-bp-service-inspect-received (first args) (second args)))
      (t (error 'fnn-usage-error
                :message (format nil "unknown bp-service command ~a" command))))))

(fnn-register-verb "bp-service" (fnn-bp-verb #'fnn-dispatch-bp-service))
