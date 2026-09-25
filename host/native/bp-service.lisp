;;; Durable BP node service for outbound work and received FNBS custody.
;;;
;;; Every decision is fn-bpnf-step.  This adapter observes files, persistence
;;; barriers, sockets and TCPCL outcomes, then reports those observations back
;;; to the step function.  A TCPCL outcome never deletes bundle bytes or emits
;;; an fn archive/application receipt.

(in-package "ACL2")

(defstruct fnn-bps
  root lifecycle tally state spool-lock lock-fd (stages nil)
  (next-session 0) (outcome :accepted))

; Bound only during a negotiated outbound TCPCL contact.  The ACL2 effect
; supplies the exact image after immutable kind-8 publication.
(defvar *fnn-bps-forward-send* nil)

(defvar *fnn-bps-lifecycle-enumerations* 0)

(defun fnn-bps-lock (root)
  (let ((fd (fnn-open (fnn-join root "lifecycle.lock")
                      (logior sb-posix:o-rdwr sb-posix:o-creat +fnn-o-nofollow+)
                      #o600)))
    (unless (fnn-regular-p (fnn-fstat fd))
      (fnn-close fd)
      (fnn-fault "bp-service: refusing non-regular lifecycle lock"))
    (handler-case (fnn-flock fd (logior +fnn-lock-ex+ +fnn-lock-nb+))
      (fnn-os-error (e)
        (fnn-close fd)
        (if (= (fnn-os-errno e) sb-posix:eagain)
            (fnn-refuse "bp-service: lifecycle queue is already locked")
          (fnn-fault "bp-service: cannot establish lifecycle ownership: ~a" e))))
    fd))

(defun fnn-bps-release (service)
  (let ((fd (fnn-bps-lock-fd service)))
    (when fd
      (ignore-errors (fnn-flock fd +fnn-lock-un+))
      (fnn-close fd)
      (setf (fnn-bps-lock-fd service) nil)))
  ; Release in reverse acquisition order: lifecycle, then the shared journal
  ; owner lock used by tcpcl, bp send/receive, and this service.
  (fnn-tcl-spool-release (fnn-bps-spool-lock service))
  (setf (fnn-bps-spool-lock service) nil))

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
           (fnn-core 'fn-bpnf-clock-domain-legacy-evidence
                     namespace-plan (and sequence-frontier t)))
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
             (raw (fnn-read-regular-bounded path limit)))
        (push (list name (fnn-octet-list raw)) rows)))))

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
  (unless (eq (fnn-core 'fn-bpnp-host-eventp event) t)
    (fnn-indeterminate "bp-service: malformed foundation event"))
  (let ((answer (fnn-core 'fn-bpnp-step
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
    (unless frame
      (fnn-fault "bp-service: ACL2 refused its pending lifecycle record"))
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
    (when (eq outcome :uncertain)
      (setf (fnn-bps-outcome service) :uncertain))
    (fnn-bps-foundation-step
     service (list :persist-result epoch operation-id outcome))))

(defun fnn-bps-route-host (route) (fnn-octets-string (fnn-octets (second route))))
(defun fnn-bps-route-port (route) (third route))
(defun fnn-bps-route-node (route) (fnn-octets-string (fnn-octets (fourth route))))
(defun fnn-bps-route-keepalive (route) (fifth route))
(defun fnn-bps-route-segment-mru (route) (sixth route))
(defun fnn-bps-route-transfer-mru (route) (seventh route))

(defun fnn-bps-send-effect (service effect)
  (let* ((route (second effect))
         (key (fourth effect))
         (wire (fifth effect))
         (socket nil)
         (outcome :uncertain))
    (handler-case
        (unwind-protect
             (progn
               ; Test-only exact core/adapter fault.  It is inside the same
               ; handler as real send-path failures so the regression proves
               ; that a fault is never collapsed into transport uncertainty.
               (when (string= (or (fnn-developer-selector "FN_BP_SERVICE_TEST_SEND_FAULT") "") "1")
                 (fnn-fault "bp-service: injected send core fault"))
               (setq socket (fnn-tcl-connect (fnn-bps-route-host route)
                                             (fnn-bps-route-port route)))
               (let ((conn (fnn-tcl-session
                            (fnn-socket-fd socket) :active
                            (fnn-tcl-params
                             (fnn-bps-route-node route) nil
                             (fnn-bps-route-keepalive route)
                             (fnn-bps-route-segment-mru route)
                             (fnn-bps-route-transfer-mru route))
                            "bp-service" (fnn-bps-root service)
                            :bundle wire :expect 0)))
                 (setq outcome (or (fnn-tclc-outcome conn) :uncertain))))
          (when socket (fnn-socket-shut socket)))
      (fnn-store-fault (e) (error e))
      ((or fnn-os-error sb-bsd-sockets:socket-error fnn-store-error) ()
        (setq outcome :uncertain)))
    (when (eq outcome :uncertain) (setf (fnn-bps-outcome service) :uncertain))
    (when (eq outcome :refused)
      (unless (eq (fnn-bps-outcome service) :uncertain)
        (setf (fnn-bps-outcome service) :refused)))
    (fnn-bps-drive-effects service
                           (fnn-bps-step service (list :forward-result key outcome)))))

(defun fnn-bps-drive-effects (service effects)
  (dolist (effect effects)
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
         (when (eq outcome :uncertain)
           (setf (fnn-bps-outcome service) :uncertain))
         (fnn-bps-drive-effects
          service (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      (:dispatch-ready
       (fnn-out "BP received carrier dispatch durable"))
      (:dispatch-answer
       (case (second effect)
         (:refused
          (unless (eq (fnn-bps-outcome service) :uncertain)
            (setf (fnn-bps-outcome service) :refused))
          (fnn-out "BP received carrier dispatch refused"))
         (otherwise
          (setf (fnn-bps-outcome service) :uncertain)
          (fnn-indeterminate "bp-service: dispatch publication uncertain"))))
      (:persist-conflict
       (fnn-bps-drive-effects service (fnn-bps-settle-conflict service effect)))
      (:persist-delete
       (unless (= (length effect) 4)
         (fnn-indeterminate "bp-service: malformed kind-10 publication effect"))
       (let* ((epoch (second effect))
              (operation-id (third effect))
              (record (fourth effect))
              (outcome
                (fnn-bps-persist-kind-ten
                 service epoch operation-id record)))
         (when (eq outcome :uncertain)
           (setf (fnn-bps-outcome service) :uncertain))
         (fnn-bps-drive-effects
          service (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      (:delete-ready
       (fnn-out "BP held carrier deletion durable arrival=~d" (second effect)))
      (:delete-answer
       (case (second effect)
         (:refused
          (unless (eq (fnn-bps-outcome service) :uncertain)
            (setf (fnn-bps-outcome service) :refused))
          (fnn-out "BP held carrier deletion refused"))
         (otherwise
          (setf (fnn-bps-outcome service) :uncertain)
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
         (when (eq outcome :uncertain)
           (setf (fnn-bps-outcome service) :uncertain))
         (fnn-bps-drive-effects
          service (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      (:family-ready
       (fnn-out "BP fragment family durable")
       (fnn-bps-fragment-progress service))
      (:family-answer
       (case (second effect)
         (:refused (fnn-out "BP fragment family publication refused"))
         (otherwise
          (setf (fnn-bps-outcome service) :uncertain)
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
         (when (eq outcome :uncertain)
           (setf (fnn-bps-outcome service) :uncertain))
         (fnn-bps-drive-effects
          service (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      ((:persist-attempt :persist-forward-result)
       (unless (= (length effect) 4)
         (fnn-indeterminate "bp-service: malformed forward publication effect"))
       (let* ((epoch (second effect))
              (operation-id (third effect))
              (record (fourth effect))
              (outcome (fnn-bps-persist-forward
                        service epoch operation-id record)))
         (when (eq outcome :uncertain)
           (setf (fnn-bps-outcome service) :uncertain))
         (fnn-bps-drive-effects
          service (fnn-bps-foundation-step
                   service (list :persist-result epoch operation-id outcome)))))
      (:deliver
       (fnn-fault "bp-service: application delivery requires the owner caller"))
      (:delivery-answer
       (case (second effect)
         (:durable (fnn-out "BP application handoff durable"))
         (:refused
          (unless (eq (fnn-bps-outcome service) :uncertain)
            (setf (fnn-bps-outcome service) :refused))
          (fnn-out "BP application handoff refused"))
         (otherwise
          (setf (fnn-bps-outcome service) :uncertain)
          (fnn-indeterminate "bp-service: application handoff uncertain"))))
      (:persist
       (let* ((token (second effect))
              (record (third effect))
              (outcome (fnn-bps-persist-record service token record)))
         (when (eq outcome :uncertain)
           (setf (fnn-bps-outcome service) :uncertain))
         (fnn-bps-drive-effects
          service (fnn-bps-step service (list :persist-result token outcome)))))
      (:cl-send
       (if (= (length effect) 7)
           (if *fnn-bps-forward-send*
               (funcall *fnn-bps-forward-send* effect)
             (fnn-indeterminate
              "bp-service: durable forward attempt lacks its session"))
         (fnn-bps-send-effect service effect)))
      (:forward-ready
       (fnn-out "BP forwarding result durable arrival=~d status=~(~a~)"
                (second effect) (third effect)))
      (:forward-answer
       (case (second effect)
         (:refused
          (unless (eq (fnn-bps-outcome service) :uncertain)
            (setf (fnn-bps-outcome service) :refused)))
         (:uncertain
          (setf (fnn-bps-outcome service) :uncertain)
          (fnn-indeterminate "bp-service: forwarding publication uncertain"))))
      (:forward-stale
       (fnn-out "BP forwarding callback stale"))
      (:forward-stranded
       ;; ACL2 decided the row reached the retry bound (spec 4.3.1); the
       ;; host only reports it.  The row, its attempt and its debt stay held.
       (fnn-out "BP forwarding stranded arrival=~d retries=~d (held; no session or restart re-offers it; bp-node resume re-arms it)"
                (second effect) (fourth effect)))
      (:resume-refused
       ;; ACL2's refusal of an operator resume (fn-bpnp-resume-refusal);
       ;; nothing was written.
       (unless (eq (fnn-bps-outcome service) :uncertain)
         (setf (fnn-bps-outcome service) :refused))
       (fnn-out "BP forwarding resume refused arrival=~d reason=~(~a~)"
                (second effect) (third effect)))
      (:progress-wait
       (fnn-out "BP node progress waiting reason=~(~a~)" (third effect)))
      (:bundle-queue-accepted
       (fnn-out "BP queue accepted work=~a attempt=~a generation=~d status=~(~a~)"
                (fnn-octets-string (fnn-octets (second effect)))
                (fnn-octets-string (fnn-octets (third effect)))
                (fourth effect) (sixth effect)))
      (:bundle-queue-refused
       (unless (eq (fnn-bps-outcome service) :uncertain)
         (setf (fnn-bps-outcome service) :refused))
       (fnn-out "BP queue refused reason=~(~a~)" (car (last effect))))
      (:bundle-queue-uncertain
       (setf (fnn-bps-outcome service) :uncertain)
       (fnn-out "BP queue uncertain reason=~(~a~)" (car (last effect))))
      (:forward-refused
       (fnn-out "BP forwarding retained reason=~(~a~)" (car (last effect))))
      (:transport
       (fnn-out "BP transport work=~a status=~(~a~)"
                (fnn-octets-string (fnn-octets (second effect)))
                (fifth effect)))
      (:restart-fault
       (setf (fnn-bps-outcome service) :uncertain)
       (if (eq (second effect) :clock-domain)
           (fnn-indeterminate "bp-service: restart fenced: clock domain ~(~a~)"
                              (third effect))
         (fnn-indeterminate "bp-service: restart fenced: ~(~a~)"
                            (second effect))))
      (:restart-ready
       (fnn-out "BP FNBS recovered held=~d" (second effect)))
      (t nil)))
  service)

(defun fnn-bps-fragment-progress (service)
  ;; The ACL2 selector chooses an exact ready family from the one held list.
  ;; Each durable :family-ready retires at least one fragment and invokes
  ;; this once more; a refusal/uncertainty does not loop.
  (let* ((tally (fnn-bps-tally service))
         (observation (fnn-bp-observation
                       (fnn-bp-tally-wall tally)
                       (fnn-bp-tally-wall-error tally)))
         (candidate (fnn-core 'fn-bpnf-family-next
                              (fnn-bps-state service) observation)))
    (when (and (consp candidate) (eq (first candidate) :ready))
      (fnn-bps-drive-effects
       service (fnn-bps-foundation-step
                service (list :family (second candidate) observation)))))
  service)

(defun fnn-bps-receive (service ingress wire)
  "Return the ACL2-selected TCPCL disposition after kind-5 custody settles."
  (let* ((tally (fnn-bps-tally service))
         (observation
           (fnn-bp-observation (fnn-bp-tally-wall tally)
                                (fnn-bp-tally-wall-error tally)))
         (prepared
           (fnn-core 'fn-bpnf-receive-wire-event
                     (fnn-bp-tally-config tally) wire observation ingress)))
    (unless (eq (fnn-core 'fn-bpnf-receive-wire-readyp prepared) t)
      (return-from fnn-bps-receive (values prepared nil)))
    (let* ((event (fnn-core 'fn-bpnf-receive-wire-event-value prepared))
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
          (fnn-bps-fragment-progress service))
        (when (eq (first result) :uncertain)
          (setf (fnn-bps-outcome service) :uncertain))
        (when (eq (first result) :refused)
          (unless (eq (fnn-bps-outcome service) :uncertain)
            (setf (fnn-bps-outcome service) :refused)))
        (values result adu)))))

(defun fnn-bps-tcpcl-ingress
  (fnbs-state conn session-counter xfer-id owner channel)
  "The CL ingress ACL2 admits for one transfer, or NIL.  FNBS-STATE names the
epoch: bp-node's live FNBS state, or the initial state for bp-app receive,
which runs no FNBS machine."
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
    (third answer)))

(defun fnn-bps-open (journal config wall wall-error)
  (let* ((root (fnn-bp-journal-dir journal))
         ; Shared journal ownership precedes cleanup and the lifecycle lock.
         ; No live bp/tcpcl writer can lose its staging file to recovery.
         (spool-lock (fnn-tcl-spool-acquire root))
         (life (fnn-join root "lifecycle"))
         (tally (make-fnn-bp-tally :config config :wall wall :wall-error wall-error
                                   :journal root :spool-lock spool-lock))
         (service nil))
    (handler-case
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
          (setq service
                (make-fnn-bps
                 :root root :lifecycle life :tally tally
                 :spool-lock spool-lock :lock-fd (fnn-bps-lock root)
                 :state (fnn-core 'fn-bpnf-initial-state
                                  config
                                  (fnn-core 'fn-bpn-host-machine-max-jobs)
                                  (fnn-core 'fn-bpn-host-machine-max-octets))))
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
                             (fnn-core 'fn-bpnf-family-recover-auto-event
                                       (fnn-bps-state service) records
                                       sequence rows)
                             (list domain))))
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
                service))))
      (error (e)
        (if service
            (fnn-bps-release service)
          (fnn-tcl-spool-release spool-lock))
        (error e)))))

(defun fnn-bps-attempt-ready (service)
  ;; Expiry changes only the BP job's lifecycle status.  The record retains
  ;; its exact bundle bytes and this layer has no archive-release effect.
  (let ((obs (fnn-bp-observation (fnn-bp-tally-wall (fnn-bps-tally service))
                                 (fnn-bp-tally-wall-error
                                  (fnn-bps-tally service)))))
    (loop repeat (fnn-core 'fn-bpn-host-machine-max-jobs)
          for effects = (fnn-bps-step service (list :clock obs))
          while effects do (fnn-bps-drive-effects service effects)))
  (dolist (peer (fnn-core 'fn-bpn-host-ready-peers (fnn-bps-base service)))
    (fnn-bps-drive-effects service (fnn-bps-step service (list :contact peer t))))
  service)

(defun fnn-bps-exit-code (service)
  (case (fnn-bps-outcome service)
    (:accepted +fnn-exit-ok+)
    (:refused +fnn-exit-refused+)
    (t +fnn-exit-uncertain+)))

(defun fnn-command-bp-service-run (host port adu-path journal node-id peer-id
                                   work attempt generation lifetime crc-type
                                   hop-limit transfer-mru wall wall-error)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (peer (fnn-bp-eid peer-id))
         (service (fnn-bps-open journal config wall wall-error)))
    (unwind-protect
         (let* ((adu (fnn-octet-list (fnn-read-regular-bounded adu-path transfer-mru)))
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
           (fnn-bps-exit-code service))
      (fnn-bps-release service))))

(defun fnn-command-bp-service-resume (journal node-id lifetime crc-type
                                      hop-limit transfer-mru wall wall-error)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (service (fnn-bps-open journal config wall wall-error)))
    (unwind-protect
         (progn (fnn-bps-attempt-ready service) (fnn-bps-exit-code service))
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
        (optional-number 6) (number 7 0)))
      ((string= command "inspect-received")
       (need 2)
       (fnn-command-bp-service-inspect-received (first args) (second args)))
      (t (error 'fnn-usage-error
                :message (format nil "unknown bp-service command ~a" command))))))

(fnn-register-verb "bp-service" #'fnn-dispatch-bp-service)
