;;; Durable outbound BP queue service.
;;;
;;; Every decision is fn-bpn-step.  This adapter observes files, persistence
;;; barriers, sockets and TCPCL outcomes, then reports those observations back
;;; to the step function.  A TCPCL outcome never deletes bundle bytes or emits
;;; an fn archive/application receipt.

(in-package "ACL2")

(defstruct fnn-bps
  root lifecycle tally state spool-lock lock-fd (stages nil) (outcome :accepted))

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
             (string= (or (sb-ext:posix-getenv
                           "FN_BP_SERVICE_TEST_FAIL_SECOND_LIFECYCLE_ENUMERATION") "")
                      "1"))
    (fnn-fault "bp-service: lifecycle namespace was enumerated after recovery"))
  (let* ((limit (fnn-core 'fn-bpn-host-lifecycle-max-namespace-entries)))
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
         (plan (fnn-core 'fn-bpn-host-lifecycle-namespace-plan names)))
      (unless (eq (fnn-core 'fn-bpn-host-lifecycle-plan-ready-p plan) t)
        (fnn-indeterminate "bp-service: ACL2 rejected lifecycle namespace"))
      (values names plan))))

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

(defun fnn-bps-step (service event)
  ;; Assurance subject: this is the host call to fn-bpn-step, with no sibling
  ;; dispatcher between the native service and the proved transition.
  (let ((answer (fnn-core 'fn-bpn-step (fnn-bps-state service) event)))
    (setf (fnn-bps-state service)
          (fnn-core 'fn-bpn-host-answer-state answer))
    (fnn-core 'fn-bpn-host-answer-effects answer)))

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
    (handler-case
        (progn
          (fnn-write-staged stage frame)
          ;; Link is no-replace.  Token reuse cannot overwrite contrary bytes.
          (fnn-link stage final)
          (when (string= (or (sb-ext:posix-getenv
                              "FN_BP_SERVICE_TEST_FAIL_FIRST_DIR_BARRIER") "")
                         "1")
            (fnn-os-fail sb-posix:eio dir))
          (fnn-fsync-dir dir)
          (fnn-unlink stage)
          (when (string= (or (sb-ext:posix-getenv
                              "FN_BP_SERVICE_TEST_FAIL_SECOND_DIR_BARRIER") "")
                         "1")
            (fnn-os-fail sb-posix:eio dir))
          (fnn-fsync-dir dir)
          :durable)
      (fnn-os-error ()
        (ignore-errors (fnn-unlink stage))
        ;; A visible byte-identical final name is still only evidence that the
        ;; link happened.  It cannot turn a failed publication or cleanup
        ;; barrier into a durable result.  Recovery repeats the directory
        ;; barrier before it consumes any visible final records.
        :uncertain))))

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
               (when (string= (or (sb-ext:posix-getenv
                                   "FN_BP_SERVICE_TEST_SEND_FAULT") "") "1")
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
      (:persist
       (let* ((token (second effect))
              (record (third effect))
              (outcome (fnn-bps-persist-record service token record)))
         (when (eq outcome :uncertain)
           (setf (fnn-bps-outcome service) :uncertain))
         (fnn-bps-drive-effects
          service (fnn-bps-step service (list :persist-result token outcome)))))
      (:cl-send (fnn-bps-send-effect service effect))
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
       (fnn-indeterminate "bp-service: restart fenced: ~(~a~)" (second effect)))
      (:restart-ready
       (fnn-out "BP queue recovered jobs=~d" (second effect)))
      (t nil)))
  service)

(defun fnn-bps-open (journal config wall wall-error)
  (let* ((root (fnn-bp-journal-dir journal))
         ; Shared journal ownership precedes cleanup and the lifecycle lock.
         ; No live bp/tcpcl writer can lose its staging file to recovery.
         (spool-lock (fnn-tcl-spool-acquire root))
         (life (fnn-join root "lifecycle"))
         (tally (make-fnn-bp-tally :config config :wall wall :wall-error wall-error
                                   :journal root))
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
                 :state (fnn-core 'fn-bpn-host-machine-initial
                                  config
                                  (fnn-core 'fn-bpn-host-machine-max-jobs)
                                  (fnn-core 'fn-bpn-host-machine-max-octets))))
          (setf *fnn-bps-lifecycle-enumerations* 0)
          (multiple-value-bind (observed-names plan)
              (fnn-bps-namespace-plan service)
            (let* ((record-names
                     (fnn-core 'fn-bpn-host-lifecycle-plan-record-names plan))
                   (decoded (fnn-bps-read-records service record-names))
                   (recovery (fnn-core 'fn-bpn-host-lifecycle-recovery
                                       observed-names decoded)))
              (unless (eq (fnn-core 'fn-bpn-host-lifecycle-recovery-ready-p
                                    recovery) t)
                (fnn-indeterminate
                 "bp-service: lifecycle names do not bind decoded record tokens"))
              (let* ((records
                       (fnn-core 'fn-bpn-host-lifecycle-recovery-records recovery))
                     (sequence (fnn-bps-sequence-ready service (and records t))))
                (setf (fnn-bps-stages service)
                      (fnn-core 'fn-bpn-host-lifecycle-recovery-stages recovery))
                (fnn-bps-drive-effects
                 service (fnn-bps-step service (list :restart records sequence)))
                (unless (eq (fnn-core 'fn-bpn-host-lifecycle-recovery-agrees-p
                                      recovery (fnn-bps-state service)) t)
                  (fnn-indeterminate
                   "bp-service: recovered namespace and machine frontier disagree"))
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
  (dolist (peer (fnn-core 'fn-bpn-host-ready-peers (fnn-bps-state service)))
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
                                    (fnn-bps-state service) work-octets
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
      (t (error 'fnn-usage-error
                :message (format nil "unknown bp-service command ~a" command))))))

(fnn-register-verb "bp-service" #'fnn-dispatch-bp-service)
