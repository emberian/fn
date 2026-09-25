;;; Shared-owner native surface for durable forwarding obligations.
(in-package "ACL2")

(defun fnn-bpo-call-with-owner-journal
    (store-root journal-root writable thunk)
  (let ((service nil) (journal nil))
    (unwind-protect
         (progn
           (setq service (fnn-owner-install store-root 1))
           (fnn-owner-serialized
            service nil
            (lambda ()
              (setq journal
                    (fnn-app-open (fnn-owner-service-store service)
                                  journal-root :workflow :owner-mode t))
              (when (and writable
                         (fnn-store-fenced (fnn-owner-service-store service)))
                (fnn-indeterminate "BP obligation owner Store is fenced"))
              (funcall thunk journal service))))
      (when journal (fnn-app-journal-close journal))
      (when service
        (fnn-owner-feed-close-all service)
        (fnn-store-close (fnn-owner-service-store service))))))

(defun fnn-command-bpo-owner-status (store journal work-id)
  (fnn-bpo-call-with-owner-journal
   store journal nil
   (lambda (opened service)
     (declare (ignore service))
     (declare (ignore opened))
     (fnn-out "BP obligation owner work=~a status=~(~a~) pinned=~a"
              work-id (fnn-core-state 'fn-workflow-work-status work-id)
              (if (eq (fnn-owner-core
                       'fn-owner-workflow-forward-pinnedp work-id) t)
                  "yes" "no"))
     +fnn-exit-ok+)))

(defun fnn-command-bpo-owner-undertake (store journal work-id charge)
  (fnn-bpo-call-with-owner-journal
   store journal t
   (lambda (opened service)
     (let ((event (fnn-owner-core 'fn-owner-workflow-store-undertake work-id charge)))
       (unless event (fnn-refuse "workflow forwarding obligation is not admissible"))
       (fnn-owner-retention-commit service event))
     (fnn-owner-action 'fn-owner-workflow-sync-store-node)
     (fnn-out "BP obligation owner durable undertaking work=~a charge=~d"
              work-id charge)
     +fnn-exit-ok+)))

(defun fnn-bpo-canonical-release (service release)
  (let ((event (fnn-owner-core 'fn-owner-workflow-store-release release)))
    (unless event
      (fnn-fault "committed receipt has no canonical Store release"))
    ;; The owner path releases through Store, so the developer namespace cut
    ;; belongs to that canonical publication, not an FNWF :release record.
    (let* ((cut-fired nil)
           (release-cut
             (string= (or (fnn-developer-selector
                           "FN_APP_JOURNAL_TEST_FAIL_RELEASE_NAMESPACE") "") "1"))
           (*fnn-record-directory-fault-observer*
             (and release-cut
                  (lambda (path)
                    (setq cut-fired t)
                    (fnn-os-fail sb-posix:eio path)))))
      (handler-case
          (fnn-owner-retention-commit service event)
        (fnn-store-indeterminate (e)
          (if cut-fired
              (fnn-indeterminate
               "application release publication is uncertain")
            (error e)))))
    (fnn-owner-action 'fn-owner-workflow-sync-store-node)))

(defun fnn-command-bpo-owner-receipt
    (store journal receipt txid generation profile)
  (fnn-bpo-call-with-owner-journal
   store journal t
   (lambda (opened service)
     (let ((receipt-id
            (fnn-workflow-accept-receipt
             opened receipt txid generation profile
             (lambda (release)
               (fnn-bpo-canonical-release service release)))))
       (fnn-out "BP obligation owner durable release receipt=~a profile=~a"
                receipt-id profile)
       +fnn-exit-ok+))))

;;; `bp-obligation request': the generic native request for one work.  ACL2
;;; plans it whole (fn-workflow-request-plan -> fn-bprq-plan,
;;; books/bp-request-plan.lisp): the :attempt record, its durable outcome, the
;;; FNBS key (work attempt generation), the request ADU (fn-bpo-request-adu
;;; over the image those two records make) and its destination EID.  The host
;;; publishes the two records, takes the one :submit effect, and only then
;;; hands the ADU to the FNBS carrier.  A work whose last attempt a reopen
;;; marked :restart-observed gets the plan's :retry-request first.  No ION record, route or helper is used;
;;; `app-journal workflow-ion-submit' is the ION adapter of the same attempt.

(defun fnn-bpo-request-pause (selector marker)
  ;; Developer-image process-death witness only, at a modelled journal cut.
  (when (string= (or (fnn-developer-selector selector) "") "1")
    (fnn-out "~a" marker)
    (finish-output)
    (loop (sleep 1))))

(defun fnn-bpo-request-publish (store journal work-id attempt-id)
  "Publish ACL2's attempt and outcome for WORK-ID; return (key adu destination)."
  (fnn-bpo-call-with-owner-journal
   store journal t
   (lambda (opened service)
     (declare (ignore service))
     (let ((plan (fnn-core-state 'fn-workflow-request-plan work-id attempt-id)))
       (unless (and (consp plan) (eq (first plan) :request)
                    (= (length plan) 7))
         (if (eq (fnn-core-state 'fn-workflow-fencedp) t)
             (fnn-refuse "ACL2 refused a request for work ~a attempt ~a: the workflow image is fenced on an uncertain publication (bp-obligation recover)"
                         work-id attempt-id)
           (fnn-refuse "ACL2 refused a request for work ~a attempt ~a"
                       work-id attempt-id)))
       (destructuring-bind (tag attempt outcome key adu destination retry) plan
         (declare (ignore tag))
         (unless (and (fnn-octet-list-p adu) (<= 1 (length adu) 65538)
                      (stringp destination))
           (fnn-fault "ACL2 returned an invalid request plan"))
         ;; A restart-observed attempt is retried by the journaled policy
         ;; decision first, so the next open replays the new attempt.
         (when retry
           (fnn-app-publish opened retry)
           (fnn-out "BP obligation request durable retry work=~a attempt=~a generation=~d"
                    (second retry) (third retry) (fourth retry)))
         (fnn-app-publish opened attempt :reserve-resolution t)
         (fnn-bpo-request-pause "FN_BP_OBLIGATION_TEST_PAUSE_AFTER_ATTEMPT"
                                "BP OBLIGATION ATTEMPT DURABLE")
         (fnn-app-publish opened outcome)
         (unless (eq (fnn-core-state 'fn-workflow-take-submit
                                     (first key) (second key) (third key))
                     t)
           (fnn-fault "durable attempt did not grant one submit effect"))
         (fnn-out "BP obligation request durable attempt work=~a attempt=~a generation=~d destination=~a adu=~d"
                  (first key) (second key) (third key) destination
                  (length adu))
         (fnn-bpo-request-pause "FN_BP_OBLIGATION_TEST_PAUSE_AFTER_SUBMIT"
                                "BP OBLIGATION SUBMIT TAKEN")
         (list key adu destination))))))

(defun fnn-command-bpo-owner-request
    (store journal work-id attempt-id fnbs node-id contact-host contact-port
     lifetime crc-type hop-limit transfer-mru wall wall-error)
  (destructuring-bind (key adu destination)
      (fnn-bpo-request-publish store journal work-id attempt-id)
    ;; The carrier: one FNBS job keyed by ACL2's (work attempt generation),
    ;; offered once now; `bp-service resume' re-offers a durable job.
    (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit
                                  transfer-mru))
           (service (fnn-bps-open fnbs config wall wall-error)))
      ;; Routing: the carrier's hop is ACL2's choice over this Store's
      ;; bp-route table, at queue time (fn-bprt-job-route) and before the
      ;; offer (fn-bpnp-contact-next).
      (unwind-protect
           (let* ((routed (fnn-bps-use-store-routes service store))
                  (work-octets (fnn-octet-list (fnn-string-octets (first key))))
                  (attempt-octets
                    (fnn-octet-list (fnn-string-octets (second key))))
                  (generation (third key))
                  (existing (fnn-core 'fn-bpn-host-existing-sequence
                                      (fnn-bps-base service) work-octets
                                      attempt-octets generation))
                  (route (fnn-bps-queue-route service (fnn-bp-eid destination)
                                              node-id transfer-mru
                                              contact-host contact-port))
                  (sequence
                    (if (eq (fnn-core 'fn-bpn-host-existing-sequence-p existing)
                            t)
                        (fnn-core 'fn-bpn-host-existing-sequence-value existing)
                      (if route
                          (fnn-bp-reserve-sequence (fnn-bps-tally service))
                        0)))
                  (event (list :enqueue work-octets attempt-octets generation
                               sequence route (fnn-bp-eid destination) adu
                               (fnn-bp-observation wall wall-error))))
             (declare (ignore routed))
             (unless route
               ;; No route: nothing is queued.  The durable attempt keeps the
               ;; obligation pinned; the carrier was refused by routing.
               (fnn-out "BP obligation request carrier no-route work=~a attempt=~a generation=~d"
                        (first key) (second key) generation)
               (return-from fnn-command-bpo-owner-request +fnn-exit-refused+))
             (fnn-bps-drive-effects service (fnn-bps-step service event))
             (case (fnn-bps-outcome service)
               (:uncertain
                (fnn-indeterminate "BP obligation request carrier publication is uncertain"))
               (:refused (fnn-refuse "BP obligation request carrier was refused")))
             (fnn-out "BP obligation request carrier durable work=~a attempt=~a generation=~d"
                      (first key) (second key) generation)
             (fnn-bps-attempt-ready service)
             (fnn-bps-exit-code service))
        (fnn-bps-release service)))))

;;; `bp-obligation recover STORE WORKFLOW WORK ATTEMPT OUTCOME': the recovery
;;; outcome of an attempt fenced by a process death between its durable
;;; record and its outcome.  OUTCOME (committed | absent) is the operator's
;;; out-of-band finding; ACL2 decides whether it names the fenced pending
;;; (fn-workflow-recovery-plan -> fn-bprq-recovery-plan) and returns the exact
;;; record, which the host publishes; a refusal carries ACL2's reason.

(defun fnn-bpo-recovery-outcome (text)
  (cond ((string= text "committed") :committed)
        ((string= text "absent") :absent)
        (t text)))

(defun fnn-command-bpo-owner-recover (store journal work-id attempt-id outcome)
  (fnn-bpo-call-with-owner-journal
   store journal t
   (lambda (opened service)
     (declare (ignore service))
     (let ((plan (fnn-core-state 'fn-workflow-recovery-plan work-id attempt-id
                                 (fnn-bpo-recovery-outcome outcome))))
       (case (and (consp plan) (first plan))
         (:refused
          (fnn-refuse "ACL2 refused recovery work=~a attempt=~a outcome=~a reason=~(~a~)"
                      work-id attempt-id outcome (second plan)))
         (:recover
          (let ((record (second plan)))
            (fnn-app-publish opened record)
            (fnn-out "BP obligation recovery durable work=~a attempt=~a outcome=~(~a~) txid=~d generation=~d"
                     work-id attempt-id (fifth record) (second record)
                     (third record))
            (fnn-out "BP obligation owner work=~a status=~(~a~) pinned=~a"
                     work-id (fnn-core-state 'fn-workflow-work-status work-id)
                     (if (eq (fnn-owner-core
                              'fn-owner-workflow-forward-pinnedp work-id) t)
                         "yes" "no"))
            +fnn-exit-ok+))
         (t (fnn-fault "ACL2 returned an invalid recovery plan")))))))

(defun fnn-dispatch-bp-obligation (command args)
  (flet ((need (n)
           (when (< (length args) n)
             (error 'fnn-usage-error
                    :message "bp-obligation: missing arguments"))))
    (cond
      ((string= command "status")
       (need 3)
       (fnn-command-bpo-owner-status (first args) (second args) (third args)))
      ((string= command "undertake")
       (need 4)
       (fnn-command-bpo-owner-undertake
        (first args) (second args) (third args) (parse-integer (fourth args))))
      ((string= command "request")
       ;; STORE WORKFLOW WORK ATTEMPT FNBS NODE-ID CONTACT-HOST CONTACT-PORT
       ;; [LIFETIME CRC HOP-LIMIT TRANSFER-MRU WALL WALL-ERROR]
       (need 8)
       (flet ((number (index default)
                (fnn-tcl-number (fnn-tcl-arg args index) default)))
         (fnn-command-bpo-owner-request
          (first args) (second args) (third args) (fourth args) (fifth args)
          (sixth args) (seventh args) (parse-integer (eighth args))
          (number 8 +fnn-bp-lifetime+) (number 9 +fnn-bp-crc-type+)
          (number 10 +fnn-bp-hop-limit+) (number 11 +fnn-tcl-transfer-mru+)
          (let ((text (fnn-tcl-arg args 12))) (and text (parse-integer text)))
          (number 13 0))))
      ((string= command "recover")
       ;; STORE WORKFLOW WORK ATTEMPT OUTCOME
       (need 5)
       (fnn-command-bpo-owner-recover
        (first args) (second args) (third args) (fourth args) (fifth args)))
      ((string= command "receipt")
       (need 6)
       (fnn-command-bpo-owner-receipt
        (first args) (second args) (third args)
        (parse-integer (fourth args)) (parse-integer (fifth args))
        (sixth args)))
      (t (error 'fnn-usage-error
                :message (format nil "unknown bp-obligation command ~a"
                                 command))))))

(fnn-register-verb "bp-obligation" #'fnn-dispatch-bp-obligation)
