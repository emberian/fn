;;; Composed BP node application dispatcher.  FNBS owns custody and delivery
;;; markers; the owner Store/FNRJ and FNWF own application commitments.
(in-package "ACL2")

(defun fnn-bpnode-observed-channel (socket)
  "Preserve the kernel-observed local listener and remote source address."
  (multiple-value-bind (local-address local-port)
      (sb-bsd-sockets:socket-name socket)
    (multiple-value-bind (remote-address remote-port)
        (sb-bsd-sockets:socket-peername socket)
      (declare (ignore remote-port))
      (if (and (vectorp local-address) (= (length local-address) 4)
               (vectorp remote-address) (= (length remote-address) 4)
               (integerp local-port) (<= 1 local-port 65535))
          (list :tcp4 (coerce local-address 'list) local-port
                (coerce remote-address 'list))
        (list :unsupported-channel)))))

(defun fnn-bpnode-pause-at-durable-cut (selector marker)
  ;; Developer-image process-death witness only.  Each caller places this
  ;; after the modeled durable transition and before its next operation.
  (when (string= (or (fnn-developer-selector selector) "") "1")
    (fnn-out "~a" marker)
    (finish-output)
    (loop (sleep 1))))

(defun fnn-bpnode-request-result
    (owner receipt-root destination policy issuer view node-id)
  (unless (eq (fnn-owner-core 'fn-owner-bp-request-trustedp view) t)
    (return-from fnn-bpnode-request-result
      (values :request-refused '(0))))
  (let ((journal nil))
    (unwind-protect
         (progn
           (setq journal (fnn-bpapp-open-journal
                          owner receipt-root destination policy issuer))
           (let* ((request (fourth view))
                  (identity (sixth view))
                  (inbound-id
                    (fnn-octets-string
                     (fnn-octets (fnn-core 'fn-id-hex-octets identity))))
                  (source (seventh view))
                  (dest (eighth view))
                  (result nil)
                  (receipt nil))
             (multiple-value-setq (result receipt)
               (fnn-owner-serialized
                owner nil
                (lambda ()
                  ;; Config can change after preflight and before this lock.
                  ;; Authorize the fresh Store decision against the live
                  ;; owner configuration under serialization.
                  (if (eq (fnn-owner-core 'fn-owner-bp-request-trustedp view) t)
                      (fnn-bpapp-accept-locked
                       owner journal inbound-id request node-id identity
                       (fifth view) source dest)
                    (values :refused nil)))))
             (case result
               ((:accepted :duplicate)
                (unless receipt
                  (fnn-fault "BP node committed request has no receipt ADU"))
                (let ((receipt-id
                        (fnn-core-state 'fn-bprj-request-receipt-id request)))
                  (unless (stringp receipt-id)
                    (fnn-fault "BP node committed request has no receipt ID"))
                  (values (if (eq result :accepted)
                              :request-accepted :request-duplicate)
                          (fnn-octet-list (fnn-string-octets receipt-id)))))
               (:refused (values :request-refused '(0)))
               (otherwise (values :uncertain '(0))))))
      (when journal (fnn-app-journal-close journal)))))

(defun fnn-bpnode-receipt-result
    (owner workflow-root view configured-peer)
  (declare (ignore configured-peer))
  (unless (eq (fnn-owner-core 'fn-owner-bp-receipt-trustedp view) t)
    (return-from fnn-bpnode-receipt-result
      (values :receipt-refused '(0))))
  (fnn-owner-serialized
   owner nil
   (lambda ()
     (unless (eq (fnn-owner-core 'fn-owner-bp-receipt-trustedp view) t)
       (return-from fnn-bpnode-receipt-result
         (values :receipt-refused '(0))))
     (let ((journal nil))
       (unwind-protect
            (progn
              (setq journal
                    (fnn-app-open (fnn-owner-service-store owner)
                                  workflow-root :workflow :owner-mode t))
              (let ((receipt-id
                      (fnn-workflow-accept-receipt-octets
                       journal (fourth view)
                       "trusted-local-observation-v0"
                       (lambda (release)
                         (fnn-bpo-canonical-release owner release)))))
                (values :receipt-accepted
                        (fnn-octet-list (fnn-string-octets receipt-id)))))
         (when journal (fnn-app-journal-close journal)))))))

(defun fnn-bpnode-app-result
    (owner receipt-root workflow-root destination policy issuer view
     node-id configured-peer)
  ;; A refused preflight is definitive.  An ambiguous Store/FNRJ/FNWF result
  ;; fences the FNBS marker and requires cold recovery before another action.
  (handler-case
      (case (third view)
        (:request
         (fnn-bpnode-request-result owner receipt-root destination policy
                                    issuer view node-id))
        (:receipt
         (fnn-bpnode-receipt-result owner workflow-root view configured-peer))
        (otherwise (values :request-refused '(0))))
    (fnn-store-indeterminate (e)
      (fnn-out "BP node application uncertain: ~a" e)
      (values :uncertain '(0)))
    (fnn-store-fault (e) (error e))
    (fnn-store-error (e)
      (fnn-out "BP node application refused: ~a" e)
      (values (if (eq (third view) :receipt)
                  :receipt-refused :request-refused)
              '(0)))))

(defun fnn-bpnode-dispatch-one
    (bp owner receipt-root workflow-root destination policy issuer node-id
     configured-peer)
  (let* ((tally (fnn-bps-tally bp))
         (observation
           (fnn-bp-observation (fnn-bp-tally-wall tally)
                                (fnn-bp-tally-wall-error tally)))
         (node (fnn-bp-eid node-id)))
    (when (eq (fnn-bps-outcome bp) :uncertain)
      (fnn-indeterminate "BP node lifecycle is uncertain; recovery required"))
    (let ((effects
            (fnn-bps-foundation-step
             bp (list :progress node observation
                      (fnn-core 'fn-bpnp-single-peer-routes
                                (fnn-bp-eid configured-peer))
                      0))))
      (unless effects (return-from fnn-bpnode-dispatch-one nil))
      (when (and (= (length effects) 1)
                 (eq (first (first effects)) :progress-wait))
        (fnn-out "BP node progress waiting reason=~(~a~)"
                 (third (first effects)))
        (return-from fnn-bpnode-dispatch-one t))
      (when (and (= (length effects) 1)
                 (eq (first (first effects)) :progress-unsupported))
        (fnn-out "BP node progress waiting reason=class")
        (return-from fnn-bpnode-dispatch-one t))
      (when (and (= (length effects) 1)
                 (eq (first (first effects)) :progress-uncertain))
        (fnn-indeterminate
         "BP node held carrier expiry is uncertain; recovery or clock evidence required"))
      (when (and (= (length effects) 1)
                 (eq (first (first effects)) :persist-dispatch))
        (fnn-bps-drive-effects bp effects)
        (return-from fnn-bpnode-dispatch-one t))
      (unless (and (= (length effects) 1)
                   (eq (first (first effects)) :deliver)
                   (= (length (first effects)) 5))
        (fnn-fault "BP node delivery marker was not issued exactly"))
      (let* ((effect (first effects))
             (key (fourth effect))
             (view (fnn-core 'fn-bpnp-delivery-view (fifth effect))))
        (unless (and (consp view) (eq (first view) :delivery)
                     (equal (second view) key)
                     (member (third view) '(:request :receipt)))
          (fnn-fault "BP node progress yielded an invalid local delivery"))
        (multiple-value-bind (status detail)
            (fnn-bpnode-app-result
             owner receipt-root workflow-root destination policy issuer
             view node-id configured-peer)
          (when (member status '(:request-accepted :request-duplicate))
            (fnn-bpapp-pause-after-decision))
          (let ((result
                  (fnn-bps-foundation-step
                   bp (list :deliver-result (second effect) (third effect)
                            key status detail))))
            (fnn-bps-drive-effects bp result)
            (when (eq status :uncertain)
              (fnn-indeterminate
               "BP node application result is uncertain; recovery required"))
            (fnn-bpnode-pause-at-durable-cut
             "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN"
             "BP NODE KIND7 DURABLE")
            (fnn-out "BP node delivery ~(~a~)" status)
            t))))))

(defun fnn-bpnode-dispatch-pending
    (bp owner receipt-root workflow-root destination policy issuer node-id
     configured-peer)
  (loop repeat (fnn-core 'fn-bpn-host-machine-max-jobs)
        while (fnn-bpnode-dispatch-one
               bp owner receipt-root workflow-root destination policy issuer
               node-id configured-peer))
  bp)

(defun fnn-bpnode-forward-contact
    (bp node-id peer-id contact-host contact-port transfer-mru wall wall-error)
  "Drive one ACL2-selected held forwarding attempt on one negotiated session."
  (let ((peer (fnn-bp-eid peer-id)))
    (unless (eq (fnn-core 'fn-bpnp-has-forward-pendingp
                           (fnn-core 'fn-bpnf-held-list (fnn-bps-state bp)) peer) t)
      (return-from fnn-bpnode-forward-contact nil))
    (let ((socket nil)
          (sent nil)
          (session-id
            (cons (fnn-core 'fn-bpnf-epoch (fnn-bps-state bp))
                  (incf (fnn-bps-next-session bp)))))
      (handler-case
          (unwind-protect
               (progn
                 (setq socket (fnn-tcl-connect contact-host contact-port))
                 (let* ((*fnn-bps-forward-send*
                          (lambda (effect)
                            (unless (and (null sent) (= (length effect) 7)
                                         (equal (second effect) peer)
                                         (equal (third effect) session-id))
                              (fnn-indeterminate
                               "bp-node: forward effect does not match session"))
                            (setq sent effect)))
                        (conn
                          (fnn-tcl-session
                           (fnn-socket-fd socket) :active
                           (fnn-tcl-params node-id peer-id +fnn-tcl-keepalive+
                                           +fnn-tcl-segment-mru+ transfer-mru)
                           "bp-node-forward" (fnn-bps-root bp)
                           :on-ready
                           (lambda (connection)
                             (let* ((negotiated
                                      (fnn-core 'fn-tcl-session-negotiated
                                                (fnn-tclc-session connection)))
                                    (mru (fnn-core 'fn-tcl-negotiated-transfer-mtu
                                                   negotiated))
                                    (obs (fnn-bp-observation wall wall-error)))
                               (fnn-bps-drive-effects
                                bp (fnn-bps-foundation-step
                                    bp (list :session peer session-id t mru obs)))
                               (when sent
                                 (setf (fnn-tclc-pending connection)
                                       (cons "bp-node-forward" (seventh sent)))
                                 (fnn-out "BP forwarding attempt durable key=~s"
                                          (sixth sent))))))))
                   (when sent
                     (let ((result
                             (fnn-core 'fn-bpnp-tcpcl-outcome
                                       (fnn-tclc-outcome conn))))
                       (when (eq result :fence)
                         (setf (fnn-bps-outcome bp) :uncertain)
                         (fnn-indeterminate
                          "bp-node: transport outcome uncertain after durable attempt"))
                       ;; Model cut N08: kind 8 durable, the transfer ran, no
                       ;; kind 9 proposed.  Recovery re-offers (spec 4.3.1).
                       (fnn-bpnode-pause-at-durable-cut
                        "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_EIGHT_SENT"
                        "BP NODE KIND8 SENT")
                       (fnn-bps-drive-effects
                        bp (fnn-bps-foundation-step
                            bp (list :forward-result
                                     (fourth sent) (fifth sent) session-id
                                     result (fnn-bp-observation wall wall-error))))))
                   (fnn-bps-drive-effects
                    bp (fnn-bps-foundation-step
                        bp (list :session peer session-id nil 1
                                 (fnn-bp-observation wall wall-error))))))
            (when socket (fnn-socket-shut socket)))
        ((or fnn-os-error sb-bsd-sockets:socket-error) (e)
          (if sent
              (fnn-indeterminate
               "bp-node: transport failed after durable attempt: ~a" e)
            (fnn-out "BP forwarding session unavailable: ~a" e))))
      sent)))

(defun fnn-bpnode-queue-outbox
    (bp owner receipt-root destination policy issuer node-id peer-id view
     contact-host contact-port transfer-mru wall wall-error)
  (let ()
    (when (eq (fnn-bps-outcome bp) :uncertain)
      (fnn-indeterminate "BP node lifecycle is uncertain; recovery required"))
    (unless (eq (fnn-core 'fn-bpah-outbox-peer-matchp view peer-id) t)
      (fnn-refuse "BP node owed receipt has a different configured peer"))
    (let* ((work (sixth view))
           (attempt (seventh view))
           (generation (eighth view))
           (existing
             (fnn-core 'fn-bpn-host-existing-sequence
                       (fnn-bps-base bp) work attempt generation)))
      (let ((journal nil))
        (unwind-protect
             (progn
               (setq journal (fnn-bpapp-open-journal
                              owner receipt-root destination policy issuer))
               (let ((adu (fnn-receipt-adu journal (fourth view))))
                 (unless adu
                   (fnn-indeterminate
                    "BP node owed receipt is absent from durable FNRJ replay"))
                 ;; A key collision alone is not handoff evidence.  ACL2 must
                 ;; bind kind-7 owed evidence, the exact FNRJ replay ADU, and
                 ;; the durable return job's payload and peer.
                 (when (eq (fnn-core 'fn-bpn-host-existing-sequence-p
                                      existing) t)
                   (let ((status
                           (fnn-core 'fn-bpah-outbox-effective-status
                                     (fnn-bps-state bp) view
                                     (fnn-octet-list adu)
                                     (fnn-bp-eid (fifth view)))))
                     (unless (and (consp status)
                                  (eq (first status) :handed-off))
                       (fnn-indeterminate
                        "BP node receipt job key has conflicting durable bytes")))
                   (return-from fnn-bpnode-queue-outbox :already-queued))
                 (let* ((peer (fnn-bp-eid (fifth view)))
                      (sequence (fnn-bp-reserve-sequence (fnn-bps-tally bp)))
                      (observation (fnn-bp-observation wall wall-error))
                      (route
                        (list :route
                              (fnn-octet-list
                               (fnn-string-octets contact-host))
                              contact-port
                              (fnn-octet-list (fnn-string-octets node-id))
                              +fnn-tcl-keepalive+ +fnn-tcl-segment-mru+
                              transfer-mru)))
                 (fnn-bps-drive-effects
                  bp (fnn-bps-step
                      bp (list :enqueue work attempt generation sequence
                               route peer (fnn-octet-list adu) observation)))
                 (when (eq (fnn-bps-outcome bp) :uncertain)
                   (fnn-indeterminate
                    "BP node receipt queue publication is uncertain"))
                 (when (eq (fnn-bps-outcome bp) :refused)
                   (fnn-refuse "BP node receipt queue was refused"))
                 (let ((status
                         (fnn-core 'fn-bpah-outbox-effective-status
                                   (fnn-bps-state bp) view
                                   (fnn-octet-list adu) peer)))
                   (unless (and (consp status)
                                (eq (first status) :handed-off))
                     (fnn-indeterminate
                      "BP node receipt lacks exact durable return handoff")))
                 (fnn-out "BP node receipt queued id=~a"
                          (fnn-octets-string (fnn-octets (second view))))
                 (fnn-bpnode-pause-at-durable-cut
                  "FN_BP_NODE_TEST_PAUSE_AFTER_OUTBOX"
                  "BP NODE OUTBOX DURABLE")
                 :queued)))
          (when journal (fnn-app-journal-close journal)))))))

(defun fnn-bpnode-queue-outboxes
    (bp owner receipt-root destination policy issuer node-id peer-id
     contact-host contact-port transfer-mru wall wall-error)
  (let ((after nil))
    (loop repeat (fnn-core 'fn-bpn-host-machine-max-jobs)
          for view = (fnn-core 'fn-bpah-outbox-view-after
                               (fnn-bps-state bp) after)
          while view
          do (fnn-bpnode-queue-outbox
              bp owner receipt-root destination policy issuer node-id peer-id
              view contact-host contact-port transfer-mru wall wall-error)
             (setq after (third view))))
  bp)

(defun fnn-bpnode-delete-expired (bp reports-enabled)
  ;; The persisted kind-5 anchor and this same-boot observation are interpreted
  ;; by ACL2. A refusal/uncertainty stops this bounded progression.
  (loop repeat (fnn-core 'fn-bpn-host-machine-max-jobs)
        while (eq (fnn-bps-outcome bp) :accepted)
        for tally = (fnn-bps-tally bp)
        for observation =
          (fnn-bp-observation (fnn-bp-tally-wall tally)
                              (fnn-bp-tally-wall-error tally))
        for effects = (fnn-bps-foundation-step
                       bp (list :expire-held observation
                                (if reports-enabled t nil)))
        while effects
        do (fnn-bps-drive-effects bp effects)
           (when (eq (fnn-bps-outcome bp) :accepted)
             (fnn-bpnode-pause-at-durable-cut
              "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_TEN" "BP NODE KIND10 DURABLE")))
  bp)

(defun fnn-bpnode-queue-report
    (bp peer-id node-id view contact-host contact-port transfer-mru
     wall wall-error)
  (when (eq (fnn-bps-outcome bp) :uncertain)
    (fnn-indeterminate "BP node status report lifecycle is uncertain"))
  (unless (eq (fnn-core 'fn-bpn-report-outbox-peer-matchp
                        view (fnn-bp-eid peer-id)) t)
    (fnn-out "BP status report intent awaits its configured return peer")
    (return-from fnn-bpnode-queue-report :await-route))
  (let* ((work (fifth view))
         (attempt (sixth view))
         (generation (seventh view))
         (existing (fnn-core 'fn-bpn-host-existing-sequence
                             (fnn-bps-base bp) work attempt generation)))
    (when (eq (fnn-core 'fn-bpn-host-existing-sequence-p existing) t)
      (unless (eq (fnn-core 'fn-bpn-report-job-matchp
                            (fnn-bps-base bp) view) t)
        (fnn-indeterminate "BP status report job key conflicts with durable bytes"))
      (return-from fnn-bpnode-queue-report :already-queued))
    (let* ((sequence (fnn-bp-reserve-sequence (fnn-bps-tally bp)))
           (observation (fnn-bp-observation wall wall-error))
           (route (list :route
                        (fnn-octet-list (fnn-string-octets contact-host))
                        contact-port
                        (fnn-octet-list (fnn-string-octets node-id))
                        +fnn-tcl-keepalive+ +fnn-tcl-segment-mru+
                        transfer-mru)))
      (fnn-bps-drive-effects
       bp (fnn-bps-foundation-step
           bp (list :queue-report (second view) sequence route observation)))
      (when (eq (fnn-bps-outcome bp) :uncertain)
        (fnn-indeterminate "BP status report queue publication uncertain"))
      (when (eq (fnn-bps-outcome bp) :refused)
        (fnn-refuse "BP status report queue refused"))
      (unless (eq (fnn-core 'fn-bpn-report-job-matchp
                            (fnn-bps-base bp) view) t)
        (fnn-indeterminate "BP status report queue lacks exact durable job"))
      (fnn-bpnode-pause-at-durable-cut
       "FN_BP_NODE_TEST_PAUSE_AFTER_REPORT_OUTBOX"
       "BP NODE REPORT OUTBOX DURABLE")
      :queued)))

(defun fnn-bpnode-queue-reports
    (bp peer-id node-id contact-host contact-port transfer-mru wall wall-error)
  (let ((after nil))
    (loop repeat (fnn-core 'fn-bpn-host-machine-max-jobs)
          for view = (fnn-core 'fn-bpn-report-outbox-next
                               (fnn-bps-state bp) after)
          while view
          do (fnn-bpnode-queue-report
              bp peer-id node-id view contact-host contact-port transfer-mru
              wall wall-error)
             (setq after (second view))))
  bp)

(defun fnn-bpnode-observe-reports (bp node-id)
  ;; Diagnostic only. ACL2 parses and correlates the received administrative
  ;; payload; this caller neither advances retry nor releases an obligation.
  (let ((after nil))
    (loop repeat (fnn-core 'fn-bpn-host-machine-max-jobs)
          for observation =
            (fnn-core 'fn-bpn-report-observe-next
                      (fnn-bps-state bp) (fnn-bp-eid node-id) after)
          while observation
          do (case (first observation)
               (:observed
                (fnn-out "BP status report observed arrival=~d correlated=~a"
                         (second observation)
                         (if (third observation) "yes" "no")))
               (:malformed
                (fnn-out "BP administrative status malformed arrival=~d"
                         (second observation))))
             (setq after (second observation))))
  bp)

(defun fnn-command-bp-node
    (listen-port once journal-root store-root receipt-root workflow-root
     node-id peer-id destination policy issuer contact-host contact-port
     lifetime crc-type hop-limit transfer-mru wall wall-error reports-enabled)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         ;; FNBS (and its clock-domain gate) opens before any Store/FNRJ or
         ;; sequence operation.  There is exactly one BP lifecycle owner.
         (bp (fnn-bps-open journal-root config wall wall-error))
         (owner nil)
         (listener nil)
         (code +fnn-exit-ok+))
    (unwind-protect
         (progn
           (setq owner (fnn-owner-install store-root 1))
           (fnn-bpc-advance-clock bp (fnn-bp-observation wall wall-error))
           (fnn-bpnode-delete-expired bp reports-enabled)
           (fnn-bpnode-observe-reports bp node-id)
           (fnn-bpnode-dispatch-pending
            bp owner receipt-root workflow-root destination policy issuer
            node-id peer-id)
           (fnn-bpnode-forward-contact
            bp node-id peer-id contact-host contact-port transfer-mru
            wall wall-error)
           (fnn-bpnode-queue-outboxes
            bp owner receipt-root destination policy issuer node-id peer-id
            contact-host contact-port transfer-mru wall wall-error)
           (fnn-bpnode-queue-reports
            bp peer-id node-id contact-host contact-port transfer-mru
            wall wall-error)
           (when listen-port
             ;; A refused reception publishes its exact wire and verdict as
             ;; receive evidence (fnn-bp-deliver-node); recover that ACL2
             ;; namespace before the first transfer, as bp receive does.
             (fnn-bp-evidence-open (fnn-bps-tally bp))
             (multiple-value-bind (bound bound-port)
                 (fnn-tcl-listen listen-port)
               (setq listener bound)
               (fnn-out "BP NODE LISTENING ~d" bound-port))
             (fnn-accept-loop
              listener
              (lambda (socket)
                (let* ((session-counter
                         (incf (fnn-bps-next-session bp)))
                       (observed-channel
                         (fnn-bpnode-observed-channel socket))
                       (*fnn-tcl-deliver*
                         (lambda (conn xfer-id octets)
                           (fnn-bp-deliver-node
                            bp conn session-counter xfer-id octets owner
                            observed-channel))))
                  (unwind-protect
                       (let ((conn
                               (fnn-tcl-session
                                (fnn-socket-fd socket) :passive
                                (fnn-tcl-params
                                 node-id peer-id +fnn-tcl-keepalive+
                                 +fnn-tcl-segment-mru+ transfer-mru)
                                "bp-node" (fnn-bps-root bp))))
                         (fnn-tcl-summary conn)
                         (setq code (fnn-bp-exit-code (fnn-bps-tally bp) conn)))
                    (fnn-socket-shut socket)))
                ;; This is after the TCPCL transfer disposition.  The final
                ;; XFER_ACK speaks only for durable kind-5 custody; application
                ;; Store/FNRJ/FNWF commitment follows in a separate cut.
                (when (eq (fnn-bps-outcome bp) :uncertain)
                  (fnn-indeterminate
                   "BP node custody publication uncertain; recovery required"))
                (fnn-bpnode-pause-at-durable-cut
                 "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_FIVE"
                 "BP NODE KIND5 DURABLE")
                (fnn-bpc-advance-clock
                 bp (fnn-bp-observation wall wall-error))
                (fnn-bpnode-delete-expired bp reports-enabled)
                (fnn-bpnode-observe-reports bp node-id)
                (fnn-bpnode-dispatch-pending
                 bp owner receipt-root workflow-root destination policy issuer
                 node-id peer-id)
                (fnn-bpnode-forward-contact
                 bp node-id peer-id contact-host contact-port transfer-mru
                 wall wall-error)
                (fnn-bpnode-queue-outboxes
                 bp owner receipt-root destination policy issuer node-id peer-id
                 contact-host contact-port transfer-mru wall wall-error)
                (fnn-bpnode-queue-reports
                 bp peer-id node-id contact-host contact-port transfer-mru
                 wall wall-error))
              once))
           (if (eq (fnn-bps-outcome bp) :uncertain)
               +fnn-exit-uncertain+
             (if (eq (fnn-bps-outcome bp) :refused)
                 +fnn-exit-refused+
               code)))
      (when listener (fnn-socket-shut listener))
      (when owner
        (ignore-errors (fnn-owner-action 'fn-owner-app-unbind-receipt-store))
        (fnn-owner-feed-close-all owner)
        (fnn-store-close (fnn-owner-service-store owner)))
      (fnn-bps-release bp))))

(defun fnn-dispatch-bp-node (command args)
  (unless (member command '("serve" "dispatch") :test #'string=)
    (error 'fnn-usage-error :message "bp-node: expected serve or dispatch"))
  (let ((offset (if (string= command "serve") 1 0)))
    (when (< (length args) (+ offset 11))
      (error 'fnn-usage-error
             :message
             "bp-node: [PORT] JOURNAL STORE RECEIPTS WORKFLOW NODE PEER DEST POLICY ISSUER CONTACT-HOST CONTACT-PORT"))
    (flet ((arg (n &optional default) (or (nth (+ offset n) args) default))
           (number (n default)
             (parse-integer (or (nth (+ offset n) args)
                                (write-to-string default))))
           (optional-number (n)
             (and (nth (+ offset n) args)
                  (parse-integer (nth (+ offset n) args)))))
      (fnn-command-bp-node
       (and (= offset 1) (parse-integer (first args)))
       (string= (arg 11 "1") "1")
       (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) (arg 5) (arg 6)
       (arg 7) (arg 8) (arg 9) (number 10 4556)
       (number 12 +fnn-bp-lifetime+) (number 13 +fnn-bp-crc-type+)
       (number 14 +fnn-bp-hop-limit+) (number 15 +fnn-tcl-transfer-mru+)
       (optional-number 16) (number 17 0)
       (string= (arg 18 "0") "1")))))

(fnn-register-verb "bp-node" #'fnn-dispatch-bp-node)
