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

(defun fnn-bpnode-source-decision (view)
  "Print ACL2's D23 source decision for VIEW; the host classifies nothing."
  (let ((line (fnn-owner-core 'fn-owner-bp-source-decision-line view)))
    (when (stringp line)
      (fnn-out "BP node source ~a" line))))

(defvar *fnn-bpnode-test-busy-answers* 0)

(defun fnn-bpnode-test-busy-p ()
  ;; Developer-image witness for BP-R17: the first N application answers
  ;; are the owner's :busy, exactly as fnn-bpapp-accept-locked returns it.
  (let ((limit (fnn-developer-selector "FN_BP_NODE_TEST_APP_BUSY")))
    (when (and limit (< *fnn-bpnode-test-busy-answers*
                        (or (parse-integer limit :junk-allowed t) 0)))
      (incf *fnn-bpnode-test-busy-answers*)
      t)))

(defun fnn-bpnode-request-result
    (owner receipt-root destination policy issuer view node-id)
  (fnn-bpnode-source-decision view)
  (unless (eq (fnn-owner-core 'fn-owner-bp-request-trustedp view) t)
    (return-from fnn-bpnode-request-result
      (values :request-refused '(0))))
  (when (fnn-bpnode-test-busy-p)
    (return-from fnn-bpnode-request-result (values :busy '(0))))
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
               ;; BP-R17: the owner deferred (a (:busy reason) plan or the
               ;; dispatcher's (:busy)); the node keeps the row held.
               (:busy (values :busy '(0)))
               (otherwise (values :uncertain '(0))))))
      (when journal (fnn-app-journal-close journal)))))

(defun fnn-bpnode-receipt-observations (view)
  "Signed receipts: the two primitive observations over ACL2's preimage.
ACL2 (`fn-bpah-receipt-signature-plan') chooses the preimage, the enrolled
keys and the signatures; the host only asks libsodium and OpenSSL, exactly
as the transit path does (`fnn-hsig-observe-raw'), and hands the
observations back.  Nil when there is nothing to observe."
  (let ((plan (fnn-owner-core 'fn-owner-bp-receipt-signature-plan view)))
    (when (and (consp plan) (= (length plan) 4))
      (destructuring-bind (preimage ed-key ml-key signatures) plan
        (let* ((observations
                 (fnn-hsig-observe-raw ed-key ml-key preimage signatures))
               (ml (second observations)))
          (list (and (consp ml) (second ml) (coerce (second ml) 'list))
                (first observations)
                (if (consp ml) (first ml) ml)))))))

(defun fnn-bpnode-release-line (view obs)
  "Print ACL2's D23 release verdict for a receipt VIEW; the host decides nothing."
  (let ((line (fnn-owner-core 'fn-owner-bp-release-line view obs)))
    (when (stringp line)
      (fnn-out "BP node release ~a" line))))

(defun fnn-bpnode-receipt-detail (view obs)
  "ACL2's release verdict for VIEW as the kind-7 delivery detail octets."
  (let ((detail (fnn-owner-core 'fn-owner-bp-receipt-release-detail view obs)))
    (unless (and (fnn-octet-list-p detail) (consp detail)
                 (<= (length detail) 256))
      (fnn-fault "BP node release detail is not a bounded octet list"))
    detail))

(defun fnn-bpnode-receipt-result
    (owner workflow-root view configured-peer)
  ;; D23: a receipt releases an obligation only through ACL2's
  ;; `fn-bpah-receipt-release-record' (books/bp-release-authority.lisp):
  ;; the delivering neighbour is the issuer or lists it, or the receipt's
  ;; own signature verifies under the issuer's enrollment here, and the
  ;; receipt names the exact held obligation.  The kind-7 detail is ACL2's
  ;; verdict, so the FNBS journal keeps it.
  (declare (ignore configured-peer))
  (fnn-bpnode-source-decision view)
  (let ((obs (fnn-bpnode-receipt-observations view)))
    (fnn-bpnode-release-line view obs)
    (unless (eq (fnn-owner-core 'fn-owner-bp-receipt-gatep view obs) t)
      (return-from fnn-bpnode-receipt-result
        (values :receipt-refused (fnn-bpnode-receipt-detail view obs))))
    (fnn-owner-serialized
     owner nil
     (lambda ()
       (unless (eq (fnn-owner-core 'fn-owner-bp-receipt-gatep view obs) t)
         (return-from fnn-bpnode-receipt-result
           (values :receipt-refused (fnn-bpnode-receipt-detail view obs))))
       (let ((journal nil))
         (unwind-protect
              (progn
                (setq journal
                      (fnn-app-open (fnn-owner-service-store owner)
                                    workflow-root :workflow :owner-mode t))
                (let ((record (fnn-owner-core
                               'fn-owner-bp-receipt-release-record view obs))
                      (detail (fnn-bpnode-receipt-detail view obs)))
                  (unless record
                    (fnn-out "BP node release refused detail=~a"
                             (fnn-octets-string (fnn-octets detail)))
                    (return-from fnn-bpnode-receipt-result
                      (values :receipt-refused detail)))
                  (fnn-workflow-commit-receipt-intent
                   journal record
                   (lambda (release)
                     (fnn-bpo-canonical-release owner release)))
                  (values :receipt-accepted detail)))
           (when journal (fnn-app-journal-close journal))))))))

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

;;; The operator's budgets (spec bp-node-machine 2.1, 4.2, 4.3.1): optional
;;; rows `owner-backoff N' and `retry-budget N' in JOURNAL/bp-node-budgets.
;;; The host bounds the text; ACL2 supplies the defaults and validates
;;; (fn-bpnp-configured-budgets).  Every event that decides with them
;;; carries them as its last field.
(defvar *fnn-bpnode-budgets* nil)

(defun fnn-bpnode-read-budgets (journal-root)
  (let* ((path (concatenate 'string journal-root "/bp-node-budgets"))
         (backoff nil) (retries nil))
    (when (probe-file path)
      (let ((text (fnn-octets-string (fnn-read-regular-bounded path 256))))
        (dolist (line (loop with start = 0
                            for end = (position #\Newline text :start start)
                            collect (subseq text start (or end (length text)))
                            while end do (setq start (1+ end))))
          (let* ((space (position #\Space line))
                 (key (and space (subseq line 0 space)))
                 (value (and space (subseq line (1+ space)))))
            (cond ((zerop (length line)))
                  ((not (and key (<= 1 (length value) 20)
                             (every #'digit-char-p value)))
                   (fnn-refuse "bp-node: malformed budget row"))
                  ((string= key "owner-backoff")
                   (setq backoff (parse-integer value)))
                  ((string= key "retry-budget")
                   (setq retries (parse-integer value)))
                  (t (fnn-refuse "bp-node: unknown budget row")))))))
    (let ((budgets (fnn-core 'fn-bpnp-configured-budgets backoff retries)))
      (unless budgets (fnn-refuse "bp-node: ACL2 refused the budget rows"))
      (fnn-out "BP node budgets owner-backoff=~d retry-budget=~d"
               (second budgets) (third budgets))
      budgets)))

(defun fnn-bpnode-budgeted (event)
  (if *fnn-bpnode-budgets* (append event (list *fnn-bpnode-budgets*)) event))

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
             bp (fnn-bpnode-budgeted
                 (list :progress node observation
                       (fnn-core 'fn-bpnp-single-peer-routes
                                 (fnn-bp-eid configured-peer))
                       0)))))
      (unless effects (return-from fnn-bpnode-dispatch-one nil))
      (when (and (= (length effects) 1)
                 (eq (first (first effects)) :delivery-stranded))
        ;; Reported on every tick while stranded; nothing else to do.
        (fnn-bps-drive-effects bp effects)
        (return-from fnn-bpnode-dispatch-one nil))
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
                   bp (if (eq status :busy)
                          ;; BP-R17: the seven-field busy event carries the
                          ;; observation ACL2 dates the deferral from.
                          (fnn-bpnode-budgeted
                           (list :deliver-result (second effect) (third effect)
                                 key :busy detail
                                 (fnn-bp-observation
                                  (fnn-bp-tally-wall tally)
                                  (fnn-bp-tally-wall-error tally))))
                        (list :deliver-result (second effect) (third effect)
                              key status detail)))))
            (fnn-bps-drive-effects bp result)
            (when (eq status :uncertain)
              (fnn-indeterminate
               "BP node application result is uncertain; recovery required"))
            (unless (eq status :busy)
              (fnn-bpnode-pause-at-durable-cut
               "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN"
               "BP NODE KIND7 DURABLE"))
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

;;; Routing (spec bp-node-machine 4.6).  ACL2 decides the outbound
;;; neighbour: `fn-bprt-outbound-choice' over the configuration's route table
;;; (`fn-owner-bp-route-table') names the boundary, the node ID its contact
;;; must announce and its contact port (the boundary's own `contact' row).
;;; CONTACT-HOST:PORT on the command line no longer chooses the next hop; a
;;; destination with no route opens no session and its rows stay held.
(defun fnn-bpnode-forward-contact (bp node-id peer-id transfer-mru wall wall-error)
  "Drive one ACL2-selected held forwarding attempt on one routed session."
  (let ((peer (fnn-bp-eid peer-id)))
    (unless (eq (fnn-core 'fn-bpnp-has-forward-pendingp
                           (fnn-core 'fn-bpnf-held-list (fnn-bps-state bp)) peer) t)
      (return-from fnn-bpnode-forward-contact nil))
    (let* ((table (fnn-owner-core 'fn-owner-bp-route-table))
           (choice (fnn-core 'fn-bprt-outbound-choice
                             (fnn-core 'fn-bpaj-eid-text peer) table)))
      (unless (eq (first choice) :hop)
        (fnn-out "BP forwarding no-route destination=~a decision=~(~a~) (held; the obligation stays)"
                 peer-id (first choice))
        (return-from fnn-bpnode-forward-contact nil))
      (fnn-bpnode-forward-session bp node-id peer transfer-mru wall wall-error
                                  (second choice) (third choice) (fourth choice)
                                  table))))

(defun fnn-bpnode-forward-session
    (bp node-id peer transfer-mru wall wall-error hop hop-eid hop-port table)
    (let ((socket nil)
          (sent nil)
          (settled nil)
          (session-id
            (cons (fnn-core 'fn-bpnf-epoch (fnn-bps-state bp))
                  (incf (fnn-bps-next-session bp)))))
      (handler-case
          (unwind-protect
               (progn
                 (fnn-out "BP forwarding route hop=~a port=~d" hop hop-port)
                 (setq socket (fnn-tcl-connect "127.0.0.1" hop-port))
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
                           ;; The expected TCPCL peer is the routed
                           ;; boundary's enrolled EID: ACL2's session
                           ;; machine refuses any other SESS_INIT node ID
                           ;; (fn-tcl-init-acceptablep), and the routed
                           ;; :session event checks it again
                           ;; (fn-bprt-offer-decision).
                           (fnn-tcl-params node-id hop-eid +fnn-tcl-keepalive+
                                           +fnn-tcl-segment-mru+ transfer-mru)
                           "bp-node-forward" (fnn-bps-root bp)
                           :on-ready
                           (lambda (connection)
                             (let* ((negotiated
                                      (fnn-core 'fn-tcl-session-negotiated
                                                (fnn-tclc-session connection)))
                                    (mru (fnn-core 'fn-tcl-negotiated-transfer-mtu
                                                   negotiated))
                                    (announced (fnn-core 'fn-tcl-negotiated-peer-node-id
                                                         negotiated))
                                    (obs (fnn-bp-observation wall wall-error)))
                               (fnn-bps-drive-effects
                                bp (fnn-bps-foundation-step
                                    bp (fnn-bpnode-budgeted
                                        (list :session peer session-id t mru obs
                                              (list :via hop announced table)))))
                               (when sent
                                 (setf (fnn-tclc-pending connection)
                                       (cons "bp-node-forward" (seventh sent)))
                                 (fnn-out "BP forwarding attempt durable key=~s"
                                          (sixth sent))))))))
                   (when sent
                     ;; ACL2 reads the transfer: :sent, (:refused r), :failed,
                     ;; or :uncertain when the connection ended without an
                     ;; XFER_ACK or XFER_REFUSE.  :uncertain is recorded as
                     ;; its kind 9 and costs this connection only (spec
                     ;; 4.3.1): the row is retried on a later session.
                     (let ((result
                             (fnn-core 'fn-bpnp-tcpcl-outcome
                                       (fnn-tclc-outcome conn)
                                       (fnn-tclc-refusal conn))))
                       ;; Model cut N08: kind 8 durable, the transfer ran, no
                       ;; kind 9 proposed.  Recovery re-offers (spec 4.3.1).
                       (fnn-bpnode-pause-at-durable-cut
                        "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_EIGHT_SENT"
                        "BP NODE KIND8 SENT")
                       (fnn-bpnode-forward-result
                        bp sent session-id result wall wall-error)
                       (setq settled t)))
                   (fnn-bps-drive-effects
                    bp (fnn-bps-foundation-step
                        bp (list :session peer session-id nil 1
                                 (fnn-bp-observation wall wall-error))))))
            (when socket (fnn-socket-shut socket)))
        ((or fnn-os-error sb-bsd-sockets:socket-error) (e)
          (cond
            ((not sent)
             (fnn-out "BP forwarding session unavailable: ~a" e))
            ((eq (fnn-bps-outcome bp) :uncertain)
             ;; A publication inside the session was uncertain: that is a
             ;; shared-owner fault, not a connection-local one.
             (fnn-indeterminate
              "bp-node: publication uncertain during forwarding: ~a" e))
            (t
             ;; The connection failed after the durable kind 8.  Unless its
             ;; kind 9 is already durable, ACL2 reads the transfer
             ;; (:uncertain), its kind 9 keeps the attempt's count, and the
             ;; node goes on; either way the session closes.
             (fnn-out "BP forwarding connection failed after durable attempt: ~a" e)
             (unless settled
               (fnn-bpnode-forward-result
                bp sent session-id
                (fnn-core 'fn-bpnp-tcpcl-outcome :connection-failed nil)
                wall wall-error))
             (fnn-bps-drive-effects
              bp (fnn-bps-foundation-step
                  bp (list :session peer session-id nil 1
                           (fnn-bp-observation wall wall-error))))))))
      sent))

(defun fnn-bpnode-forward-result (bp sent session-id result wall wall-error)
  (when (eq result :uncertain)
    (fnn-out "BP forwarding transfer uncertain arrival-key=~s (connection-local; retried on a later session)"
             (sixth sent)))
  (fnn-bps-drive-effects
   bp (fnn-bps-foundation-step
       bp (list :forward-result (fourth sent) (fifth sent) session-id
                result (fnn-bp-observation wall wall-error)))))

;;; `bp-node resume JOURNAL NODE-ID ARRIVAL [WALL WALL-ERROR]': the operator
;;; re-arms a stranded forwarding row (spec bp-node-machine 4.3.1).  ACL2
;;; decides (fn-bpnp-step's :operator-resume arm): a stranded row gets a
;;; durable kind 9 :resumed naming its last attempt and becomes a forward
;;; candidate again; anything else is refused with its reason.  Run it with
;;; the node stopped: it takes the FNBS lifecycle lock as `bp-node serve' does.
(defun fnn-command-bp-node-resume (journal-root node-id arrival wall wall-error)
  (let* ((config (fnn-bp-config node-id +fnn-bp-lifetime+ +fnn-bp-crc-type+
                                +fnn-bp-hop-limit+ +fnn-tcl-transfer-mru+))
         (bp (fnn-bps-open journal-root config wall wall-error)))
    (setq *fnn-bpnode-budgets* (fnn-bpnode-read-budgets journal-root))
    (unwind-protect
         (progn
           (fnn-bps-drive-effects
            bp (fnn-bps-foundation-step
                bp (fnn-bpnode-budgeted (list :operator-resume arrival))))
           (fnn-bps-exit-code bp))
      (fnn-bps-release bp))))
;;; `bp-node checkpoint JOURNAL NODE-ID [WALL WALL-ERROR]': rotate the FNBS
;;; journal (spec bp-node-machine 3.6, N16).  Open recovers; ACL2 names the
;;; next generation (fn-bpnr-next-generation over the selected one and every
;;; generation directory observed) and the checkpoint of the replay the
;;; recovery event carried (fn-bpnr-checkpoint-of-event); fn-bpnp-step's
;;; :rotate arm admits it only when it is the recovered state's own durable
;;; projection, and resets the record count only on the durable answer of
;;; the selection publication.  Run it with the node stopped.
(defun fnn-command-bp-node-checkpoint (journal-root node-id wall wall-error)
  (let* ((config (fnn-bp-config node-id +fnn-bp-lifetime+ +fnn-bp-crc-type+
                                +fnn-bp-hop-limit+ +fnn-tcl-transfer-mru+))
         (bp (fnn-bps-open journal-root config wall wall-error)))
    (unwind-protect
         (let* ((root (fnn-bps-root bp))
                (names (fnn-list-directory-bounded
                        root (fnn-core 'fn-bpnf-namespace-max-entries)
                        "bp journal root"))
                (generation (fnn-core 'fn-bpnr-next-generation
                                      (fnn-core 'fn-bpnr-plan-generation
                                                (fnn-bps-plan bp))
                                      names))
                (ck (fnn-core 'fn-bpnr-checkpoint-of-event
                              (fnn-bps-recovery-event bp) generation)))
           (fnn-out "BP journal rotation generation=~d" generation)
           (fnn-bps-drive-effects
            bp (fnn-bps-foundation-step bp (list :rotate generation ck)))
           (fnn-bps-exit-code bp))
      (fnn-bps-release bp))))

(defvar *fnn-bpnode-receipt-signer* nil
  "Directory of B's receipt-signing material, or nil for bare receipts:
principal (32 octets), ed25519.public (32), ed25519.secret (64),
ml-dsa-65.public.pem, ml-dsa-65.private.pem.")

(defun fnn-bpnode-signer-file (name width label)
  (let ((octets (fnn-read-regular-bounded
                 (concatenate 'string *fnn-bpnode-receipt-signer* "/" name)
                 width)))
    (unless (= (length octets) width)
      (fnn-refuse (format nil "BP node receipt signer ~a is not ~d octets"
                          label width)))
    (fnn-octet-list octets)))

(defun fnn-bpnode-signed-receipt (adu requester)
  "The receipt payload B queues, as an octet list: FNRJ's ADU, signed by
B's keys when B has them.  ACL2 builds the preimage
(`fn-bpsr-host-preimage') and the frame (`fn-bpsr-host-encode'); the host
only runs the two signing primitives, the path `fn hybrid-sign' uses."
  (let ((bare (fnn-octet-list adu)))
    (unless *fnn-bpnode-receipt-signer*
      (return-from fnn-bpnode-signed-receipt bare))
    (let* ((dir *fnn-bpnode-receipt-signer*)
           (principal (fnn-bpnode-signer-file "principal" 32 "principal"))
           (ed-public (fnn-bpnode-signer-file "ed25519.public" 32
                                              "Ed25519 public key"))
           (ed-secret (fnn-bpnode-signer-file "ed25519.secret" 64
                                              "Ed25519 secret key"))
           (ml-private (concatenate 'string dir "/ml-dsa-65.private.pem"))
           (ml-public
             (coerce (fnn-hsig-ml-dsa-65-public-key
                      (concatenate 'string dir "/ml-dsa-65.public.pem"))
                     'list))
           (keys (list (cons :ed25519 ed-public) (cons :ml-dsa-65 ml-public)))
           (preimage (fnn-core 'fn-bpsr-host-preimage
                               principal keys requester bare)))
      (unless (and (consp preimage) (fnn-octet-list-p preimage))
        (fnn-refuse "BP node receipt is outside the signed-receipt profile"))
      (let* ((ed (fnn-octet-list
                  (fnn-hsig-ed25519-sign (fnn-octets ed-secret) preimage)))
             (ml (fnn-octet-list
                  (fnn-hsig-ml-dsa-65-sign ml-private preimage)))
             (signed (fnn-core 'fn-bpsr-host-encode bare principal ed ml)))
        (unless (and (consp signed) (fnn-octet-list-p signed))
          (fnn-refuse "ACL2 refused the signed receipt frame"))
        (fnn-out "BP node receipt signed principal=~a octets=~d"
                 (subseq (fnn-hex principal) 0 16) (length signed))
        signed))))

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
                      ;; Signed receipts: B signs FNRJ's exact ADU when it
                      ;; has keys; the status checks below still bind the
                      ;; job to FNRJ's ADU (`fn-bpah-outbox-job-matchp').
                      (payload (fnn-bpnode-signed-receipt adu (fifth view)))
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
                               route peer payload observation)))
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

(defun fnn-bpnode-send-receipts (bp peer-id)
  "Send the owed receipts `fnn-bpnode-queue-outboxes' queued for PEER-ID on
this node's own base contact, so `bp-contact tick' is not the only path
(spec bp-node-machine 9.4).  ACL2 decides whether a contact opens
(fn-bpnp-receipt-contact-event: a queued job for the peer, nothing issued,
fenced or pending); the offer is the lower machine's, on the job's route.
The send drives the same effects as `bp-contact tick', so an uncertain or
refused transfer stays in (fnn-bps-outcome bp) for the exit code."
  (when (eq (fnn-bps-outcome bp) :uncertain)
    (fnn-indeterminate "BP node lifecycle is uncertain; recovery required"))
  (let ((event (fnn-core 'fn-bpnp-receipt-contact-event
                         (fnn-bps-state bp) (fnn-bp-eid peer-id))))
    (when event
      (fnn-out "BP node receipt contact peer=~a" peer-id)
      (fnn-bpc-drive-contact bp event))
    bp))

(defun fnn-command-bp-node
    (listen-port once journal-root store-root receipt-root workflow-root
     node-id peer-id destination policy issuer contact-host contact-port
     lifetime crc-type hop-limit transfer-mru wall wall-error reports-enabled
     &optional receipt-signer)
  ;; Signed receipts: the directory of this node's receipt-signing keys, or
  ;; nil (bare receipts, the delegation profile).
  (setq *fnn-bpnode-receipt-signer* receipt-signer)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         ;; FNBS (and its clock-domain gate) opens before any Store/FNRJ or
         ;; sequence operation.  There is exactly one BP lifecycle owner.
         (bp (fnn-bps-open journal-root config wall wall-error))
         (owner nil)
         (listener nil)
         (code +fnn-exit-ok+))
    (setq *fnn-bpnode-budgets* (fnn-bpnode-read-budgets journal-root))
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
            bp node-id peer-id transfer-mru wall wall-error)
           (fnn-bpnode-queue-outboxes
            bp owner receipt-root destination policy issuer node-id peer-id
            contact-host contact-port transfer-mru wall wall-error)
           (fnn-bpnode-send-receipts bp peer-id)
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
                                ;; No expected TCPCL peer: the neighbour is
                                ;; whichever node the enrolled boundary names,
                                ;; decided by ACL2's fn-bpaj-session-principal
                                ;; from the announced EID and the observed
                                ;; channel (fnn-bp-deliver-node).  PEER-ID is
                                ;; the application peer (receipt routes), and
                                ;; through a relay it is not the neighbour.
                                (fnn-tcl-params
                                 node-id nil +fnn-tcl-keepalive+
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
                 bp node-id peer-id transfer-mru wall wall-error)
                (fnn-bpnode-queue-outboxes
                 bp owner receipt-root destination policy issuer node-id peer-id
                 contact-host contact-port transfer-mru wall wall-error)
                (fnn-bpnode-send-receipts bp peer-id)
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
  (when (string= command "resume")
    ;; JOURNAL NODE-ID ARRIVAL [WALL WALL-ERROR]
    (when (< (length args) 3)
      (error 'fnn-usage-error
             :message "bp-node resume: JOURNAL NODE-ID ARRIVAL [WALL WALL-ERROR]"))
    (return-from fnn-dispatch-bp-node
      (fnn-command-bp-node-resume
       (first args) (second args) (parse-integer (third args))
       (and (fourth args) (parse-integer (fourth args)))
       (if (fifth args) (parse-integer (fifth args)) 0))))
  (when (string= command "checkpoint")
    ;; JOURNAL NODE-ID [WALL WALL-ERROR]
    (when (< (length args) 2)
      (error 'fnn-usage-error
             :message "bp-node checkpoint: JOURNAL NODE-ID [WALL WALL-ERROR]"))
    (return-from fnn-dispatch-bp-node
      (fnn-command-bp-node-checkpoint
       (first args) (second args)
       (and (third args) (parse-integer (third args)))
       (if (fourth args) (parse-integer (fourth args)) 0))))
  (unless (member command '("serve" "dispatch") :test #'string=)
    (error 'fnn-usage-error :message "bp-node: expected serve, dispatch or resume"))
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
       (string= (arg 18 "0") "1")
       (arg 19)))))

(fnn-register-verb "bp-node" #'fnn-dispatch-bp-node)
