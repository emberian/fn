;;; Native BP application receiver over the one writable owner Store.
(in-package "ACL2")

(defun fnn-bpapp-core-record (name &rest args)
  (let ((record (apply #'fnn-core-state name args)))
    (unless (and (consp record) (keywordp (first record)))
      (fnn-fault "BP application core returned no record from ~a" name))
    record))

(defun fnn-bpapp-action (journal request generation)
  (declare (ignore journal))
  (let ((answer (fnn-core-state 'fn-bprj-request-action
                                (fnn-octet-list request) generation)))
    (unless (and (consp answer) (keywordp (first answer)))
      (fnn-fault "BP application dispatcher returned malformed action"))
    answer))

(defun fnn-bpapp-bind-owner-store ()
  (unless (eq (fnn-owner-action 'fn-owner-app-bind-receipt-store) :ready)
    (fnn-fault "BP application could not bind the canonical owner Store")))

(defun fnn-bpapp-request-intent (journal inbound-id request generation txid result)
  (let ((record
          (fnn-bpapp-core-record
           'fn-bprj-request-intent-record inbound-id (fnn-octet-list request)
           generation txid result)))
    (fnn-app-publish journal record)))

(defun fnn-bpapp-bind-context (journal request application-result)
  ;; Rebind after the Store transition, then select the one exact committed
  ;; record through ACL2.  The native adapter never enumerates candidates.
  (fnn-bpapp-bind-owner-store)
  (unless (eq (fnn-owner-action 'fn-owner-app-record) :found)
    (fnn-fault "BP application completion has no exact committed Store record"))
  (let* ((inbound-id
           (fnn-core-state 'fn-bprj-request-bound-inbound-id
                           (fnn-octet-list request)))
         (generation
           (fnn-core-state 'fn-bprj-request-bound-generation
                           (fnn-octet-list request)))
         (planned
           (fnn-core-state 'fn-bprj-request-planned-result
                           (fnn-octet-list request)))
         (record (fnn-global 'fn-owner-app-record))
         (txid (fnn-global 'fn-owner-app-record-txid))
         (record-generation (fnn-global 'fn-owner-app-record-generation)))
    (unless (and (stringp inbound-id) (integerp generation) (>= generation 0)
                 (member planned '(:accepted :duplicate))
                 (eq application-result planned)
                 (fnn-octet-list-p record)
                 (integerp txid) (>= txid 0)
                 (integerp record-generation) (>= record-generation 0))
      (fnn-fault "BP application result disagrees with durable request intent"))
    (let ((context
            (fnn-bpapp-core-record
             'fn-bprj-request-context-v2-record
             inbound-id (fnn-octet-list request) record generation txid
             record-generation application-result)))
      (fnn-app-publish journal context))))

(defun fnn-bpapp-receipt (journal request)
  (let ((work-id (fnn-core-state 'fn-bprj-request-work-id
                                 (fnn-octet-list request)))
        (receipt-id (fnn-core-state 'fn-bprj-request-receipt-id
                                   (fnn-octet-list request))))
    (unless (and (stringp work-id) (stringp receipt-id))
      (fnn-fault "BP application request has no receipt identity"))
    (fnn-receipt-prepare journal work-id receipt-id)
    (fnn-receipt-decide journal work-id receipt-id :committed)
    (let ((adu (fnn-receipt-adu journal (fnn-octet-list request))))
      (unless adu (fnn-fault "durable BP application receipt did not replay"))
      adu)))

(defun fnn-bpapp-accept-locked
    (service journal inbound-id request node-id bundle-identity
             bundle-source bundle-destination)
  "Run one request through FNRJ, owner Store, FNFD, and receipt decision.
The caller holds SERVICE's mutex for this whole function."
  (fnn-bpapp-bind-owner-store)
  (unless (eq (fnn-owner-action
               'fn-owner-app-plan inbound-id (fnn-octet-list request) node-id
               (fnn-octet-list bundle-identity) bundle-source bundle-destination)
              :ready)
    (return-from fnn-bpapp-accept-locked (values :refused nil)))
  (let ((generation (fnn-nat (fnn-global 'fn-owner-app-generation)))
        (txid (fnn-nat (fnn-global 'fn-owner-app-txid)))
        (planned (fnn-global 'fn-owner-app-planned-result))
        (application-result nil))
    (dotimes (step 8)
      (declare (ignore step))
      ;; The owner may have committed a Store record on the preceding
      ;; iteration.  Rebind the FNRJ dispatcher to that same canonical Store
      ;; before asking for its next action; a stale pre-commit snapshot would
      ;; incorrectly ask to submit the request a second time.
      (fnn-bpapp-bind-owner-store)
      (let ((action (fnn-bpapp-action journal request generation)))
        (case (first action)
          (:persist-intent
           (fnn-bpapp-request-intent journal inbound-id request generation
                                     txid planned))
          (:submit
           (let ((msgid (fnn-octets (fnn-global 'fn-owner-app-msgid)))
                 (payload (fnn-octets (fnn-global 'fn-owner-app-article)))
                 (groups (mapcar #'fnn-octets
                                 (fnn-global 'fn-owner-app-groups)))
                 (evidence (fnn-octets (fnn-global 'fn-owner-app-evidence))))
             ;; Observe at the actual Store submission, under the owner lock.
             ;; A replay that only binds a committed result does not need time.
             (unless (and (eq (fnn-owner-advance-clock) :observed)
                          (eq (fnn-owner-action 'fn-owner-stamp-status)
                              :usable))
               (return-from fnn-bpapp-accept-locked
                 (values :clock-unusable nil)))
             (setq application-result
                   (fnn-owner-complete-bound-submission
                    service
                    (lambda () (fnn-owner-action 'fn-owner-app-submit))
                    msgid payload groups evidence generation txid))
             (unless (member application-result '(:accepted :duplicate))
               (return-from fnn-bpapp-accept-locked
                 (values application-result nil)))))
          (:bind
           (unless application-result
             (setq application-result
                   (fnn-core-state 'fn-bprj-request-planned-result
                                   (fnn-octet-list request))))
           (fnn-bpapp-bind-context journal request application-result))
          (:prepare-receipt
           (let ((adu (fnn-bpapp-receipt journal request))
                 (result (or application-result
                             (fnn-core-state 'fn-bprj-request-result
                                             (fnn-octet-list request)))))
             (return-from fnn-bpapp-accept-locked (values result adu))))
          (:resolve-absent
           (let ((record (fnn-bpapp-core-record
                          'fn-bprj-pending-receipt-resolution)))
             (fnn-app-publish journal record)))
          (:return-receipt
           (let ((adu (fnn-receipt-adu journal (fnn-octet-list request)))
                 (result (fnn-core-state 'fn-bprj-request-result
                                         (fnn-octet-list request))))
             (unless (and adu (member result '(:accepted :duplicate)))
               (fnn-fault "committed BP application receipt lost its result"))
             (return-from fnn-bpapp-accept-locked (values result adu))))
          (:busy (return-from fnn-bpapp-accept-locked (values :busy nil)))
          (:refused (return-from fnn-bpapp-accept-locked (values :refused nil)))
          (otherwise (fnn-fault "unknown BP application action ~a" action)))))
    (fnn-fault "BP application dispatcher did not reach a terminal state")))

(defun fnn-bpapp-pause-after-decision ()
  ;; Test-only process-death cut named by books/bp-native-app's replay states:
  ;; decision is durable, no receipt bundle has yet been authored or offered.
  (when (string= (or (fnn-developer-selector "FN_BP_APP_TEST_PAUSE_AFTER_DECISION") "") "1")
    (fnn-out "BP APP DECISION DURABLE")
    (finish-output)
    (loop (sleep 1))))

(defun fnn-bpapp-deliver (service journal tally node-id conn xfer-id wire)
  (let* ((obs (fnn-bp-observation (fnn-bp-tally-wall tally)
                                  (fnn-bp-tally-wall-error tally)))
         (received (fnn-core 'fn-bpapp-receive
                             (fnn-bp-tally-config tally) wire obs))
         (outcome (fnn-core 'fn-bpapp-receive-outcome received))
         (reason (fnn-core 'fn-bpapp-receive-reason received))
         (adu (fnn-core 'fn-bpapp-receive-adu received)))
    (case outcome
      (:accepted
       (let* ((identity (fnn-core 'fn-bpapp-receive-identity received))
              (source (fnn-core 'fn-bpapp-receive-source received))
              (destination (fnn-core 'fn-bpapp-receive-destination received))
              (inbound-id
                (fnn-octets-string
                 (fnn-octets (fnn-core 'fn-id-hex-octets identity))))
              (path (fnn-bp-evidence-publish tally :accepted wire adu))
              (app-result nil)
              (receipt nil))
         (multiple-value-setq (app-result receipt)
           (fnn-owner-serialized
            service nil
            (lambda ()
              (fnn-bpapp-accept-locked
               service journal inbound-id (fnn-octets adu) node-id
               (fnn-octets identity) source destination))))
         (unless (member app-result '(:accepted :duplicate))
           (incf (fnn-bp-tally-refused tally))
           (fnn-out "BP application ~(~a~) xfer=~d" app-result xfer-id)
           (return-from fnn-bpapp-deliver (list :refused app-result)))
         (fnn-bpapp-pause-after-decision)
         (let* ((peer (fnn-bp-eid source))
                (sequence (fnn-bp-reserve-sequence tally))
                (reply-observation
                  (fnn-bp-observation (fnn-bp-tally-wall tally)
                                      (fnn-bp-tally-wall-error tally)))
                (bundle (fnn-core 'fn-bpn-host-send
                                  (fnn-bp-tally-config tally) peer
                                  (fnn-octet-list receipt) sequence
                                  reply-observation)))
           (unless bundle
             (fnn-fault "BP application receipt could not be authored"))
           (when (fnn-tclc-pending conn)
             (fnn-fault "BP application connection already has an offer"))
           (setf (fnn-tclc-pending conn) (cons "receipt" bundle))
           (incf (fnn-bp-tally-accepted tally))
           (setf (fnn-bp-tally-last-adu tally) adu)
           (fnn-out "BP application ~(~a~) xfer=~d receipt=~d"
                    app-result xfer-id (length receipt))
           (list :accepted path))))
      (:refused
       (incf (fnn-bp-tally-refused tally))
       (fnn-bp-evidence-publish
        tally :refused wire
        (fnn-octet-list (fnn-string-octets (format nil "~(~a~)~%" reason))))
       (list :refused reason))
      (otherwise
       (incf (fnn-bp-tally-uncertain tally))
       (fnn-bp-evidence-publish
        tally :uncertain wire
        (fnn-octet-list (fnn-string-octets (format nil "~(~a~)~%" reason))))
       (list :uncertain reason)))))

(defun fnn-bpapp-open-journal (service receipt-root destination policy issuer)
  (fnn-owner-serialized
   service nil
   (lambda ()
     (fnn-bpapp-bind-owner-store)
     (let ((journal (fnn-app-open (fnn-owner-service-store service)
                                  receipt-root :receipt)))
       (case (fnn-owner-action 'fn-bprj-config-status
                               destination policy issuer)
         (:absent (fnn-receipt-initialize journal
                                          (list destination policy issuer)))
         (:match nil)
         (otherwise
          (fnn-app-journal-close journal)
          (fnn-refuse "BP application receipt configuration conflicts")))
       journal))))

(defun fnn-command-bp-app-receive
    (port once spool store-root receipt-root node-id peer-eid destination
          policy issuer lifetime crc-type hop-limit transfer-mru
          max-connections wall wall-error)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (journal-root (fnn-bp-journal-dir spool))
         (spool-lock (fnn-tcl-spool-acquire journal-root))
         (service nil) (journal nil) (listener nil))
    (unwind-protect
         (progn
           (setq service (fnn-owner-install store-root max-connections))
           (setq journal (fnn-bpapp-open-journal
                          service receipt-root destination policy issuer))
           (let ((tally (fnn-bp-evidence-open
                         (make-fnn-bp-tally
                          :config config :wall wall :wall-error wall-error
                          :journal journal-root :spool-lock spool-lock))))
             (let ((*fnn-tcl-deliver*
                     (lambda (conn xfer-id octets)
                       (fnn-bpapp-deliver service journal tally node-id
                                          conn xfer-id octets))))
               (multiple-value-bind (bound bound-port) (fnn-tcl-listen port)
                 (setf listener bound
                       (fnn-owner-service-listener service) bound)
                 (fnn-out "BP APP LISTENING ~d" bound-port))
               (fnn-accept-loop
                listener
                (lambda (socket)
                  (unwind-protect
                       (fnn-tcl-session
                        (fnn-socket-fd socket) :passive
                        (fnn-tcl-params node-id peer-eid +fnn-tcl-keepalive+
                                        +fnn-tcl-segment-mru+ transfer-mru)
                        "bp-app" journal-root)
                    (fnn-socket-shut socket)))
                once)
               (fnn-bp-summary tally)
               (fnn-bp-exit-code tally nil))))
      (when listener (fnn-socket-shut listener))
      (when journal (fnn-app-journal-close journal))
      (when service
        (ignore-errors (fnn-owner-action 'fn-owner-app-unbind-receipt-store))
        (fnn-owner-feed-close-all service)
        (fnn-store-close (fnn-owner-service-store service)))
      (fnn-tcl-spool-release spool-lock))))

(defun fnn-dispatch-bp-app (command args)
  (unless (string= command "receive")
    (error 'fnn-usage-error :message "unknown bp-app command"))
  (when (< (length args) 11)
    (error 'fnn-usage-error
           :message "bp-app receive PORT SPOOL STORE RECEIPTS NODE PEER DEST POLICY ISSUER ONCE MAX-CONNS"))
  (flet ((arg (n &optional default) (or (nth n args) default))
         (number (n default) (parse-integer (or (nth n args)
                                                (write-to-string default))))
         (optional-number (n) (and (nth n args) (parse-integer (nth n args)))))
    (fnn-command-bp-app-receive
     (parse-integer (arg 0)) (string= (arg 9 "1") "1")
     (arg 1) (arg 2) (arg 3) (arg 4) (arg 5) (arg 6) (arg 7) (arg 8)
     (number 11 +fnn-bp-lifetime+) (number 12 +fnn-bp-crc-type+)
     (number 13 +fnn-bp-hop-limit+) (number 14 +fnn-tcl-transfer-mru+)
     (number 10 16) (optional-number 15) (number 16 0))))

(fnn-register-verb "bp-app" #'fnn-dispatch-bp-app)
