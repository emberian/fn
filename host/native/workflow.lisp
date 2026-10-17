;;; Native durable application workflow and receiver receipt journals.
;;;
;;; FNWF and FNRJ retain distinct ACL2 record interpreters.  They share only
;;; the immutable no-replace publication effect below.  At every physical
;;; boundary raw Lisp executes the action selected by books/journal-publish
;;; and reports the syscall observation back to that machine; raw Lisp never
;;; upgrades visible bytes after an error to :durable.
(in-package "ACL2")

(defstruct fnn-app-journal
  root records staging lock-fd store domain frontier
  (owner-mode nil)
  (close-debt nil)
  (fenced t))

(defun fnn-app-retain-close-debt (store holder fd condition)
  "Retain physical journal custody independently of persisted record outcomes."
  (when store
    (setf (fnn-store-fenced store) t)
    (push (list holder fd condition) (fnn-store-application-close-debts store))))

(defun fnn-app-journal-close (journal)
  (when (fnn-app-journal-close-debt journal)
    (fnn-indeterminate "application journal physical return unobserved; custody held: ~a"
                       (second (fnn-app-journal-close-debt journal))))
  (setf (fnn-app-journal-fenced journal) t)
  (let ((fd (fnn-app-journal-lock-fd journal)))
    (when fd
      ;; Consume the integer before close: a failed close may have released it.
      (setf (fnn-app-journal-lock-fd journal) nil)
      (handler-case
          (fnn-unwind-cleanups ()
            (fnn-flock fd +fnn-lock-un+)
            (fnn-close fd))
        (serious-condition (condition)
          (setf (fnn-app-journal-close-debt journal) (list fd condition))
          (fnn-app-retain-close-debt (fnn-app-journal-store journal) journal fd condition)
          (fnn-indeterminate "application journal physical return unobserved; custody held: ~a"
                             condition)))))
  nil)

(defun fnn-app-journal-lock (root domain &optional store)
  (let* ((name (case domain
                 (:workflow "workflow.lock")
                 (:carry "carry.lock")
                 (t "receipt.lock")))
         (path (fnn-join root name))
         (fd nil) (returned nil))
    (handler-case
        (setq fd (fnn-open path
                           (logior sb-posix:o-rdwr sb-posix:o-creat
                                   +fnn-o-nofollow+)
                           #o600))
      (fnn-os-error (e)
        (fnn-fault "application journal lock open failed: ~a" e)))
    (fnn-unwind-cleanups
        ((unless (fnn-regular-p (fnn-fstat fd))
           (fnn-fault "refusing non-regular application journal lock"))
         (handler-case (fnn-flock fd (logior +fnn-lock-ex+ +fnn-lock-nb+))
           (fnn-os-error (e)
             (if (or (= (fnn-os-errno e) sb-posix:eagain)
                     (= (fnn-os-errno e) sb-posix:eacces))
                 (fnn-refuse "application journal is already owned")
               (fnn-fault "application journal lock failed: ~a" e))))
         (setq returned t)
         fd)
      (unless returned
        (handler-case (fnn-close fd)
          (serious-condition (condition)
            (fnn-app-retain-close-debt store (list domain path) fd condition)
            (error condition)))))))

(defun fnn-app-require-live-store (store)
  ; The Store lock establishes ownership, but a fenced Store has no authority
  ; to derive or publish new application facts until recovery clears it.
  (unless (and (typep store 'fnn-store) (fnn-store-lock-fd store))
    (fnn-fault "application journal requires the live Store owner"))
  (when (fnn-store-fenced store)
    (fnn-indeterminate "application journal Store is fenced pending recovery"))
  t)

(defun fnn-app-record-names (journal)
  ; Ordering is an observation only.  fn-aj-host-recover decides whether each
  ; spelling is ACL2's exact next name and whether the frontier may advance.
  (sort (fnn-list-directory (fnn-app-journal-records journal)) #'string<))

(defun fnn-app-frame (journal record)
  (let* ((wrapper (case (fnn-app-journal-domain journal)
                   (:workflow 'fn-store-frame-workflow-logical-protected)
                   (:carry 'fn-workflow-carry-frame-protected)
                   (t 'fn-store-frame-receipt-logical-protected)))
         (prefix (fnn-core wrapper (first record) (rest record))))
    (when (or (keywordp prefix) (not (fnn-octet-list-p prefix)))
      ;; Name the journal and the record kind ACL2 refused (PKT-646).
      (fnn-refuse "ACL2 refused application journal record domain=~(~a~) kind=~(~a~)"
                  (fnn-app-journal-domain journal) (first record)))
    (fnn-seal (fnn-octets prefix))))

(defun fnn-app-unframe (journal raw)
  (let* ((wrapper (case (fnn-app-journal-domain journal)
                   (:workflow 'fn-store-frame-workflow-logical-decode)
                   (:carry 'fn-workflow-carry-frame-decode)
                   (t 'fn-store-frame-receipt-logical-decode)))
         (answer (fnn-core wrapper (fnn-octet-list raw)
                           (fnn-digest-of raw))))
    (unless (and (consp answer) (eq (first answer) :ok)
                 (keywordp (second answer)) (listp (third answer)))
      (fnn-fault "application journal frame refused"))
    (cons (second answer) (third answer))))

(defun fnn-app-read-profile (root domain)
  "ACL2's reading of ROOT's `app-journal-profile' for a DOMAIN journal
(fn-ajpf-read, books/app-journal): the default when the file is absent, the
operator's (RECORDS OCTETS) when it is one valid profile frame; anything else
is refused before a record is read."
  (let* ((path (fnn-join root (fnn-core 'fn-aj-host-profile-file-name)))
         (present (fnn-check-regular path))
         (profile (fnn-core 'fn-aj-host-profile-read domain (and present t)
                            (and present
                                 (fnn-octet-list
                                  (fnn-read-regular-bounded
                                   path (fnn-core 'fn-aj-host-profile-read-bound)))))))
    (unless profile
      (fnn-refuse "ACL2 refused the application journal profile ~a" path))
    profile))

(defun fnn-app-read-records (journal names)
  (let ((records nil)
        (frontier (fnn-app-journal-frontier journal))
        (maximum (fnn-core 'fn-aj-host-max-record-length
                           (fnn-app-journal-domain journal))))
    (dolist (name names)
      (let* ((path (fnn-join (fnn-app-journal-records journal) name))
             (raw (fnn-read-regular-bounded path maximum))
             (record (fnn-app-unframe journal raw))
             (next (fnn-core 'fn-aj-host-recover frontier name (length raw)
                             (first record))))
        (when (eq next :beyond-profile)
          (fnn-refuse "application journal ~a holds more than its profile admits (record ~a)"
                      (fnn-app-journal-root journal) name))
        (when (eq next :fault)
          (fnn-fault "ACL2 rejected application journal namespace/frontier"))
        (setq frontier next)
        (push record records)))
    (setf (fnn-app-journal-frontier journal) frontier)
    (nreverse records)))

(defun fnn-app-install (journal records)
  (when (eq (fnn-app-journal-domain journal) :carry)
    ;; PKT-869: the carry controls replay over the workflow image already
    ;; installed (books/bp-carry-control.lisp fn-bpcc-replay).
    (unless (eq (fnn-core-state 'fn-workflow-carry-install records) :ready)
      (fnn-fault "ACL2 rejected the carry control journal's replay"))
    (return-from fnn-app-install :ready))
  (let ((answer
          (if records
              (if (eq (fnn-app-journal-domain journal) :workflow)
                  (fnn-core-state
                   (if (fnn-app-journal-owner-mode journal)
                       'fn-owner-workflow-install-replay
                     'fn-workflow-install-replay)
                   records)
                (fnn-core-arena-state 'fn-bprj-install records))
            (if (eq (fnn-app-journal-domain journal) :workflow)
                (fnn-core-state
                 (if (fnn-app-journal-owner-mode journal)
                     'fn-owner-workflow-reset
                   'fn-workflow-reset))
              (fnn-core-state 'fn-bprj-reset)))))
    (unless (eq answer :ready)
      (fnn-fault "ACL2 rejected application journal replay"))
    :ready))

(defun fnn-app-open (store root domain &key owner-mode)
  "Open a journal beside an already-open Store; never replace its ACL2 image."
  (fnn-app-require-live-store store)
  (unless (member domain '(:workflow :receipt :carry))
    (fnn-fault "unknown application journal domain"))
  (let* ((absolute (fnn-absolute root))
         (records (fnn-join absolute "records"))
         (staging (fnn-join absolute "staging"))
         (journal nil))
    (handler-case
        (progn
          (fnn-safe-directory absolute t)
          (fnn-safe-directory records t)
          (fnn-safe-directory staging t)
          ; Repeat both namespace barriers before treating any visible final
          ; record as durable evidence after a prior uncertain publication.
          (fnn-fsync-dir (fnn-parent absolute))
          (fnn-fsync-dir absolute)
          (fnn-fsync-dir records)
          (setq journal
                (make-fnn-app-journal
                 :root absolute :records records :staging staging :store store
                 :domain domain :owner-mode (and owner-mode t)
                 :frontier nil
                 :lock-fd (fnn-app-journal-lock absolute domain store)))
          ;; The profile is read under the journal lock, so `app-journal
          ;; profile' (which holds it) never races the open.
          (setf (fnn-app-journal-frontier journal)
                (fnn-core 'fn-aj-host-initial domain
                          (fnn-app-read-profile absolute domain)))
          (let* ((names (fnn-app-record-names journal))
                 (records-image (fnn-app-read-records journal names)))
            (fnn-app-install journal records-image)
            (setf (fnn-app-journal-fenced journal) nil)
            journal))
      (error (e)
        (fnn-unwind-cleanups ((error e))
          (when journal (fnn-app-journal-close journal)))))))

(defun fnn-app-preflight (journal record)
  (let ((domain (fnn-app-journal-domain journal)))
    (when (eq domain :carry)
      (return-from fnn-app-preflight
        (eq (fnn-core-state 'fn-workflow-carry-preflight record) :ready)))
    (if (eq (first record) :config)
        (if (eq domain :workflow)
            (and (fnn-core 'fn-workflow-valid-config record) t)
          (eq (fnn-core-state 'fn-bprj-valid-config record) t))
      ;; The BP receiver reads the Store's rows through the arena (flip-L4).
      (eq (if (eq domain :workflow)
              (fnn-core-state
               (if (fnn-app-journal-owner-mode journal)
                   'fn-owner-workflow-preflight-record
                 'fn-workflow-preflight-record)
               record)
            (fnn-core-arena-state 'fn-bprj-preflight record))
          :ready))))

(defun fnn-app-apply (journal record)
  (when (eq (fnn-app-journal-domain journal) :carry)
    (unless (eq (fnn-core-state 'fn-workflow-carry-apply record) :ready)
      (fnn-fault "ACL2 rejected a durable carry control record"))
    (return-from fnn-app-apply :ready))
  (if (eq (first record) :config)
      (fnn-app-install journal (list record))
    (let ((answer
            (if (eq (fnn-app-journal-domain journal) :workflow)
                (fnn-core-state
                 (if (fnn-app-journal-owner-mode journal)
                     'fn-owner-workflow-apply-record
                   'fn-workflow-apply-record)
                 record)
              (fnn-core-arena-state 'fn-bprj-apply record))))
      (unless (eq answer :ready)
        (fnn-fault "ACL2 rejected durable application journal record"))
      :ready)))

(defun fnn-app-authorized-publish (journal kind frame reserve-resolution)
  "Ask ACL2 to allocate/admit one exact final name, then execute that operation."
  (let* ((frontier (fnn-app-journal-frontier journal))
         (candidate (fnn-core 'fn-aj-host-next-name frontier))
         (final (fnn-join (fnn-app-journal-records journal) candidate))
         ; The held lock and exact-name absence are observations.  ACL2 decides
         ; whether they authorize this record and reserves its outcome room.
         (operation
           (fnn-core 'fn-aj-host-authorize frontier kind (length frame)
                     (if reserve-resolution t nil)
                     (if (fnn-app-journal-lock-fd journal) t nil)
                     (if (fnn-lstat final) nil t))))
    (unless (eq (first operation) :ok)
      (fnn-refuse "ACL2 refused application journal admission"))
    (unless (eq (fnn-core 'fn-aj-host-operationp operation) t)
      (fnn-fault "ACL2 returned malformed application journal operation"))
    (unless (string= candidate
                     (fnn-core 'fn-aj-host-operation-name operation))
      (fnn-fault "ACL2 application journal allocation changed"))
    (let* ((stage (fnn-join (fnn-app-journal-staging journal)
                            (format nil "~d.~a.tmp" (sb-posix:getpid)
                                    (fnn-random-hex 16))))
           (observer
             (when (string= (or (fnn-developer-selector "FN_APP_JOURNAL_TEST_OBSERVER") "")
                            "assert-reported")
               (lambda (point publication)
                 (let ((phase (fnn-core 'fn-jpub-host-phase publication))
                       (expected (case point
                                   (:file-barrier :link-ready)
                                   (:link-result :directory-barrier)
                                   (:directory-barrier :durable))))
                   (unless (eq phase expected)
                     (fnn-fault "publication observer preceded ACL2 report"))))))
           (fault-observer
             (when (or (string= (or (fnn-developer-selector "FN_APP_JOURNAL_TEST_FAIL_RECEIPT_DECISION_NAMESPACE")
                                     "") "1")
                       (string= (or (fnn-developer-selector "FN_APP_JOURNAL_TEST_FAIL_RELEASE_NAMESPACE")
                                     "") "1"))
               (lambda (label point publication path)
                 (declare (ignore publication))
                 (when (and (eq point :directory-barrier)
                            (or (and (eq label :receipt-decision)
                                     (string= (or (fnn-developer-selector "FN_APP_JOURNAL_TEST_FAIL_RECEIPT_DECISION_NAMESPACE")
                                                  "") "1"))
                                (and (eq label :release)
                                     (string= (or (fnn-developer-selector "FN_APP_JOURNAL_TEST_FAIL_RELEASE_NAMESPACE")
                                                  "") "1"))))
                   (fnn-os-fail sb-posix:eio path)))))
           (outcome
             (fnn-immutable-publish-effect
              (fnn-core 'fn-aj-host-operation-publication operation)
              stage final (fnn-app-journal-records journal) frame
              :cleanup-directory (fnn-app-journal-staging journal)
              :observer observer
              :operation-label
              (fnn-core 'fn-aj-host-operation-label operation)
              :fault-observer fault-observer)))
      (cond ((eq outcome :durable)
             (setf (fnn-app-journal-frontier journal)
                   (fnn-core 'fn-aj-host-operation-successor operation)))
            ((eq outcome :uncertain)
             (setf (fnn-app-journal-fenced journal) t)))
      outcome)))

(defun fnn-app-publish (journal record &key reserve-resolution)
  "Preflight, durably publish, then apply one record through its ACL2 owner."
  ; Test injection models the owner fencing its Store between journal open and
  ; this operation.  The production guard below is the path under test.
  (when (string= (or (fnn-developer-selector "FN_APP_JOURNAL_TEST_FENCE_STORE") "")
                 "before-publish")
    (setf (fnn-store-fenced (fnn-app-journal-store journal)) t))
  (fnn-require-writer (fnn-app-journal-store journal))
  (fnn-app-require-live-store (fnn-app-journal-store journal))
  (when (fnn-app-journal-fenced journal)
    (fnn-indeterminate "application journal is fenced"))
  (unless (fnn-app-preflight journal record)
    (fnn-refuse "ACL2 rejected application journal ~(~a~) before publication"
                (first record)))
  (let ((frame (fnn-app-frame journal record)))
    (case (fnn-app-authorized-publish journal (first record) frame
                                      reserve-resolution)
      (:durable
       (handler-case (fnn-app-apply journal record)
         (error (e)
           (setf (fnn-app-journal-fenced journal) t)
           (error e)))
       :durable)
      (:refused (fnn-refuse "application journal publication refused"))
      (otherwise
       (fnn-indeterminate "application journal publication is uncertain")))))

;;; Sender workflow operations.  ACL2 preflight checks the recovered Store
;;; binding.  The durable outcome record is a separate immutable transaction.

(defun fnn-workflow-initialize (journal values)
  (when (fnn-core 'fn-aj-initializedp (fnn-app-journal-frontier journal))
    (fnn-refuse "workflow journal is already initialized"))
  (fnn-app-publish journal (cons :config values)))

(defun fnn-workflow-enqueue (journal values)
  (let ((intent (cons :enqueue values)))
    (fnn-app-publish journal intent :reserve-resolution t)
    (fnn-app-publish journal
                     (list :outcome (second intent) (third intent)
                           :ordinary :durable))))

(defun fnn-workflow-enqueue-for-article
  (journal txid generation work-id msgid forward-obligation-id peer-eid
           policy-id terms-id)
  (let ((record (fnn-core-state
                 'fn-workflow-enqueue-record txid generation work-id msgid
                 forward-obligation-id peer-eid policy-id terms-id)))
    (unless (and (consp record) (eq (first record) :enqueue))
      (fnn-refuse "workflow enqueue has no durable Store binding"))
    (fnn-workflow-enqueue journal (rest record))))

(defun fnn-workflow-status (journal work-id)
  (declare (ignore journal))
  (fnn-core-state 'fn-workflow-work-status work-id))

(defun fnn-workflow-undertake (journal work-id charge)
  (let ((record (fnn-core-state 'fn-workflow-undertake-record work-id charge)))
    (unless (and (consp record) (eq (first record) :undertake))
      (fnn-refuse "workflow forwarding obligation is not admissible"))
    (fnn-app-publish journal record)))

;;; Optional pinned-ION submission. The first network operation is inside the
;;; C helper, after both the FNWF attempt and ION route records are durable.
;;; Its observation file is transport evidence, not a receipt.

(defun fnn-workflow-ion-private-directory (path)
  (let* ((absolute (fnn-absolute path))
         (st (fnn-safe-directory absolute t)))
    (unless (and (= (sb-posix:stat-uid st) (sb-posix:geteuid))
                 (zerop (logand (sb-posix:stat-mode st) #o077)))
      (fnn-refuse "ION observation directory must be owner-private"))
    (fnn-fsync-dir absolute)
    absolute))

(defun fnn-workflow-ion-request-file (directory adu)
  (let* ((path (fnn-join directory
                         (format nil "request.~a.adu" (fnn-random-hex 16))))
         (fd nil))
    (unless (and (fnn-octet-list-p adu) (< 0 (length adu))
                 (<= (length adu) 65538))
      (fnn-fault "ACL2 returned an invalid ION request ADU"))
    (setq fd (fnn-open path
                       (logior sb-posix:o-wronly sb-posix:o-creat
                               sb-posix:o-excl +fnn-o-nofollow+)
                       #o600))
    (unwind-protect
         (progn (fnn-write-all fd adu) (fnn-fsync-file fd))
      (when fd (fnn-close fd)))
    (fnn-fsync-dir directory)
    path))

(defun fnn-workflow-ion-run-helper (helper own destination peer adu ttl observation)
  (let ((process
          (handler-case
              (sb-ext:run-program
               helper (list own destination peer adu (format nil "~d" ttl)
                            observation)
               :search nil :wait nil :output *standard-output*
               :error *error-output*)
            (error (e)
              (fnn-refuse "ION helper could not start before send: ~a" e)))))
    (let ((deadline (+ (fnn-now) (* 90 internal-time-units-per-second))))
      (loop while (sb-ext:process-alive-p process) do
        (when (<= (fnn-seconds-to-deadline deadline) 0)
          (ignore-errors (sb-ext:process-kill process sb-unix:sigkill))
          (sb-ext:process-wait process)
          (fnn-indeterminate "ION helper timed out after launch"))
        (sleep 0.05)))
    (sb-ext:process-wait process)
    (sb-ext:process-exit-code process)))

(defun fnn-workflow-ion-submit
    (journal txid tx-generation work-id attempt-id bp-destination own-bp-eid
             helper observation-directory)
  (let* ((seconds (fnn-core-state 'fn-workflow-ion-helper-seconds))
         ;; Admission precedes all journal publication and helper launch.
         (directory (progn
                      (unless seconds
                        (fnn-refuse "ION lifetime not exactly representable by helper"))
                      (fnn-workflow-ion-private-directory observation-directory)))
         (plan (fnn-core-state 'fn-workflow-ion-attempt-plan
                               txid tx-generation work-id attempt-id))
         (retry (first plan))
         (attempt (second plan)))
    ;; books/bp-payload-gate.lisp: no canonical :forward pin, or a reclaimed
    ;; article, is refused by name before anything is published.
    (when (and (eq retry :refused) (keywordp attempt))
      (fnn-refuse "ACL2 refused ION attempt reason=~(~a~)" attempt))
    (unless (and (consp attempt) (eq (first attempt) :attempt))
      (fnn-refuse "ACL2 refused ION attempt"))
    (let ((generation (sixth attempt)))
      ;; A restart-observed attempt is retried by the journaled policy
      ;; decision first, so the next open replays the new attempt
      ;; (fn-bprq-ion-attempt-plan).
      (when retry
        (fnn-app-publish journal retry)
        (fnn-out "ION durable retry work=~a attempt=~a generation=~d"
                 (second retry) (third retry) (fourth retry)))
      (fnn-app-publish journal attempt :reserve-resolution t)
      (fnn-app-publish journal
                       (list :outcome txid tx-generation :ordinary :durable))
      (unless (eq (fnn-core-state 'fn-workflow-take-submit
                                  work-id attempt-id generation) t)
        (fnn-fault "durable ION attempt did not grant one submit effect"))
      (let ((route (fnn-core-state 'fn-workflow-ion-route-record
                                    work-id attempt-id generation
                                    bp-destination own-bp-eid)))
        (unless (and (consp route) (eq (first route) :ion-route))
          (fnn-refuse "ACL2 refused ION route"))
        (fnn-app-publish journal route)
        (let* ((adu (let ((a (fnn-core-state 'fn-workflow-ion-request-adu
                                              work-id attempt-id generation)))
                      ;; A keyword is ACL2's refusal by name (:request-refused,
                      ;; :article-reclaimed: fn-bppg-ion-adu); never sent.
                      (when (keywordp a)
                        (fnn-refuse "ACL2 refused ION request ADU reason=~(~a~)" a))
                      (unless (and (consp a) (fnn-octet-list-p a))
                        (fnn-fault "ACL2 returned a malformed ION request ADU"))
                      a))
               (observation (fnn-join directory
                                      (format nil "observation.~a"
                                              (fnn-random-hex 16))))
               (request nil))
          (when (> (length observation) 240)
            (fnn-refuse "ION observation path exceeds private source bound"))
          (setq request (fnn-workflow-ion-request-file directory adu))
          (unwind-protect
               (let ((exit (fnn-workflow-ion-run-helper
                            helper (seventh route) (sixth route) (fifth route)
                            request seconds observation)))
                 (cond
                  ((eql exit 1) (fnn-refuse "ION helper refused before send"))
                  ((eql exit 5) (fnn-fault "ION helper rejected invocation"))
                  ((not (eql exit 0))
                   (fnn-indeterminate "ION send entered without durable observation"))
                  (t
                   (handler-case
                       (let* ((raw (fnn-octet-list
                                    (fnn-read-regular-bounded observation 1023)))
                              (record (fnn-core-state
                                       'fn-workflow-ion-observation-record
                                       work-id attempt-id generation
                                       bp-destination own-bp-eid raw)))
                         (unless (and (consp record)
                                      (eq (first record) :ion-observed))
                           (fnn-indeterminate
                            "ACL2 refused ION observation after send"))
                         (fnn-app-publish journal record)
                         (fnn-out
                          "ION observed work=~a attempt=~a source=~a msec=~d sequence=~d"
                          work-id attempt-id (seventh record)
                          (eighth record) (ninth record))
                         :observed)
                     (error (e)
                       (fnn-indeterminate
                        "ION observation binding requires recovery: ~a" e))))))
            (when request
              (ignore-errors (fnn-unlink request)
                             (fnn-fsync-dir directory)))))))))

(defun fnn-workflow-commit-receipt-intent
    (journal intent canonical-release-callback)
  (unless (and (consp intent) (eq (first intent) :receipt-intent))
    (fnn-refuse "ACL2 refused application receipt"))
  (fnn-app-publish journal intent :reserve-resolution t)
  (fnn-app-publish journal
                   (list :outcome (second intent) (third intent)
                         :ordinary :durable))
  (let* ((receipt-id (fourth intent))
         (release (fnn-core-state 'fn-workflow-release-record receipt-id)))
    (unless (and (consp release) (eq (first release) :release))
      (fnn-fault "committed receipt did not authorize its exact release"))
    (if canonical-release-callback
        (funcall canonical-release-callback release)
      (fnn-app-publish journal release))
    receipt-id))

(defun fnn-workflow-accept-receipt
    (journal receipt-path txid generation authorization-profile
     &optional canonical-release-callback)
  (unless (string= authorization-profile "trusted-local-observation-v0")
    (fnn-refuse "workflow receipt authentication profile is unsupported"))
  (let ((octets (fnn-octet-list
                 (fnn-read-regular-bounded receipt-path 131072))))
    (fnn-workflow-commit-receipt-intent
     journal (fnn-core-state 'fn-workflow-receipt-record
                              octets txid generation t)
     canonical-release-callback)))

;;; Receiver operations.  Request context and receipt intent are separate
;;; durable facts; only a committed decision makes receipt bytes available
;;; after restart.

(defun fnn-receipt-initialize (journal values)
  (when (fnn-core 'fn-aj-initializedp (fnn-app-journal-frontier journal))
    (fnn-refuse "receiver journal is already initialized"))
  (fnn-app-publish journal (cons :config values)))

(defun fnn-receipt-accept-request (journal inbound-bid request store-record)
  (fnn-app-publish journal
                   (list :request-context inbound-bid request store-record t)))

(defun fnn-receipt-prepare (journal work-id receipt-id)
  (let ((adu (fnn-core-state 'fn-bprj-preview-receipt work-id receipt-id)))
    (unless (fnn-octet-list-p adu)
      (fnn-refuse "ACL2 refused receipt intent"))
    (fnn-app-publish journal
                     (list :receipt-intent work-id receipt-id adu t)
                     :reserve-resolution t)
    (fnn-octets adu)))

(defun fnn-receipt-decide (journal work-id receipt-id outcome)
  (fnn-app-publish journal
                   (list :receipt-decision work-id receipt-id outcome)))

(defun fnn-receipt-adu (journal request)
  (declare (ignore journal))
  (let ((adu (fnn-core-state 'fn-bprj-receipt-adu request)))
    (and (fnn-octet-list-p adu) (fnn-octets adu))))

;;; -------------------------------------------------------------------------
;;; Operator surface and owner callback surface.
;;;
;;; The functions above take an existing FNN-STORE.  The native owner calls
;;; them while holding its service lock, so no second Store image or owner is
;;; created.  These commands are a single-process operator/restart witness:
;;; they open one Store, replay one application journal against that same
;;; global, perform the requested operation, and close both in reverse order.

(defun fnn-app-call-with-journal (store-root journal-root domain writable thunk)
  (let ((store nil) (journal nil))
    (fnn-unwind-cleanups
         ((progn
           (setq store
                 (fnn-open-live-store
                  store-root
                  (and writable
                       (not (string=
                             (or (fnn-developer-selector "FN_APP_JOURNAL_TEST_READ_ONLY_STORE") "")
                             "1")))))
           (setq journal (fnn-app-open store journal-root domain))
           (funcall thunk journal)))
      (when journal (fnn-app-journal-close journal))
      (when store (fnn-store-close store)))))

(defun fnn-command-workflow-init (store-root journal-root values)
  (fnn-app-call-with-journal
   store-root journal-root :workflow t
   (lambda (journal)
     (fnn-workflow-initialize journal values)
     (fnn-out "workflow durable records=1")
     +fnn-exit-ok+)))

(defun fnn-command-workflow-enqueue (store-root journal-root txid generation
                                     work-id msgid forward-obligation-id
                                     peer-eid policy-id terms-id)
  (fnn-app-call-with-journal
   store-root journal-root :workflow t
   (lambda (journal)
     (fnn-workflow-enqueue-for-article
      journal txid generation work-id msgid forward-obligation-id peer-eid
      policy-id terms-id)
     (fnn-out "workflow durable work=~a status=~(~a~)"
              work-id (fnn-workflow-status journal work-id))
     +fnn-exit-ok+)))

(defun fnn-command-workflow-status (store-root journal-root work-id)
  (fnn-app-call-with-journal
   store-root journal-root :workflow nil
   (lambda (journal)
     (fnn-out "workflow status work=~a status=~(~a~)"
              work-id (fnn-workflow-status journal work-id))
     +fnn-exit-ok+)))

(defun fnn-command-workflow-undertake
    (store-root journal-root work-id charge)
  (fnn-app-call-with-journal
   store-root journal-root :workflow t
   (lambda (journal)
     (fnn-workflow-undertake journal work-id charge)
     (fnn-out "workflow durable undertaking work=~a charge=~d" work-id charge)
     +fnn-exit-ok+)))

(defun fnn-command-workflow-ion-submit
    (store-root journal-root txid tx-generation work-id attempt-id
                bp-destination own-bp-eid helper observation-directory)
  (fnn-app-call-with-journal
   store-root journal-root :workflow t
   (lambda (journal)
     (unless (eq (fnn-workflow-ion-submit
                  journal txid tx-generation work-id attempt-id
                  bp-destination own-bp-eid helper observation-directory)
                 :observed)
       (fnn-indeterminate "ION attempt has no durable observed binding"))
     +fnn-exit-ok+)))

(defun fnn-command-workflow-ion-status
    (store-root journal-root work-id attempt-id generation)
  (fnn-app-call-with-journal
   store-root journal-root :workflow nil
   (lambda (journal)
     (declare (ignore journal))
     (let* ((status (fnn-core-state 'fn-workflow-ion-status
                                     work-id attempt-id generation))
            (record (second status)))
       (case (first status)
         (:observed
          (fnn-out "ION observed work=~a attempt=~a source=~a msec=~d sequence=~d"
                   work-id attempt-id (seventh record)
                   (eighth record) (ninth record))
          +fnn-exit-ok+)
         (:uncertain
          (fnn-out "ION uncertain work=~a attempt=~a; do not repost automatically"
                   work-id attempt-id)
          +fnn-exit-uncertain+)
         (otherwise
          (fnn-out "ION absent work=~a attempt=~a" work-id attempt-id)
          +fnn-exit-refused+))))))

(defun fnn-command-workflow-receipt
    (store-root journal-root receipt-path txid generation profile)
  (fnn-app-call-with-journal
   store-root journal-root :workflow t
   (lambda (journal)
     (let ((receipt-id (fnn-workflow-accept-receipt
                        journal receipt-path txid generation profile)))
       (fnn-out "workflow durable release receipt=~a profile=~a"
                receipt-id profile)
       +fnn-exit-ok+))))

(defun fnn-command-receipt-init (store-root journal-root values)
  (fnn-app-call-with-journal
   store-root journal-root :receipt t
   (lambda (journal)
     (fnn-receipt-initialize journal values)
     (fnn-out "receipt durable records=1")
     +fnn-exit-ok+)))

(defun fnn-command-receipt-complete (store-root journal-root inbound-bid
                                     request-path record-path work-id receipt-id)
  (fnn-app-call-with-journal
   store-root journal-root :receipt t
   (lambda (journal)
     (let* ((request (fnn-octet-list
                      (fnn-read-regular-bounded request-path 131072)))
            (record (fnn-octet-list
                     (fnn-read-regular-bounded record-path 131072))))
       (fnn-receipt-accept-request journal inbound-bid request record)
       (let ((adu (fnn-receipt-prepare journal work-id receipt-id)))
         (fnn-receipt-decide journal work-id receipt-id :committed)
         (fnn-out "receipt durable work=~a receipt=~a octets=~d"
                  work-id receipt-id (length adu))
         +fnn-exit-ok+)))))

(defun fnn-command-receipt-replay (store-root journal-root request-path)
  (fnn-app-call-with-journal
   store-root journal-root :receipt nil
   (lambda (journal)
     (let* ((request (fnn-octet-list
                      (fnn-read-regular-bounded request-path 131072)))
            (adu (fnn-receipt-adu journal request)))
       (unless adu (fnn-refuse "no committed receipt for request"))
       (fnn-out "receipt replay octets=~d hex=~a" (length adu) (fnn-hex adu))
       +fnn-exit-ok+))))

;;; `app-journal profile STORE JOURNAL DOMAIN RECORDS OCTETS': set the
;;; journal's profile, the records it admits over its life and the octets
;;; they total (D27, lane caps; books/app-journal.lisp).  ACL2 takes the
;;; recovered frontier (which carries the profile in force) and answers the
;;; frame to publish, or refuses a write that leaves the relation or lowers a
;;; field of a journal that holds a record (fn-ajpf-write-octets).  The
;;; journal is opened (its lock held, its records replayed under the profile
;;; in force) while the file is replaced; the next open runs under it.
(defun fnn-app-domain-argument (text)
  (cond ((string= text "workflow") :workflow)
        ((string= text "receipt") :receipt)
        ((string= text "carry") :carry)
        (t (error 'fnn-usage-error
                  :message "app-journal profile: DOMAIN is workflow, receipt or carry"))))

(defun fnn-app-count-argument (text label)
  ; A syntactic input bound before PARSE-INTEGER; ACL2 decides the range.
  (unless (and (stringp text) (<= 1 (length text) 20)
               (every #'digit-char-p text))
    (error 'fnn-usage-error
           :message (format nil "app-journal profile: invalid ~a" label)))
  (parse-integer text))

(defun fnn-command-app-journal-profile (store-root journal-root domain
                                        records octets)
  (fnn-app-call-with-journal
   store-root journal-root domain t
   (lambda (journal)
     (let* ((root (fnn-app-journal-root journal))
            (frame (fnn-core 'fn-aj-host-profile-write-octets
                             (fnn-app-journal-frontier journal) records octets))
            (final (fnn-join root (fnn-core 'fn-aj-host-profile-file-name)))
            (stage (fnn-join (fnn-app-journal-staging journal)
                             (format nil "profile.~d.~a.tmp" (sb-posix:getpid)
                                     (fnn-random-hex 12)))))
       (unless frame
         (fnn-refuse "app-journal profile: ACL2 refused max-records=~a max-octets=~a"
                     records octets))
       (fnn-write-staged stage (fnn-octets frame))
       (handler-case
           (progn (fnn-replace stage final) (fnn-fsync-dir root))
         (fnn-os-error (condition)
           (fnn-indeterminate "app-journal profile replacement/barrier return is uncertain: ~a"
                              condition)))
       (fnn-out "app-journal profile domain=~(~a~) max-records=~d max-octets=~d"
                domain records octets)
       +fnn-exit-ok+))))

;;; The experimental ION/LTP subverbs (workflow-ion-*) belong to the
;;; developer image only (docs/operator-internals.md "Experimental offline
;;; ION/LTP submission"; PKT-590): a production image refuses them before
;;; reading an argument.  The other app-journal subverbs stay in both images
;;; (the BP tests drive workflow-init, -enqueue and the receipt replay).
(defun fnn-app-journal-developer-only-p (command)
  (and (>= (length command) 13) (string= "workflow-ion-" command :end2 13)))

(defun fnn-dispatch-app-journal (command args)
  (when (and (fnn-app-journal-developer-only-p command)
             (not (fnn-developer-image-p)))
    (error 'fnn-usage-error
           :message (format nil "app-journal ~a is available only in the developer image"
                            command)))
  (flet ((need (n)
           (when (< (length args) n)
             (error 'fnn-usage-error
                    :message "app-journal: missing arguments"))))
    (cond
      ((string= command "workflow-init")
       (need 9)
       (fnn-command-workflow-init
        (first args) (second args)
        (list (third args) (fourth args) (fifth args) (sixth args)
              (parse-integer (seventh args)) (eighth args) (ninth args))))
      ((string= command "workflow-enqueue")
       (need 10)
       (fnn-command-workflow-enqueue
        (first args) (second args) (parse-integer (third args))
        (parse-integer (fourth args)) (fifth args) (sixth args)
        (seventh args) (eighth args) (ninth args) (tenth args)))
      ((string= command "workflow-status")
       (need 3)
       (fnn-command-workflow-status (first args) (second args) (third args)))
      ((string= command "workflow-undertake")
       (need 4)
       (fnn-command-workflow-undertake
        (first args) (second args) (third args) (parse-integer (fourth args))))
      ((string= command "workflow-ion-submit")
       (need 10)
       (fnn-command-workflow-ion-submit
        (first args) (second args) (parse-integer (third args))
        (parse-integer (fourth args)) (fifth args) (sixth args)
        (seventh args) (eighth args) (ninth args) (tenth args)))
      ((string= command "workflow-ion-status")
       (need 5)
       (fnn-command-workflow-ion-status
        (first args) (second args) (third args) (fourth args)
        (parse-integer (fifth args))))
      ((string= command "workflow-receipt")
       (need 6)
       (fnn-command-workflow-receipt
        (first args) (second args) (third args)
        (parse-integer (fourth args)) (parse-integer (fifth args))
        (sixth args)))
      ((string= command "receipt-init")
       (need 5)
       (fnn-command-receipt-init
        (first args) (second args) (list (third args) (fourth args) (fifth args))))
      ((string= command "receipt-complete")
       (need 7)
       (fnn-command-receipt-complete
        (first args) (second args) (third args) (fourth args) (fifth args)
        (sixth args) (seventh args)))
      ((string= command "profile")
       (need 5)
       (fnn-command-app-journal-profile
        (first args) (second args) (fnn-app-domain-argument (third args))
        (fnn-app-count-argument (fourth args) "max records")
        (fnn-app-count-argument (fifth args) "max octets")))
      ((string= command "receipt-replay")
       (need 3)
       (fnn-command-receipt-replay (first args) (second args) (third args)))
      (t (error 'fnn-usage-error
                :message (format nil "unknown app-journal command ~a" command))))))

(fnn-register-verb "app-journal" #'fnn-dispatch-app-journal)
