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
  (records-image nil) (fenced t))

(defun fnn-app-journal-close (journal)
  (setf (fnn-app-journal-fenced journal) t)
  (let ((fd (fnn-app-journal-lock-fd journal)))
    (when fd
      (ignore-errors (fnn-flock fd +fnn-lock-un+))
      (ignore-errors (fnn-close fd))
      (setf (fnn-app-journal-lock-fd journal) nil)))
  nil)

(defun fnn-app-journal-lock (root domain)
  (let* ((name (if (eq domain :workflow) "workflow.lock" "receipt.lock"))
         (path (fnn-join root name))
         (fd nil))
    (handler-case
        (setq fd (fnn-open path
                           (logior sb-posix:o-rdwr sb-posix:o-creat
                                   +fnn-o-nofollow+)
                           #o600))
      (fnn-os-error (e)
        (fnn-fault "application journal lock open failed: ~a" e)))
    (handler-case
        (unless (fnn-regular-p (fnn-fstat fd))
          (fnn-fault "refusing non-regular application journal lock"))
      (error (e) (ignore-errors (fnn-close fd)) (error e)))
    (handler-case
        (fnn-flock fd (logior +fnn-lock-ex+ +fnn-lock-nb+))
      (fnn-os-error (e)
        (fnn-close fd)
        (if (or (= (fnn-os-errno e) sb-posix:eagain)
                (= (fnn-os-errno e) sb-posix:eacces))
            (fnn-refuse "application journal is already owned")
          (fnn-fault "application journal lock failed: ~a" e))))
    fd))

(defun fnn-app-record-names (journal)
  ; Ordering is an observation only.  fn-aj-host-recover decides whether each
  ; spelling is ACL2's exact next name and whether the frontier may advance.
  (sort (fnn-list-directory (fnn-app-journal-records journal)) #'string<))

(defun fnn-app-frame (journal record)
  (let* ((wrapper (if (eq (fnn-app-journal-domain journal) :workflow)
                      'fn-store-frame-workflow-logical-protected
                    'fn-store-frame-receipt-logical-protected))
         (prefix (fnn-core wrapper (first record) (rest record))))
    (when (or (keywordp prefix) (not (fnn-octet-list-p prefix)))
      (fnn-refuse "ACL2 refused application journal record"))
    (fnn-seal (fnn-octets prefix))))

(defun fnn-app-unframe (journal raw)
  (let* ((wrapper (if (eq (fnn-app-journal-domain journal) :workflow)
                      'fn-store-frame-workflow-logical-decode
                    'fn-store-frame-receipt-logical-decode))
         (answer (fnn-core wrapper (fnn-octet-list raw)
                           (fnn-digest-of raw))))
    (unless (and (consp answer) (eq (first answer) :ok)
                 (keywordp (second answer)) (listp (third answer)))
      (fnn-fault "application journal frame refused"))
    (cons (second answer) (third answer))))

(defun fnn-app-read-records (journal names)
  (let ((records nil)
        (frontier (fnn-core 'fn-aj-host-initial
                            (fnn-app-journal-domain journal)))
        (maximum (fnn-core 'fn-aj-host-max-record-length
                           (fnn-app-journal-domain journal))))
    (dolist (name names)
      (let* ((path (fnn-join (fnn-app-journal-records journal) name))
             (raw (fnn-read-regular-bounded path maximum))
             (record (fnn-app-unframe journal raw))
             (next (fnn-core 'fn-aj-host-recover frontier name (length raw)
                             (first record))))
        (when (eq next :fault)
          (fnn-fault "ACL2 rejected application journal namespace/frontier"))
        (setq frontier next)
        (push record records)))
    (setf (fnn-app-journal-frontier journal) frontier)
    (nreverse records)))

(defun fnn-app-install (journal records)
  (let ((answer
          (if records
              (if (eq (fnn-app-journal-domain journal) :workflow)
                  (fnn-core-state 'fn-workflow-install-replay records)
                (fnn-core-state 'fn-bprj-install records))
            (if (eq (fnn-app-journal-domain journal) :workflow)
                (fnn-core-state 'fn-workflow-reset)
              (fnn-core-state 'fn-bprj-reset)))))
    (unless (eq answer :ready)
      (fnn-fault "ACL2 rejected application journal replay"))
    (setf (fnn-app-journal-records-image journal) records)
    :ready))

(defun fnn-app-open (store root domain)
  "Open a journal beside an already-open Store; never replace its ACL2 image."
  (unless (and (typep store 'fnn-store) (fnn-store-lock-fd store))
    (fnn-fault "application journal requires the live Store owner"))
  (unless (member domain '(:workflow :receipt))
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
                 :domain domain
                 :frontier (fnn-core 'fn-aj-host-initial domain)
                 :lock-fd (fnn-app-journal-lock absolute domain)))
          (let* ((names (fnn-app-record-names journal))
                 (records-image (fnn-app-read-records journal names)))
            (fnn-app-install journal records-image)
            (setf (fnn-app-journal-records-image journal) records-image
                  (fnn-app-journal-fenced journal) nil)
            journal))
      (error (e)
        (when journal (fnn-app-journal-close journal))
        (error e)))))

(defun fnn-app-preflight (journal record)
  (let ((domain (fnn-app-journal-domain journal)))
    (if (eq (first record) :config)
        (if (eq domain :workflow)
            (and (fnn-core 'fn-workflow-valid-config record) t)
          (eq (fnn-core-state 'fn-bprj-valid-config record) t))
      (eq (fnn-core-state
           (if (eq domain :workflow)
               'fn-workflow-preflight-record
             'fn-bprj-preflight)
           record)
          :ready))))

(defun fnn-app-apply (journal record)
  (if (eq (first record) :config)
      (fnn-app-install journal (list record))
    (let ((answer
            (fnn-core-state
             (if (eq (fnn-app-journal-domain journal) :workflow)
                 'fn-workflow-apply-record
               'fn-bprj-apply)
             record)))
      (unless (eq answer :ready)
        (fnn-fault "ACL2 rejected durable application journal record"))
      (setf (fnn-app-journal-records-image journal)
            (append (fnn-app-journal-records-image journal) (list record)))
      :ready)))

(defun fnn-app-authorized-publish (journal kind frame reserve-resolution)
  "Ask ACL2 to allocate/admit one exact final name, then execute its capability."
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
           (outcome
             (fnn-immutable-publish-effect
              (fnn-core 'fn-aj-host-operation-publication operation)
              stage final (fnn-app-journal-records journal) frame
              :cleanup-directory (fnn-app-journal-staging journal))))
      (cond ((eq outcome :durable)
             (setf (fnn-app-journal-frontier journal)
                   (fnn-core 'fn-aj-host-operation-successor operation)))
            ((eq outcome :uncertain)
             (setf (fnn-app-journal-fenced journal) t)))
      outcome)))

(defun fnn-app-publish (journal record &key reserve-resolution)
  "Preflight, durably publish, then apply one record through its ACL2 owner."
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
  (unless (null (fnn-app-journal-records-image journal))
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

;;; Receiver operations.  Request context and receipt intent are separate
;;; durable facts; only a committed decision makes receipt bytes available
;;; after restart.

(defun fnn-receipt-initialize (journal values)
  (unless (null (fnn-app-journal-records-image journal))
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

(defun fnn-app-call-with-journal (store-root journal-root domain thunk)
  (let ((store nil) (journal nil))
    (unwind-protect
         (progn
           (setq store (fnn-open-live-store store-root nil))
           (setq journal (fnn-app-open store journal-root domain))
           (funcall thunk journal))
      (when journal (fnn-app-journal-close journal))
      (when store (fnn-store-close store)))))

(defun fnn-command-workflow-init (store-root journal-root values)
  (fnn-app-call-with-journal
   store-root journal-root :workflow
   (lambda (journal)
     (fnn-workflow-initialize journal values)
     (fnn-out "workflow durable records=1")
     +fnn-exit-ok+)))

(defun fnn-command-workflow-enqueue (store-root journal-root txid generation
                                     work-id msgid forward-obligation-id
                                     peer-eid policy-id terms-id)
  (fnn-app-call-with-journal
   store-root journal-root :workflow
   (lambda (journal)
     (fnn-workflow-enqueue-for-article
      journal txid generation work-id msgid forward-obligation-id peer-eid
      policy-id terms-id)
     (fnn-out "workflow durable work=~a status=~(~a~)"
              work-id (fnn-workflow-status journal work-id))
     +fnn-exit-ok+)))

(defun fnn-command-workflow-status (store-root journal-root work-id)
  (fnn-app-call-with-journal
   store-root journal-root :workflow
   (lambda (journal)
     (fnn-out "workflow status work=~a status=~(~a~)"
              work-id (fnn-workflow-status journal work-id))
     +fnn-exit-ok+)))

(defun fnn-command-receipt-init (store-root journal-root values)
  (fnn-app-call-with-journal
   store-root journal-root :receipt
   (lambda (journal)
     (fnn-receipt-initialize journal values)
     (fnn-out "receipt durable records=1")
     +fnn-exit-ok+)))

(defun fnn-command-receipt-complete (store-root journal-root inbound-bid
                                     request-path record-path work-id receipt-id)
  (fnn-app-call-with-journal
   store-root journal-root :receipt
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
   store-root journal-root :receipt
   (lambda (journal)
     (let* ((request (fnn-octet-list
                      (fnn-read-regular-bounded request-path 131072)))
            (adu (fnn-receipt-adu journal request)))
       (unless adu (fnn-refuse "no committed receipt for request"))
       (fnn-out "receipt replay octets=~d hex=~a" (length adu) (fnn-hex adu))
       +fnn-exit-ok+))))

(defun fnn-dispatch-app-journal (command args)
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
      ((string= command "receipt-init")
       (need 5)
       (fnn-command-receipt-init
        (first args) (second args) (list (third args) (fourth args) (fifth args))))
      ((string= command "receipt-complete")
       (need 7)
       (fnn-command-receipt-complete
        (first args) (second args) (third args) (fourth args) (fifth args)
        (sixth args) (seventh args)))
      ((string= command "receipt-replay")
       (need 3)
       (fnn-command-receipt-replay (first args) (second args) (third args)))
      (t (error 'fnn-usage-error
                :message (format nil "unknown app-journal command ~a" command))))))

(fnn-register-verb "app-journal" #'fnn-dispatch-app-journal)
