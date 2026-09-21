;;; Native durable application workflow and receiver receipt journals.
;;;
;;; FNWF and FNRJ retain distinct ACL2 record interpreters.  They share only
;;; the immutable no-replace publication effect below.  At every physical
;;; boundary raw Lisp executes the action selected by books/journal-publish
;;; and reports the syscall observation back to that machine; raw Lisp never
;;; upgrades visible bytes after an error to :durable.
(in-package "ACL2")

(defconstant +fnn-app-max-records+ 4096)
(defconstant +fnn-workflow-max-aggregate+ (* 16 1024 1024))
(defconstant +fnn-receipt-max-aggregate+ (* 64 1024 1024))

(defstruct fnn-app-journal
  root records staging lock-fd store domain suffix max-record max-aggregate
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

(defun fnn-app-record-name (journal sequence)
  (format nil "~16,'0x~a" sequence (fnn-app-journal-suffix journal)))

(defun fnn-app-record-name-p (journal name)
  (let ((suffix (fnn-app-journal-suffix journal)))
    (and (= (length name) (+ 16 (length suffix)))
         (string= suffix (subseq name 16))
         (every (lambda (c) (digit-char-p c 16)) (subseq name 0 16)))))

(defun fnn-app-record-names (journal)
  (let ((names (fnn-list-directory (fnn-app-journal-records journal))))
    (when (> (length names) +fnn-app-max-records+)
      (fnn-fault "application journal record count exceeds bound"))
    (dolist (name names)
      (unless (fnn-app-record-name-p journal name)
        (fnn-fault "unknown application journal entry ~a" name)))
    (setq names (sort names #'string<))
    (loop for name in names for sequence from 0 do
      (unless (string= name (fnn-app-record-name journal sequence))
        (fnn-fault "application journal sequence gap")))
    names))

(defun fnn-app-frame (journal record)
  (let* ((wrapper (if (eq (fnn-app-journal-domain journal) :workflow)
                      'fn-store-frame-workflow-protected
                    'fn-store-frame-receipt-protected))
         (prefix (fnn-core wrapper (first record) (rest record))))
    (when (or (keywordp prefix) (not (fnn-octet-list-p prefix)))
      (fnn-refuse "ACL2 refused application journal record"))
    (fnn-seal (fnn-octets prefix))))

(defun fnn-app-unframe (journal raw)
  (let* ((wrapper (if (eq (fnn-app-journal-domain journal) :workflow)
                      'fn-store-frame-workflow-decode
                    'fn-store-frame-receipt-decode))
         (answer (fnn-core wrapper (fnn-octet-list raw)
                           (fnn-digest-of raw))))
    (unless (and (consp answer) (eq (first answer) :ok)
                 (keywordp (second answer)) (listp (third answer)))
      (fnn-fault "application journal frame refused"))
    (cons (second answer) (third answer))))

(defun fnn-app-read-records (journal names)
  (let ((records nil) (aggregate 0))
    (dolist (name names (nreverse records))
      (let* ((path (fnn-join (fnn-app-journal-records journal) name))
             (raw (fnn-read-regular-bounded
                   path (fnn-app-journal-max-record journal))))
        (incf aggregate (length raw))
        (when (> aggregate (fnn-app-journal-max-aggregate journal))
          (fnn-fault "application journal aggregate exceeds bound"))
        (push (fnn-app-unframe journal raw) records)))))

(defun fnn-app-install (journal records)
  (let ((answer
          (if (eq (fnn-app-journal-domain journal) :workflow)
              (fnn-core-state 'fn-workflow-install-replay records)
            (fnn-core-state 'fn-bprj-install records))))
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
                 :domain domain :suffix (if (eq domain :workflow) ".wf" ".rj")
                 :max-record (if (eq domain :workflow) 16384 270000)
                 :max-aggregate (if (eq domain :workflow)
                                    +fnn-workflow-max-aggregate+
                                  +fnn-receipt-max-aggregate+)
                 :lock-fd (fnn-app-journal-lock absolute domain)))
          (let* ((names (fnn-app-record-names journal))
                 (records-image (fnn-app-read-records journal names)))
            (when records-image (fnn-app-install journal records-image))
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

(defun fnn-app-test-fault (point path)
  ; Injection is reached only from the production handler action loop.
  (let ((chosen (or (sb-ext:posix-getenv "FN_APP_JOURNAL_TEST_FAIL") "")))
    (when (string= chosen point) (fnn-os-fail sb-posix:eio path))))

(defun fnn-app-publish-effect (journal sequence frame)
  "Run one ACL2-directed immutable publication; return its ACL2 outcome."
  (let* ((stage (fnn-join (fnn-app-journal-staging journal)
                          (format nil "~16,'0x.~d.~a.tmp" sequence
                                  (sb-posix:getpid) (fnn-random-hex 8))))
         (final (fnn-join (fnn-app-journal-records journal)
                          (fnn-app-record-name journal sequence)))
         (publication (fnn-core 'fn-jpub-host-initial t))
         (fd nil))
    (labels ((advance (event)
               (setq publication (fnn-core 'fn-jpub-host-step publication event)))
             (observe (ok-event error-event thunk)
               (handler-case (progn (funcall thunk) (advance ok-event))
                 (fnn-os-error () (advance error-event)))))
      (unwind-protect
           (loop until (eq (fnn-core 'fn-jpub-host-terminalp publication) t) do
             (case (fnn-core 'fn-jpub-host-action publication)
               (:stage
                (observe '(:stage-result :ok) '(:stage-result :error)
                         (lambda ()
                           (fnn-app-test-fault "stage" stage)
                           (setq fd (fnn-open stage
                                              (logior sb-posix:o-wronly
                                                      sb-posix:o-creat
                                                      sb-posix:o-excl)
                                              #o600))
                           (fnn-write-all fd frame))))
               (:file-barrier
                (observe '(:file-barrier-result :ok)
                         '(:file-barrier-result :error)
                         (lambda ()
                           (fnn-app-test-fault "file-barrier" stage)
                           (fnn-fsync-file fd)
                           (fnn-close fd)
                           (setq fd nil))))
               (:begin-link (advance '(:link-begin)))
               (:link
                (handler-case
                    (progn (fnn-app-test-fault "link" final)
                           (fnn-link stage final)
                           (advance '(:link-result :ok)))
                  (fnn-os-error (e)
                    (advance (if (= (fnn-os-errno e) sb-posix:eexist)
                                 '(:link-result :exists)
                               '(:link-result :error))))))
               (:directory-barrier
                (observe '(:directory-barrier-result :ok)
                         '(:directory-barrier-result :error)
                         (lambda ()
                           (fnn-app-test-fault "namespace" final)
                           (fnn-fsync-dir (fnn-app-journal-records journal)))))
               (otherwise
                (fnn-fault "ACL2 returned no application publication action"))))
        (when fd (ignore-errors (fnn-close fd)))
        (ignore-errors (fnn-unlink stage))))
    (let ((outcome (fnn-core 'fn-jpub-host-outcome publication)))
      (when (eq outcome :uncertain)
        (setf (fnn-app-journal-fenced journal) t))
      outcome)))

(defun fnn-app-publish (journal record &key reserve-resolution)
  "Preflight, durably publish, then apply one record through its ACL2 owner."
  (when (fnn-app-journal-fenced journal)
    (fnn-indeterminate "application journal is fenced"))
  (unless (fnn-app-preflight journal record)
    (fnn-refuse "ACL2 rejected application journal record before publication"))
  (let* ((names (fnn-app-record-names journal))
         (sequence (length names))
         (frame (fnn-app-frame journal record))
         (aggregate (loop for name in names sum
                      (sb-posix:stat-size
                       (fnn-lstat (fnn-join (fnn-app-journal-records journal)
                                           name)))))
         (slots (if reserve-resolution 2 1))
         (reserve (if reserve-resolution (fnn-app-journal-max-record journal) 0)))
    (when (or (> (+ sequence slots) +fnn-app-max-records+)
              (> (+ aggregate (length frame) reserve)
                 (fnn-app-journal-max-aggregate journal)))
      (fnn-refuse "application journal lacks resolution headroom"))
    ; The exact-name scan under this journal's exclusive lock establishes the
    ; authority premise supplied to fn-jpub-host-initial.
    (when (fnn-lstat (fnn-join (fnn-app-journal-records journal)
                               (fnn-app-record-name journal sequence)))
      (fnn-fault "application journal next name is already occupied"))
    (case (fnn-app-publish-effect journal sequence frame)
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

(defun fnn-command-workflow-enqueue (store-root journal-root values)
  (fnn-app-call-with-journal
   store-root journal-root :workflow
   (lambda (journal)
     (fnn-workflow-enqueue journal values)
     (fnn-out "workflow durable work=~a status=~(~a~)"
              (third values) (fnn-workflow-status journal (third values)))
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
       (need 12)
       (fnn-command-workflow-enqueue
        (first args) (second args)
        (list (parse-integer (third args)) (parse-integer (fourth args))
              (fifth args) (sixth args) (seventh args) (eighth args)
              (ninth args) (tenth args) (nth 10 args) (nth 11 args))))
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
