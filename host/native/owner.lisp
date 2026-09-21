;;; host/native/owner.lisp -- the writable native owner service.
;;;
;;; This file is raw Common Lisp under the native host trust tag.  It owns
;;; scheduling, sockets and filesystem effects only.  Every protocol, owner,
;;; configuration, submission and outcome decision is a direct call to a
;;; host/owner-host.lisp wrapper through fnn-core/fnn-core-state.  All calls
;;; and Store mutations are serialized by one mutex because ACL2's live state
;;; and the exclusive Store writer are one process-owned machine; client
;;; sockets remain concurrent and never carry semantic state in raw Lisp.

(in-package "ACL2")

(defstruct (fnn-owner-service (:constructor %make-fnn-owner-service))
  store records lock listener stopping)

(defun fnn-owner-core (name &rest args)
  (apply #'fnn-core-state name args))

(defun fnn-owner-octets-global (name)
  (let ((value (fnn-global name)))
    (unless (fnn-octet-list-p value)
      (fnn-fault "owner returned non-octets in ~a" name))
    (fnn-octets value)))

(defun fnn-owner-bool-global (name)
  (let ((value (fnn-global name)))
    (unless (member value '(t nil))
      (fnn-fault "owner returned non-boolean in ~a" name))
    value))

(defun fnn-owner-action (name &rest args)
  (let ((value (apply #'fnn-owner-core name args)))
    (unless (keywordp value)
      (fnn-fault "owner returned non-action from ~a" name))
    value))

(defun fnn-owner-observe (operation result)
  (fnn-owner-action 'fn-owner-io operation result))

(defun fnn-owner-finish ()
  (fnn-owner-action 'fn-owner-finish))

(defun fnn-owner-config-names (wrapper)
  "Split ACL2's LF-joined name projection; LF is excluded by the name grammar."
  (let ((octets (fnn-owner-core wrapper)) (names nil) (current nil))
    (unless (fnn-octet-list-p octets)
      (fnn-fault "owner returned a non-octet name table"))
    (dolist (octet octets)
      (if (= octet 10)
          (progn
            (push (fnn-octets-string (fnn-octets (nreverse current))) names)
            (setq current nil))
          (push octet current)))
    (when current
      (push (fnn-octets-string (fnn-octets (nreverse current))) names))
    (nreverse names)))

(defun fnn-owner-install (root max-connections)
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (handler-case
        (let ((result (fnn-owner-core
                       'fn-owner-recover
                       (mapcar #'fnn-octet-list records)
                       (fnn-store-frontier store)
                       (mapcar #'fnn-octet-list (fnn-config-records store))
                       max-connections)))
          (unless (eq result :recovering)
            (fnn-fault "owner rejected committed history"))
          ;; Five fresh namespace observations, now delivered to fn-owner.
          (let ((phase nil))
            (dolist (barrier (list (lambda () (fnn-fsync-regular (fnn-config-path store)))
                                   (lambda () (fnn-fsync-regular (fnn-frontier-path store)))
                                   (lambda () (fnn-fsync-dir (fnn-transactions store)))
                                   (lambda () (fnn-fsync-dir (fnn-store-root store)))
                                   (lambda () (fnn-fsync-dir
                                               (fnn-parent (fnn-store-root store))))))
              (handler-case (funcall barrier)
                (fnn-os-error (e)
                  (fnn-owner-observe :recovery-barrier :uncertain)
                  (error e)))
              (setq phase (fnn-owner-observe :recovery-barrier :ok)))
            (unless (eq phase :ready)
              (fnn-fault "owner did not complete recovery barriers")))
          (let ((peers (fnn-owner-core 'fn-owner-feed-configure)))
            (unless (fnn-octet-list-p peers)
              (fnn-fault "owner returned a malformed feed table"))
            ;; The local-POST slice never drops a durable obligation.  A
            ;; configured feed is admitted when the native FNFD runner lands.
            (when peers
              (fnn-refuse "native FNFD runner is required for configured peers")))
          (let* ((monotonic (floor (* (get-internal-real-time) 1000)
                                   internal-time-units-per-second))
                 (dtn-epoch (encode-universal-time 0 0 0 1 1 2000 0))
                 (wall (* 1000 (max 0 (- (get-universal-time) dtn-epoch)))))
            (unless (eq (fnn-owner-action 'fn-owner-observe
                                          monotonic wall 1000 t)
                        :observed)
              (fnn-fault "owner refused its first clock observation")))
          (%make-fnn-owner-service
           :store store :records (length records)
           :lock (sb-thread:make-mutex :name "fn owner/store")
           :stopping nil))
      (error (e) (fnn-store-close store) (error e)))))

(defmacro fnn-with-owner ((service) &body body)
  `(sb-thread:with-mutex ((fnn-owner-service-lock ,service)) ,@body))

(defun fnn-owner-frame-count ()
  (let ((frames (fnn-global 'fn-owner-feed-frames)))
    (unless (listp frames) (fnn-fault "owner returned malformed feed frame list"))
    (length frames)))

(defun fnn-owner-require-no-feed-write ()
  "The first vertical slice permits no unpersisted obligation to escape.

The full native FNFD runner replaces this guard.  A store with no configured
outbound target produces no frame and follows the complete intent ordering;
one with a target fails before Store mutation."
  (unless (zerop (fnn-owner-frame-count))
    (fnn-indeterminate "native FNFD durability runner is not installed")))

(defun fnn-owner-submit-groups ()
  (let ((groups (fnn-global 'fn-owner-submit-groups)))
    (unless (and (listp groups) (every #'fnn-octet-list-p groups))
      (fnn-fault "owner returned malformed submission groups"))
    (mapcar #'fnn-octets groups)))

(defun fnn-owner-attempt (service msgid payload groups evidence)
  "One Store attempt under the owner callbacks; return its observed word."
  (let* ((store (fnn-owner-service-store service))
         (names (mapcar #'fnn-octets-string groups))
         (codes (fnn-group-codes-for store names))
         (charge (fnn-charge (length payload))))
    (handler-case
        (progn
          (fnn-validate-post-boundary msgid payload codes charge)
          (case (fnn-owner-action 'fn-owner-existing-action
                                  (fnn-octet-list msgid)
                                  (fnn-octet-list payload) codes)
            (:duplicate (return-from fnn-owner-attempt :duplicate))
            (:conflict (return-from fnn-owner-attempt :refused)))
          (when (>= (fnn-owner-service-records service) +fnn-max-transactions+)
            (return-from fnn-owner-attempt :refused))
          (let ((*fnn-observe-callback* #'fnn-owner-observe)
                (*fnn-finish-callback* #'fnn-owner-finish))
            (fnn-advance-frontier store
                                  (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
            (multiple-value-bind (obligation subject ignored)
                (fnn-metadata msgid payload)
              (declare (ignore ignored))
              (let ((prepared
                      (fnn-owner-action
                       'fn-owner-prepare (fnn-octet-list msgid)
                       (fnn-octet-list payload) codes
                       (fnn-octet-list obligation) (fnn-octet-list subject)
                       (fnn-octet-list evidence) charge)))
                (unless (eq prepared :prepared)
                  (setf (fnn-store-fenced store) t)
                  (unless (eq (fnn-owner-action 'fn-owner-refuse-reservation)
                              :refused)
                    (fnn-indeterminate "owner could not consume refused reservation"))
                  (return-from fnn-owner-attempt :refused))))
            (let ((record (fnn-owner-core 'fn-owner-pending-octets)))
              (unless (fnn-octet-list-p record)
                (fnn-fault "owner returned malformed pending record"))
              (handler-case
                  (fnn-publish store (fnn-owner-service-records service)
                               (fnn-octets record))
                (fnn-store-indeterminate (e) (error e))
                (fnn-store-error (e)
                  (unless (fnn-store-fenced store)
                    (setf (fnn-store-fenced store) t)
                    (unless (eq (fnn-owner-action 'fn-owner-known-abort) :aborted)
                      (fnn-indeterminate "owner rejected known abort")))
                  (error e))))
            (setf (fnn-store-fenced store) t)
            (fnn-finish store)
            (incf (fnn-owner-service-records service)))
          :durable)
      (fnn-store-indeterminate () :uncertain)
      ((or fnn-store-error fnn-os-error) () :refused))))

(defun fnn-owner-drain-one (service)
  "Take and complete at most one queued local submission; return cid/reply."
  (let ((taken (fnn-owner-action 'fn-owner-take)))
    (unless (member taken '(:idle :taken :taken-control :taken-transit))
      (fnn-fault "owner returned unexpected take result"))
    (if (eq taken :idle)
        (values nil (fnn-make-octets 0) nil)
        (let* ((cid (fnn-nat (fnn-global 'fn-owner-submit-id)))
               (msgid (fnn-owner-octets-global 'fn-owner-submit-msgid))
               (payload (fnn-owner-octets-global 'fn-owner-submit-octets))
               (groups (fnn-owner-submit-groups)))
          (when (not (eq taken :taken))
            (fnn-owner-action 'fn-owner-fault cid)
            (return-from fnn-owner-drain-one
              (values cid (fnn-owner-octets-global 'fn-owner-output) t)))
          (let* ((evidence (fnn-octets (fnn-owner-core 'fn-owner-prov-post)))
                 (generation (fnn-nat (fnn-owner-core 'fn-owner-config-generation)))
                 (txid (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
                 (intent (fnn-owner-action 'fn-owner-submission-intent
                                           (fnn-octet-list evidence)
                                           generation txid)))
            (if (not (eq intent :ready))
                (progn
                  (fnn-owner-action 'fn-owner-outcome cid :refused)
                  (values cid (fnn-owner-octets-global 'fn-owner-output) nil))
                (progn
                  ;; Durable intent before the first Store mutation.  Empty is
                  ;; a complete batch when the ACL2 target set is empty.
                  (fnn-owner-require-no-feed-write)
                  (let ((word (fnn-owner-attempt service msgid payload groups evidence)))
                    (fnn-owner-action 'fn-owner-submission-resolution
                                      word (fnn-octet-list evidence)
                                      generation txid)
                    (fnn-owner-require-no-feed-write)
                    (fnn-owner-action 'fn-owner-outcome cid word)
                    (values cid (fnn-owner-octets-global 'fn-owner-output)
                            (eq word :uncertain))))))))))

(defun fnn-owner-handle-chunk (service cid incoming)
  "Run one owner read and its serial writer drain under the service mutex."
  (fnn-with-owner (service)
    (unless (eq (fnn-owner-action 'fn-owner-chunk cid
                                  (fnn-octet-list incoming)) :ok)
      (fnn-refuse "owner no longer knows connection ~d" cid))
    (let ((reply (fnn-owner-octets-global 'fn-owner-output))
          (closing (fnn-owner-bool-global 'fn-owner-closep))
          (uncertain nil))
      (when (fnn-owner-bool-global 'fn-owner-submittedp)
        (multiple-value-bind (reply-cid completion stop)
            (fnn-owner-drain-one service)
          (when (and reply-cid (not (= reply-cid cid)))
            (fnn-fault "writer drained a different connection"))
          (setq reply (concatenate 'fnn-octets reply completion)
                uncertain stop)))
      (values reply (or closing uncertain)))))

(defun fnn-owner-serve-client (service socket)
  (let ((fd (fnn-socket-fd socket)) (cid nil))
    (unwind-protect
         (handler-case
             (progn
               (multiple-value-bind (opened greeting)
                   (fnn-with-owner (service)
                     (let ((opened (fnn-owner-core 'fn-owner-open)))
                       (values opened
                               (if opened (fnn-owner-octets-global 'fn-owner-output)
                                 (fnn-make-octets 0)))))
                 (unless (and opened (integerp opened))
                   (return-from fnn-owner-serve-client nil))
                 (setq cid opened)
                 (when (> (length greeting) 0) (fnn-send-all fd greeting 10)))
               (loop
                 (let ((incoming (fnn-recv fd 10)))
                   (cond ((eq incoming :timeout) nil)
                         ((zerop (length incoming)) (return))
                         (t (multiple-value-bind (reply closing)
                                (fnn-owner-handle-chunk service cid incoming)
                              (when (> (length reply) 0)
                                (fnn-send-all fd reply 10))
                              (when closing
                                (fnn-graceful-close fd)
                                (return))))))))
           ((or fnn-store-error fnn-os-error sb-bsd-sockets:socket-error) (e)
             (fnn-err "owner connection: ~a" e))
           (serious-condition (e)
             (fnn-err "owner connection fault: ~a" e)
             (when cid
               (ignore-errors
                 (fnn-with-owner (service)
                   (fnn-owner-action 'fn-owner-fault cid))))))
      (when cid
        (ignore-errors
          (fnn-with-owner (service)
            (fnn-owner-action 'fn-owner-close cid))))
      (fnn-socket-shut socket))))

(defun fnn-owner-accept (service listener once)
  (if once
      (fnn-owner-serve-client service
                              (sb-bsd-sockets:socket-accept listener))
      (loop until (fnn-owner-service-stopping service) do
        (let ((socket (sb-bsd-sockets:socket-accept listener)))
          (sb-thread:make-thread
           (lambda () (fnn-owner-serve-client service socket))
           :name "fn owner client")))))

(defun fnn-command-owner (command args)
  (unless (string= command "run")
    (error 'fnn-usage-error :message "unknown owner command"))
  (when (< (length args) 4)
    (error 'fnn-usage-error
           :message "owner run ROOT PORT ONCE MAX-CONNECTIONS"))
  (let ((service nil) (listener nil))
    (unwind-protect
         (progn
           (setq service (fnn-owner-install (first args)
                                            (parse-integer (fourth args))))
           (multiple-value-bind (bound bound-port)
               (fnn-listen (parse-integer (second args)))
             (setq listener bound
                   (fnn-owner-service-listener service) bound)
             (fnn-out "LISTENING ~d" bound-port))
           (fnn-owner-accept service listener (string= (third args) "1"))
           +fnn-exit-ok+)
      (when listener (fnn-socket-shut listener))
      (when service (fnn-store-close (fnn-owner-service-store service))))))

(fnn-register-verb "owner" #'fnn-command-owner)
