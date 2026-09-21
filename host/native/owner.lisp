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
  store records lock listener stopping (exit-code +fnn-exit-ok+) (feeds nil)
  (workers nil) (clients nil))

(defstruct (fnn-owner-feed-journal (:constructor %make-fnn-owner-feed-journal))
  peer path fd phase (replayed 0))

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

(defun fnn-owner-name-list (octets)
  "Split ACL2's LF-joined name projection; LF is excluded by the name grammar."
  (let ((names nil) (current nil))
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

(defun fnn-owner-config-names (wrapper)
  (fnn-owner-name-list (fnn-owner-core wrapper)))

(defun fnn-owner-feed-directory (store)
  (fnn-join (fnn-store-root store) "feed"))

(defun fnn-owner-feed-path (store peer)
  (fnn-join (fnn-owner-feed-directory store) (fnn-concat peer ".fnfd")))

(defun fnn-owner-feed-phase (journal event)
  (let ((next (fnn-core 'fn-feed-journal-phase-step
                        (fnn-owner-feed-journal-phase journal) event)))
    (unless (keywordp next) (fnn-fault "malformed FNFD phase result"))
    (setf (fnn-owner-feed-journal-phase journal) next)
    (when (eq next :uncertain)
      (fnn-indeterminate "FNFD journal requires recovery"))
    next))

(defun fnn-owner-feed-read (journal size)
  (let ((out (fnn-make-octets size)) (at 0))
    (loop while (< at size) do
      (let* ((tmp (fnn-make-octets (- size at)))
             (piece (fnn-read-fd (fnn-owner-feed-journal-fd journal) tmp)))
        (when (zerop piece) (return))
        (replace out tmp :start1 at :end2 piece)
        (incf at piece)))
    (subseq out 0 at)))

(defun fnn-owner-feed-close (journal)
  (let ((fd (fnn-owner-feed-journal-fd journal)))
    (when fd
      (setf (fnn-owner-feed-journal-fd journal) nil)
      (fnn-close fd))))

(defun fnn-owner-feed-open (store peer)
  "Open, replay and repair one FNFD file through the ACL2 scanner."
  (let* ((directory (fnn-owner-feed-directory store))
         (path (fnn-owner-feed-path store peer))
         (fd nil) (journal nil))
    (fnn-safe-directory directory t)
    (handler-case
        (progn
          (setq fd (fnn-open path (logior sb-posix:o-rdwr sb-posix:o-creat
                                          +fnn-o-nofollow+) #o600))
          (unless (fnn-regular-p (fnn-fstat fd))
            (fnn-fault "refusing non-regular FNFD journal: ~a" path))
          (setq journal (%make-fnn-owner-feed-journal
                         :peer peer :path path :fd fd :phase :closed))
          (fnn-owner-feed-phase journal :opened)
          (unless (eq (fnn-owner-action 'fn-owner-feed-journal-begin) :ok)
            (fnn-fault "owner refused FNFD scan start"))
          (let ((prefix-size
                  (fnn-nat (fnn-owner-core 'fn-owner-feed-journal-prefix-size))))
            (loop
              (let* ((prefix (fnn-owner-feed-read journal prefix-size))
                     (plan (fnn-core 'fn-feed-journal-prefix
                                     (fnn-octet-list prefix)))
                     (frame (if (and (integerp plan) (>= plan 0))
                                (fnn-owner-feed-read journal plan)
                              (fnn-make-octets 0)))
                     (status
                       (fnn-owner-action
                        'fn-owner-feed-journal-scan
                        (fnn-octet-list (fnn-string-octets peer))
                        (fnn-octet-list prefix) (fnn-octet-list frame))))
                (case status
                  (:next (incf (fnn-owner-feed-journal-replayed journal)))
                  (:invalid
                   (fnn-fault "invalid complete FNFD evidence: ~a" path))
                  (:migration-required
                   (fnn-fault "FNFD migration required before legacy timing outcome: ~a"
                              path))
                  ((:end :repair)
                   (fnn-owner-feed-phase journal status)
                   (when (eq status :repair)
                     (fnn-posix (path)
                       (sb-posix:ftruncate
                        fd (fnn-nat
                            (fnn-owner-core 'fn-owner-feed-journal-offset))))
                     (fnn-owner-feed-phase journal :truncated))
                   (return))
                  (t (fnn-fault "unexpected FNFD scan result: ~a" status))))))
          (fnn-fsync-file fd)
          (fnn-owner-feed-phase journal :content-durable)
          (fnn-fsync-dir directory)
          (fnn-owner-feed-phase journal :directory-durable)
          (fnn-fsync-dir (fnn-store-root store))
          (fnn-owner-feed-phase journal :parent-durable)
          (fnn-posix (path) (sb-posix:lseek fd 0 sb-posix:seek-end))
          journal)
      (error (e)
        (when fd (ignore-errors (fnn-close fd)))
        (error e)))))

(defun fnn-owner-feed-append (journal frame)
  "Append one ACL2-sealed frame and cross every ordered durability barrier."
  (handler-case
      (let ((envelope (fnn-core 'fn-feed-journal-wrap
                                (fnn-octet-list frame))))
        (unless (fnn-octet-list-p envelope)
          (fnn-fault "owner refused FNFD envelope"))
        (fnn-owner-feed-phase journal :append)
        (fnn-write-all (fnn-owner-feed-journal-fd journal)
                       (fnn-octets envelope))
        (fnn-owner-feed-phase journal :written)
        (fnn-fsync-file (fnn-owner-feed-journal-fd journal))
        (fnn-owner-feed-phase journal :append-durable))
    (error (e)
      (ignore-errors (fnn-owner-feed-phase journal :failed))
      (fnn-owner-feed-close journal)
      (fnn-indeterminate "FNFD append uncertain: ~a (~a)"
                         (fnn-owner-feed-journal-path journal) e))))

(defun fnn-owner-feed-existing-peers (store)
  (let ((directory (fnn-owner-feed-directory store)) (peers nil))
    (when (fnn-lstat directory)
      (fnn-safe-directory directory)
      (dolist (name (fnn-list-directory directory))
        (let ((n (length name)))
          (when (and (> n 5) (string= ".fnfd" (subseq name (- n 5))))
            (let ((peer (subseq name 0 (- n 5))))
              (unless (eq (fnn-owner-core
                           'fn-owner-feed-journal-peer-validp
                           (fnn-octet-list (fnn-string-octets peer))) t)
                (fnn-fault "invalid FNFD peer filename: ~a" name))
              (pushnew peer peers :test #'string=))))))
    (nreverse peers)))

(defun fnn-owner-feed-open-all (service configured)
  (let* ((store (fnn-owner-service-store service))
         (peers (append configured (fnn-owner-feed-existing-peers store)))
         (opened nil))
    (handler-case
        (progn
          (dolist (peer (remove-duplicates peers :test #'string=))
            (push (cons peer (fnn-owner-feed-open store peer)) opened))
          (nreverse opened))
      (error (e)
        (dolist (entry opened) (fnn-owner-feed-close (cdr entry)))
        (error e)))))

(defun fnn-owner-feed-close-all (service)
  (dolist (entry (fnn-owner-service-feeds service))
    (fnn-owner-feed-close (cdr entry)))
  (setf (fnn-owner-service-feeds service) nil))

(defun fnn-owner-feed-flush (service)
  "Persist the exact pending owner frame batch before its authorized effect."
  (let* ((raw-frames (fnn-global 'fn-owner-feed-frames))
         (peers (fnn-owner-name-list
                 (fnn-owner-core 'fn-owner-feed-record-peers))))
    (unless (listp raw-frames)
      (fnn-fault "owner returned malformed FNFD frame batch"))
    (unless (= (length raw-frames) (length peers))
      (fnn-fault "owner FNFD frame/peer count mismatch"))
    (loop for peer in peers for index from 0 do
      (let ((journal (cdr (assoc peer (fnn-owner-service-feeds service)
                                 :test #'string=)))
            (frame (fnn-owner-core 'fn-owner-feed-sealed-frame index)))
        (unless journal
          (fnn-fault "FNFD obligation has no journal for peer ~a" peer))
        (unless (fnn-octet-list-p frame)
          (fnn-fault "owner returned malformed sealed FNFD frame"))
        (fnn-owner-feed-append journal (fnn-octets frame))))))

(defun fnn-owner-feed-reconcile (service)
  (loop
    (let ((resolution (fnn-owner-action 'fn-owner-feed-reconcile-next)))
      (case resolution
        (:done (return))
        (:uncertain
         (fnn-indeterminate "feed intent cannot be resolved from recovered store"))
        ((:feed-commit :feed-abort)
         (fnn-owner-feed-flush service)
         (unless (eq (fnn-owner-action 'fn-owner-feed-reconcile-apply) :ok)
           (fnn-fault "owner refused recovered feed resolution")))
        (t (fnn-fault "unexpected feed reconciliation: ~a" resolution))))))

(defun fnn-owner-install (root max-connections &optional fault)
  (multiple-value-bind (store records) (fnn-open-live-store root t fault)
    (let ((service nil))
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
              (dolist (barrier
                       (list (lambda () (fnn-fsync-regular (fnn-config-path store)))
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
            (let* ((monotonic (floor (* (get-internal-real-time) 1000)
                                     internal-time-units-per-second))
                   (dtn-epoch (encode-universal-time 0 0 0 1 1 2000 0))
                   (wall (* 1000 (max 0 (- (get-universal-time) dtn-epoch)))))
              (unless (eq (fnn-owner-action 'fn-owner-observe
                                            monotonic wall 1000 t)
                          :observed)
                (fnn-fault "owner refused its first clock observation")))
            (let ((peers (fnn-owner-core 'fn-owner-feed-configure)))
              (unless (fnn-octet-list-p peers)
                (fnn-fault "owner returned a malformed feed table"))
              (setq service
                    (%make-fnn-owner-service
                     :store store :records (length records)
                     :lock (sb-thread:make-mutex :name "fn owner/store")
                     :stopping nil))
              (let ((configured (fnn-owner-name-list peers)))
                (setf (fnn-owner-service-feeds service)
                      (fnn-owner-feed-open-all service configured))
                (fnn-owner-feed-reconcile service)
                (when configured
                  (let ((count (fnn-owner-core 'fn-owner-feed-restart)))
                    (unless (and (integerp count) (>= count 0))
                      (fnn-fault "owner returned malformed feed restart count")))
                  (fnn-owner-feed-flush service)))
              service))
        (error (e)
          (when service (fnn-owner-feed-close-all service))
          (fnn-store-close store)
          (error e))))))

(defmacro fnn-with-owner ((service) &body body)
  `(sb-thread:with-mutex ((fnn-owner-service-lock ,service)) ,@body))

(defun fnn-owner-stop-service-locked (service exit-code)
  "Fence while the owner mutex is held; the first terminal outcome wins."
  (unless (fnn-owner-service-stopping service)
    (setf (fnn-owner-service-stopping service) t
          (fnn-owner-service-exit-code service) exit-code))
  (let ((listener (fnn-owner-service-listener service)))
    (when listener (ignore-errors (fnn-socket-shut listener))))
  ;; Wake every client before command cleanup waits for its worker.  Shared
  ;; journals and Store state remain open until all workers have returned.
  (dolist (socket (fnn-owner-service-clients service))
    (ignore-errors (fnn-socket-shut socket))))

(defun fnn-owner-stop-service (service exit-code)
  (fnn-with-owner (service)
    (fnn-owner-stop-service-locked service exit-code)))

(defun fnn-owner-fence-service (service)
  "Stop this owner image after an ambiguous Store or FNFD observation."
  (fnn-owner-stop-service service +fnn-exit-uncertain+))

(defun fnn-owner-fault-service (service cid condition)
  "Contain an invalid core/store image, distinct from client refusal or EOF."
  (fnn-with-owner (service)
    (unless (fnn-owner-service-stopping service)
      (when cid
        (ignore-errors (fnn-owner-action 'fn-owner-fault cid)))
      (fnn-owner-stop-service-locked service +fnn-exit-fault+)))
  (fnn-err "owner core/store fault; process stopped: ~a" condition))

(defun fnn-owner-serialized (service cid thunk)
  "Run one semantic action, fencing before its mutex can be released."
  (fnn-with-owner (service)
    (when (fnn-owner-service-stopping service)
      (fnn-refuse "owner service is stopping"))
    (handler-case (funcall thunk)
      (fnn-store-indeterminate (e)
        (fnn-owner-stop-service-locked service +fnn-exit-uncertain+)
        (error e))
      (fnn-store-fault (e)
        (when cid (ignore-errors (fnn-owner-action 'fn-owner-fault cid)))
        (fnn-owner-stop-service-locked service +fnn-exit-fault+)
        (error e)))))

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
          (fnn-validate-post-boundary store msgid payload codes charge)
          (case (fnn-owner-action 'fn-owner-existing-action
                                  (fnn-octet-list msgid)
                                  (fnn-octet-list payload) codes)
            (:duplicate (return-from fnn-owner-attempt :duplicate))
            (:conflict (return-from fnn-owner-attempt :refused)))
          (when (>= (fnn-owner-service-records service)
                    (fnn-config-max-transactions store))
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
                  (fnn-owner-feed-flush service)
                  (let ((word (fnn-owner-attempt service msgid payload groups evidence)))
                    (fnn-owner-action 'fn-owner-submission-resolution
                                      word (fnn-octet-list evidence)
                                      generation txid)
                    (fnn-owner-feed-flush service)
                    (fnn-owner-action 'fn-owner-outcome cid word)
                    (values cid (fnn-owner-octets-global 'fn-owner-output)
                            (eq word :uncertain))))))))))

(defun fnn-owner-handle-chunk (service cid incoming)
  "Run one owner read and its serial writer drain under the service mutex."
  (fnn-owner-serialized
   service cid
   (lambda ()
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
       (when uncertain
         (fnn-owner-stop-service-locked service +fnn-exit-uncertain+))
       (values reply (or closing uncertain))))))

(defun fnn-owner-serve-client (service socket)
  (let ((fd (fnn-socket-fd socket)) (cid nil))
    (unwind-protect
         (handler-case
             (progn
               (multiple-value-bind (opened greeting)
                   (fnn-owner-serialized
                    service nil
                    (lambda ()
                      (let ((opened (fnn-owner-core 'fn-owner-open)))
                        (values opened
                                (if opened (fnn-owner-octets-global 'fn-owner-output)
                                  (fnn-make-octets 0))))))
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
           (fnn-store-indeterminate (e)
             (fnn-owner-fence-service service)
             (fnn-err "owner uncertain; recovery required: ~a" e))
           (fnn-store-fault (e)
             (fnn-owner-fault-service service cid e))
           ((or fnn-store-error fnn-os-error sb-bsd-sockets:socket-error) (e)
             (fnn-err "owner connection: ~a" e))
           (serious-condition (e)
             (fnn-owner-fault-service service cid e)))
      (when cid
        (ignore-errors
          (fnn-owner-serialized
           service cid (lambda () (fnn-owner-action 'fn-owner-close cid)))))
      (fnn-socket-shut socket))))

(defun fnn-owner-client-done (service socket)
  (fnn-with-owner (service)
    (setf (fnn-owner-service-clients service)
          (delete socket (fnn-owner-service-clients service) :test #'eq)
          (fnn-owner-service-workers service)
          (delete sb-thread:*current-thread*
                  (fnn-owner-service-workers service) :test #'eq))))

(defun fnn-owner-launch-client (service socket)
  "Register the socket and worker before either can enter the owner core."
  (fnn-with-owner (service)
    (if (fnn-owner-service-stopping service)
        (progn (ignore-errors (fnn-socket-shut socket)) nil)
      (progn
        (push socket (fnn-owner-service-clients service))
        (let ((worker
                (sb-thread:make-thread
                 (lambda ()
                   (unwind-protect (fnn-owner-serve-client service socket)
                     (fnn-owner-client-done service socket)))
                 :name "fn owner client")))
          (push worker (fnn-owner-service-workers service))
          worker)))))

(defun fnn-owner-wait-workers (service)
  "Join client workers before closing any shared journal or Store object."
  (loop
    (let ((workers
            (fnn-with-owner (service)
              (copy-list (fnn-owner-service-workers service)))))
      (when (null workers) (return))
      (dolist (worker workers) (sb-thread:join-thread worker)))))

(defun fnn-owner-accept (service listener once)
  (if once
      (fnn-owner-serve-client service
                              (sb-bsd-sockets:socket-accept listener))
      (loop until (fnn-owner-service-stopping service) do
        (handler-case
            (let ((socket (sb-bsd-sockets:socket-accept listener)))
              (fnn-owner-launch-client service socket))
          (sb-bsd-sockets:socket-error (e)
            (unless (fnn-owner-service-stopping service) (error e)))))))

(defun fnn-command-owner (command args)
  (unless (string= command "run")
    (error 'fnn-usage-error :message "unknown owner command"))
  (when (< (length args) 4)
    (error 'fnn-usage-error
           :message "owner run ROOT PORT ONCE MAX-CONNECTIONS"))
  (let ((service nil) (listener nil))
    (unwind-protect
         (progn
           (let* ((inject (fifth args))
                  (fault (and inject
                              (cdr (assoc inject +fnn-cli-faults+
                                          :test #'string=)))))
             (when (and inject (null fault))
               (error 'fnn-usage-error :message "unknown owner fault point"))
             (setq service (fnn-owner-install (first args)
                                              (parse-integer (fourth args))
                                              fault)))
           (multiple-value-bind (bound bound-port)
               (fnn-listen (parse-integer (second args)))
             (setq listener bound
                   (fnn-owner-service-listener service) bound)
             (fnn-out "LISTENING ~d" bound-port))
           (fnn-owner-accept service listener (string= (third args) "1"))
           (fnn-owner-service-exit-code service))
      (when listener (fnn-socket-shut listener))
      (when service
        (fnn-owner-wait-workers service)
        (fnn-owner-feed-close-all service)
        (fnn-store-close (fnn-owner-service-store service))))))

(fnn-register-verb "owner" #'fnn-command-owner)
