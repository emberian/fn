;;; host/native/pull-service.lisp -- the NEWNEWS pull feed's socket adapter
;;; (PRF-100; books/peer-pull.lisp, books/scheduler-peers.lisp).
;;;
;;; ACL2 owns which peers are pulled and when (fn-owner-pull-plans,
;;; fn-pull-schedule, fn-sched-pull-due/-start/-finish), whether a peer may be
;;; dialled with its transport and credential and whether its secret is read
;;; at all (fn-pull-plan-verdict, fn-pull-plan-profile-path,
;;; fn-pull-session-begin), every command sent to either side, when the TLS
;;; handshake happens and what every reply means (fn-pull-session-step: the
;;; feed-connection machine's preamble, then fn-pull-step), whether the
;;; cursor moves (fn-pull-close), the FNPL record and its envelope (fn-pull-cursor-
;;; envelope, fn-pull-cursor-envelope) and what a journal read means at open
;;; (fn-pull-journal-scan, fn-pull-records-replay).  This file dials, moves octets,
;;; appends and fsyncs, and carries the ACL2 values it is handed back to ACL2
;;; unopened.
;;;
;;; The local answers are the node's own: each listed Message-ID is offered on
;;; a logical transit connection of the pulled peer (fn-owner-open-peer, the
;;; same entry the listener uses for that peer's source address), fed through
;;; FNN-OWNER-HANDLE-CHUNK exactly as a socket read would be.
;;;
;;; Order: every (:journal . cursor) effect is appended and fsynced before the
;;; effects after it run; the begin's record precedes the dial.

(in-package "ACL2")

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :sb-posix))

(defconstant +fnn-pull-poll-seconds+ 1)
(defconstant +fnn-pull-read-seconds+ 60)

(defstruct (fnn-pull-runtime (:constructor %make-fnn-pull-runtime))
  service worker (stopping nil) lock (schedule nil) (cursors nil)
  (journals nil) (socket nil))

(defparameter *fnn-pull-runtime-lock* (sb-thread:make-mutex :name "fn pull runtimes"))
(defparameter *fnn-pull-runtimes* (make-hash-table :test #'eq))

(defun fnn-pull-runtime-get (service)
  (sb-thread:with-mutex (*fnn-pull-runtime-lock*) (gethash service *fnn-pull-runtimes*)))

(defun fnn-pull-stoppingp (runtime)
  (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
    (fnn-pull-runtime-stopping runtime)))

(defun fnn-pull-monotonic ()
  (floor (* 1000 (get-internal-real-time)) internal-time-units-per-second))

(defun fnn-pull-peer-string (peer-octets)
  (fnn-octets-string (fnn-octets peer-octets)))

;;; ---------------------------------------------------------------------------
;;; FNPL files: <store>/pull/ plus the FNFD filename codec's components.

(defun fnn-pull-directory (store) (fnn-join (fnn-store-root store) "pull"))

(defun fnn-pull-path (store peer)
  (let* ((components (fnn-feed-filename-components peer))
         (directory (fnn-pull-directory store)))
    (fnn-safe-directory directory t)
    (dolist (component (butlast components))
      (setq directory (fnn-join directory component))
      (fnn-safe-directory directory t))
    (values directory (fnn-join directory (car (last components))))))

(defun fnn-pull-sync-namespace (store directory journal)
  (fnn-fsync-dir directory)
  (fnn-owner-feed-phase journal :directory-durable)
  (let ((top (fnn-pull-directory store)))
    (unless (string= directory top)
      (let ((parent (fnn-parent directory)))
        (loop while (not (string= parent top)) do
          (fnn-fsync-dir parent)
          (setq parent (fnn-parent parent))))
      (fnn-fsync-dir top)))
  (fnn-fsync-dir (fnn-store-root store))
  (fnn-owner-feed-phase journal :parent-durable))

(defun fnn-pull-journal-open (store peer-octets)
  "Open, scan and repair one FNPL file; return (values journal cursor)."
  (let ((peer (fnn-pull-peer-string peer-octets)) (fd nil) (journal nil)
        (records nil) (offset 0) (committed 0))
    (handler-case
        (multiple-value-bind (directory path) (fnn-pull-path store peer)
          (setq fd (fnn-open path (logior sb-posix:o-rdwr sb-posix:o-creat
                                          +fnn-o-nofollow+) #o600))
          (unless (fnn-regular-p (fnn-fstat fd))
            (fnn-fault "refusing non-regular FNPL journal: ~a" path))
          (setq journal (%make-fnn-owner-feed-journal
                         :peer peer :path path :fd fd :phase :closed))
          (fnn-owner-feed-phase journal :opened)
          (let ((prefix-size (fnn-nat (fnn-core 'fn-pull-journal-prefix-size))))
            (loop
              (let* ((prefix (fnn-owner-feed-read journal prefix-size))
                     (plan (fnn-core 'fn-feed-journal-prefix (fnn-octet-list prefix)))
                     (frame (if (and (integerp plan) (>= plan 0))
                                (fnn-owner-feed-read journal plan)
                              (fnn-make-octets 0)))
                     ;; PRF-165: ACL2 carries the committed offset (the end of
                     ;; the last cursor record); a repair truncates to it.
                     (result (fnn-core 'fn-pull-journal-scan peer-octets
                                       (fnn-octet-list prefix)
                                       (fnn-octet-list frame) offset committed))
                     (status (first result)))
                (case status
                  (:next (setq offset (fnn-nat (second result))
                               committed (fnn-nat (fourth result)))
                         (push (third result) records))
                  (:invalid (fnn-fault "invalid complete FNPL evidence: ~a" path))
                  ((:end :repair)
                   (fnn-owner-feed-phase journal status)
                   (when (eq status :repair)
                     (fnn-posix (path)
                       (sb-posix:ftruncate fd (fnn-nat (second result))))
                     (fnn-owner-feed-phase journal :truncated))
                   (return))
                  (t (fnn-fault "unexpected FNPL scan result: ~a" status))))))
          (fnn-fsync-file fd)
          (fnn-owner-feed-phase journal :content-durable)
          (fnn-pull-sync-namespace store directory journal)
          (fnn-posix (path) (sb-posix:lseek fd 0 sb-posix:seek-end))
          (values journal
                  (fnn-core 'fn-pull-records-replay
                            (fnn-core 'fn-pull-fresh-cursor peer-octets)
                            (nreverse records))))
      (error (e)
        (when fd (ignore-errors (fnn-close fd)))
        (error e)))))

;;; Packet 5 (PRF-124): the cursor publication's crash cuts.  A developer
;;; image started with FN_PULL_TEST_KILL=CUT:N dies by SIGKILL at CUT of this
;;; process's Nth FNPL append: before-write (nothing of it on disk),
;;; after-write (written, not fenced) or after-fsync (durable, before the
;;; round goes on).  Production has no injection branch.
(defvar *fnn-pull-append-count* 0)

(defun fnn-pull-test-cut (cut)
  (let ((raw (fnn-developer-selector "FN_PULL_TEST_KILL")))
    (when raw
      (let* ((colon (position #\: raw))
             (name (and colon (subseq raw 0 colon)))
             (n (and colon (parse-integer raw :start (1+ colon) :junk-allowed t))))
        (unless (and n (member name '("before-write" "after-write" "after-fsync")
                               :test #'string=))
          (fnn-fault "invalid FN_PULL_TEST_KILL (expected CUT:N)"))
        (when (and (string= name cut) (= n *fnn-pull-append-count*))
          (fnn-err "pull: developer kill at ~a of append ~d" cut n)
          (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
          (fnn-fault "test SIGKILL did not terminate the process"))))))

(defun fnn-pull-journal-append (journal cursor)
  (incf *fnn-pull-append-count*)
  (handler-case
      ;; PRF-165: one :pull-unavailable frame per pending id, then the
      ;; :pull-cursor frame that commits them, in one write and one fsync.
      (let* ((envelope (fnn-core 'fn-pull-cursor-envelope cursor)))
        (unless (fnn-octet-list-p envelope)
          (fnn-fault "owner refused FNPL envelope"))
        (fnn-pull-test-cut "before-write")
        (fnn-owner-feed-phase journal :append)
        (fnn-write-all (fnn-owner-feed-journal-fd journal) (fnn-octets envelope))
        (fnn-owner-feed-phase journal :written)
        (fnn-pull-test-cut "after-write")
        (fnn-fsync-file (fnn-owner-feed-journal-fd journal))
        (fnn-owner-feed-phase journal :append-durable)
        (fnn-pull-test-cut "after-fsync"))
    (error (e)
      (ignore-errors (fnn-owner-feed-phase journal :failed))
      (fnn-owner-feed-close journal)
      (fnn-indeterminate "FNPL append uncertain: ~a (~a)"
                         (fnn-owner-feed-journal-path journal) e))))

;;; ---------------------------------------------------------------------------
;;; One round

(defun fnn-pull-local-open (service peer-octets)
  "Open the logical transit connection of PEER; return (values cid greeting)."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (fnn-owner-advance-clock)
     (let ((cid (fnn-owner-core 'fn-owner-open-peer peer-octets)))
       (unless (and (integerp cid) (>= cid 0))
         (fnn-refuse "owner refused the pull transit connection"))
       (fnn-owner-log)
       (values cid (fnn-owner-octets-global 'fn-owner-output))))))

(defun fnn-pull-local-send (service cid octets)
  "Feed OCTETS to the logical connection; return (values reply closing)."
  (let ((pending (fnn-octets octets)) (reply (fnn-make-octets 0)) (closing nil))
    (loop while (and (> (length pending) 0) (not closing)) do
      (multiple-value-bind (out close starttls consumed)
          (fnn-owner-handle-chunk service cid pending)
        (declare (ignore starttls))
        (setq reply (concatenate 'fnn-octets reply out) closing close)
        (when (and (zerop consumed) (not close))
          (fnn-fault "owner consumed no octets of a pull transit write"))
        (setq pending (subseq pending consumed))))
    (values reply closing)))

;;; The credential profile ACL2 names for PLAN (`fn-pull-plan-profile-path':
;;; nil for a plan without a credential and for a refused plan), read and
;;; decoded exactly as the push feed reads its own (`fnn-feed-auth-profile',
;;; ACL2's `fn-fap-decode').  An unreadable profile is NIL, which
;;; `fn-pull-session-begin' refuses; the host never dials without it.
(defun fnn-pull-profile (plan)
  (let ((path (fnn-core 'fn-pull-plan-profile-path plan)))
    (when (stringp path)
      (handler-case
          (multiple-value-bind (user pass) (fnn-feed-auth-profile (list :authinfo path nil))
            (list user pass))
        (error ()
          (fnn-err "pull: the credential profile of peer ~a is unreadable"
                   (fnn-pull-peer-string (fnn-core 'fn-pull-plan-peer plan)))
          nil)))))

(defun fnn-pull-round (runtime plan journal cursor)
  "Drive one ACL2 pull session; return the cursor after its close."
  (let* ((service (fnn-pull-runtime-service runtime))
         (peer (fnn-core 'fn-pull-plan-peer plan))
         (wall (fnn-owner-wall-milliseconds))
         (begun (fnn-core 'fn-pull-session-begin-pair plan cursor wall
                          (fnn-pull-profile plan)))
         (session (first begun))
         (socket nil) (fd nil) (context nil) (channel nil) (cid nil) (events nil))
    (labels ((enqueue (event) (setq events (append events (list event))))
             (send-remote (octets)
               (if channel
                   (fnn-tls-send-all channel octets 10)
                 (fnn-send-all fd octets 10)))
             (perform (effects)
               (dolist (effect effects)
                 (case (car effect)
                   (:journal (fnn-pull-journal-append journal (cdr effect)))
                   (:dial
                    (handler-case
                        (setq socket (fnn-connect (fnn-pull-peer-string
                                                   (fnn-core 'fn-pull-plan-host plan))
                                                  (fnn-core 'fn-pull-plan-port plan)
                                                  :timeout 10)
                              fd (fnn-socket-fd socket))
                      (error () (enqueue (list :lost))))
                    (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
                      (setf (fnn-pull-runtime-socket runtime) socket)))
                   ;; (:tls SERVER-NAME TRUST-ANCHOR): the handshake ACL2 asked
                   ;; for, verified against exactly that name and anchor; only a
                   ;; verified handshake is reported (:tls-up).
                   (:tls
                    (if (null fd)
                        (enqueue (list :lost))
                      (handler-case
                          (progn
                            (setq context (fnn-tls-open-client-context (third effect)))
                            (setq channel (fnn-tls-connect context fd (second effect) 10))
                            (enqueue (list :tls-up)))
                        (error (e)
                          (fnn-err "pull: TLS to peer ~a failed: ~a"
                                   (fnn-pull-peer-string peer) e)
                          (enqueue (list :lost))))))
                   (:remote (handler-case (send-remote (fnn-octets (cdr effect)))
                              (error () (enqueue (list :lost)))))
                   (:open-local
                    (multiple-value-bind (opened greeting)
                        (fnn-pull-local-open service peer)
                      (setq cid opened)
                      (enqueue (cons :local (fnn-octet-list greeting)))))
                   ;; PRF-165: the peer answered ARTICLE 430; the transit
                   ;; connection is inside an IHAVE it cannot finish.  Close
                   ;; it (the owner discards the unfinished IHAVE) and open a
                   ;; fresh one; its greeting is the round's next event.
                   (:reopen-local
                    (when cid
                      (let ((old cid))
                        (setq cid nil)
                        (fnn-owner-serialized service nil
                                              (lambda () (fnn-owner-action 'fn-owner-close old)))))
                    (multiple-value-bind (opened greeting)
                        (fnn-pull-local-open service peer)
                      (setq cid opened)
                      (enqueue (cons :local (fnn-octet-list greeting)))))
                   (:local
                    (multiple-value-bind (reply closing)
                        (fnn-pull-local-send service cid (cdr effect))
                      (when (> (length reply) 0)
                        (enqueue (cons :local (fnn-octet-list reply))))
                      (when closing
                        (setq cid nil)
                        (enqueue (list :lost)))))
                   (:close nil)
                   (t (fnn-fault "unknown pull effect ~s" (car effect))))))
             (advance (event)
               (let ((pair (fnn-core 'fn-pull-session-step-pair session event)))
                 (setq session (first pair))
                 (perform (second pair))))
             (receive ()
               (let ((limit (or (fnn-core 'fn-pull-session-read-limit session)
                                +fnn-max-read+)))
                 (handler-case
                     (if channel
                         (fnn-tls-read channel +fnn-pull-read-seconds+ limit)
                       (fnn-recv fd +fnn-pull-read-seconds+ limit))
                   (error () :lost)))))
      (unwind-protect
           (progn
             (perform (second begun))
             (loop until (or (fnn-core 'fn-pull-session-done-p session)
                             (fnn-pull-stoppingp runtime)) do
               (if (or events (null fd))
                   (advance (if events (pop events) (list :lost)))
                 (let ((incoming (receive)))
                   (advance (if (or (eq incoming :timeout) (eq incoming :lost)
                                    (zerop (length incoming)))
                                (list :lost)
                              (cons :remote (fnn-octet-list incoming))))))))
        (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
          (setf (fnn-pull-runtime-socket runtime) nil))
        (when cid
          (ignore-errors
           (fnn-owner-serialized service nil
                                 (lambda () (fnn-owner-action 'fn-owner-close cid)))))
        (when channel (ignore-errors (fnn-tls-close-channel channel)))
        (when context (ignore-errors (fnn-tls-close-context context)))
        (when socket (ignore-errors (fnn-socket-shut socket))))
      (perform (fnn-core 'fn-pull-session-close-effects session))
      (fnn-log-line (fnn-core 'fn-pull-session-log-line session))
      (fnn-core 'fn-pull-session-close session))))

;;; ---------------------------------------------------------------------------
;;; The worker

(defun fnn-pull-cursor-for (runtime plan)
  (let* ((peer (fnn-core 'fn-pull-plan-peer plan))
         (key (fnn-pull-peer-string peer))
         (entry (assoc key (fnn-pull-runtime-journals runtime) :test #'string=)))
    (if entry
        (values (cdr entry) (cdr (assoc key (fnn-pull-runtime-cursors runtime) :test #'string=)))
      (multiple-value-bind (journal cursor)
          (fnn-pull-journal-open (fnn-owner-service-store (fnn-pull-runtime-service runtime)) peer)
        (push (cons key journal) (fnn-pull-runtime-journals runtime))
        (push (cons key cursor) (fnn-pull-runtime-cursors runtime))
        (values journal cursor)))))

(defun fnn-pull-worker (runtime)
  (let ((service (fnn-pull-runtime-service runtime)))
    (unwind-protect
         (loop until (fnn-pull-stoppingp runtime) do
           (let* ((plans (fnn-owner-serialized
                          service nil (lambda () (fnn-owner-core 'fn-owner-pull-plans))))
                  (now (fnn-pull-monotonic)))
             (setf (fnn-pull-runtime-schedule runtime)
                   (fnn-core 'fn-pull-schedule plans now (fnn-pull-runtime-schedule runtime)))
             (let ((peer (fnn-core 'fn-sched-pull-due (fnn-pull-runtime-schedule runtime) now)))
               (when peer
                 (let ((plan (fnn-core 'fn-pull-plan-for peer plans)))
                   (setf (fnn-pull-runtime-schedule runtime)
                         (fnn-core 'fn-sched-pull-start peer (fnn-pull-runtime-schedule runtime)))
                   (multiple-value-bind (journal cursor) (fnn-pull-cursor-for runtime plan)
                     (let ((closed (fnn-pull-round runtime plan journal cursor))
                           (key (fnn-pull-peer-string peer)))
                       (setf (cdr (assoc key (fnn-pull-runtime-cursors runtime) :test #'string=))
                             closed)))
                   (setf (fnn-pull-runtime-schedule runtime)
                         (fnn-core 'fn-sched-pull-finish peer (fnn-pull-monotonic)
                                   (fnn-pull-runtime-schedule runtime)))))))
           (sleep +fnn-pull-poll-seconds+))
      (dolist (entry (fnn-pull-runtime-journals runtime))
        (fnn-owner-feed-close (cdr entry))))))

(defun fnn-pull-worker-guarded (runtime)
  (handler-case (fnn-pull-worker runtime)
    (fnn-store-indeterminate (e)
      (fnn-owner-fence-service (fnn-pull-runtime-service runtime))
      (fnn-err "pull feed uncertain; recovery required: ~a" e))
    (serious-condition (e)
      (unless (fnn-pull-stoppingp runtime)
        (fnn-owner-fault-service (fnn-pull-runtime-service runtime) nil e)))))

(defun fnn-pull-service-start (service)
  (unless (fnn-pull-runtime-get service)
    (let ((runtime (%make-fnn-pull-runtime
                    :service service
                    :lock (sb-thread:make-mutex :name "fn pull runtime"))))
      (sb-thread:with-mutex (*fnn-pull-runtime-lock*)
        (setf (gethash service *fnn-pull-runtimes*) runtime))
      (setf (fnn-pull-runtime-worker runtime)
            (sb-thread:make-thread (lambda () (fnn-pull-worker-guarded runtime))
                                   :name "fn pull feed"))))
  nil)

(defun fnn-pull-service-wake (service)
  (let ((runtime (fnn-pull-runtime-get service)))
    (when runtime
      (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
        (setf (fnn-pull-runtime-stopping runtime) t)
        (let ((socket (fnn-pull-runtime-socket runtime)))
          (when socket (ignore-errors (fnn-socket-shutdown socket)))))))
  nil)

(defun fnn-pull-service-close (service)
  (let ((runtime (fnn-pull-runtime-get service)))
    (when runtime
      (fnn-pull-service-wake service)
      (let ((worker (fnn-pull-runtime-worker runtime)))
        (when worker (sb-thread:join-thread worker)))
      (sb-thread:with-mutex (*fnn-pull-runtime-lock*)
        (remhash service *fnn-pull-runtimes*))))
  nil)
