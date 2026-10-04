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
;;;
;;; Catch-up (PRF-325, books/peer-catchup.lisp) runs on the same worker and
;;; the same round driver: ACL2 owns which peers catch up (fn-owner-catchup-
;;; plans, `peer catch-up NAME SECONDS'), the session (fn-cu-session-*: the
;;; pull's preamble, then XFNCATCHUP batches verified against the peer's
;;; digest chain and offered by IHAVE on the local transit connection), the
;;; FNCU record and envelope (fn-cu-cursor-envelope) and the open's reading
;;; (fn-cu-journal-scan, fn-cu-records-replay).  Its journals live in
;;; <store>/catch-up/; FN_CATCHUP_TEST_KILL is its developer cut.

(in-package "ACL2")

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :sb-posix))

(defconstant +fnn-pull-poll-seconds+ 1)
(defconstant +fnn-pull-read-seconds+ 60)

(defstruct (fnn-pull-runtime (:constructor %make-fnn-pull-runtime))
  service worker (stopping nil) lock (schedule nil) (cursors nil)
  (journals nil) (socket nil) (flights nil)
  ;; Physical thread completion cannot discharge a failed terminal release.
  ;; Retain the runtime and its journals/flights until recovery, never retry
  ;; the worker's already attempted cleanup from the close hook.
  (cleanup-debt nil) (cleanup-stage nil)
  ;; PRF-325: the catch-up rounds' own schedule, cursors and FNCU journals.
  (cu-schedule nil) (cu-cursors nil) (cu-journals nil)
  ;; Catch-up flight leases whose spool worker has been stopped but not yet
  ;; joined: settled only after the actual thread is dead (never twice).
  ;; Owned by the pull worker thread alone (finish, sweep and cleanup).
  (settling nil))

(defparameter *fnn-pull-runtime-lock* (sb-thread:make-mutex :name "fn pull runtimes"))
;; guarded-by: *fnn-pull-runtime-lock*
(defparameter *fnn-pull-runtimes* (make-hash-table :test #'eq))

(defun fnn-pull-runtime-get (service)
  (sb-thread:with-mutex (*fnn-pull-runtime-lock*) (gethash service *fnn-pull-runtimes*)))

(defun fnn-pull-stoppingp (runtime)
  (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
    (fnn-pull-runtime-stopping runtime)))

(defun fnn-pull-monotonic ()
  (fnn-monotonic-ms))

(defun fnn-pull-peer-string (peer-octets)
  (fnn-octets-string (fnn-octets peer-octets)))

;;; ---------------------------------------------------------------------------
;;; FNPL files: <store>/pull/ plus the FNFD filename codec's components.

(defun fnn-pull-directory (store &optional (top "pull"))
  (fnn-join (fnn-store-root store) top))

(defun fnn-pull-path (store peer &optional (top "pull"))
  (let* ((components (fnn-feed-filename-components peer))
         (directory (fnn-pull-directory store top)))
    (fnn-safe-directory directory t)
    (dolist (component (butlast components))
      (setq directory (fnn-join directory component))
      (fnn-safe-directory directory t))
    (values directory (fnn-join directory (car (last components))))))

(defun fnn-pull-sync-namespace (store directory journal &optional (top-name "pull"))
  (fnn-fsync-dir directory)
  (fnn-owner-feed-phase journal :directory-durable)
  (let ((top (fnn-pull-directory store top-name)))
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

;;; PRF-325: one FNCU file, <store>/catch-up/ plus the FNFD filename codec's
;;; components.  ACL2 reads each frame (fn-cu-journal-scan: the safe offset
;;; advances only over a complete verified cursor frame of this peer) and
;;; recovers the last cursor (fn-cu-records-replay); a torn tail is
;;; truncated to the safe offset before anything is appended.
(defun fnn-catchup-journal-open (store peer-octets)
  "Open, scan and repair one FNCU file; return (values journal cursor)."
  (let ((peer (fnn-pull-peer-string peer-octets)) (fd nil) (journal nil)
        (records nil) (offset 0))
    (handler-case
        (multiple-value-bind (directory path) (fnn-pull-path store peer "catch-up")
          (setq fd (fnn-open path (logior sb-posix:o-rdwr sb-posix:o-creat
                                          +fnn-o-nofollow+) #o600))
          (unless (fnn-regular-p (fnn-fstat fd))
            (fnn-fault "refusing non-regular FNCU journal: ~a" path))
          (setq journal (%make-fnn-owner-feed-journal
                         :peer peer :path path :fd fd :phase :closed))
          (fnn-owner-feed-phase journal :opened)
          (let ((prefix-size (fnn-nat (fnn-core 'fn-cu-journal-prefix-size))))
            (loop
              (let* ((prefix (fnn-owner-feed-read journal prefix-size))
                     (plan (fnn-core 'fn-feed-journal-prefix (fnn-octet-list prefix)))
                     (frame (if (and (integerp plan) (>= plan 0))
                                (fnn-owner-feed-read journal plan)
                              (fnn-make-octets 0)))
                     (result (fnn-core 'fn-cu-journal-scan peer-octets
                                       (fnn-octet-list prefix)
                                       (fnn-octet-list frame) offset))
                     (status (first result)))
                (case status
                  (:next (setq offset (fnn-nat (second result)))
                         (push (third result) records))
                  (:invalid (fnn-fault "invalid complete FNCU evidence: ~a" path))
                  ((:end :repair)
                   (fnn-owner-feed-phase journal status)
                   (when (eq status :repair)
                     (fnn-posix (path)
                       (sb-posix:ftruncate fd (fnn-nat (second result))))
                     (fnn-owner-feed-phase journal :truncated))
                   (return))
                  (t (fnn-fault "unexpected FNCU scan result: ~a" status))))))
          (fnn-fsync-file fd)
          (fnn-owner-feed-phase journal :content-durable)
          (fnn-pull-sync-namespace store directory journal "catch-up")
          (fnn-posix (path) (sb-posix:lseek fd 0 sb-posix:seek-end))
          (values journal
                  (fnn-core 'fn-cu-records-replay
                            (fnn-core 'fn-cu-fresh-cursor peer-octets)
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
;;; PRF-325: the catch-up journal's appends are counted apart and cut by
;;; FN_CATCHUP_TEST_KILL (the same CUT:N grammar), so one selector never
;;; reaches the other's appends.
(defvar *fnn-catchup-append-count* 0)

(defun fnn-pull-test-cut (cut &optional (kind :pull))
  (let* ((variable (if (eq kind :catch-up) "FN_CATCHUP_TEST_KILL" "FN_PULL_TEST_KILL"))
         (count (if (eq kind :catch-up) *fnn-catchup-append-count* *fnn-pull-append-count*))
         (raw (fnn-developer-selector variable)))
    (when raw
      (let* ((colon (position #\: raw))
             (name (and colon (subseq raw 0 colon)))
             (n (and colon (parse-integer raw :start (1+ colon) :junk-allowed t))))
        (unless (and n (member name '("before-write" "after-write" "after-fsync")
                               :test #'string=))
          (fnn-fault "invalid ~a (expected CUT:N)" variable))
        (when (and (string= name cut) (= n count))
          (fnn-err "~a: developer kill at ~a of append ~d"
                   (if (eq kind :catch-up) "catch-up" "pull") cut n)
          (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
          (fnn-fault "test SIGKILL did not terminate the process"))))))

(defun fnn-pull-journal-append (journal cursor &optional (kind :pull))
  (if (eq kind :catch-up)
      (incf *fnn-catchup-append-count*)
    (incf *fnn-pull-append-count*))
  ;; Seal and validate before any append attempt: a definite refusal/fault
  ;; keeps its class. FNPL's pending frames and cursor share one barrier;
  ;; FNCU has one cursor frame. The bytes and phase decisions remain ACL2's.
  (let* ((envelope (fnn-core (if (eq kind :catch-up)
                               'fn-cu-cursor-envelope
                             'fn-pull-cursor-envelope)
                           cursor)))
    (unless (fnn-octet-list-p envelope)
      (fnn-fault "owner refused ~a envelope" (if (eq kind :catch-up) "FNCU" "FNPL")))
    (let ((bytes (fnn-octets envelope)))
      (fnn-pull-test-cut "before-write" kind)
      (fnn-owner-feed-phase journal :append)
      (handler-case
          (progn
            (fnn-write-all (fnn-owner-feed-journal-fd journal) bytes)
            (fnn-owner-feed-phase journal :written)
            (fnn-pull-test-cut "after-write" kind)
            (fnn-fsync-file (fnn-owner-feed-journal-fd journal)))
        (error (e)
          (ignore-errors (fnn-owner-feed-phase journal :failed))
          (let ((cleanup-error
                  (handler-case (progn (fnn-owner-feed-close journal) nil)
                    (serious-condition (close-error) close-error))))
            ;; Cleanup cannot erase an ambiguous persistence outcome.
            (fnn-indeterminate "~a append uncertain: ~a (~a)~@[; close failed: ~a~]"
                               (if (eq kind :catch-up) "FNCU" "FNPL")
                               (fnn-owner-feed-journal-path journal) e cleanup-error))))
      ;; The barrier returned: subsequent classification/cut faults are
      ;; definite faults, never a claim that the persisted cursor vanished.
      (fnn-owner-feed-phase journal :append-durable)
      (fnn-pull-test-cut "after-fsync" kind))))

;;; ---------------------------------------------------------------------------
;;; One round

(defun fnn-pull-local-open (service peer-octets)
  "Open the logical transit connection of PEER; return (values cid greeting)."
  (fnn-owner-transit-serialized
   service nil
   (lambda ()
     (fnn-owner-advance-clock)
     (let ((cid (fnn-owner-core 'fn-owner-open-peer peer-octets)))
       (unless (and (integerp cid) (>= cid 0))
         (fnn-refuse "owner refused the pull transit connection"))
       (fnn-owner-log)
       (values cid (fnn-owner-octets-global 'fn-owner-output))))))

(defun fnn-pull-local-send (service cid octets)
  "Feed OCTETS to the logical connection; return (values reply closing).
The owner's logical feed (host/native/owner.lisp fnn-owner-feed-logical):
the served step's plan rendered here, off the owner mutex, and an
article's submission awaited off it through the batch it joins (r71 F5:
no inline commit).  A completion with no rendered reply (the batch's
barrier failed or the owner stopped) closes the transit connection, the
round's lost local connection: uncertain, never a refusal or an
acceptance (the owner is stopping or fenced then)."
  (multiple-value-bind (reply closing uncertain)
      (fnn-owner-feed-logical service cid octets :transit "pull transit write")
    (values reply (or closing uncertain))))

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
        ((or fnn-feed-auth-error fnn-os-error) (condition)
          (fnn-peer-dial-report :pull (fnn-core 'fn-pull-plan-peer plan)
                                (fnn-core 'fn-pull-plan-host plan)
                                (if (typep condition 'fnn-feed-auth-error) condition
                                  (make-condition 'fnn-feed-auth-error)))
          nil)))))

(defun fnn-pull-round (runtime plan journal cursor &optional (kind :pull))
  "Blocking compatibility adapter; the worker uses retained flights directly."
  (let ((flight (fnn-pull-flight-begin runtime plan journal cursor kind)) (primary nil))
    (handler-bind ((serious-condition (lambda (condition) (unless primary (setq primary condition)))))
      (unwind-protect
           (progn
             (loop for result = (if (fnn-pull-stoppingp runtime) :stopping
                                  (fnn-pull-flight-quantum flight))
                   until (member result '(:stopping :finished))
                   do (when (eq result :wait) (sleep (/ (fnn-core 'fn-prd-idle-ms) 1000))))
             (fnn-pull-flight-finish flight)
             (fnn-pull-settle-leases runtime t)
             (fnn-core (if (eq kind :catch-up) 'fn-csp-close 'fn-pull-session-close)
                       (fnn-pull-flight-session flight)))
        (if primary (ignore-errors (fnn-pull-flight-dispose flight))
          (fnn-pull-flight-dispose flight))))))

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

(defun fnn-catchup-cursor-for (runtime plan)
  (let* ((peer (fnn-core 'fn-pull-plan-peer plan))
         (key (fnn-pull-peer-string peer))
         (entry (assoc key (fnn-pull-runtime-cu-journals runtime) :test #'string=)))
    (if entry
        (values (cdr entry) (cdr (assoc key (fnn-pull-runtime-cu-cursors runtime)
                                        :test #'string=)))
      (multiple-value-bind (journal cursor)
          (fnn-catchup-journal-open (fnn-owner-service-store
                                     (fnn-pull-runtime-service runtime))
                                    peer)
        (push (cons key journal) (fnn-pull-runtime-cu-journals runtime))
        (push (cons key cursor) (fnn-pull-runtime-cu-cursors runtime))
        (values journal cursor)))))

(defun fnn-pull-prune-journals (runtime plans &optional (kind :pull))
  "Retire descriptor custody only for peers ACL2's current plans no longer name."
  (let* ((catchup (eq kind :catch-up))
         (journals (if catchup (fnn-pull-runtime-cu-journals runtime)
                     (fnn-pull-runtime-journals runtime)))
         (retired (make-hash-table :test #'equal))
         (keep nil) (close nil))
    (dolist (entry journals)
      (if (fnn-core 'fn-pull-plan-for
                    (fnn-octet-list (fnn-string-octets (car entry))) plans)
          (push entry keep)
        (progn
          (setf (gethash (car entry) retired) t)
          (push (cdr entry) close))))
    (flet ((live-cursor (entry) (not (gethash (car entry) retired))))
      (if catchup
          (setf (fnn-pull-runtime-cu-journals runtime) (nreverse keep)
                (fnn-pull-runtime-cu-cursors runtime)
                (remove-if-not #'live-cursor (fnn-pull-runtime-cu-cursors runtime)))
        (setf (fnn-pull-runtime-journals runtime) (nreverse keep)
              (fnn-pull-runtime-cursors runtime)
              (remove-if-not #'live-cursor (fnn-pull-runtime-cursors runtime)))))
    ;; Drop retired cache entries before close: a close fault never leaves
    ;; a cached nil descriptor available to a later round.
    (let ((failure nil))
      (dolist (journal close)
        (handler-case (fnn-owner-feed-close journal)
          (serious-condition (condition) (unless failure (setq failure condition)))))
      (when failure (error failure)))))

;;; PRF-325: one due catch-up round, scheduled exactly as a pull
;;; (fn-pull-schedule and fn-sched-pull-* over the catch-up plans, which are
;;; pull plans with the catch-up interval) but on its own table.
(defun fnn-catchup-tick (runtime)
  (let* ((service (fnn-pull-runtime-service runtime))
         (plans (fnn-owner-transit-serialized
                 service nil (lambda () (fnn-owner-core 'fn-owner-catchup-plans))))
         (now (fnn-pull-monotonic)))
    (fnn-pull-prune-journals runtime plans :catch-up)
    (setf (fnn-pull-runtime-cu-schedule runtime)
          (fnn-core 'fn-pull-schedule plans now (fnn-pull-runtime-cu-schedule runtime)))
    (let ((peer (fnn-core 'fn-sched-pull-due (fnn-pull-runtime-cu-schedule runtime) now)))
      (when peer
        (let ((plan (fnn-core 'fn-pull-plan-for peer plans)))
          (setf (fnn-pull-runtime-cu-schedule runtime)
                (fnn-core 'fn-sched-pull-start peer (fnn-pull-runtime-cu-schedule runtime)))
          (multiple-value-bind (journal cursor) (fnn-catchup-cursor-for runtime plan)
            (let ((closed (fnn-pull-round runtime plan journal cursor :catch-up))
                  (key (fnn-pull-peer-string peer)))
              (setf (cdr (assoc key (fnn-pull-runtime-cu-cursors runtime) :test #'string=))
                    closed)))
          (setf (fnn-pull-runtime-cu-schedule runtime)
                (fnn-core 'fn-sched-pull-finish peer (fnn-pull-monotonic)
                          (fnn-pull-runtime-cu-schedule runtime))))))))

;;; A worker owns these continuations. Callback threads publish only a cell
;;; under the runtime mutex; they never call the owner while holding it.
(defstruct (fnn-pull-flight (:constructor %make-fnn-pull-flight))
  runtime plan journal kind key peer session effects events why
  socket fd context channel tls-name io deadline data (offset 0) end
  cid input cold cold-word await completion render cursor-cold-since parts closing resume-at
  (closed nil)
  ;; Catch-up only (books/peer-catchup-spool.lisp): the bank lease, its spool
  ;; worker, the private digest cursor and the one outstanding spool operation.
  lease worker hash hash-total hash-base spool-op
  ;; S054/S067: the round's ACL2 deadline (fn-prd-round-deadline).
  round-deadline)

(defun fnn-pull-flight-event (flight event)
  (setf (fnn-pull-flight-events flight)
        (append (fnn-pull-flight-events flight) (list event))))

(defun fnn-pull-flight-service (flight)
  (fnn-pull-runtime-service (fnn-pull-flight-runtime flight)))

(defun fnn-pull-flight-set-socket (flight socket)
  (let ((runtime (fnn-pull-flight-runtime flight)))
    (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
      (setf (fnn-pull-flight-socket flight) socket))))

(defun fnn-pull-flight-close-local (flight)
  "Revoke publication and attempt every local release, preserving first failure."
  (let ((cid (fnn-pull-flight-cid flight))
        (cold (fnn-pull-flight-cold flight))
        (service (fnn-pull-flight-service flight)) (await nil) (failure nil))
    ;; Invalidate the callback's captured await identity before owner calls.
    ;; Abandonment revokes publication; it is not a physical-job receipt.
    (sb-thread:with-mutex ((fnn-pull-runtime-lock (fnn-pull-flight-runtime flight)))
      (setq await (fnn-pull-flight-await flight))
      (setf (fnn-pull-flight-cid flight) nil
            (fnn-pull-flight-await flight) nil
            (fnn-pull-flight-completion flight) nil))
    (setf (fnn-pull-flight-cold flight) nil
          (fnn-pull-flight-input flight) nil
          (fnn-pull-flight-render flight) nil
          (fnn-pull-flight-cursor-cold-since flight) nil)
    (flet ((release (thunk)
             (handler-case (funcall thunk)
               (serious-condition (condition) (unless failure (setq failure condition))))))
      (when cold (release (lambda () (fnn-owner-cold-abandon (first cold)))))
      (when cid
        (when await (release (lambda () (fnn-owner-await-abandon service cid))))
        (release (lambda () (fnn-owner-response-unpin service cid)))
        (release (lambda ()
                   (fnn-owner-transit-serialized
                    service nil (lambda () (fnn-owner-action 'fn-owner-close cid)))))))
    (when failure (error failure))))

(defun fnn-pull-flight-dispose (flight)
  "Attempt all releases; preserve the first cleanup condition."
  (when (sb-thread:with-mutex ((fnn-pull-runtime-lock (fnn-pull-flight-runtime flight)))
          (unless (fnn-pull-flight-closed flight)
            (setf (fnn-pull-flight-closed flight) t)
            t))
    (let ((failure nil))
      (flet ((release (thunk)
               (handler-case (funcall thunk)
                 (serious-condition (condition) (unless failure (setq failure condition))))))
        (release (lambda () (fnn-pull-flight-close-local flight)))
        (release (lambda () (fnn-tls-close-channel (fnn-pull-flight-channel flight))))
        (release (lambda () (fnn-tls-close-context (fnn-pull-flight-context flight))))
        (release (lambda () (when (fnn-pull-flight-socket flight)
                              (fnn-socket-shut (fnn-pull-flight-socket flight)))))
        (fnn-pull-flight-set-socket flight nil))
      (when failure (error failure)))))

;;; A catch-up flight draws its independent bank lease before the session
;;; exists; ACL2 names the spool allowance and refuses a round without one.
(defun fnn-pull-flight-catchup-lease (runtime)
  (let ((bank (fnn-owner-service-peer-flight-bank (fnn-pull-runtime-service runtime))))
    (when bank
      (let ((lease (fnn-peer-flight-draw bank)))
        (when lease
          (values lease (fnn-core 'fn-csp-flight-spool (fnn-peer-flight-bank-policy bank))))))))

(defun fnn-pull-flight-begin (runtime plan journal cursor kind)
  (let ((peer (fnn-core 'fn-pull-plan-peer plan)))
    (if (eq kind :catch-up)
        (multiple-value-bind (lease limit) (fnn-pull-flight-catchup-lease runtime)
          ;; The flight holds the lease from here; a refused round settles it.
          (let* ((flight (%make-fnn-pull-flight
                          :runtime runtime :plan plan :journal journal :kind kind
                          :key (fnn-core 'fn-prd-key kind peer) :peer peer :lease lease
                          :round-deadline (fnn-core 'fn-prd-round-deadline (fnn-pull-monotonic))))
                 (begun (fnn-core 'fn-csp-begin plan cursor (fnn-pull-profile plan) limit)))
            (setf (fnn-pull-flight-session flight) (first begun)
                  (fnn-pull-flight-effects flight) (second begun))
            flight))
      (let ((begun (fnn-core 'fn-pull-session-begin-pair plan cursor
                             (fnn-owner-wall-milliseconds) (fnn-pull-profile plan))))
        (%make-fnn-pull-flight :runtime runtime :plan plan :journal journal :kind kind
                              :key (fnn-core 'fn-prd-key kind peer) :peer peer
                              :round-deadline (fnn-core 'fn-prd-round-deadline (fnn-pull-monotonic))
                              :session (first begun) :effects (second begun))))))

(defun fnn-pull-flight-metered-event (flight event)
  "EVENT, or (:work-refused) when the bank refuses the step's metered work."
  (let ((lease (fnn-pull-flight-lease flight)))
    (if (and lease
             (not (fnn-peer-flight-work
                   lease (fnn-core 'fn-csp-work-units (fnn-pull-flight-session flight) event))))
        (list :work-refused)
      event)))

(defun fnn-pull-flight-advance (flight event)
  (let ((triple (if (eq (fnn-pull-flight-kind flight) :catch-up)
                    (append (fnn-core 'fn-csp-step (fnn-pull-flight-session flight)
                                      (fnn-pull-flight-metered-event flight event))
                            (list nil))
                  (fnn-core 'fn-pull-session-step-triple
                            (fnn-pull-flight-session flight) event))))
    (setf (fnn-pull-flight-session flight) (first triple)
          (fnn-pull-flight-effects flight) (second triple))
    (unless (fnn-pull-flight-why flight)
      (setf (fnn-pull-flight-why flight) (third triple)))))

(defun fnn-pull-flight-set-io (flight io &optional timed)
  (setf (fnn-pull-flight-io flight) io
        (fnn-pull-flight-deadline flight)
        (and timed (fnn-core 'fn-prd-deadline (fnn-pull-monotonic)
                            (fnn-core 'fn-owner-feed-connect-timeout)))))

(defun fnn-pull-flight-local-open (flight)
  (multiple-value-bind (cid greeting)
      (fnn-pull-local-open (fnn-pull-flight-service flight) (fnn-pull-flight-peer flight))
    (setf (fnn-pull-flight-cid flight) cid)
    (fnn-pull-flight-event flight (cons :local (fnn-octet-list greeting)))))

;;; ---------------------------------------------------------------------------
;;; Catch-up spool I/O (books/peer-catchup-spool.lisp decides every offset,
;;; count and octet; host/native/catchup-spool.lisp performs them).  One
;;; operation is outstanding per flight; the driver polls it, never waits.

;; A process-unique private name; the worker opens it O_EXCL and unlinks it
;; at once, so no name outlives the descriptor.
(defvar *fnn-csp-spool-serial* (list 0))

(defun fnn-pull-flight-spool-path (flight)
  (let* ((store (fnn-owner-service-store (fnn-pull-flight-service flight)))
         (directory (fnn-pull-directory store "catch-up")))
    (fnn-safe-directory directory t)
    (fnn-join directory (format nil ".spool-~d-~d" (sb-posix:getpid)
                                (sb-ext:atomic-incf (car *fnn-csp-spool-serial*))))))

;;; SPOOL-OP is (operation offset count bytes phase next): phase :ready (not
;;; yet submitted) or :submitted; NEXT is the operation queued behind the
;;; worker's own :open, the only one that can precede another.

(defun fnn-pull-flight-ensure-worker (flight)
  "Start the lease's private spool worker; its first operation opens the file."
  (unless (fnn-pull-flight-worker flight)
    (let ((lease (fnn-pull-flight-lease flight)))
      (unless lease (fnn-fault "catch-up spool effect without a flight lease"))
      (fnn-csp-worker-start
       (fnn-pull-flight-spool-path flight) lease
       (lambda (worker)
         ;; Custody is published before the thread exists.
         (setf (fnn-peer-flight-lease-worker lease) worker
               (fnn-pull-flight-worker flight) worker)))
      (setf (fnn-pull-flight-spool-op flight) (list :open 0 0 nil :ready nil))))
  (fnn-pull-flight-worker flight))

(defun fnn-pull-flight-spool-begin (flight operation offset count &optional bytes)
  (let ((op (list operation offset count bytes :ready nil))
        (open (fnn-pull-flight-spool-op flight)))
    (if (and open (eq (first open) :open))
        (setf (sixth (fnn-pull-flight-spool-op flight)) op)
      (setf (fnn-pull-flight-spool-op flight) op))))

(defun fnn-pull-flight-spool-submit (flight operation offset count)
  "Draw the operation's metered work, then hand it to the worker; nil if refused."
  (when (fnn-peer-flight-work (fnn-pull-flight-lease flight)
                              (fnn-core 'fn-csp-io-work-units operation count))
    (fnn-csp-worker-submit (fnn-pull-flight-worker flight) operation offset count)
    t))

(defun fnn-pull-flight-spool-event (flight operation status actual)
  "The controller's event for a completed (or failed) worker operation."
  (let ((worker (fnn-pull-flight-worker flight)))
    (case operation
      (:write (list :spool-written status actual))
      (:replay
       (let ((replay (fnn-csp-worker-replay worker)))
         (list :spool-read status actual
               (if (eq status :ok)
                   (loop for i below (min actual (length replay)) collect (aref replay i))
                 nil))))
      (:digest (list :digest nil))
      (t (fnn-fault "unknown catch-up spool completion ~s" operation)))))

(defun fnn-pull-flight-spool-step (flight)
  "One poll of the outstanding spool operation; never waits on the worker."
  (let ((worker (fnn-pull-flight-worker flight)))
    (destructuring-bind (operation offset count bytes phase next) (fnn-pull-flight-spool-op flight)
      (flet ((finish (event)
               (setf (fnn-pull-flight-spool-op flight) nil)
               (fnn-pull-flight-set-io flight nil)
               (fnn-pull-flight-event flight event)))
        (case phase
          (:ready
           (when (eq operation :write)
             (let ((input (fnn-csp-worker-input worker)) (i 0))
               (dolist (byte bytes) (setf (aref input i) byte) (incf i))))
           (if (fnn-pull-flight-spool-submit flight operation offset count)
               (setf (fifth (fnn-pull-flight-spool-op flight)) :submitted)
             (finish (list :work-refused)))
           :progress)
          (:submitted
           (multiple-value-bind (ready status actual condition) (fnn-csp-worker-take worker)
             (if (not ready) :wait
              (progn
               (let ((status (if condition :error status)) (actual (if condition 0 actual)))
                 (cond
                   ((eq operation :open)
                    (if (eq status :ok)
                        (setf (fnn-pull-flight-spool-op flight) next)
                      (finish (fnn-pull-flight-spool-event flight (first next) :error 0))))
                   ((eq operation :digest)
                    (setf (fnn-pull-flight-spool-op flight) nil)
                    (fnn-pull-flight-hash-read flight status actual))
                   (t (finish (fnn-pull-flight-spool-event flight operation status actual)))))
               :progress))))
          (t (fnn-fault "unknown catch-up spool phase ~s" phase)))))))

(defun fnn-pull-flight-hash-lease (flight)
  (let ((lease (fnn-pull-flight-lease flight)))
    (fnn-core 'fn-csp-hash-lease (fnn-peer-flight-lease-slot lease)
              (fnn-peer-flight-lease-generation lease))))

(defun fnn-pull-flight-hash-read (flight status actual)
  (let ((worker (fnn-pull-flight-worker flight)))
    (destructuring-bind (word hash)
        (fnn-call 'fn-csp-hash-read (fnn-pull-flight-hash-total flight)
                  (fnn-pull-flight-hash-lease flight) status actual
                  (fnn-csp-worker-digest-input worker) (fnn-pull-flight-hash flight))
      (setf (fnn-pull-flight-hash flight) hash)
      (when (eq word :refused)
        (fnn-pull-flight-set-io flight nil)
        (fnn-pull-flight-event flight (list :digest nil))))))

(defun fnn-pull-flight-hash-step (flight)
  "One quantum of the ACL2 digest cursor over the immutable spool (io :hash)."
  (if (fnn-pull-flight-spool-op flight)
      (fnn-pull-flight-spool-step flight)
    (let* ((total (fnn-pull-flight-hash-total flight))
           (lease (fnn-pull-flight-hash-lease flight))
           (action (fnn-core 'fn-csp-hash-action total (fnn-pull-flight-hash-base flight)
                             lease (fnn-pull-flight-hash flight))))
      (case (first action)
        (:done (fnn-pull-flight-set-io flight nil)
               (fnn-pull-flight-event flight (list :digest (second action))))
        (:read
         (fnn-pull-flight-spool-begin flight :digest (second action) (third action))
         (fnn-pull-flight-spool-step flight))
        (:tick
         (if (fnn-peer-flight-work (fnn-pull-flight-lease flight)
                                   (fnn-core 'fn-csp-io-work-units :tick 0))
             (destructuring-bind (word hash)
                 (fnn-call 'fn-csp-hash-tick total lease (fnn-pull-flight-hash flight))
               (setf (fnn-pull-flight-hash flight) hash)
               (when (eq word :refused)
                 (fnn-pull-flight-set-io flight nil)
                 (fnn-pull-flight-event flight (list :digest nil))))
           (progn (fnn-pull-flight-set-io flight nil)
                  (fnn-pull-flight-event flight (list :work-refused)))))
        (t (fnn-pull-flight-set-io flight nil)
           (fnn-pull-flight-event flight (list :digest nil))))
      :progress)))

(defun fnn-pull-flight-effect (flight effect)
  (case (car effect)
    (:journal (fnn-pull-journal-append (fnn-pull-flight-journal flight) (cdr effect)
                                     (fnn-pull-flight-kind flight)))
    (:dial
     (multiple-value-bind (socket word)
         (fnn-peer-connect-start (fnn-core 'fn-pull-plan-host (fnn-pull-flight-plan flight))
                                 (fnn-core 'fn-pull-plan-port (fnn-pull-flight-plan flight)))
       (fnn-pull-flight-set-socket flight socket)
       (setf (fnn-pull-flight-fd flight) (fnn-socket-fd socket))
       (unless (eq word :connected) (fnn-pull-flight-set-io flight :dial t))))
    (:tls
     (unless (fnn-pull-flight-fd flight)
       (fnn-pull-flight-event flight (list :lost :dial))
       (return-from fnn-pull-flight-effect nil))
     (let ((verification (fnn-core 'fn-peer-tls-verification (second effect) (third effect))))
       (unless (eq (first verification) :verify)
         (error 'fnn-peer-dial-error :outcome (if (eq (second verification) :trust)
                                                :trust :server-name)))
       (setf (fnn-pull-flight-context flight) (fnn-tls-open-client-context (fourth verification))
             (fnn-pull-flight-tls-name flight) (second verification)
             (fnn-pull-flight-channel flight)
             (fnn-tls-client-begin (fnn-pull-flight-context flight) (fnn-pull-flight-fd flight)
                                   (second verification) :sni (third verification)))
       (fnn-pull-flight-set-io flight :tls t)))
    (:remote
     (setf (fnn-pull-flight-data flight) (fnn-octets (cdr effect))
           (fnn-pull-flight-offset flight) 0
           (fnn-pull-flight-end flight) nil)
     (unless (zerop (length (fnn-pull-flight-data flight)))
       (fnn-pull-flight-set-io flight :send t)))
    (:open-local (fnn-pull-flight-local-open flight))
    (:reopen-local (fnn-pull-flight-close-local flight) (fnn-pull-flight-local-open flight))
    (:local
     (setf (fnn-pull-flight-input flight) (fnn-octets (cdr effect))
           (fnn-pull-flight-parts flight) nil
           (fnn-pull-flight-closing flight) nil
           (fnn-pull-flight-resume-at flight) nil)
     (fnn-pull-flight-set-io flight :local))
    (:close nil)
    (:spool-write
     (fnn-pull-flight-ensure-worker flight)
     (fnn-pull-flight-spool-begin flight :write (second effect) (length (third effect))
                                  (third effect))
     (fnn-pull-flight-set-io flight :spool))
    (:spool-read
     (fnn-pull-flight-ensure-worker flight)
     (fnn-pull-flight-spool-begin flight :replay (second effect) (third effect))
     (fnn-pull-flight-set-io flight :spool))
    (:spool-hash
     (fnn-pull-flight-ensure-worker flight)
     (let ((hash (or (fnn-pull-flight-hash flight) (create-pgs-digest-state))))
       (setf (fnn-pull-flight-hash-total flight) (third effect)
             (fnn-pull-flight-hash-base flight) (second effect)
             (fnn-pull-flight-hash flight)
             (first (fnn-call 'fn-csp-hash-begin (third effect)
                              (fnn-pull-flight-hash-lease flight) hash))))
     (fnn-pull-flight-set-io flight :hash))
    (t (fnn-fault "unknown pull effect ~s" (car effect)))))

(defun fnn-pull-flight-local-step (flight)
  "One local cold/commit/render/input quantum; no page or completion waits."
  (let ((service (fnn-pull-flight-service flight)) (cid (fnn-pull-flight-cid flight))
        (now (fnn-pull-monotonic)))
    (when (and (fnn-pull-flight-resume-at flight)
               (< now (fnn-pull-flight-resume-at flight)))
      (return-from fnn-pull-flight-local-step :wait))
    (setf (fnn-pull-flight-resume-at flight) nil)
    (cond
      ((fnn-pull-flight-cold flight)
       (destructuring-bind (read line-since since &optional kind) (fnn-pull-flight-cold flight)
         (multiple-value-bind (word since at limit)
             (fnn-owner-cold-poll service read line-since since)
           (cond
             ((consp word)
              (when (eq kind :cursor)
                (setf (fnn-pull-flight-resume-at flight)
                      (fnn-core 'fn-prd-resume-at now (second word)))))
             ((eq kind :cursor)
              ;; A rendered response resumes its exact plan, never the input
              ;; decoder. Keep the read for cleanup if polling refuses/faults.
              (unless (eq word :serve)
                (error 'fnn-store-io-refusal
                       :message (format nil "pull cursor: payload read ~(~a~); the reply is terminated" word)))
              (setf (fnn-pull-flight-cold flight) nil))
             (t
              (setf (fnn-pull-flight-cold flight) nil
                    (fnn-pull-flight-cold-word flight)
                    (list word since at limit (or line-since since))))))))
      ((fnn-pull-flight-await flight)
       (let ((completion nil))
         (sb-thread:with-mutex ((fnn-pull-runtime-lock (fnn-pull-flight-runtime flight)))
           (setq completion (fnn-pull-flight-completion flight))
           (setf (fnn-pull-flight-completion flight) nil))
         (unless completion (return-from fnn-pull-flight-local-step :wait))
         (destructuring-bind (step redeem) (fnn-pull-flight-await flight)
           (sb-thread:with-mutex ((fnn-pull-runtime-lock (fnn-pull-flight-runtime flight)))
             (setf (fnn-pull-flight-await flight) nil))
           (let ((value (car completion)))
             (if (eq value :uncertain)
                 (setf (fnn-pull-flight-closing flight) t)
               (let ((closing (and (consp value) (eq (car value) :close))))
                 (when closing (setf (fnn-pull-flight-closing flight) t))
                 (setf (fnn-pull-flight-render flight)
                       (fnn-core 'fn-splan-step-plan step (if closing (cdr value) value) redeem))))))))
      ((fnn-pull-flight-render flight)
       (multiple-value-bind (part rest done yielded cold-read)
           (fnn-owner-render-next-quantum service cid (fnn-pull-flight-render flight) :transit)
         (setf (fnn-pull-flight-render flight) (unless done rest))
         (if cold-read
             (progn
               (unless (fnn-pull-flight-cursor-cold-since flight)
                 (setf (fnn-pull-flight-cursor-cold-since flight) now))
               (setf (fnn-pull-flight-cold flight)
                     (list cold-read (fnn-pull-flight-cursor-cold-since flight) now :cursor)))
           (push part (fnn-pull-flight-parts flight)))
         (when (and (not done) yielded)
           (setf (fnn-pull-flight-resume-at flight)
                 (fnn-core 'fn-prd-resume-at now (fnn-core 'fn-splan-cursor-resume-ms))))
         (when done
           (setf (fnn-pull-flight-cursor-cold-since flight) nil)
           (fnn-owner-response-unpin service cid))))
      ((or (fnn-pull-flight-closing flight)
           (zerop (length (fnn-pull-flight-input flight))))
       (let ((reply (fnn-owner-join-octets (nreverse (fnn-pull-flight-parts flight)))))
         (cond ((> (length reply) 0)
                (fnn-pull-flight-event flight (cons :local (fnn-octet-list reply))))
               ;; A catch-up body window the local node took without a reply:
               ;; the controller's next window may follow.
               ((and (eq (fnn-pull-flight-kind flight) :catch-up)
                     (not (fnn-pull-flight-closing flight)))
                (fnn-pull-flight-event flight (list :local-window)))))
       (when (fnn-pull-flight-closing flight)
         (fnn-pull-flight-close-local flight)
         (fnn-pull-flight-event flight (list :lost :local)))
       (fnn-pull-flight-set-io flight nil))
      (t
       (let* ((input (fnn-pull-flight-input flight))
              (word (fnn-pull-flight-cold-word flight))
              (results (multiple-value-list
                        (destructuring-bind (&optional w since at limit line-since) word
                          (fnn-owner-handle-chunk-step service cid input nil
                                                      (fnn-owner-peer-read-class service) t
                                                      w line-since since at limit)))))
         (setf (fnn-pull-flight-cold-word flight) nil)
         (case (first results)
           (:cold (setf (fnn-pull-flight-cold flight)
                        (list (second results) (fifth word) now)))
           (:defer (setf (fnn-pull-flight-resume-at flight)
                         (fnn-core 'fn-prd-resume-at now (second results))))
           (t
            (let* ((await (eq (first results) :await))
                   (used (if await (sixth results) (fourth results)))
                   (closing (if await (fourth results) (second results))))
              (unless (and (integerp used) (<= 0 used (length input))
                           (or (plusp used) closing))
                (fnn-fault "owner consumed no octets of a pull transit write"))
              (setf (fnn-pull-flight-input flight) (subseq input used)
                    (fnn-pull-flight-closing flight) closing)
              (if await
                  (progn
                    (sb-thread:with-mutex ((fnn-pull-runtime-lock (fnn-pull-flight-runtime flight)))
                      (setf (fnn-pull-flight-await flight) (list (second results) (third results))))
                    (let* ((marker (fnn-pull-flight-await flight))
                           (early
                            (fnn-owner-await-register
                             service cid
                             (lambda (completion)
                               (sb-thread:with-mutex
                                   ((fnn-pull-runtime-lock (fnn-pull-flight-runtime flight)))
                                 (when (and (not (fnn-pull-flight-closed flight))
                                            (eq marker (fnn-pull-flight-await flight)))
                                   (setf (fnn-pull-flight-completion flight) (list completion)))))
                             nil)))
                      (when early
                        (sb-thread:with-mutex ((fnn-pull-runtime-lock (fnn-pull-flight-runtime flight)))
                          (setf (fnn-pull-flight-completion flight) (list early))))))
                (progn
                  (setf (fnn-pull-flight-render flight) (first results))
                  (unless (first results) (fnn-owner-response-unpin service cid))))))))))))

(defun fnn-pull-flight-try (flight action stage)
  (handler-case (funcall action)
    (serious-condition (condition)
      (unless (fnn-core 'fn-prd-loss-class-ok stage (fnn-condition-class condition))
        (error condition))
      (when (eq stage :dial)
        (fnn-peer-dial-report :pull (fnn-pull-flight-peer flight)
                              (fnn-core 'fn-pull-plan-host (fnn-pull-flight-plan flight)) condition))
      (fnn-pull-flight-set-io flight nil)
      (setf (fnn-pull-flight-effects flight) nil (fnn-pull-flight-events flight) nil)
      (fnn-pull-flight-advance flight (list :lost stage)))))

(defun fnn-pull-flight-read (flight)
  (unless (fnn-pull-flight-fd flight)
    (fnn-pull-flight-event flight (list :lost :dial))
    (return-from fnn-pull-flight-read nil))
  (let* ((limit (fnn-core 'fn-prd-read-limit
                          (fnn-core (if (eq (fnn-pull-flight-kind flight) :catch-up)
                                        'fn-csp-read-limit 'fn-pull-session-read-limit)
                                    (fnn-pull-flight-session flight))))
         (incoming (if (fnn-pull-flight-channel flight)
                       (fnn-tls-read-now (fnn-pull-flight-channel flight) limit)
                     (fnn-socket-read-now (fnn-pull-flight-fd flight) limit))))
    (if (member incoming '(:wait :input :output))
        :wait
      (fnn-pull-flight-event flight (if (zerop (length incoming)) (list :lost :eof)
                                     (cons :remote (fnn-octet-list incoming)))))))

(defun fnn-pull-flight-io-step (flight)
  (case (fnn-pull-flight-io flight)
    (:dial (when (eq (fnn-connect-poll (fnn-pull-flight-socket flight)) :connected)
             (fnn-pull-flight-set-io flight nil)))
    (:tls (when (eq (fnn-tls-client-step (fnn-pull-flight-channel flight)
                                       (fnn-pull-flight-tls-name flight)) :connected)
            (fnn-pull-flight-set-io flight nil)
            (fnn-pull-flight-event flight (list :tls-up))))
    (:send
     (let* ((data (fnn-pull-flight-data flight)) (offset (fnn-pull-flight-offset flight))
            (end (or (fnn-pull-flight-end flight)
                     (setf (fnn-pull-flight-end flight)
                           (fnn-core 'fn-prd-write-end offset (length data)))))
            (written (if (fnn-pull-flight-channel flight)
                         (fnn-tls-write-now-range (fnn-pull-flight-channel flight) data offset end)
                       (fnn-socket-write-now (fnn-pull-flight-fd flight) data offset end))))
       (when (integerp written)
         (incf (fnn-pull-flight-offset flight) written)
         (when (= (fnn-pull-flight-offset flight) end)
           (setf (fnn-pull-flight-end flight) nil))
         (when (= (fnn-pull-flight-offset flight) (length data))
           (setf (fnn-pull-flight-data flight) nil)
           (fnn-pull-flight-set-io flight nil)))))
    (:local (fnn-pull-flight-local-step flight))
    (:spool (fnn-pull-flight-spool-step flight))
    (:hash (fnn-pull-flight-hash-step flight))
    (t (fnn-fault "unknown pull continuation"))))

(defun fnn-pull-flight-step (flight)
  "One driver action: :finished, :progress (state advanced without waiting on
a peer or the local node), or :wait.  Local, dial, TLS and send continuations
are always :wait here, so a selection never spins on them."
  (let* ((catchup (eq (fnn-pull-flight-kind flight) :catch-up))
         (action (fnn-core 'fn-prd-action
                           (fnn-core (if catchup 'fn-csp-done-p 'fn-pull-session-done-p)
                                     (fnn-pull-flight-session flight))
                           (fnn-pull-flight-effects flight) (fnn-pull-flight-events flight)
                           (fnn-pull-flight-io flight) (fnn-pull-monotonic)
                           (fnn-pull-flight-deadline flight)
                           (fnn-pull-flight-round-deadline flight))))
    (case (car action)
      (:lost (fnn-pull-flight-set-io flight nil)
             (setf (fnn-pull-flight-effects flight) nil (fnn-pull-flight-events flight) nil)
             (fnn-pull-flight-advance flight action)
             :progress)
      (:io (let ((r (fnn-pull-flight-try flight (lambda () (fnn-pull-flight-io-step flight))
                                         (second action))))
             (if (and (member (second action) '(:spool :hash)) (eq r :progress)) :progress :wait)))
      (:effect
       (pop (fnn-pull-flight-effects flight))
       (fnn-pull-flight-try flight
                            (lambda () (fnn-pull-flight-effect flight (second action)))
                            (case (car (second action))
                              ((:local :open-local :reopen-local) :local)
                              (:remote :send) (t (car (second action)))))
       :progress)
      (:event (pop (fnn-pull-flight-events flight))
              (fnn-pull-flight-advance flight (second action))
              :progress)
      (:read
       (if (and catchup (fnn-core 'fn-csp-tick-p (fnn-pull-flight-session flight)))
           ;; The controller has retained input or a spool step of its own:
           ;; one bounded quantum before any further peer read.
           (progn (fnn-pull-flight-advance flight (list :tick)) :progress)
         (if (eq (fnn-pull-flight-try flight (lambda () (fnn-pull-flight-read flight)) :read)
                 :wait)
             :wait :progress)))
      (:finish :finished)
      (t (fnn-fault "unknown ACL2 pull driver action")))))

(defun fnn-pull-flight-quantum (flight)
  "Run FLIGHT for at most ACL2's per-selection quantum of actions, while they
progress; answer :finished, :progress or :wait (the last action's)."
  (let ((result :wait))
    (loop repeat (fnn-core 'fn-prd-flight-quantum)
          do (setq result (fnn-pull-flight-step flight))
          until (member result '(:finished :wait)))
    result))

;;; Catch-up custody: the bank lease settles only after the actual worker
;;; thread is dead with a clean cleanup, the socket is shut and the local
;;; transit connection is closed (fnn-pull-flight-dispose).  A worker still
;;; running is stopped and parked in the runtime's SETTLING list; a reported
;;; cleanup failure keeps the lease held, so the bank never reads as drained.
(defun fnn-pull-flight-release-lease (flight)
  (let ((lease (fnn-pull-flight-lease flight)))
    (when lease
      (setf (fnn-pull-flight-lease flight) nil
            (fnn-peer-flight-lease-socket lease) t
            (fnn-peer-flight-lease-semantic lease) t)
      (let ((worker (fnn-pull-flight-worker flight)))
        (setf (fnn-pull-flight-worker flight) nil (fnn-pull-flight-hash flight) nil)
        (if worker
            (let ((runtime (fnn-pull-flight-runtime flight)))
              (fnn-csp-worker-stop worker)
              (push lease (fnn-pull-runtime-settling runtime)))
          (progn (setf (fnn-peer-flight-lease-physical lease) t)
                 (fnn-peer-flight-settle lease)))))))

(defun fnn-pull-settle-leases (runtime &optional wait)
  "Settle parked leases whose worker has been joined; WAIT joins them all."
  (loop
    (let ((pending nil))
      (dolist (lease (copy-list (fnn-pull-runtime-settling runtime)))
        (multiple-value-bind (joined condition)
            (fnn-csp-worker-join-now (fnn-peer-flight-lease-worker lease))
          (cond ((not joined) (setq pending t))
                (t (setf (fnn-pull-runtime-settling runtime)
                         (remove lease (fnn-pull-runtime-settling runtime)))
                   (if condition
                       (setf (fnn-peer-flight-lease-fault lease) condition)
                     (progn (setf (fnn-peer-flight-lease-physical lease) t)
                            (fnn-peer-flight-settle lease)))))))
      (unless (and wait pending) (return))
      (sleep (/ (fnn-core 'fn-prd-idle-ms) 1000)))))

(defun fnn-pull-flight-finish (flight)
  (let* ((runtime (fnn-pull-flight-runtime flight))
         (catchup (eq (fnn-pull-flight-kind flight) :catch-up))
         (session (fnn-pull-flight-session flight)))
    (fnn-pull-flight-dispose flight)
    (if catchup
        (fnn-pull-flight-release-lease flight)
      (dolist (effect (fnn-core 'fn-pull-session-close-effects session))
        (fnn-pull-flight-effect flight effect)))
    (fnn-log-line (if catchup (fnn-core 'fn-csp-log-line session)
                   (fnn-core 'fn-pull-session-log-line-why session (fnn-pull-flight-why flight))))
    (let ((closed (fnn-core (if catchup 'fn-csp-close 'fn-pull-session-close) session))
          (key (fnn-pull-peer-string (fnn-pull-flight-peer flight))))
      (setf (cdr (assoc key (if catchup (fnn-pull-runtime-cu-cursors runtime)
                             (fnn-pull-runtime-cursors runtime)) :test #'string=)) closed))
    (if catchup
        (setf (fnn-pull-runtime-cu-schedule runtime)
              (fnn-core 'fn-sched-pull-finish (fnn-pull-flight-peer flight) (fnn-pull-monotonic)
                        (fnn-pull-runtime-cu-schedule runtime)))
      (setf (fnn-pull-runtime-schedule runtime)
            (fnn-core 'fn-sched-pull-finish (fnn-pull-flight-peer flight) (fnn-pull-monotonic)
                      (fnn-pull-runtime-schedule runtime))))))

(defun fnn-pull-admit-flight (runtime plans kind)
  (let* ((catchup (eq kind :catch-up)) (now (fnn-pull-monotonic))
         (schedule (fnn-core 'fn-pull-schedule plans now
                             (if catchup (fnn-pull-runtime-cu-schedule runtime)
                               (fnn-pull-runtime-schedule runtime))))
         (peer (fnn-core 'fn-sched-pull-due schedule now)))
    (when peer
      (setq schedule (fnn-core 'fn-sched-pull-start peer schedule))
      (let ((plan (fnn-core 'fn-pull-plan-for peer plans)))
        (multiple-value-bind (journal cursor)
            (if catchup (fnn-catchup-cursor-for runtime plan) (fnn-pull-cursor-for runtime plan))
          (let ((flight (fnn-pull-flight-begin runtime plan journal cursor kind)))
            (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
              (setf (fnn-pull-runtime-flights runtime)
                    (append (fnn-pull-runtime-flights runtime) (list flight))))))))
    (if catchup (setf (fnn-pull-runtime-cu-schedule runtime) schedule)
      (setf (fnn-pull-runtime-schedule runtime) schedule))))

(defun fnn-pull-retire-flights (runtime plans kind)
  (dolist (flight (copy-list (fnn-pull-runtime-flights runtime)))
    (when (and (eq kind (fnn-pull-flight-kind flight))
               (not (fnn-core 'fn-pull-plan-for (fnn-pull-flight-peer flight) plans)))
      ;; A removed peer's unfinished session closes through its existing
      ;; cursor machine before the cached journal descriptor is retired.
      (fnn-pull-flight-advance flight (list :lost :local))
      (fnn-pull-flight-finish flight)
      (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
        (setf (fnn-pull-runtime-flights runtime)
              (remove flight (fnn-pull-runtime-flights runtime)))))))

(defun fnn-pull-worker (runtime)
  (let ((service (fnn-pull-runtime-service runtime)) (remaining nil) (primary nil)
        (progressed nil))
    (handler-bind ((serious-condition (lambda (condition) (unless primary (setq primary condition)))))
    (unwind-protect
         (loop until (fnn-pull-stoppingp runtime) do
           (let ((plans (fnn-owner-transit-serialized
                         service nil (lambda () (fnn-owner-core 'fn-owner-pull-plans))))
                 (cu-plans (fnn-owner-transit-serialized
                            service nil (lambda () (fnn-owner-core 'fn-owner-catchup-plans)))))
             (fnn-pull-retire-flights runtime plans :pull)
             (fnn-pull-retire-flights runtime cu-plans :catch-up)
             (fnn-pull-prune-journals runtime plans)
             (fnn-pull-prune-journals runtime cu-plans :catch-up)
             (fnn-pull-admit-flight runtime plans :pull)
             (fnn-pull-admit-flight runtime cu-plans :catch-up))
           (let* ((active (mapcar #'fnn-pull-flight-key (fnn-pull-runtime-flights runtime)))
                  ;; The host calls the keystone's actual subject. Removed
                  ;; keys drop out; newcomers join only after this sweep.
                  (sweep (fnn-core 'fn-prd-sweep active (or remaining active)))
                  (selected (fnn-core 'fn-prd-select active sweep))
                  (flight (find (first selected) (fnn-pull-runtime-flights runtime)
                                :key #'fnn-pull-flight-key :test #'equal)))
             (setq remaining (second selected))
             (when flight
               (let ((result (fnn-pull-flight-quantum flight)))
                 (unless (eq result :wait) (setq progressed t))
                 (when (eq result :finished)
                   (fnn-pull-flight-finish flight)
                   (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
                     (setf (fnn-pull-runtime-flights runtime)
                           (remove flight (fnn-pull-runtime-flights runtime)))))))
             (fnn-pull-settle-leases runtime)
             ;; One scheduling pause per sweep in which no round progressed,
             ;; not per peer. It limits polling work without truncating input
             ;; or ending any round.
             (unless remaining
               (unless progressed (sleep (/ (fnn-core 'fn-prd-idle-ms) 1000)))
               (setq progressed nil))))
      (let ((failure nil))
        (setf (fnn-pull-runtime-cleanup-stage runtime) :calling)
        (flet ((release (thunk)
                 (handler-case (funcall thunk)
                   (serious-condition (condition) (unless failure (setq failure condition))))))
          (dolist (flight (fnn-pull-runtime-flights runtime))
            (release (lambda () (fnn-pull-flight-dispose flight)
                       (fnn-pull-flight-release-lease flight))))
          (release (lambda () (fnn-pull-settle-leases runtime t)))
          (dolist (entry (append (fnn-pull-runtime-journals runtime)
                                (fnn-pull-runtime-cu-journals runtime)))
            (release (lambda () (fnn-owner-feed-close (cdr entry))))))
        (when failure (setf (fnn-pull-runtime-cleanup-debt runtime) failure))
        (setf (fnn-pull-runtime-cleanup-stage runtime) :returned)
        (when (and failure (null primary)) (error failure)))))))

(defun fnn-pull-worker-guarded (runtime)
  (handler-case (fnn-pull-worker runtime)
    (serious-condition (e)
      ;; Stopping does not erase a late store fault or uncertain outcome.
      (fnn-owner-thread-escape (fnn-pull-runtime-service runtime) e "pull feed"))))

(def-actor fnn-pull-spawn :thread-name "fn pull feed" :roster t)

(defun fnn-pull-service-start (service)
  ;; Publish the runtime before spawn; only one start owns its reservation.
  ;; Do not hold the table or runtime mutex across actor creation/cleanup.
  (let ((runtime
          (sb-thread:with-mutex (*fnn-pull-runtime-lock*)
            (unless (gethash service *fnn-pull-runtimes*)
              (setf (gethash service *fnn-pull-runtimes*)
                    (%make-fnn-pull-runtime
                     :service service
                     :lock (sb-thread:make-mutex :name "fn pull runtime")))))))
    (when runtime
      (handler-case
          (setf (fnn-pull-runtime-worker runtime)
                (fnn-pull-spawn
                 service (list runtime) (lambda () (fnn-pull-worker runtime))
                 (lambda (condition) (fnn-owner-thread-escape service condition "pull feed"))))
        (serious-condition (condition)
          ;; A post-create starter escape may leave a parked/live child.
          ;; Its registration retains RUNTIME independently of this slot.
          (let ((actor (fnn-owner-actor-for-custody service runtime)))
            (if actor
                (setf (fnn-pull-runtime-worker runtime) (fnn-owner-actor-thread actor))
              ;; No reservation remains: either no child existed or the
              ;; starter physically terminated it before its body ran.
              (unless (or (fnn-pull-runtime-cleanup-debt runtime)
                          (eq (fnn-pull-runtime-cleanup-stage runtime) :calling))
                (sb-thread:with-mutex (*fnn-pull-runtime-lock*)
                  (when (eq (gethash service *fnn-pull-runtimes*) runtime)
                    (remhash service *fnn-pull-runtimes*))))))
          (error condition)))))
  nil)

(defun fnn-pull-service-wake (service)
  (let ((runtime (fnn-pull-runtime-get service)))
    (when runtime
      (sb-thread:with-mutex ((fnn-pull-runtime-lock runtime))
        (setf (fnn-pull-runtime-stopping runtime) t)
        (dolist (socket (cons (fnn-pull-runtime-socket runtime)
                             (mapcar #'fnn-pull-flight-socket
                                     (fnn-pull-runtime-flights runtime))))
          (when socket (ignore-errors (fnn-socket-shutdown socket)))))))
  nil)

(defun fnn-pull-service-close (service)
  (let ((runtime (fnn-pull-runtime-get service)))
    (when runtime
      (fnn-pull-service-wake service)
      (let ((worker (fnn-pull-runtime-worker runtime)))
        (when (and worker (not (fnn-owner-actor-join service worker)))
          (fnn-fault "pull worker remains physically live during close")))
      (when (fnn-pull-runtime-cleanup-debt runtime)
        (error (fnn-pull-runtime-cleanup-debt runtime)))
      (when (eq (fnn-pull-runtime-cleanup-stage runtime) :calling)
        (fnn-fault "pull terminal cleanup escaped without a receipt"))
      (sb-thread:with-mutex (*fnn-pull-runtime-lock*)
        (when (eq (gethash service *fnn-pull-runtimes*) runtime)
          (remhash service *fnn-pull-runtimes*)))))
  nil)
