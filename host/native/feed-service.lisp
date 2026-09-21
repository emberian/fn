;;; host/native/feed-service.lisp -- outbound NNTP feed socket adapter.
;;;
;;; This is deliberately smaller than an NNTP client.  ACL2 owns the peer
;;; endpoint projection, backoff number, reply framing and every delivery
;;; decision.  This file owns only socket lifetime, monotonic observations and
;;; worker scheduling.  In particular it does not scan CRLF, parse reply
;;; codes, render commands, or decide whether an article is deliverable.
;;;
;;; Each completed owner transition is serialized with the Store and FNFD
;;; journaled before its copied command bytes leave the mutex.  A socket read
;;; that contains two lines is drained through FN-OWNER-FEED-REPLY-CHUNK one
;;; event at a time, so a later reply cannot overwrite an unpersisted effect.

(in-package "ACL2")

(eval-when (:load-toplevel :execute)
  (unless (fboundp 'fnn-core)
    (load "host/native/io.lisp")))

(defconstant +fnn-feed-poll-seconds+ 1/20)

(defstruct (fnn-feed-link (:constructor %make-fnn-feed-link))
  peer peer-octets socket fd (ready nil) (next-dial 0))

(defstruct (fnn-feed-runtime (:constructor %make-fnn-feed-runtime))
  service links lock worker (stopping nil) limit)

;;; The owner lifecycle extension hooks carry only SERVICE.  Keep the raw
;;; socket registry private to this module rather than widening the logical
;;; service or introducing a second owner.  Access is short and never covers
;;; a syscall or an ACL2 call.
(defparameter *fnn-feed-runtime-lock*
  (sb-thread:make-mutex :name "fn outbound feed runtimes"))
(defparameter *fnn-feed-runtimes* (make-hash-table :test #'eq))

(defun fnn-feed-now ()
  "One monotonic observation, in the ACL2 feed port's milliseconds."
  (floor (* 1000 (get-internal-real-time)) internal-time-units-per-second))

(defun fnn-feed-runtime-get (service)
  (sb-thread:with-mutex (*fnn-feed-runtime-lock*)
    (gethash service *fnn-feed-runtimes*)))

(defun fnn-feed-runtime-put (service runtime)
  (sb-thread:with-mutex (*fnn-feed-runtime-lock*)
    (setf (gethash service *fnn-feed-runtimes*) runtime))
  runtime)

(defun fnn-feed-runtime-drop (service)
  (sb-thread:with-mutex (*fnn-feed-runtime-lock*)
    (remhash service *fnn-feed-runtimes*))
  nil)

(defun fnn-feed-stoppingp (runtime)
  (sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))
    (fnn-feed-runtime-stopping runtime)))

(defun fnn-feed-links (runtime)
  (sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))
    (copy-list (fnn-feed-runtime-links runtime))))

(defun fnn-feed-checked-word (word allowed where)
  (unless (member word allowed)
    (fnn-fault "feed core returned ~s from ~a" word where))
  word)

(defun fnn-feed-octets (value where)
  (unless (fnn-octet-list-p value)
    (fnn-fault "feed core returned non-octets for ~a" where))
  (fnn-octets value))

(defun fnn-feed-peer-list (service)
  (fnn-owner-serialized
   service nil
   (lambda ()
     (fnn-owner-name-list (fnn-owner-core 'fn-owner-feed-peers)))))

(defun fnn-feed-read-limit (service)
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((limit (fnn-owner-core 'fn-owner-feed-read-limit)))
       (unless (and (integerp limit) (<= 0 limit)
                    (<= limit +fnn-max-read+))
         (fnn-fault "invalid ACL2 feed reply limit: ~s" limit))
       limit))))

(defun fnn-feed-dial-plan (service peer-octets)
  "Read only ACL2's endpoint, queue and configured reconnect delay."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((queued (fnn-owner-core 'fn-owner-feed-has-queued peer-octets))
           (host (fnn-owner-core 'fn-owner-feed-host peer-octets))
           (port (fnn-owner-core 'fn-owner-feed-port peer-octets))
           (backoff (fnn-owner-core 'fn-owner-feed-backoff-ms peer-octets)))
       (unless (member queued '(t nil))
         (fnn-fault "feed core returned malformed queued predicate"))
       (unless (fnn-octet-list-p host)
         (fnn-fault "feed core returned malformed peer host"))
       (unless (and (integerp port) (<= 1 port 65535))
         (fnn-fault "feed core returned malformed peer port"))
       (unless (and (integerp backoff) (>= backoff 0))
         (fnn-fault "feed core returned malformed peer backoff"))
       (values queued (fnn-octets-string (fnn-octets host)) port backoff)))))

(defun fnn-feed-connect-core (service link)
  "Start ACL2's greeting/MODE phase; this does not make a feed live."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (fnn-feed-checked-word
      (fnn-owner-action 'fn-owner-feed-dial-open
                        (fnn-feed-link-peer-octets link)
                        (fnn-feed-link-fd link))
      '(:await-greeting) 'fn-owner-feed-dial-open))))

(defun fnn-feed-copy-command (service word)
  "Persist the current FNFD batch while serialized, then copy its bytes.

WORD is returned by a port wrapper which has just installed the matching
records/effects projection.  No caller can write the returned bytes until
this function's durable append has completed."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (fnn-owner-feed-flush service)
     (values word
             (if (member word '(:offer :send))
                 (let ((command (fnn-owner-octets-global 'fn-owner-feed-command)))
                   (when (zerop (length command))
                     (fnn-fault "feed core authorized an empty command"))
                   command)
               (fnn-make-octets 0))))))

(defun fnn-feed-tick (service link now)
  "One ACL2 tick.  Its command, if any, is copied only after FNFD append."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((word (fnn-feed-checked-word
                  (fnn-owner-action 'fn-owner-feed-tick
                                    (fnn-feed-link-peer-octets link) now)
                  '(:offer :idle :refused) 'fn-owner-feed-tick)))
       (fnn-owner-feed-flush service)
       (values word
               (if (eq word :offer)
                   (let ((command (fnn-owner-octets-global 'fn-owner-feed-command)))
                     (when (zerop (length command))
                       (fnn-fault "feed tick authorized an empty command"))
                     command)
                 (fnn-make-octets 0)))))))

(defun fnn-feed-reply-step (service link octets now)
  "Apply one ACL2-framed reply event, never a host-parsed line."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((word (fnn-feed-checked-word
                  (fnn-owner-action 'fn-owner-feed-reply-chunk
                                    (fnn-feed-link-peer-octets link)
                                    (fnn-octet-list octets) now)
                  '(:mode :ready :send :quiet :refused :need-input :closed :invalid :fault)
                  'fn-owner-feed-reply-chunk)))
       (when (eq word :fault)
         (fnn-fault "feed reply framer state is malformed"))
       ;; Only a complete post-ready :line reaches the feed port and replaces
       ;; its FNFD projection.  MODE is a connection-phase command, not a
       ;; delivery effect, and :ready has no socket bytes.
       (when (member word '(:send :quiet :refused))
         (fnn-owner-feed-flush service))
       (values word
               (if (member word '(:mode :send))
                   (let ((command (fnn-owner-octets-global 'fn-owner-feed-command)))
                     (when (zerop (length command))
                       (fnn-fault "feed connection/reply authorized an empty command"))
                     command)
                 (fnn-make-octets 0)))))))

(defun fnn-feed-lost (service link now)
  "Record one peer-local loss before closing or retrying its socket."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((word (fnn-feed-checked-word
                  (fnn-owner-action 'fn-owner-feed-lost
                                    (fnn-feed-link-peer-octets link) now)
                  '(:ok :refused) 'fn-owner-feed-lost)))
       (fnn-owner-feed-flush service)
       word))))

(defun fnn-feed-close-link (link)
  (let ((socket (fnn-feed-link-socket link)))
    (when socket
      (setf (fnn-feed-link-socket link) nil
            (fnn-feed-link-fd link) nil
            (fnn-feed-link-ready link) nil)
      (ignore-errors (fnn-socket-shut socket)))))

(defun fnn-feed-drop-link (runtime link now backoff)
  "A peer socket failed.  The core records the loss before the next retry."
  ;; A failed dial is still a named loss: it advances the ACL2-owned retry
  ;; state even though no descriptor was established to close.
  (fnn-feed-lost (fnn-feed-runtime-service runtime) link now)
  (fnn-feed-close-link link)
  (setf (fnn-feed-link-next-dial link) (+ now backoff)))

(defun fnn-feed-dial (runtime link now)
  "Dial an ACL2-projected endpoint when its core queue and delay allow it.

DNS resolution and connect(2) retain FNN-CONNECT's separately documented
availability limit; after an established socket is made nonblocking, all
read/write waits use the bounded FNN-RECV/FNN-SEND-ALL contract."
  (when (and (null (fnn-feed-link-socket link))
             (<= (fnn-feed-link-next-dial link) now))
    (multiple-value-bind (queued host port backoff)
        (fnn-feed-dial-plan (fnn-feed-runtime-service runtime)
                            (fnn-feed-link-peer-octets link))
      (when queued
        (handler-case
            (let ((socket (fnn-connect host port)))
              (setf (fnn-feed-link-socket link) socket
                    (fnn-feed-link-fd link) (fnn-socket-fd socket)
                    (fnn-feed-link-ready link) nil)
              (fnn-feed-connect-core (fnn-feed-runtime-service runtime) link))
          ((or fnn-os-error sb-bsd-sockets:socket-error) ()
            ;; A failed open has no outgoing bytes, but it is still the
            ;; named peer-loss observation that advances the ACL2 backoff.
            (fnn-feed-drop-link runtime link now backoff)))))))

(defun fnn-feed-consume (runtime link octets eofp now)
  "Drain a received chunk through one ACL2 event at a time.

NIL means ``drain retained suffix'' after the first iteration.  EOFP is kept
separate, so an EOF cannot discard a complete line already retained by the
ACL2 framer."
  (let ((input octets) (service (fnn-feed-runtime-service runtime)))
    (loop
      (multiple-value-bind (word command)
          (fnn-feed-reply-step service link input now)
        (when (> (length command) 0)
          (fnn-send-all (fnn-feed-link-fd link) command 10))
        (case word
          (:need-input
           (when eofp
             (multiple-value-bind (ignored host port backoff)
                 (fnn-feed-dial-plan service (fnn-feed-link-peer-octets link))
               (declare (ignore ignored host port))
               (fnn-feed-drop-link runtime link now backoff)))
           (return))
          ((:closed :invalid :refused)
           (multiple-value-bind (ignored host port backoff)
               (fnn-feed-dial-plan service (fnn-feed-link-peer-octets link))
             (declare (ignore ignored host port))
             (fnn-feed-drop-link runtime link now backoff))
           (return))
          (:ready
           (setf (fnn-feed-link-ready link) t)
           (setq input nil))
          ((:mode :send :quiet)
           ;; The next call receives the framer's already-retained suffix,
           ;; not a concatenation constructed in raw Lisp.
           (setq input nil)))))))

(defun fnn-feed-pump-link (runtime link now)
  (when (fnn-feed-link-socket link)
    (handler-case
        (progn
          (when (fnn-feed-link-ready link)
            (multiple-value-bind (word command)
                (fnn-feed-tick (fnn-feed-runtime-service runtime) link now)
              (declare (ignore word))
              (when (> (length command) 0)
                (fnn-send-all (fnn-feed-link-fd link) command 10))))
          (let ((incoming (fnn-recv (fnn-feed-link-fd link) 0)))
            (cond ((eq incoming :timeout) nil)
                  ((zerop (length incoming))
                   (fnn-feed-consume runtime link nil t now))
                  ((> (length incoming) (fnn-feed-runtime-limit runtime))
                   (fnn-fault "socket returned more than ACL2 feed input bound"))
                  (t (fnn-feed-consume runtime link incoming nil now)))))
      ((or fnn-os-error sb-bsd-sockets:socket-error) ()
        (multiple-value-bind (ignored host port backoff)
            (fnn-feed-dial-plan (fnn-feed-runtime-service runtime)
                                (fnn-feed-link-peer-octets link))
          (declare (ignore ignored host port))
          (fnn-feed-drop-link runtime link now backoff))))))

(defun fnn-feed-worker (runtime)
  (loop until (fnn-feed-stoppingp runtime) do
    (let ((now (fnn-feed-now)))
      (dolist (link (fnn-feed-links runtime))
        (unless (fnn-feed-stoppingp runtime)
          (fnn-feed-dial runtime link now)
          (fnn-feed-pump-link runtime link now))))
    ;; The worker's cadence is availability-only.  ACL2 gates actual offers
    ;; with its monotonic observation and peer backoff state.
    (sleep +fnn-feed-poll-seconds+)))

(defun fnn-feed-worker-guarded (runtime)
  "Contain an adapter defect without turning a peer disconnect into a fence."
  (handler-case
      (fnn-feed-worker runtime)
    (fnn-store-indeterminate (e)
      (fnn-owner-fence-service (fnn-feed-runtime-service runtime))
      (fnn-err "outbound feed uncertain; recovery required: ~a" e))
    (fnn-store-fault (e)
      (fnn-owner-fault-service (fnn-feed-runtime-service runtime) nil e))
    (fnn-store-error (e)
      ;; Owner shutdown refuses a final serialized callback.  Any other
      ;; store error here is not a remote peer verdict and is a host fault.
      (unless (fnn-feed-stoppingp runtime)
        (fnn-owner-fault-service (fnn-feed-runtime-service runtime) nil e)))
    (serious-condition (e)
      (unless (fnn-feed-stoppingp runtime)
        (fnn-owner-fault-service (fnn-feed-runtime-service runtime) nil e)))))

;;; These are registered through the owner's composable resource lifecycle
;;; hooks by the owner convergence lane.  They are idempotent: stop closes
;;; sockets to wake nonblocking waits, then close joins before FNFD/Store close.
(defun fnn-feed-service-start (service)
  (unless (fnn-feed-runtime-get service)
    (let* ((names (fnn-feed-peer-list service))
           (runtime
             (%make-fnn-feed-runtime
              :service service
              :links (mapcar (lambda (peer)
                               (%make-fnn-feed-link
                                :peer peer
                                :peer-octets (fnn-octets (fnn-string-octets peer))))
                             names)
              :lock (sb-thread:make-mutex :name "fn outbound feed runtime")
              :limit (fnn-feed-read-limit service))))
      (fnn-feed-runtime-put service runtime)
      (setf (fnn-feed-runtime-worker runtime)
            (sb-thread:make-thread (lambda () (fnn-feed-worker-guarded runtime))
                                   :name "fn outbound feed"))))
  nil)

(defun fnn-feed-service-wake (service)
  "Owner stop hook: no core call, no wait, and safe to invoke more than once."
  (let ((runtime (fnn-feed-runtime-get service)))
    (when runtime
      (let ((links nil))
        (sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))
          (setf (fnn-feed-runtime-stopping runtime) t
                links (copy-list (fnn-feed-runtime-links runtime))))
        (dolist (link links) (fnn-feed-close-link link)))))
  nil)

(defun fnn-feed-service-close (service)
  "Owner close hook: join before its journals and Store can be released."
  (let ((runtime (fnn-feed-runtime-get service)))
    (when runtime
      (fnn-feed-service-wake service)
      (let ((worker (fnn-feed-runtime-worker runtime)))
        (when worker (sb-thread:join-thread worker)))
      (fnn-feed-runtime-drop service)))
  nil)
