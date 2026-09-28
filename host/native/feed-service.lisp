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

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :sb-posix))

(eval-when (:load-toplevel :execute)
  (unless (fboundp 'fnn-core)
    (load "host/native/io.lisp")))

(defconstant +fnn-feed-poll-seconds+ 1/20)

(define-condition fnn-feed-auth-error (error) ())

;;; STREAK is the value books/feed-link-backoff.lisp `fn-flb-lost' last
;;; answered (consecutive link failures since the link was last ready): the
;;; host carries it and hands it back, and never computes it.
(defstruct (fnn-feed-link (:constructor %make-fnn-feed-link))
  peer peer-octets socket fd tls-context tls-channel (ready nil) (next-dial 0)
  (streak 0))

;;; What the pump was doing when an I/O condition arrived, so a dropped link
;;; names it (fn-flb-drop-line): :read or :send.  Each feed worker binds it
;;; (fnn-feed-worker), so the assignments below are that thread's own.
(defvar *fnn-feed-io-phase* :read)

(defstruct (fnn-feed-runtime (:constructor %make-fnn-feed-runtime))
  service links lock worker (stopping nil) limit)

;;; The owner lifecycle extension hooks carry only SERVICE.  Keep the raw
;;; socket registry private to this module rather than widening the logical
;;; service or introducing a second owner.  Access is short and never covers
;;; a syscall or an ACL2 call.
(defparameter *fnn-feed-runtime-lock*
  (sb-thread:make-mutex :name "fn outbound feed runtimes"))
;; guarded-by: *fnn-feed-runtime-lock*
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

(defun fnn-feed-link-for-peer (peer)
  (%make-fnn-feed-link
   ;; This slot crosses into ACL2 wrappers, whose octets are lists. Socket
   ;; buffers use vectors; retaining one here makes the logical peer lookup
   ;; see malformed input and lose the configured endpoint.
   :peer peer :peer-octets (fnn-octet-list (fnn-string-octets peer))))

(defun fnn-feed-refresh-links (runtime)
  "Make the socket workers follow ACL2's current live feed table.

This runs in the sole feed worker.  ACL2 owns membership; the runtime lock
only publishes the corresponding socket resources.  Removed links are
closed by this worker, preserving the one-closer rule."
  (let* ((service (fnn-feed-runtime-service runtime))
         (names (fnn-feed-peer-list service))
         (removed nil))
    (sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))
      (let ((old (fnn-feed-runtime-links runtime)) (next nil))
        (dolist (name names)
          (let ((link (find name old :key #'fnn-feed-link-peer :test #'string=)))
            (push (or link (fnn-feed-link-for-peer name)) next)))
        (setq removed
              (loop for link in old
                    unless (member (fnn-feed-link-peer link) names :test #'string=)
                    collect link))
        (setf (fnn-feed-runtime-links runtime) (nreverse next))))
    (dolist (link removed) (fnn-feed-close-link runtime link))))

(defun fnn-feed-checked-word (word allowed where)
  (unless (member word allowed)
    (fnn-fault "feed core returned ~s from ~a" word where))
  word)

(defun fnn-feed-peer-list (service)
  (fnn-owner-transit-serialized
   service nil
   (lambda ()
     (fnn-owner-names 'fn-owner-feed-peers))))

(defun fnn-feed-read-limit (service)
  (declare (ignore service))
  (let ((limit (fnn-core 'fn-owner-feed-read-limit)))
    (unless (and (integerp limit) (<= 1 limit)
                 (<= limit +fnn-max-read+))
      (fnn-fault "invalid ACL2 feed reply limit: ~s" limit))
    limit))

(defun fnn-feed-checked-connect-timeout (timeout)
  "Validate ACL2's TCP completion deadline at the raw boundary."
  (unless (and (integerp timeout) (>= timeout 0))
    (fnn-fault "invalid ACL2 feed TCP connect timeout: ~s" timeout))
  timeout)

(defun fnn-feed-dial-plan (service peer-octets)
  "Read ACL2's endpoint, queue, retry delay, and TCP completion deadline."
  (fnn-owner-transit-serialized
   service nil
   (lambda ()
     (let ((queued (fnn-owner-core 'fn-owner-feed-has-queued peer-octets))
           (host (fnn-owner-core 'fn-owner-feed-host peer-octets))
           (port (fnn-owner-core 'fn-owner-feed-port peer-octets))
           (backoff (fnn-owner-core 'fn-owner-feed-backoff-ms peer-octets))
           (security (fnn-owner-core 'fn-owner-feed-security peer-octets))
           (auth (fnn-owner-core 'fn-owner-feed-auth-policy peer-octets)))
       (unless (member queued '(t nil))
         (fnn-fault "feed core returned malformed queued predicate"))
       (unless (fnn-octet-list-p host)
         (fnn-fault "feed core returned malformed peer host"))
       (unless (and (integerp port) (<= 1 port 65535))
         (fnn-fault "feed core returned malformed peer port"))
       (unless (and (integerp backoff) (>= backoff 0))
         (fnn-fault "feed core returned malformed peer backoff"))
       (unless (and (consp security)
                    (member (car security) '(:clear :tls)))
         (fnn-fault "feed core returned malformed security policy"))
       (unless (or (null auth)
                   (and (consp auth) (eq (car auth) :authinfo)
                        (= (length auth) 3) (stringp (second auth))
                        (member (third auth) '(t nil))))
         (fnn-fault "feed core returned malformed auth policy"))
       (values queued (fnn-octets-string (fnn-octets host)) port backoff
               (fnn-feed-checked-connect-timeout
                (fnn-core 'fn-owner-feed-connect-timeout)) security auth)))))

(defun fnn-feed-auth-profile (policy)
  "Read a private regular profile and let ACL2 decode its bounded bytes."
  (if (null policy) (values nil nil nil)
    (let* ((path (second policy))
           (maximum (fnn-core 'fn-owner-feed-profile-max-octets))
           (fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
      (unwind-protect
           (let ((info (fnn-fstat fd)))
             (unless (and (fnn-regular-p info)
                          (= (sb-posix:stat-uid info) (sb-posix:getuid))
                          (zerop (logand (sb-posix:stat-mode info) #o077))
                          (<= (sb-posix:stat-size info) maximum))
               (error 'fnn-feed-auth-error))
             (let* ((bytes
                      (handler-case (fnn-read-bounded-fd fd maximum)
                        (fnn-store-fault () (error 'fnn-feed-auth-error))))
                    (decoded (fnn-core 'fn-owner-feed-profile-decode
                                       (fnn-octet-list bytes))))
               (unless (and (consp decoded) (eq (car decoded) :ok)
                            (= (length decoded) 3))
                 (error 'fnn-feed-auth-error))
               (values (second decoded) (third decoded) (third policy))))
        (fnn-close fd)))))

(defun fnn-feed-connect-core (service peer-octets fd user pass allow-clear)
  "Start ACL2's greeting/MODE phase; this does not make a feed live."
  (fnn-owner-transit-serialized
   service nil
   (lambda ()
     (fnn-feed-checked-word
      (fnn-owner-action 'fn-owner-feed-dial-open peer-octets fd user pass allow-clear)
      '(:await-greeting :await-tls) 'fn-owner-feed-dial-open))))

(defun fnn-feed-tls-established-core (service link)
  (fnn-owner-transit-serialized
   service nil
   (lambda ()
     (let* ((publication (fnn-owner-feed-step 'fn-owner-feed-tls-established
                                              (fnn-feed-link-peer-octets link)))
            (word (fnn-feed-checked-word
                   (fnn-owner-feed-word publication)
                   '(:auth-user :mode :ready :need-input) 'fn-owner-feed-tls-established)))
       (values word (if (member word '(:auth-user :mode))
                        (fnn-owner-feed-command publication)
                      (fnn-make-octets 0)))))))

(defun fnn-feed-enable-tls (runtime link security)
  (unless (and (equal (car security) :tls) (= (length security) 4))
    (fnn-fault "TLS transition without a TLS peer policy"))
  ;; PKT-613 (PRF-231): which check the transport selects is ACL2's
  ;; (`fn-peer-tls-verification'): the configured name, SNI for a DNS name
  ;; only, and a pinned anchor file or the system's public roots.
  (let* ((verification (fnn-core 'fn-peer-tls-verification (third security)
                                 (fourth security)))
         (server-name (and (eq (first verification) :verify) (second verification)))
         (context (progn
                    (unless server-name
                      (error 'fnn-peer-dial-error
                             :outcome (if (eq (second verification) :trust)
                                          :trust :server-name)))
                    (fnn-tls-open-client-context (fourth verification)))))
    ;; Publish ownership before SSL_connect: every failure path can now close
    ;; the context through the link, including a repeated certificate failure.
    (setf (fnn-feed-link-tls-context link) context)
    (handler-case
        (let ((channel (fnn-tls-connect context (fnn-feed-link-fd link) server-name 10
                                        :sni (third verification))))
          (setf (fnn-feed-link-tls-channel link) channel)
          (multiple-value-bind (word command)
              (fnn-feed-tls-established-core (fnn-feed-runtime-service runtime) link)
            (when (> (length command) 0) (fnn-tls-send-all channel command 10))
            (when (eq word :ready) (fnn-feed-link-became-ready link))))
      (error (condition)
        (when (fnn-feed-link-tls-context link)
          (fnn-tls-close-context (fnn-feed-link-tls-context link))
          (setf (fnn-feed-link-tls-context link) nil))
        (error condition)))))

(defun fnn-feed-send (link octets)
  (setq *fnn-feed-io-phase* :send)
  (if (fnn-feed-link-tls-channel link)
      (fnn-tls-send-all (fnn-feed-link-tls-channel link) octets 10)
    (fnn-send-all (fnn-feed-link-fd link) octets 10)))

(defun fnn-feed-recv (link limit)
  "A zero-second read: octets, an empty vector at EOF, or :timeout when the
socket (or, over TLS, OpenSSL: a record with no application data such as a
TLS 1.3 NewSessionTicket) has nothing for the feed yet."
  (setq *fnn-feed-io-phase* :read)
  (if (fnn-feed-link-tls-channel link)
      (fnn-tls-read (fnn-feed-link-tls-channel link) 0 limit)
    (fnn-recv (fnn-feed-link-fd link) 0 limit)))

(defun fnn-feed-tick (service link now)
  "One ACL2 tick.  Its command, if any, is copied only after FNFD append."
  (fnn-owner-transit-serialized
   service nil
   (lambda ()
     (let* ((publication (fnn-owner-feed-step 'fn-owner-feed-tick
                                              (fnn-feed-link-peer-octets link) now))
            (word (fnn-feed-checked-word
                   (fnn-owner-feed-word publication)
                   '(:offer :idle :refused :unsendable) 'fn-owner-feed-tick)))
       (fnn-owner-feed-flush service publication)
       ;; :unsendable (books/owner-feed-article.lisp fn-ofa-publication): the
       ;; records are flushed above; its ACL2 line names the reason and the
       ;; caller drops the link, so fn-feed-lost requeues the offer.
       (when (eq word :unsendable)
         (fnn-owner-feed-log publication))
       (values word
               (if (eq word :offer)
                   (let ((command (fnn-owner-feed-command publication)))
                     (when (zerop (length command))
                       (fnn-fault "feed tick authorized an empty command"))
                     command)
                 (fnn-make-octets 0)))))))

(defun fnn-feed-reply-step (service link octets now)
  "Apply one ACL2-framed reply event, never a host-parsed line."
  (fnn-owner-transit-serialized
   service nil
   (lambda ()
     (let* ((publication (fnn-owner-feed-arena-step 'fn-owner-feed-reply-chunk
                                                    (fnn-feed-link-peer-octets link)
                                                    (fnn-octet-list octets) now))
            (word (fnn-feed-checked-word
                  (fnn-owner-feed-word publication)
                  '(:starttls :tls :auth-user :auth-pass :mode :ready :send :quiet :refused :unsendable :connection-refused :streaming-refused :need-input :closed :invalid :fault)
                  'fn-owner-feed-reply-chunk)))
       (when (eq word :fault)
         (fnn-fault "feed reply framer state is malformed"))
       ;; Only a complete post-ready :line reaches the feed port and replaces
       ;; its FNFD projection.  MODE is a connection-phase command, not a
       ;; delivery effect, and :ready has no socket bytes.
       ;; :unsendable (fn-ofa-publication-command-words-have-octets): the
       ;; port moved and its records are flushed like a :send's; the line
       ;; names ACL2's reason and fnn-feed-consume drops the link, so
       ;; fn-feed-lost requeues the offer.  Never an owner stop.
       (when (member word '(:send :quiet :refused :unsendable))
         (fnn-owner-feed-flush service publication)
         ;; A reply outcome (not a 335/238 prompt) has one ACL2-rendered
         ;; line: a peer's refusal or deferral is never silent.
         (fnn-owner-feed-log publication))
       ;; friend-path-2: a refused, closed or unreadable connection names
       ;; why, in ACL2's line (fn-peer-feed-failure-line).
       (when (member word '(:connection-refused :closed :invalid))
         (fnn-owner-feed-log publication))
       ;; The peer refused MODE STREAM: ACL2 recorded the stop and its line.
       (when (eq word :streaming-refused)
         (fnn-owner-feed-log publication))
       ;; Ready: after a 500/501 to MODE STREAM ACL2 rendered the IHAVE
       ;; fallback line (PRF-207) into the publication; otherwise there is none.
       (when (eq word :ready)
         (fnn-owner-feed-log publication))
       (values word
               (if (member word '(:starttls :auth-user :auth-pass :mode :send))
                   (let ((command (fnn-owner-feed-command publication)))
                     (when (zerop (length command))
                       (fnn-fault "feed connection/reply authorized an empty command"))
                     command)
                 (fnn-make-octets 0)))))))

(defun fnn-feed-lost (service link now)
  "Record one peer-local loss before closing or retrying its socket."
  (fnn-owner-transit-serialized
   service nil
   (lambda ()
     (let* ((publication (fnn-owner-feed-step 'fn-owner-feed-lost
                                              (fnn-feed-link-peer-octets link) now))
            (word (fnn-feed-checked-word
                   (fnn-owner-feed-word publication)
                   '(:ok :refused) 'fn-owner-feed-lost)))
       (fnn-owner-feed-flush service publication)
       word))))

(defun fnn-feed-publish-socket (runtime link socket fd)
  "Publish an established descriptor unless the stop boundary already won.

The runtime lock makes a dial that finishes during stop close its private
socket rather than publishing a descriptor the stop hook cannot wake."
  (sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))
    (unless (fnn-feed-runtime-stopping runtime)
      (setf (fnn-feed-link-socket link) socket
            (fnn-feed-link-fd link) fd
            (fnn-feed-link-ready link) nil)
      t)))

(defun fnn-feed-close-link (runtime link)
  "Clear one published link under the runtime lock, then close it once.

The worker is the only closer.  The stop hook may only shutdown a live socket
while holding this same lock, so it can never act on a descriptor after close
has made the kernel free to reuse it."
  (let ((socket nil))
    (sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))
      (setq socket (fnn-feed-link-socket link))
      (when socket
        (setf (fnn-feed-link-socket link) nil
              (fnn-feed-link-fd link) nil
              (fnn-feed-link-ready link) nil)))
    (when (fnn-feed-link-tls-channel link)
      (ignore-errors (fnn-tls-close-channel (fnn-feed-link-tls-channel link)))
      (setf (fnn-feed-link-tls-channel link) nil))
    (when (fnn-feed-link-tls-context link)
      (ignore-errors (fnn-tls-close-context (fnn-feed-link-tls-context link)))
      (setf (fnn-feed-link-tls-context link) nil))
    (when socket (ignore-errors (fnn-socket-shut socket)))))

(defun fnn-feed-link-became-ready (link)
  "The reply machine reported :ready: ACL2 restarts the redial streak."
  (setf (fnn-feed-link-ready link) t)
  (let ((streak (fnn-core 'fn-flb-ready (fnn-feed-link-streak link))))
    (unless (and (integerp streak) (>= streak 0))
      (fnn-fault "feed core returned a malformed link streak: ~s" streak))
    (setf (fnn-feed-link-streak link) streak)))

(defun fnn-feed-drop-link (runtime link now base cause)
  "A peer link failed for CAUSE (books/feed-link-backoff.lisp *fn-flb-causes*).
The core records the loss before the next retry; ACL2's `fn-flb-lost' answers
the delay before the next dial from the peer record's BASE and the link's
streak, and the drop is logged by ACL2's line, whatever its cause."
  ;; A failed dial is still a named loss: it advances the ACL2-owned retry
  ;; state even though no descriptor was established to close.
  (let ((stopping (fnn-feed-stoppingp runtime)))
    (unless stopping
      (fnn-feed-lost (fnn-feed-runtime-service runtime) link now))
    (fnn-feed-close-link runtime link)
    (let* ((answer (fnn-core 'fn-flb-lost base (fnn-feed-link-streak link)))
           (delay (first answer))
           (streak (second answer)))
      (unless (and (integerp delay) (>= delay 0) (integerp streak) (>= streak 0))
        (fnn-fault "feed core returned a malformed link backoff: ~s" answer))
      (setf (fnn-feed-link-streak link) streak
            (fnn-feed-link-next-dial link) (+ now delay))
      (unless stopping
        (fnn-log-line (fnn-core 'fn-flb-drop-line (fnn-feed-link-peer-octets link)
                                cause delay))))))

(defun fnn-feed-dial (runtime link now)
  "Dial an ACL2-projected endpoint when its core queue and delay allow it.

DNS resolution remains FNN-CONNECT's separately documented availability
boundary.  ACL2 supplies the deadline for the nonblocking TCP completion; once
established, read/write waits use FNN-RECV/FNN-SEND-ALL.  ACL2 gets a
connection-phase state before the descriptor is published; a concurrent stop
therefore makes the worker close its private socket instead of leaking it into
the shared link table."
  (when (and (not (fnn-feed-stoppingp runtime))
             (null (fnn-feed-link-socket link))
             (<= (fnn-feed-link-next-dial link) now))
    (multiple-value-bind (queued host port backoff timeout security auth)
        (fnn-feed-dial-plan (fnn-feed-runtime-service runtime)
                            (fnn-feed-link-peer-octets link))
      (when queued
        (let ((socket nil) (published nil))
          (handler-case
              (progn
                (setq socket (fnn-peer-connect host port :timeout timeout))
                (let ((fd (fnn-socket-fd socket)))
                  (multiple-value-bind (user pass allow-clear)
                      (fnn-feed-auth-profile auth)
                    (fnn-feed-connect-core (fnn-feed-runtime-service runtime)
                                           (fnn-feed-link-peer-octets link) fd
                                           user pass allow-clear))
                  (setq published (fnn-feed-publish-socket runtime link socket fd))
                  (when (and published (equal (car security) :tls)
                             (equal (cadr security) :implicit))
                    (fnn-feed-enable-tls runtime link security))
                  (unless published
                    (fnn-socket-shut socket))))
            ((or fnn-os-error sb-bsd-sockets:socket-error fnn-tls-error
                 fnn-feed-auth-error fnn-peer-dial-error) (condition)
              (when (and socket (not published)) (fnn-socket-shut socket))
              (fnn-peer-dial-report :feed (fnn-feed-link-peer-octets link) host condition)
              ;; A failed open has no outgoing bytes, but it is still the
              ;; named peer-loss observation that advances the ACL2 backoff.
              (unless (fnn-feed-stoppingp runtime)
                (fnn-feed-drop-link runtime link now backoff
                                    (if (typep condition 'fnn-tls-error) :tls :dial))))))))))

(defun fnn-feed-consume (runtime link octets eofp now)
  "Drain a received chunk through one ACL2 event at a time.

NIL means ``drain retained suffix'' after the first iteration.  EOFP is kept
separate, so an EOF cannot discard a complete line already retained by the
ACL2 framer."
  (let ((input octets) (service (fnn-feed-runtime-service runtime)))
    (loop
      (multiple-value-bind (word command)
          (fnn-feed-reply-step service link input now)
        ;; Developer image only: fnn-feed-reply-step has crossed the FNFD
        ;; append/fsync barrier for :feed-sent. Stop this worker before its
        ;; TAKETHIS/article bytes reach the protected socket, so a test can
        ;; kill the process at an unresolved attempt that fn-feed-restart
        ;; expresses. Production images reject this selector at startup.
        (when (and (eq word :send)
                   (string= (or (fnn-developer-selector
                                 "FN_NATIVE_FEED_TEST_STOP_AFTER_SENT") "")
                            "1"))
          (fnn-control-stop-calling-thread))
        (when (> (length command) 0)
          (fnn-feed-send link command))
        (when (fnn-feed-stoppingp runtime) (return))
        (case word
          (:need-input
           (when eofp
             ;; The drop line (fn-flb-drop-line, reason=lost-eof) names it.
             (multiple-value-bind (ignored host port backoff timeout security auth)
                 (fnn-feed-dial-plan service (fnn-feed-link-peer-octets link))
               (declare (ignore ignored host port timeout security auth))
               (fnn-feed-drop-link runtime link now backoff :eof)))
           (return))
          ((:closed :invalid :connection-refused :streaming-refused :unsendable)
           ;; The reply step logged ACL2's line naming the peer's answer; the
           ;; drop line names the retry.
           (multiple-value-bind (ignored host port backoff timeout security auth)
               (fnn-feed-dial-plan service (fnn-feed-link-peer-octets link))
             (declare (ignore ignored host port timeout security auth))
             (fnn-feed-drop-link runtime link now backoff
                                 (if (eq word :unsendable) :unsendable :peer)))
           (return))
          (:ready
           (fnn-feed-link-became-ready link)
           (setq input nil))
          (:tls
           (multiple-value-bind (ignored host port backoff timeout security auth)
               (fnn-feed-dial-plan service (fnn-feed-link-peer-octets link))
             (declare (ignore ignored host port backoff timeout auth))
             (fnn-feed-enable-tls runtime link security))
           (setq input nil))
          ((:starttls :auth-user :auth-pass :mode :send :quiet)
           ;; The next call receives the framer's already-retained suffix,
           ;; not a concatenation constructed in raw Lisp.
           (setq input nil)))))))

(defun fnn-feed-pump-link (runtime link now)
  (when (and (not (fnn-feed-stoppingp runtime)) (fnn-feed-link-socket link))
    (setq *fnn-feed-io-phase* :read)
    (handler-case
        (progn
          (when (fnn-feed-link-ready link)
            (multiple-value-bind (word command)
                (fnn-feed-tick (fnn-feed-runtime-service runtime) link now)
              (when (> (length command) 0)
                (fnn-feed-send link command))
              (when (eq word :unsendable)
                (multiple-value-bind (ignored host port backoff timeout security auth)
                    (fnn-feed-dial-plan (fnn-feed-runtime-service runtime)
                                        (fnn-feed-link-peer-octets link))
                  (declare (ignore ignored host port timeout security auth))
                  (fnn-feed-drop-link runtime link now backoff :unsendable))
                (return-from fnn-feed-pump-link nil))))
          (unless (fnn-feed-stoppingp runtime)
            ;; The ACL2-projected limit sizes this buffer before read(2); a
            ;; peer cannot make the host allocate a larger coalesced batch.
            (let ((incoming (fnn-feed-recv link (fnn-feed-runtime-limit runtime))))
              (cond ((eq incoming :timeout) nil)
                    ((zerop (length incoming))
                     (fnn-feed-consume runtime link nil t now))
                    (t (fnn-feed-consume runtime link incoming nil now))))))
      ((or fnn-os-error sb-bsd-sockets:socket-error fnn-tls-error
           fnn-peer-dial-error) (condition)
        (if (fnn-feed-stoppingp runtime)
            (fnn-feed-close-link runtime link)
          (multiple-value-bind (ignored host port backoff timeout security auth)
              (fnn-feed-dial-plan (fnn-feed-runtime-service runtime)
                                  (fnn-feed-link-peer-octets link))
            (declare (ignore ignored port timeout security auth))
            ;; PKT-613: a refused STARTTLS handshake (the name, the chain, the
            ;; configured check) is a dial outcome and is logged by name; a
            ;; later I/O loss on an established link is not a dial.
            (when (typep condition '(or fnn-tls-handshake-error fnn-peer-dial-error))
              (fnn-peer-dial-report :feed (fnn-feed-link-peer-octets link) host condition))
            ;; Every drop names its cause in ACL2's line (defect M3: a TLS
            ;; read error on an established link used to drop it silently).
            (fnn-feed-drop-link runtime link now backoff
                                (typecase condition
                                  (fnn-tls-handshake-error :tls)
                                  (fnn-peer-dial-error :dial)
                                  (t *fnn-feed-io-phase*)))))))))

(defun fnn-feed-worker (runtime)
  (let ((*fnn-feed-io-phase* :read))
    (fnn-feed-worker-loop runtime)))

(defun fnn-feed-worker-loop (runtime)
  (unwind-protect
       (loop until (fnn-feed-stoppingp runtime) do
         (fnn-feed-refresh-links runtime)
         (let ((now (fnn-feed-now)))
           (dolist (link (fnn-feed-links runtime))
             (unless (fnn-feed-stoppingp runtime)
               (fnn-feed-dial runtime link now)
               (unless (fnn-feed-stoppingp runtime)
                 (fnn-feed-pump-link runtime link now)))))
         ;; The worker's cadence is availability-only.  ACL2 gates actual
         ;; offers with its monotonic observation and peer backoff state.
         (sleep +fnn-feed-poll-seconds+))
    ;; Stop only shutdowns; this worker is the sole final closer.
    (dolist (link (fnn-feed-links runtime))
      (fnn-feed-close-link runtime link))))

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
;;; hooks by the owner convergence lane.  They are idempotent: stop only
;;; shutdowns live sockets to wake I/O, then this worker closes and close joins
;;; before FNFD/Store close.
(defun fnn-feed-service-start (service)
  (unless (fnn-feed-runtime-get service)
    (let* ((names (fnn-feed-peer-list service))
           (runtime
             (%make-fnn-feed-runtime
              :service service
              :links (mapcar #'fnn-feed-link-for-peer names)
              :lock (sb-thread:make-mutex :name "fn outbound feed runtime")
              :limit (fnn-feed-read-limit service))))
      (fnn-feed-runtime-put service runtime)
      (setf (fnn-feed-runtime-worker runtime)
            (sb-thread:make-thread (lambda () (fnn-feed-worker-guarded runtime))
                                   :name "fn outbound feed"))))
  nil)

(defun fnn-feed-service-wake (service)
  "Owner stop hook: shutdown only, no core call/wait, safe to repeat.

The socket shutdowns occur while the runtime lock still excludes final close.
That leaves the worker as the only closer and prevents a cached descriptor
from being closed then reused before this stop hook touches it."
  (let ((runtime (fnn-feed-runtime-get service)))
    (when runtime
      (sb-thread:with-mutex ((fnn-feed-runtime-lock runtime))
        (setf (fnn-feed-runtime-stopping runtime) t)
        (dolist (link (fnn-feed-runtime-links runtime))
          (let ((socket (fnn-feed-link-socket link)))
            (when socket (ignore-errors (fnn-socket-shutdown socket))))))))
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
