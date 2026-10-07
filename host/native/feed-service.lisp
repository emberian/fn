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


;;; The worker's pace (SCEN-FEED-PACE, lane feed-pace; S145 before it, lane
;;; served-live).  Each round pumps every link until its next action waits on
;;; the kernel or its ACL2 quantum (fn-prd-feed-quantum) is spent, then waits
;;; as books/peer-round-driver.lisp fn-prd-feed-pause answers from what each
;;; link reports: not at all while any link can act (an offer to ask for, a
;;; reply read, a write the kernel has not refused), on poll(2) of the
;;; sockets a peer owes something, or on the owner's commit signal
;;; (fnn-owner-signal-commit: every durable publication and the stop) when
;;; nothing is in progress, for ACL2's bounded time.  It used to sleep a
;;; fixed 1/20 s after every round that did anything, one action per link a
;;; round: about eight rounds an article.  Scheduling only: ACL2 still
;;; decides every offer, dial and backoff.

;;; Set by a round that did something; bound per round by the worker loop.
(defvar *fnn-feed-active* nil)

(define-condition fnn-feed-auth-error (fnn-peer-dial-error) ()
  (:default-initargs :outcome :credential))

;;; STREAK is the value books/feed-link-backoff.lisp `fn-flb-lost' last
;;; answered (consecutive link failures since the link was last ready): the
;;; host carries it and hands it back, and never computes it.
(defstruct (fnn-feed-link (:constructor %make-fnn-feed-link))
  peer peer-octets socket fd tls-context tls-channel (ready nil) (next-dial 0)
  (streak 0)
  phase security dial-auth tls-name deadline
  output (output-offset 0) output-end output-quantum-end output-quantum
  (drain nil) (eof nil) (tick-due t))

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
(defparameter *fnn-feed-runtimes* (make-hash-table :test #'eq))
(fnn-guarded-by *fnn-feed-runtimes* *fnn-feed-runtime-lock*)

(defun fnn-feed-now ()
  "One monotonic observation, in the ACL2 feed port's milliseconds."
  (fnn-monotonic-ms))

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
closed by this worker, preserving the one-closer rule.  A removed link that
held a connection is reported to ACL2 as a loss first, exactly as every other
close is (fnn-feed-drop-link): the feed port still holds that connection and
its in-flight offer, and without the loss a re-created link (`peer feed NAME
resume') offers nothing until the stale state is cleared, which nothing does."
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
    (dolist (link removed)
      (when (and (fnn-feed-link-socket link) (not (fnn-feed-stoppingp runtime)))
        (setq *fnn-feed-active* t)
        (fnn-feed-lost service link (fnn-feed-now)))
      (fnn-feed-close-link runtime link))))

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
       ;; No NNTP endpoint: ACL2 answers host NIL and port 0 for a peer whose
       ;; record is gone or has no :nntp transport (host/owner-host.lisp
       ;; fn-owner-feed-host/-port), e.g. removed by live reconfiguration
       ;; after this pass refreshed its links.  Nothing to dial: not queued
       ;; (inspection sweep 2026-10-03 S036; it was a fault that stopped the
       ;; node).
       (when (and (null host) (eql port 0))
         (setq queued nil host nil))
       (unless (or (null queued) (fnn-octet-list-p host))
         (fnn-fault "feed core returned malformed peer host"))
       (unless (or (null queued) (and (integerp port) (<= 1 port 65535)))
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
       (values queued (and host (fnn-octets-string (fnn-octets host))) port backoff
               (fnn-feed-checked-connect-timeout
                (fnn-core 'fn-owner-feed-connect-timeout)) security auth)))))

(defun fnn-feed-loss-backoff (service peer-octets)
  "ACL2's retry base for a link being dropped: the peer record's backoff,
0 for a peer whose record is gone (fn-owner-feed-backoff-ms).  A loss path
asks this alone, never the dial plan: the link may belong to a peer that
live reconfiguration just removed (S036)."
  (let ((backoff (fnn-owner-transit-serialized
                  service nil
                  (lambda () (fnn-owner-core 'fn-owner-feed-backoff-ms peer-octets)))))
    (unless (and (integerp backoff) (>= backoff 0))
      (fnn-fault "feed core returned malformed peer backoff"))
    backoff))

(defun fnn-feed-auth-profile (policy)
  "Read a private regular descriptor without blocking on a substituted FIFO.
ACL2 decodes its bounded bytes; only named input/OS refusal is credential loss."
  (if (null policy) (values nil nil nil)
    (handler-case
        (let* ((path (second policy))
               (maximum (fnn-core 'fn-owner-feed-profile-max-octets)))
          (unless (and (integerp maximum) (> maximum 0))
            (fnn-fault "invalid ACL2 credential profile bound"))
          (let ((fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+
                                         sb-posix:o-nonblock)))
                (primary nil))
            (unwind-protect
                 (handler-bind ((serious-condition (lambda (e) (setq primary e))))
                   (let ((info (fnn-fstat fd)))
                     (unless (and (fnn-regular-p info)
                                  (= (sb-posix:stat-uid info) (sb-posix:getuid))
                                  (zerop (logand (sb-posix:stat-mode info) #o077))
                                  (<= (sb-posix:stat-size info) maximum))
                       (error 'fnn-feed-auth-error))
                     (let* ((bytes
                              (handler-case (fnn-read-bounded-fd fd maximum)
                                (fnn-input-overbound (e)
                                  ;; Unknown subclasses retain the fault class.
                                  (if (eq (type-of e) 'fnn-input-overbound)
                                      (error 'fnn-feed-auth-error)
                                    (error e)))))
                            (decoded (fnn-core 'fn-owner-feed-profile-decode
                                               (fnn-octet-list bytes))))
                       (cond ((equal decoded '(:bad nil nil))
                              (error 'fnn-feed-auth-error))
                             ((and (consp decoded) (eq (car decoded) :ok)
                                   (consp (cdr decoded)) (consp (cddr decoded))
                                   (null (cdddr decoded)))
                              (values (second decoded) (third decoded) (third policy)))
                             (t (fnn-fault "malformed ACL2 credential profile result"))))))
              (handler-case (fnn-close fd)
                (serious-condition (e)
                  ;; A cleanup OS failure must not reclassify a core fault.
                  (error (or primary e)))))))
      (fnn-os-error () (error 'fnn-feed-auth-error)))))

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
     (let* ((publication (fnn-owner-feed-arena-step 'fn-owner-feed-tls-established
                                              (fnn-feed-link-peer-octets link)))
            (word (fnn-feed-checked-word
                   (fnn-owner-feed-word publication)
                   '(:auth-user :mode :ready :need-input) 'fn-owner-feed-tls-established)))
       (values word (if (member word '(:auth-user :mode))
                        (fnn-owner-feed-command publication)
                      (fnn-make-octets 0)))))))

(defun fnn-feed-enable-tls (runtime link security)
  "Retain authenticated TLS setup; one handshake attempt runs per later turn."
  (declare (ignore runtime))
  (unless (and (equal (car security) :tls) (= (length security) 4))
    (fnn-fault "TLS transition without a TLS peer policy"))
  (let* ((verification (fnn-core 'fn-peer-tls-verification (third security) (fourth security)))
         (name (and (eq (first verification) :verify) (second verification))))
    (unless name
      (error 'fnn-peer-dial-error :outcome (if (eq (second verification) :trust) :trust :server-name)))
    (setf (fnn-feed-link-tls-context link) (fnn-tls-open-client-context (fourth verification))
          (fnn-feed-link-tls-name link) name
          (fnn-feed-link-tls-channel link)
          (fnn-tls-client-begin (fnn-feed-link-tls-context link) (fnn-feed-link-fd link)
                                name :sni (third verification))
          (fnn-feed-link-phase link) :tls
          (fnn-feed-link-deadline link)
          (fnn-core 'fn-prd-deadline (fnn-feed-now) (fnn-core 'fn-owner-feed-connect-timeout)))))

(defun fnn-feed-send (link octets)
  "Retain one journal-authorized command; physical writes yield between peers."
  (when (fnn-feed-link-output link) (fnn-fault "feed replaced an undrained command"))
  (when (plusp (length octets))
    (let ((bound (fnn-core 'fn-owner-feed-send-quantum)) (data (fnn-octets octets)))
      (unless (and (consp bound) (integerp (car bound)) (plusp (car bound))
                   (integerp (cdr bound)) (plusp (cdr bound)))
        (fnn-fault "invalid ACL2 feed send quantum: ~s" bound))
      (setf (fnn-feed-link-output link) data
            (fnn-feed-link-output-offset link) 0
            (fnn-feed-link-output-quantum link) bound
            (fnn-feed-link-output-quantum-end link)
            (fnn-core 'fn-prd-write-quantum-end 0 (length data) (car bound))
            (fnn-feed-link-output-end link)
            (fnn-core 'fn-prd-write-end 0 (fnn-feed-link-output-quantum-end link))
            (fnn-feed-link-deadline link) (fnn-core 'fn-prd-deadline (fnn-feed-now) (cdr bound))))))

(defun fnn-feed-write-step (link now)
  "One physical attempt, retaining the exact buffer/range on TLS WANT.
Answers :progress, or the readiness the attempt waits on (:input/:output)."
  (setq *fnn-feed-io-phase* :send)
  (let* ((data (fnn-feed-link-output link)) (offset (fnn-feed-link-output-offset link))
         (end (fnn-feed-link-output-end link))
         (sent (if (fnn-feed-link-tls-channel link)
                   (fnn-tls-write-now-range (fnn-feed-link-tls-channel link) data offset end)
                 (fnn-socket-write-now (fnn-feed-link-fd link) data offset end))))
    (unless (integerp sent)
      (return-from fnn-feed-write-step (fnn-feed-readiness sent :output)))
    (setq *fnn-feed-active* t)
    (incf (fnn-feed-link-output-offset link) sent)
    (let ((offset (fnn-feed-link-output-offset link)))
      (cond ((= offset (length data))
             ;; Every feed command is answered: the drained command arms
             ;; the wait for that reply (fn-prd-feed-action).
             (setf (fnn-feed-link-output link) nil
                   (fnn-feed-link-deadline link) (fnn-core 'fn-prd-round-deadline now)))
            (t
             (when (= offset (fnn-feed-link-output-quantum-end link))
               (let ((bound (fnn-feed-link-output-quantum link)))
                 (setf (fnn-feed-link-output-quantum-end link)
                       (fnn-core 'fn-prd-write-quantum-end offset (length data) (car bound))
                       (fnn-feed-link-deadline link) (fnn-core 'fn-prd-deadline now (cdr bound)))))
             (when (= offset end)
               (setf (fnn-feed-link-output-end link)
                     (fnn-core 'fn-prd-write-end offset (fnn-feed-link-output-quantum-end link)))))))
    :progress))

(defun fnn-feed-readiness (word default)
  "A physical attempt's wait word as a readiness direction: a socket's :wait
(EAGAIN/EINTR) is DEFAULT, a TLS WANT says its own direction."
  (case word
    ((:input :output) word)
    (:wait default)
    (t (fnn-fault "feed transport answered ~s" word))))

(defun fnn-feed-recv (link limit)
  "One physical read: octets (empty at end of input), or the readiness it
waits on (:input, or :output for a TLS WANT), the ACL2 framer state untouched."
  (setq *fnn-feed-io-phase* :read)
  (let ((result (if (fnn-feed-link-tls-channel link)
                    (fnn-tls-read-now (fnn-feed-link-tls-channel link) limit)
                  (fnn-socket-read-now (fnn-feed-link-fd link) limit))))
    (if (member result '(:wait :input :output)) (fnn-feed-readiness result :input) result)))

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

(defconstant +fnn-feed-reply-cold-attempts+ 4
  "At most this many cold reads of one feed reply's article before the link
is dropped: ACL2's line deadline (fn-otb-line-dependency-step) normally ends
the wait first; this bounds the re-runs when the realizer's cache evicts the
page between its read and the warm re-run.")

(defun fnn-feed-reply-step (service link octets now)
  "Apply one ACL2-framed reply event, never a host-parsed line.

The article a 335/238 sends is read BEFORE the reply is committed, by ACL2's
pure probe (fn-owner-feed-reply-article) inside the owner quantum with the
extent realizer in its no-I/O mode.  Warm, the committing step runs in that
same quantum with the article.  Cold, nothing was committed: the quantum is
left, the page is read holding neither the owner nor the extent mutex (the
served read's issue and await, fnn-owner-cold-await), and the event runs
again.  A page ACL2's deadline gives up on drops the link, as a lost reply
does (fn-feed-lost requeues the offer)."
  (let ((peer-octets (fnn-feed-link-peer-octets link))
        (octet-list (fnn-octet-list octets))
        (cold-since nil))
    (dotimes (attempt +fnn-feed-reply-cold-attempts+)
      (declare (ignorable attempt))
      (let ((step (fnn-owner-transit-serialized
                   service nil
                   (lambda ()
                     (multiple-value-bind (state article-or-read)
                         (fnn-owner-feed-reply-probe-locked service peer-octets octet-list)
                       (if (eq state :warm)
                           (list :done
                                 (multiple-value-list
                                  (fnn-feed-reply-commit service peer-octets octet-list
                                                         now article-or-read)))
                         (list :cold article-or-read)))))))
        (when (eq (first step) :done)
          (return-from fnn-feed-reply-step (values-list (second step))))
        (multiple-value-bind (word since)
            (fnn-owner-cold-await service (second step) cold-since :transit)
          (unless cold-since (setq cold-since since))
          (unless (eq word :serve)
            (return-from fnn-feed-reply-step
              (fnn-feed-reply-unavailable peer-octets word))))))
    (fnn-feed-reply-unavailable peer-octets :attempts)))

(defun fnn-feed-reply-unavailable (peer-octets word)
  "The article could not be had within ACL2's deadline (WORD: :unavailable,
ACL2's refusal word, or :attempts): nothing of the reply was committed, so the
link is lost (:lost, no command) and fn-feed-lost requeues the offer."
  (fnn-err "feed reply article unavailable for peer ~a: ~s"
           (map 'string #'code-char peer-octets) word)
  (values :lost (fnn-make-octets 0)))

(defun fnn-feed-reply-commit (service peer-octets octets now article)
  "The committing step, owner quantum held: ACL2's reply chunk with the article
the probe read, then the publication's effects.  It reads no payload."
  (let* ((publication (fnn-owner-feed-arena-step 'fn-owner-feed-reply-chunk
                                                 peer-octets
                                                 octets now article))
         (word (fnn-feed-checked-word
               (fnn-owner-feed-word publication)
               '(:starttls :tls :auth-user :auth-pass :mode :ready :send :quiet :lost :refused :unsendable :connection-refused :streaming-refused :need-input :closed :invalid :fault)
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
    ;; :lost (books/owner-feed.lisp fn-own-feed-reply-word): ACL2 took the
    ;; reply as a loss and moved the port; its records are flushed like a
    ;; :quiet's and fnn-feed-consume drops the link.
    (when (member word '(:send :quiet :lost :refused :unsendable))
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
              (fnn-make-octets 0)))))

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
    (when socket (ignore-errors (fnn-socket-shut socket)))
    (setf (fnn-feed-link-phase link) nil (fnn-feed-link-security link) nil
          (fnn-feed-link-dial-auth link) nil (fnn-feed-link-tls-name link) nil
          (fnn-feed-link-deadline link) nil (fnn-feed-link-output link) nil
          (fnn-feed-link-drain link) nil (fnn-feed-link-eof link) nil
          (fnn-feed-link-tick-due link) t)))

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
  (setq *fnn-feed-active* t)
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
  "Capture an admitted profile before one nonblocking connect attempt.
DNS/profile/context filesystem work remains a separate availability frontier."
  (when (and (not (fnn-feed-stoppingp runtime)) (null (fnn-feed-link-socket link))
             (<= (fnn-feed-link-next-dial link) now))
    (multiple-value-bind (queued host port backoff timeout security auth)
        (fnn-feed-dial-plan (fnn-feed-runtime-service runtime) (fnn-feed-link-peer-octets link))
      (when queued
        (setq *fnn-feed-active* t)
        (let ((socket nil) (published nil))
          (handler-case
              (multiple-value-bind (user pass allow-clear) (fnn-feed-auth-profile auth)
                (multiple-value-bind (opened word) (fnn-peer-connect-start host port)
                  (setq socket opened)
                  (unless (member word '(:connected :pending)) (fnn-fault "invalid connect-start outcome"))
                  (setq published (fnn-feed-publish-socket runtime link socket (fnn-socket-fd socket)))
                  (if published
                      (setf (fnn-feed-link-phase link) (if (eq word :connected) :connected :connect)
                            (fnn-feed-link-security link) security
                            (fnn-feed-link-dial-auth link) (list user pass allow-clear)
                            (fnn-feed-link-deadline link) (fnn-core 'fn-prd-deadline now timeout))
                    (fnn-socket-shut socket))))
            ((or fnn-os-error sb-bsd-sockets:socket-error fnn-tls-error
                 fnn-feed-auth-error fnn-peer-dial-error) (condition)
              (when (and socket (not published)) (fnn-socket-shut socket))
              (fnn-peer-dial-report :feed (fnn-feed-link-peer-octets link) host condition)
              (unless (fnn-feed-stoppingp runtime)
                (fnn-feed-drop-link runtime link now backoff
                                    (typecase condition (fnn-feed-auth-error :credential)
                                      (fnn-tls-error :tls) (t :dial)))))))))))

(defun fnn-feed-connected-step (runtime link now)
  "Establish ACL2's connection phase after TCP completion, never before it.
The greeting is then awaited under the reply wait (fn-prd-feed-action)."
  (destructuring-bind (user pass clear) (fnn-feed-link-dial-auth link)
    (fnn-feed-connect-core (fnn-feed-runtime-service runtime) (fnn-feed-link-peer-octets link)
                           (fnn-feed-link-fd link) user pass clear))
  (setf (fnn-feed-link-dial-auth link) nil (fnn-feed-link-phase link) nil
        (fnn-feed-link-deadline link) (fnn-core 'fn-prd-round-deadline now))
  (let ((security (fnn-feed-link-security link)))
    (when (and (equal (car security) :tls) (equal (cadr security) :implicit))
      (fnn-feed-enable-tls runtime link security))))

(defun fnn-feed-consume (runtime link octets eofp now)
  "Consume one ACL2 event; its retained framer suffix resumes on a later turn."
  (when eofp (setf (fnn-feed-link-eof link) t))
  (let ((service (fnn-feed-runtime-service runtime)))
    (multiple-value-bind (word command) (fnn-feed-reply-step service link octets now)
      (when (and (eq word :send)
                 (string= (or (fnn-developer-selector "FN_NATIVE_FEED_TEST_STOP_AFTER_SENT") "") "1"))
        (fnn-control-stop-calling-thread))
      (if (> (length command) 0)
          (fnn-feed-send link command)
        ;; A complete reply ends the wait its command armed; a partial line
        ;; (:need-input) does not, so a trickling peer cannot extend it.
        (unless (eq word :need-input) (setf (fnn-feed-link-deadline link) nil)))
      (setf (fnn-feed-link-drain link) (not (eq word :need-input)))
      (case word
        (:need-input
         (setf (fnn-feed-link-tick-due link) t)
         (when (fnn-feed-link-eof link)
           (fnn-feed-drop-link runtime link now
                               (fnn-feed-loss-backoff service (fnn-feed-link-peer-octets link)) :eof)))
        ((:closed :invalid :connection-refused :streaming-refused :unsendable :lost)
         (setf (fnn-feed-link-drain link) nil)
         (fnn-feed-drop-link runtime link now
                             (fnn-feed-loss-backoff service (fnn-feed-link-peer-octets link))
                             (if (eq word :unsendable) :unsendable :peer)))
        (:ready (fnn-feed-link-became-ready link))
        (:tls
         (multiple-value-bind (ignored host port backoff timeout security auth)
             (fnn-feed-dial-plan service (fnn-feed-link-peer-octets link))
           (declare (ignore ignored host port timeout auth))
           (if (equal (car security) :tls) (fnn-feed-enable-tls runtime link security)
             (fnn-feed-drop-link runtime link now backoff :peer))))))))

(defun fnn-feed-pump-link (runtime link now)
  "One ACL2-chosen action on LINK (fn-prd-feed-action).  Answers what it saw:
:progress, :idle (the feed port had no offer), the readiness a physical
attempt waits on (:input/:output), or nil when the link has no connection."
  (when (and (not (fnn-feed-stoppingp runtime)) (fnn-feed-link-socket link))
    (setq *fnn-feed-io-phase* :read)
    (handler-case
        (let ((action (fnn-core 'fn-prd-feed-action (fnn-feed-link-phase link)
                                 (not (null (fnn-feed-link-output link))) (fnn-feed-link-drain link)
                                 (and (fnn-feed-link-ready link) (fnn-feed-link-tick-due link))
                                 now (fnn-feed-link-deadline link))))
          (setq *fnn-feed-io-phase*
                (case action ((:connect :connected) :dial) (:tls :tls) (:write :send) (t :read)))
          (case action
            (:timeout (fnn-os-fail sb-posix:etimedout))
            (:connect
             (cond ((eq (fnn-connect-poll (fnn-feed-link-socket link)) :connected)
                    (setf (fnn-feed-link-phase link) :connected)
                    :progress)
                   ;; TCP completion is the socket becoming writable.
                   (t :output)))
            (:connected (fnn-feed-connected-step runtime link now) :progress)
            (:tls
             (let ((step (fnn-tls-client-step (fnn-feed-link-tls-channel link)
                                              (fnn-feed-link-tls-name link))))
               (cond ((eq step :connected)
                      (setf (fnn-feed-link-phase link) nil (fnn-feed-link-deadline link) nil)
                      (multiple-value-bind (word command)
                          (fnn-feed-tls-established-core (fnn-feed-runtime-service runtime) link)
                        ;; Implicit TLS then awaits the greeting (:need-input).
                        (when (eq word :need-input)
                          (setf (fnn-feed-link-deadline link) (fnn-core 'fn-prd-round-deadline now)))
                        (when (> (length command) 0) (fnn-feed-send link command))
                        (when (eq word :ready) (fnn-feed-link-became-ready link)))
                      :progress)
                     (t (fnn-feed-readiness step :input)))))
            (:write (fnn-feed-write-step link now))
            (:reply (fnn-feed-consume runtime link nil nil now) :progress)
            (:offer
             (setf (fnn-feed-link-tick-due link) nil)
             (multiple-value-bind (word command) (fnn-feed-tick (fnn-feed-runtime-service runtime) link now)
               (when (> (length command) 0) (fnn-feed-send link command))
               (case word
                 (:offer :progress)
                 (:unsendable
                  (fnn-feed-drop-link runtime link now
                                      (fnn-feed-loss-backoff (fnn-feed-runtime-service runtime)
                                                             (fnn-feed-link-peer-octets link)) :unsendable)
                  :progress)
                 (t :idle))))
            (:read
             (let ((incoming (fnn-feed-recv link (fnn-core 'fn-prd-read-limit (fnn-feed-runtime-limit runtime)))))
               (cond ((member incoming '(:input :output)) incoming)
                     (t (setq *fnn-feed-active* t)
                        (fnn-feed-consume runtime link incoming (zerop (length incoming)) now)
                        :progress))))
            (t (fnn-fault "unknown feed driver action ~s" action))))
      ((or fnn-os-error sb-bsd-sockets:socket-error fnn-tls-error
           fnn-peer-dial-error) (condition)
        (if (fnn-feed-stoppingp runtime)
            (fnn-feed-close-link runtime link)
          (let ((backoff (fnn-feed-loss-backoff (fnn-feed-runtime-service runtime)
                                                (fnn-feed-link-peer-octets link))))
            ;; PKT-613: a refused STARTTLS handshake (the name, the chain, the
            ;; configured check) is a dial outcome and is logged by name; a
            ;; later I/O loss on an established link is not a dial.  The
            ;; host is ACL2's endpoint, empty for a peer whose record is gone.
            (when (typep condition '(or fnn-tls-handshake-error fnn-peer-dial-error))
              (fnn-peer-dial-report
               :feed (fnn-feed-link-peer-octets link)
               (or (fnn-owner-transit-serialized
                    (fnn-feed-runtime-service runtime) nil
                    (lambda () (fnn-owner-core 'fn-owner-feed-host
                                               (fnn-feed-link-peer-octets link))))
                   "")
               condition))
            ;; Every drop names its cause in ACL2's line (defect M3: a TLS
            ;; read error on an established link used to drop it silently).
            (fnn-feed-drop-link runtime link now backoff
                                (typecase condition
                                  (fnn-tls-handshake-error :tls)
                                  (fnn-peer-dial-error :dial)
                                  (t *fnn-feed-io-phase*)))))
        :progress))))

(defun fnn-feed-pump-quantum (runtime link)
  "Pump LINK while it progresses, at most ACL2's quantum (fn-prd-feed-quantum)
of actions, each at its own monotonic observation.  A physical wait ends the
turn; a tick with no offer does not (its next action is the read).  Answers
LINK's report for fn-prd-feed-pause, (ACTION BLOCKED AWAITING)."
  (let ((outcome nil) (now (fnn-feed-now)))
    (loop repeat (fnn-core 'fn-prd-feed-quantum)
          while (and (fnn-feed-link-socket link) (not (fnn-feed-stoppingp runtime)))
          do (setq now (fnn-feed-now)
                   outcome (fnn-feed-pump-link runtime link now))
             (when (eq outcome :progress) (setq *fnn-feed-active* t))
          until (member outcome '(:input :output)))
    (if (null (fnn-feed-link-socket link))
        (list :dial nil nil)
      (list (fnn-core 'fn-prd-feed-action (fnn-feed-link-phase link)
                      (not (null (fnn-feed-link-output link))) (fnn-feed-link-drain link)
                      (and (fnn-feed-link-ready link) (fnn-feed-link-tick-due link))
                      now (fnn-feed-link-deadline link))
            (and (member outcome '(:input :output)) outcome)
            (not (null (fnn-feed-link-deadline link)))))))

(defun fnn-feed-worker (runtime)
  (let ((*fnn-feed-io-phase* :read))
    (fnn-feed-worker-loop runtime)))

(defun fnn-feed-idle-wait (runtime seen ms)
  "Sleep up to MS milliseconds on the owner's commit signal unless a commit
(or the stop) came after SEEN was read; a missed signal is seen by the count.
Answers :commit when the count moved, else :timeout."
  (let* ((service (fnn-feed-runtime-service runtime))
         (lock (fnn-owner-service-wait-lock service))
         (queue (fnn-owner-service-wait-queue service)))
    (sb-thread:grab-mutex lock)
    (unwind-protect
         ;; The stop hook raises the signal after setting stopping, so a
         ;; stop after SEEN changes the count and is never slept through.
         (progn
           (when (= seen (fnn-owner-service-commits service))
             (sb-thread:condition-wait queue lock :timeout (/ ms 1000d0)))
           (unless (sb-thread:holding-mutex-p lock)
             (sb-thread:grab-mutex lock))
           (if (= seen (fnn-owner-service-commits service)) :timeout :commit))
      ;; A timed-out condition-wait may return without the mutex.
      (when (sb-thread:holding-mutex-p lock)
        (sb-thread:release-mutex lock)))))

(defun fnn-feed-commits-seen (runtime)
  (let ((service (fnn-feed-runtime-service runtime)))
    (sb-thread:with-mutex ((fnn-owner-service-wait-lock service))
      (fnn-owner-service-commits service))))

(defun fnn-feed-poll-wait (runtime seen ms links reports)
  "Wait up to MS milliseconds for a socket ACL2 names as waited on
(fn-prd-feed-link-wait of its report: :input is POLLIN, :output POLLOUT), a
commit after SEEN, or the stop.  A commit cannot wake poll(2), so it runs in
slices of ACL2's I/O poll (fn-prd-feed-poll-ms) with the commit count read
between them: a worker waiting on one peer's reply still offers a new
article within a slice, and the slices take no owner hold.  The stop
shutdowns the sockets (they poll ready) and raises the signal.  Answers
:ready, :commit or :timeout."
  (let ((fds nil) (events nil))
    (loop for link in links
          for report in reports
          for wait = (fnn-core 'fn-prd-feed-link-wait report)
          when (and (member wait '(:input :output)) (fnn-feed-link-fd link))
            do (push (fnn-feed-link-fd link) fds)
               (push (if (eq wait :output) +fnn-mux-pollout+ +fnn-mux-pollin+) events))
    (let ((fds (coerce (nreverse fds) 'vector))
          (events (coerce (nreverse events) 'vector))
          (slice (fnn-core 'fn-prd-feed-poll-ms))
          (deadline (+ (get-internal-real-time)
                       (ceiling (* ms internal-time-units-per-second) 1000))))
      (loop
        (let ((left (floor (* 1000 (- deadline (get-internal-real-time)))
                           internal-time-units-per-second)))
          (when (<= left 0) (return :timeout))
          (when (some #'plusp (fnn-mux-poll fds events (min left slice)))
            (return :ready))
          (when (or (fnn-feed-stoppingp runtime)
                    (/= seen (fnn-feed-commits-seen runtime)))
            (return :commit)))))))

(defun fnn-feed-worker-loop (runtime)
  (unwind-protect
       (let ((idle 0))
         (loop until (fnn-feed-stoppingp runtime) do
           (let ((seen (fnn-feed-commits-seen runtime))
                 (*fnn-feed-active* nil)
                 (links nil) (reports nil))
             (fnn-feed-refresh-links runtime)
             (setq links (fnn-feed-links runtime))
             (dolist (link links)
               (unless (fnn-feed-stoppingp runtime)
                 (fnn-feed-dial runtime link (fnn-feed-now)))
               (push (if (fnn-feed-stoppingp runtime)
                         (list :dial nil nil)
                       (fnn-feed-pump-quantum runtime link))
                     reports))
             (setq reports (nreverse reports)
                   idle (if *fnn-feed-active* 0 (1+ idle)))
             ;; ACL2 decides the wait from what each link reported: none while
             ;; any link can act (fn-prd-feed-never-sleeps-while-an-article-
             ;; can-leave), the sockets a peer owes something, or the commit
             ;; signal; bounded, and never past a redial.
             (let* ((now (fnn-feed-now))
                    (dials (loop for link in links
                                 unless (fnn-feed-link-socket link)
                                   collect (fnn-feed-link-next-dial link)))
                    (pause (fnn-core 'fn-prd-feed-pause reports idle dials now))
                    (woke (case (first pause)
                            (:now :ready)
                            (:poll (fnn-feed-poll-wait runtime seen (second pause) links reports))
                            (:signal (fnn-feed-idle-wait runtime seen (second pause)))
                            (t (fnn-fault "feed core returned a malformed pause: ~s" pause)))))
               ;; A commit or the clock may have made an offer due on any link
               ;; (a new article, a retry come due): each asks the feed port
               ;; again.  A socket's readiness concerns only its own link,
               ;; whose read asks again once a reply is consumed.
               (unless (eq woke :ready)
                 (dolist (link links)
                   (setf (fnn-feed-link-tick-due link) t)))))))
    ;; Stop only shutdowns; this worker is the sole final closer.
    (dolist (link (fnn-feed-links runtime))
      (fnn-feed-close-link runtime link))))

(defun fnn-feed-worker-guarded (runtime)
  "Contain an adapter defect without turning a peer disconnect into a fence."
  (handler-case
      (fnn-feed-worker runtime)
    (serious-condition (e)
      ;; Exact concrete class, including failures during terminal cleanup.
      ;; A known stopping refusal is scoped; an unknown subclass is a fault.
      (fnn-owner-thread-escape (fnn-feed-runtime-service runtime) e "outbound feed"))))

(def-actor fnn-feed-spawn-worker :kind :feed :thread-name "fn outbound feed" :roster t
  :join fnn-feed-service-close :failure :service)

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
            (fnn-feed-spawn-worker service (list runtime)
                                   (lambda () (fnn-feed-worker-guarded runtime))))))
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
            (when socket (ignore-errors (fnn-socket-shutdown socket))))))
      ;; An idle worker sleeps on the commit signal (S145): wake it.
      (fnn-owner-signal-commit service)))
  nil)

(defun fnn-feed-service-close (service)
  "Owner close hook: join before its journals and Store can be released."
  (let ((runtime (fnn-feed-runtime-get service)))
    (when runtime
      (fnn-feed-service-wake service)
      ;; The starter may have raised after creating a parked/live child and
      ;; before returning its worker. Shared registration retains that child.
      (let* ((actor (fnn-owner-actor-for-custody service runtime))
             (worker (or (fnn-feed-runtime-worker runtime)
                         (and actor (fnn-owner-actor-thread actor)))))
        (when (and actor (null worker))
          (fnn-fault "outbound feed spawn remains physically unobserved"))
        (when (and worker (not (fnn-owner-actor-join service worker)))
          (fnn-fault "outbound feed worker remains physically live")))
      (fnn-feed-runtime-drop service)))
  nil)
