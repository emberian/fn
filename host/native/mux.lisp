;;; host/native/mux.lisp -- the served connections on a fixed set of I/O loops
;;; (lane connection-multiplexing, 2026-09-26; PKT-605; HST-024; PRF-223).
;;;
;;; Raw Common Lisp under the native host trust tag.  It schedules sockets and
;;; nothing else: every protocol, exposure and owner decision is the same call
;;; host/native/owner.lisp made from its per-connection worker thread before
;;; this file (fnn-owner-handle-chunk, which decides fn-owner-exposure-charge
;;; in the step's own quantum, fn-owner-exposure-open / -idle / -close /
;;; -release, fn-owner-tls-established), under the same owner mutex
;;; (fnn-owner-serialized, admitted by the scheduler gate as the connection's
;;; class), in the same order for one connection.
;;;
;;; What changed is who waits.  A connection used to be a thread whose
;;; control stack and runtime regions were reserved for its whole life and
;;; which slept in recv(2), in the exposure wait and in the one-second drain
;;; after its last reply.  Now +fnn-mux-loops+ threads each poll(2) the
;;; connections they own and a wake pipe; a connection is a record
;;; (fnn-mux-conn) holding what the worker held on its stack:
;;;
;;;   input   the octets the next step is handed: the read in hand, or the
;;;           suffix a step left (at most one read of ACL2's size,
;;;           fn-cbud-step-read-octets: 4 KiB, 512 under a step rate);
;;;   out     the one window of the reply being written, its offset and
;;;           deadline, and the render plan's continuation (HST-023: the step
;;;           answers a plan; fnn-owner-render-next renders the next window,
;;;           off the owner mutex, when the socket took the last); while a
;;;           window is queued the connection is not read and not stepped, so
;;;           a client that does not read its replies meets TCP backpressure
;;;           as before and holds one window, never a queue of them;
;;;   timers  the exposure wait (fn-exp-charge's milliseconds), the idle check
;;;           (fn-exp-idle every second without input, RFC 3977 3.1), the send
;;;           deadline (10 s, as fnn-send-all's), the handshake deadline and
;;;           the drain after a graceful close (1 s).
;;;
;;; TLS runs in the loop without waiting inside OpenSSL (host/native/tls.lisp
;;; fnn-tls-accept-step, -read-now, -write-now): at most
;;; +fnn-mux-handshakes-per-loop+ handshakes are in progress per loop and
;;; the rest wait their turn, already admitted.  PKT-639: an implicit-TLS
;;; connection meets fn-exp-open BEFORE any handshake work, so the capacity,
;;; the per-address limit and the trusted range bound handshakes too, and a
;;; refused one is closed without SSL_accept (the 400 cannot be sent in
;;; clear on a TLS port).  PKT-640: a TLS failure is named in the service
;;; log (books/connection-budget.lisp fn-cbud-tls-refusal-line).
;;;
;;; The memory a connection costs, the fixed threads, and the refusal of a
;;; capacity the machine cannot hold are books/connection-budget.lisp's; the
;;; host observes and installs (fnn-mux-budget-install).

(in-package "ACL2")

(defconstant +fnn-mux-loops+ 2)
(defconstant +fnn-mux-handshakes-per-loop+ 8)
(defconstant +fnn-mux-queued-per-loop+ 256)
(defconstant +fnn-mux-send-seconds+ 10)
(defconstant +fnn-mux-handshake-seconds+ 10)
(defconstant +fnn-mux-idle-seconds+ 1)
(defconstant +fnn-mux-drain-seconds+ 1)
(defconstant +fnn-mux-tick-ms+ 250)
;;; The node's threads that are not loops or control clients: main (accept),
;;; finalizer, log writer, checkpoint publisher, feed and pull workers,
;;; control accept, three listeners, two spare (image-floor's count).
(defconstant +fnn-mux-fixed-threads+ 12)

(defconstant +fnn-mux-pollin+ 1)
(defconstant +fnn-mux-pollout+ 4)
(defconstant +fnn-mux-poll-trouble+ (logior 8 16 32)) ; POLLERR POLLHUP POLLNVAL

(defstruct (fnn-mux-loop (:constructor %make-fnn-mux-loop))
  service thread
  (lock (sb-thread:make-mutex :name "fn mux inbox"))
  (inbox nil) (conns nil) wake-read wake-write
  (handshaking 0) (waiting nil)
  ;; Implicit-TLS sockets not yet admitted, waiting for a handshake slot.
  (queued nil)
  ;; Lane commit-onto-log: (CONN . COMPLETION) pairs the committer thread
  ;; handed over for connections waiting on their batch (under LOCK); the
  ;; loop's completed passes and whether it sleeps in poll(2) now, which the
  ;; committer reads to know every ready connection was stepped
  ;; (host/native/owner.lisp fnn-owner-loops-passed-p).
  (arrived nil) (passes 0) (polling nil)
  ;; PKT-875: at the end of each pass, how many of this loop's connections
  ;; wait for a batch's completion or still owe their client its reply (under
  ;; LOCK); a graceful stop's drain reads it (fnn-mux-unsent).
  (unsent 0)
  ;; The loop's one read buffer, of the served read size ACL2 decided
  ;; (fnn-mux-read-buffer): a read allocates only the octets it returns.
  (buffer nil))

(defstruct (fnn-mux-conn (:constructor %make-fnn-mux-conn))
  socket fd implicit-tls channel ssl cid opened-cid
  ;; :new :handshake :hs-wait :serving :draining :done
  (phase :new)
  input
  out (out-at 0) out-deadline out-op after
  want resume-at idle-at hs-deadline drain-deadline
  greeting done
  ;; The service class this connection's quanta are admitted as (:reader, or
  ;; :transit when ACL2 named a peer at open) and the render plan whose
  ;; windows the loop is writing (nil between replies).
  (class :reader) plan
  ;; Lane commit-onto-log: (STEP REDEEM AFTER) while the step's submission
  ;; waits for its commit quantum; nil otherwise.
  (await nil)
  ;; PKT-875: the output queued is a batch's completion (a POST's reply):
  ;; a stop's drain waits for it to leave (fnn-mux-iterate's count).
  (replying nil))

(defun fnn-mux-ticks (seconds)
  (+ (fnn-now) (round (* seconds internal-time-units-per-second))))

;;; ---------------------------------------------------------------------------
;;; poll(2): struct pollfd {int fd; short events; short revents}, 8 octets,
;;; little-endian as host/native/io.lisp fnn-poll-readable writes it.

(defun fnn-mux-poll (fds events timeout-ms)
  "REVENTS for each of FDS (a vector of the same length), after at most
TIMEOUT-MS milliseconds; all zero after a timeout or an interrupted wait."
  (unless (member :little-endian *features*)
    (fnn-fault "fnn-mux-poll: struct pollfd is written little-endian"))
  (let* ((n (length fds))
         (buf (make-array (* 8 (max n 1)) :element-type '(unsigned-byte 8)
                                          :initial-element 0))
         (revents (make-array n :initial-element 0)))
    (loop for i from 0 below n
          for fd = (aref fds i) for ev = (aref events i)
          do (loop for k from 0 below 4
                   do (setf (aref buf (+ (* 8 i) k)) (ldb (byte 8 (* 8 k)) fd)))
             (setf (aref buf (+ (* 8 i) 4)) (ldb (byte 8 0) ev)
                   (aref buf (+ (* 8 i) 5)) (ldb (byte 8 8) ev)))
    (let ((ready
            (sb-sys:with-pinned-objects (buf)
              (sb-alien:alien-funcall
               (sb-alien:extern-alien
                "poll" (function sb-alien:int sb-sys:system-area-pointer
                                 sb-alien:unsigned-long sb-alien:int))
               (sb-sys:vector-sap buf) n timeout-ms))))
      (when (and (integerp ready) (> ready 0))
        (loop for i from 0 below n
              do (setf (aref revents i)
                       (logior (aref buf (+ (* 8 i) 6))
                               (ash (aref buf (+ (* 8 i) 7)) 8))))))
    revents))

;;; ---------------------------------------------------------------------------
;;; Transport, one attempt each.

(defun fnn-mux-read-plain (fd &optional buffer)
  "One read(2) into BUFFER (a fresh +fnn-max-read+ one when NIL): the octets
read, empty at end of input, or :input."
  (let* ((buffer (or buffer (fnn-make-octets +fnn-max-read+)))
         (count (fnn-read-fd fd buffer nil t)))
    (if (eq count :would-block) :input (subseq buffer 0 count))))

(defun fnn-mux-peek-plain (fd buffer)
  "One MSG_PEEK into BUFFER: the octets waiting (not consumed), empty at end,
or :input."
  (loop
    (multiple-value-bind (count errno)
        (funcall *fnn-tls-peek-syscall* fd buffer)
      (cond ((and (null count) (fnn-eintr-p errno)) nil)
            ((and (null count) (fnn-would-block-p errno)) (return :input))
            ((null count) (fnn-os-fail errno))
            (t (return (subseq buffer 0 count)))))))

(defun fnn-mux-read-buffer (service loop)
  "LOOP's read buffer, of exactly the octets one served step may read:
ACL2's fn-cbud-step-read-octets (books/connection-budget.lisp), installed by
fnn-owner-refresh-read-octets under the owner mutex.  Reallocated only when
that size changes (a live change of the step rate)."
  (let ((size (fnn-owner-service-read-octets service))
        (buffer (fnn-mux-loop-buffer loop)))
    (unless (and (integerp size) (> size 0))
      (fnn-fault "the served read size is not installed"))
    (if (and buffer (= (length buffer) size))
        buffer
      (setf (fnn-mux-loop-buffer loop) (fnn-make-octets size)))))

(defun fnn-mux-receive-now (service loop conn)
  "The served read, as fnn-owner-receive chose it: through TLS once
protected; by MSG_PEEK while a loaded context makes STARTTLS reachable (ACL2
then chooses the exact prefix to consume); else read(2).  At most the octets
ACL2 lets one served step read (fnn-mux-read-buffer)."
  (let ((channel (fnn-mux-conn-channel conn)) (fd (fnn-mux-conn-fd conn))
        (buffer (fnn-mux-read-buffer service loop)))
    (cond (channel (fnn-tls-read-now channel (length buffer) buffer))
          ((fnn-owner-service-tls-context service) (fnn-mux-peek-plain fd buffer))
          (t (fnn-mux-read-plain fd buffer)))))

(defun fnn-mux-write-now (conn)
  "One write of the queued reply from its offset: the octets written, or the
direction to wait for."
  (let ((channel (fnn-mux-conn-channel conn))
        (data (fnn-mux-conn-out conn))
        (offset (fnn-mux-conn-out-at conn)))
    (if channel
        (fnn-tls-write-now channel data offset)
      (let* ((remaining (- (length data) offset))
             (progress (fnn-write-progress
                        (lambda () (funcall *fnn-write-syscall*
                                            (fnn-mux-conn-fd conn) data offset remaining))
                        remaining "socket" nil t)))
        (if (eq progress :would-block) :output progress)))))

(defun fnn-mux-wake (loop)
  (let ((one (fnn-make-octets 1)))
    (ignore-errors
      (sb-sys:with-pinned-objects (one)
        (sb-unix:unix-write (fnn-mux-loop-wake-write loop) one 0 1)))))

(defun fnn-mux-drain-wake (loop)
  (let ((buffer (fnn-make-octets 64)))
    (loop
      (multiple-value-bind (count errno)
          (sb-sys:with-pinned-objects (buffer)
            (sb-unix:unix-read (fnn-mux-loop-wake-read loop)
                               (sb-sys:vector-sap buffer) 64))
        (declare (ignore errno))
        (unless (and count (> count 0)) (return))))))

;;; ---------------------------------------------------------------------------
;;; The connection's life.  Every function below runs on the connection's
;;; loop thread inside fnn-mux-guarded, whose handlers are the worker's.

(defun fnn-mux-service (loop) (fnn-mux-loop-service loop))

(defun fnn-mux-tls-log (loop conn reason)
  "PKT-640: the service log names a TLS refusal (ACL2's line)."
  (let* ((service (fnn-mux-service loop))
         (line (ignore-errors
                (fnn-with-roster (service)
                  (fnn-core 'fn-cbud-tls-refusal-line reason
                            (or (fnn-mux-conn-opened-cid conn) 0))))))
    (when (stringp line)
      (ignore-errors (fnn-log-line (map 'list #'char-code line))))))

(defun fnn-mux-finish (loop conn)
  "The worker's unwind: the owner close (CID), the exposure release (the id
fn-exp-open registered, kept even when a fault path cleared CID; PRF-161),
the TLS session, then the socket.  Idempotent."
  (unless (eq (fnn-mux-conn-phase conn) :done)
    (let ((service (fnn-mux-service loop))
          (cid (fnn-mux-conn-cid conn))
          (opened-cid (fnn-mux-conn-opened-cid conn))
          (was (fnn-mux-conn-phase conn)))
      (setf (fnn-mux-conn-phase conn) :done)
      (when (fnn-mux-conn-ssl conn)
        (ignore-errors (fnn-%ssl-free (fnn-mux-conn-ssl conn)))
        (setf (fnn-mux-conn-ssl conn) nil))
      (when (eq was :handshake)
        (decf (fnn-mux-loop-handshaking loop)))
      (setf (fnn-mux-loop-waiting loop)
            (delete conn (fnn-mux-loop-waiting loop) :test #'eq)
            (fnn-mux-loop-queued loop)
            (delete conn (fnn-mux-loop-queued loop) :test #'eq))
      (when cid
        (ignore-errors
          (fnn-owner-serialized
           service cid (lambda () (fnn-owner-action 'fn-owner-close cid))
           (fnn-mux-conn-class conn))))
      (when opened-cid
        (ignore-errors
          (fnn-owner-serialized
           service nil
           (lambda () (fnn-owner-action 'fn-owner-exposure-release opened-cid))
           (fnn-mux-conn-class conn))))
      (when (fnn-mux-conn-channel conn)
        (ignore-errors (fnn-tls-close-channel (fnn-mux-conn-channel conn))))
      (fnn-socket-shut (fnn-mux-conn-socket conn))
      (setf (fnn-mux-loop-conns loop)
            (delete conn (fnn-mux-loop-conns loop) :test #'eq))
      (ignore-errors
        (fnn-with-roster (service)
          (setf (fnn-owner-service-clients service)
                (delete (fnn-mux-conn-socket conn)
                        (fnn-owner-service-clients service) :test #'eq))))
      (when (fnn-mux-conn-done conn)
        (sb-thread:signal-semaphore (fnn-mux-conn-done conn)))
      (fnn-mux-start-waiting-handshake loop))))

(defmacro fnn-mux-guarded ((loop conn) &body body)
  "The worker's handlers (fnn-owner-serve-client before this file), each
ending the connection with fnn-mux-finish."
  (let ((l (gensym "LOOP")) (c (gensym "CONN")) (service (gensym "SERVICE")))
    `(let* ((,l ,loop) (,c ,conn) (,service (fnn-mux-service ,l)))
       (handler-case (progn ,@body)
         (fnn-store-indeterminate (e)
           ;; The shared boundary has already stopped mutation; the cleanup
           ;; must not attempt a later close transition.
           (setf (fnn-mux-conn-cid ,c) nil)
           (fnn-owner-fence-service ,service)
           (fnn-err "owner uncertain; recovery required: ~a" e)
           (fnn-mux-finish ,l ,c))
         (fnn-store-fault (e)
           (let ((faulted-cid (fnn-mux-conn-cid ,c)))
             (setf (fnn-mux-conn-cid ,c) nil)
             (fnn-owner-fault-service ,service faulted-cid e))
           (fnn-mux-finish ,l ,c))
         (fnn-owner-connection-fault (e)
           ;; Exactly one ACL2 fault transition owns semantic cleanup.
           (let ((faulted-cid (fnn-mux-conn-cid ,c)))
             (setf (fnn-mux-conn-cid ,c) nil)
             (handler-case
                 (let ((reply (and faulted-cid
                                   (fnn-owner-abandon-connection ,service faulted-cid e))))
                   (when (and reply (> (length reply) 0))
                     (ignore-errors
                       (fnn-owner-send (fnn-mux-conn-fd ,c) (fnn-mux-conn-channel ,c)
                                       reply 0))))
               (fnn-store-indeterminate (nested)
                 (fnn-owner-fence-service ,service)
                 (fnn-err "owner uncertain while abandoning connection: ~a" nested))
               (serious-condition (nested)
                 (fnn-owner-fault-service ,service nil nested))))
           (fnn-mux-finish ,l ,c))
         ((or fnn-store-error fnn-os-error sb-bsd-sockets:socket-error) (e)
           (fnn-err "owner connection: ~a" e)
           (fnn-mux-finish ,l ,c))
         (fnn-tls-error (e)
           ;; Scoped to this peer; the listener and the context stay live.
           (fnn-err "owner TLS connection: ~a" e)
           (fnn-mux-tls-log ,l ,c (if (search "timed out" (princ-to-string e))
                                      :timeout :handshake))
           (fnn-mux-finish ,l ,c))
         (serious-condition (e)
           (let ((faulted-cid (fnn-mux-conn-cid ,c)))
             (setf (fnn-mux-conn-cid ,c) nil)
             (fnn-owner-fault-service ,service faulted-cid e))
           (fnn-mux-finish ,l ,c))))))

(defun fnn-mux-arm-idle (conn)
  (setf (fnn-mux-conn-idle-at conn) (fnn-mux-ticks +fnn-mux-idle-seconds+)))

(defun fnn-mux-queue (loop conn octets op after)
  "Queue the one reply OCTETS (a greeting, a rendered window); AFTER (nil,
:close or :starttls) runs when the socket has taken it and no window of the
plan remains."
  (let ((service (fnn-mux-service loop)))
    ;; The named non-semantic scope (and its private test injection) of the
    ;; worker's send, fnn-owner-connection-call's.
    (fnn-owner-connection-call service op (lambda () nil))
    (setf (fnn-mux-conn-out conn) (fnn-octets octets)
          (fnn-mux-conn-out-at conn) 0
          (fnn-mux-conn-out-op conn) op
          (fnn-mux-conn-out-deadline conn) (fnn-mux-ticks +fnn-mux-send-seconds+)
          (fnn-mux-conn-after conn) after
          (fnn-mux-conn-want conn) nil)
    (fnn-mux-flush loop conn)))

(defun fnn-mux-queue-plan (loop conn plan after)
  "Write the step's render PLAN a window at a time (HST-023): the first
window now, each next one when the socket took the last (fnn-mux-flush).
The connection holds one window and the plan's continuation, never the
whole reply; a plan with nothing to write runs AFTER at once."
  (multiple-value-bind (octets rest donep) (fnn-owner-render-next plan)
    (setf (fnn-mux-conn-plan conn) (if donep nil rest))
    (if (> (length octets) 0)
        (fnn-mux-queue loop conn octets :send-reply after)
      (fnn-mux-after loop conn after))))

(defun fnn-mux-flush (loop conn)
  "Write the queued window; when the socket took it, render the plan's next
window (off the owner mutex) and go on; with nothing left, run AFTER."
  (let ((service (fnn-mux-service loop)))
    (loop
      (loop while (and (fnn-mux-conn-out conn)
                       (< (fnn-mux-conn-out-at conn) (length (fnn-mux-conn-out conn))))
            do (let ((progress (fnn-owner-connection-call
                                service (fnn-mux-conn-out-op conn)
                                (lambda () (fnn-mux-write-now conn)))))
                 (if (integerp progress)
                     (setf (fnn-mux-conn-out-at conn) (+ (fnn-mux-conn-out-at conn) progress)
                           (fnn-mux-conn-want conn) nil)
                   (progn (setf (fnn-mux-conn-want conn) progress)
                          (return-from fnn-mux-flush nil)))))
      (unless (fnn-mux-conn-out conn)
        (return-from fnn-mux-flush nil))
      (let ((plan (fnn-mux-conn-plan conn)))
        (if plan
            (multiple-value-bind (octets rest donep) (fnn-owner-render-next plan)
              (setf (fnn-mux-conn-plan conn) (if donep nil rest)
                    (fnn-mux-conn-out conn) octets
                    (fnn-mux-conn-out-at conn) 0
                    (fnn-mux-conn-out-deadline conn) (fnn-mux-ticks +fnn-mux-send-seconds+)))
          (let ((after (fnn-mux-conn-after conn)))
            (setf (fnn-mux-conn-out conn) nil (fnn-mux-conn-after conn) nil
                  (fnn-mux-conn-out-deadline conn) nil)
            (fnn-mux-after loop conn after)
            (return-from fnn-mux-flush nil)))))))

(defun fnn-mux-begin-drain (loop conn)
  "The graceful close: close_notify first on a protected channel, then
shutdown the output side and read what the peer still sends for at most one
second, so its receive queue keeps the final reply (fnn-graceful-close's
contract, without blocking the loop)."
  (let ((service (fnn-mux-service loop)))
    (fnn-owner-connection-call
     service :graceful-close
     (lambda ()
       (when (fnn-mux-conn-channel conn)
         (fnn-tls-close-channel (fnn-mux-conn-channel conn))
         (setf (fnn-mux-conn-channel conn) nil))
       (if (< (fnn-%shutdown (fnn-mux-conn-fd conn) +fnn-shut-wr+) 0)
           (fnn-mux-finish loop conn)
         (setf (fnn-mux-conn-phase conn) :draining
               (fnn-mux-conn-want conn) :input
               (fnn-mux-conn-drain-deadline conn)
               (fnn-mux-ticks +fnn-mux-drain-seconds+)))))))

(defun fnn-mux-after (loop conn after)
  (case after
    (:close (fnn-mux-begin-drain loop conn))
    (:starttls (fnn-mux-request-handshake loop conn))
    (t (when (eq (fnn-mux-conn-phase conn) :serving)
         (fnn-mux-arm-idle conn)
         (fnn-mux-work loop conn)))))

(defun fnn-mux-step (loop conn)
  "One served step over the held input and what follows it: the worker's
body after fnn-owner-handle-chunk, line for line.  The step decides the
exposure charge in its own quantum (PRF-161; one gate pass per read):
(values :defer MS) keeps the input in hand and arms the resume timer, and
the same octets are handed to the next step."
  (let* ((service (fnn-mux-service loop))
         (incoming (fnn-mux-conn-input conn))
         (channel (fnn-mux-conn-channel conn))
         (results (multiple-value-list
                   ;; PKT-858: a peer connection's read enters as ACL2's
                   ;; class for it (fnn-owner-peer-read-class: :reader while
                   ;; the disk sheds, so IHAVE/CHECK are answered 436/431
                   ;; at once instead of waiting for the barrier).
                   (let ((peerp (eq (fnn-mux-conn-class conn) :transit)))
                     (fnn-owner-handle-chunk service (fnn-mux-conn-cid conn) incoming
                                             (fnn-mux-conn-socket conn)
                                             (if peerp
                                                 (fnn-owner-peer-read-class service)
                                               (fnn-mux-conn-class conn))
                                             peerp)))))
    ;; Format 9 (lane commit-onto-log): the step queued its submission for the
    ;; next commit quantum.  The rest is the submitted step's handling, with
    ;; the plan built when the completion arrives (fnn-mux-await-done).
    (when (eq (first results) :await)
      (destructuring-bind (tag step redeem closing starttls consumed) results
        (declare (ignore tag))
        (setq results (list (list :await step redeem) closing starttls consumed
                            (and redeem t) t))))
    (when (eq (first results) :defer)
      (let ((ms (second results)))
        (unless (and (integerp ms) (> ms 0))
          (fnn-fault "owner returned a malformed exposure charge"))
        (setf (fnn-mux-conn-resume-at conn)
              (+ (fnn-now) (round (* (min ms 1000) internal-time-units-per-second) 1000))))
      (return-from fnn-mux-step nil))
    (destructuring-bind (plan closing starttls consumed redeemed &optional submitted)
        results
      ;; Whatever this step does not consume is set again below; nothing
      ;; carried here is ever read from the socket twice.
      (setf (fnn-mux-conn-input conn) nil)
      (cond
        (channel
         ;; Once protected, no transport suffix may be reclassified as a
         ;; second handshake.  A closing step stops at the octet that closed
         ;; the wire; an XREDEEM PASS (PRF-164) and an article's submission
         ;; (PKT-600) leave the rest of this record as the next step's input.
         (cond ((or closing (= consumed (length incoming))))
               ((or redeemed submitted)
                (setf (fnn-mux-conn-input conn) (subseq incoming consumed)))
               (t (fnn-fault "protected owner read left a TLS suffix"))))
        ((fnn-owner-service-tls-context service)
         ;; The loop is the sole reader of this socket.  A failed or short
         ;; consume ends this connection; the transition is never replayed.
         (fnn-tls-consume-plaintext (fnn-mux-conn-fd conn)
                                    (subseq incoming 0 consumed) 10))
        ((/= consumed (length incoming))
         ;; The suffix is the next step's input and is already in hand (the
         ;; oversize article's close, PKT-600's submission).  A step that
         ;; consumes nothing and neither closes nor hands the transport
         ;; over IS a broken invariant: the same octets cannot progress.
         (when (and (zerop consumed) (not closing) (not starttls))
           (fnn-fault "owner consumed no octets and left the connection open"))
         (setf (fnn-mux-conn-input conn) (subseq incoming consumed))))
      (when starttls
        (when channel
          (fnn-fault "owner requested STARTTLS on a protected channel"))
        (unless (fnn-owner-service-tls-context service)
          (fnn-fault "owner requested STARTTLS without a TLS context")))
      ;; STARTTLS is ACL2's handshake owed (books/served-plan.lisp
      ;; fn-splan-step-handshake-owed): never with the step's own close or the
      ;; exposure's.  CLOSING with it is only a service stop (the drain was
      ;; uncertain), and a stopping service is closed, not upgraded.
      (let ((after (cond (closing :close) (starttls :starttls) (t nil))))
        (if (and (consp plan) (eq (first plan) :await))
            (fnn-mux-await loop conn (second plan) (third plan) after)
          (fnn-mux-queue-plan loop conn plan after))))))

(defun fnn-mux-await (loop conn step redeem after)
  "CONN waits for its submission's completion from the next commit quantum
(host/native/owner.lisp fnn-owner-commit-queued-locked)."
  (let ((service (fnn-mux-service loop)))
    (setf (fnn-mux-conn-await conn) (list step redeem after)
          (fnn-mux-conn-replying conn) nil)
    (let ((early (fnn-owner-await-register
                  service (fnn-mux-conn-cid conn)
                  (lambda (completion)
                    (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
                      (push (cons conn completion) (fnn-mux-loop-arrived loop)))
                    (fnn-mux-wake loop))
                  (fnn-mux-conn-socket conn))))
      (when early
        (fnn-mux-await-done loop conn early)))))

(defun fnn-mux-await-done (loop conn completion)
  "The batch answered: COMPLETION is the member's rendered completion, (:close
. OCTETS) for the uncertain line ACL2 gave it, or :uncertain (the batch's
barrier failed or another member was uncertain: no reply, the connection
closes).  The plan is ACL2's (fn-splan-step-plan), as fnn-owner-handle-chunk
builds it for a step that drained in its own quantum."
  (destructuring-bind (step redeem after) (fnn-mux-conn-await conn)
    (setf (fnn-mux-conn-await conn) nil)
    (cond ((eq completion :uncertain)
           (fnn-mux-begin-drain loop conn))
          (t
           (let* ((closing (and (consp completion) (eq (car completion) :close)))
                  (octets (if closing (cdr completion) completion)))
             (setf (fnn-mux-conn-replying conn) t)
             (fnn-mux-queue-plan loop conn
                                 (fnn-core 'fn-splan-step-plan step octets redeem)
                                 (if closing :close after)))))))

(defun fnn-mux-work (loop conn)
  "Step the held input while the connection may: serving, no reply queued,
no exposure wait pending."
  (let ((service (fnn-mux-service loop)))
    (loop while (and (eq (fnn-mux-conn-phase conn) :serving)
                     (fnn-mux-conn-input conn)
                     (null (fnn-mux-conn-out conn))
                     (null (fnn-mux-conn-await conn))
                     (null (fnn-mux-conn-resume-at conn)))
          do (when (or *fnn-sigterm-requested* (fnn-owner-service-stopping service))
               (return))
             (fnn-mux-step loop conn))))

(defun fnn-mux-readable (loop conn)
  (let* ((service (fnn-mux-service loop))
         (incoming (fnn-owner-connection-call
                    service :receive
                    (lambda ()
                      (let ((value (fnn-mux-receive-now service loop conn)))
                        (unless (or (member value '(:input :output))
                                    (typep value 'fnn-octets))
                          (error "malformed connection receive result"))
                        value)))))
    (cond ((member incoming '(:input :output))
           (setf (fnn-mux-conn-want conn) incoming))
          ((zerop (length incoming)) (fnn-mux-finish loop conn))
          (t (setf (fnn-mux-conn-want conn) nil
                   (fnn-mux-conn-input conn) incoming)
             (fnn-mux-arm-idle conn)
             (fnn-mux-work loop conn)))))

(defun fnn-mux-idle (loop conn)
  "RFC 3977 3.1's autologout, decided by ACL2 (fn-exp-idle): the close sends
nothing."
  ;; PKT-858: the idle quantum is exposure accounting only (fn-exp-idle: no
  ;; offer, no session, no store), a reader-class quantum for a peer
  ;; connection as for a reader: as :transit it waited at the gate for the
  ;; batch in flight -- the whole barrier when the disk stalls -- and held
  ;; this I/O loop, every connection it serves included (the native case
  ;; found it: the peer's IHAVE during a stall was never read).
  (if (eq (fnn-owner-exposure-idle (fnn-mux-service loop) (fnn-mux-conn-cid conn) :reader)
          :close)
      (progn (setf (fnn-mux-conn-idle-at conn) nil)
             (fnn-mux-begin-drain loop conn))
    (fnn-mux-arm-idle conn)))

(defun fnn-mux-drain-readable (loop conn)
  (let ((got (handler-case (fnn-mux-read-plain (fnn-mux-conn-fd conn))
               (fnn-os-error () (fnn-make-octets 0)))))
    (when (and (typep got 'fnn-octets) (zerop (length got)))
      (fnn-mux-finish loop conn))))

;;; The handshakes: at most +fnn-mux-handshakes-per-loop+ at once per loop.

(defun fnn-mux-request-handshake (loop conn)
  (setf (fnn-mux-conn-phase conn) :hs-wait)
  (if (< (fnn-mux-loop-handshaking loop) +fnn-mux-handshakes-per-loop+)
      (fnn-mux-start-handshake loop conn)
    (setf (fnn-mux-loop-waiting loop)
          (append (fnn-mux-loop-waiting loop) (list conn)))))

(defun fnn-mux-start-handshake (loop conn)
  (let ((service (fnn-mux-service loop)))
    (setf (fnn-mux-conn-ssl conn)
          (fnn-tls-accept-begin (fnn-owner-service-tls-context service)
                                (fnn-mux-conn-fd conn))
          (fnn-mux-conn-phase conn) :handshake
          (fnn-mux-conn-hs-deadline conn) (fnn-mux-ticks +fnn-mux-handshake-seconds+)
          (fnn-mux-conn-want conn) :input)
    (incf (fnn-mux-loop-handshaking loop))
    (fnn-mux-handshake-step loop conn)))

(defun fnn-mux-slot-free-p (loop)
  (< (fnn-mux-loop-handshaking loop) +fnn-mux-handshakes-per-loop+))

(defun fnn-mux-start-waiting-handshake (loop)
  "A slot freed: an admitted STARTTLS upgrade first, then the oldest queued
implicit-TLS socket, which is admitted now (fnn-mux-admit), just before its
handshake."
  (loop while (fnn-mux-slot-free-p loop)
        do (cond ((fnn-mux-loop-waiting loop)
                  (let ((next (pop (fnn-mux-loop-waiting loop))))
                    (fnn-mux-guarded (loop next)
                      (fnn-mux-start-handshake loop next))))
                 ((fnn-mux-loop-queued loop)
                  (let ((next (pop (fnn-mux-loop-queued loop))))
                    (setf (fnn-mux-conn-phase next) :new
                          (fnn-mux-conn-hs-deadline next) nil)
                    (fnn-mux-guarded (loop next)
                      (fnn-mux-admit loop next))))
                 (t (return)))))

(defun fnn-mux-handshake-step (loop conn)
  (let ((service (fnn-mux-service loop))
        (answer (fnn-tls-accept-step (fnn-mux-conn-ssl conn))))
    (if (member answer '(:input :output))
        (setf (fnn-mux-conn-want conn) answer)
      (let ((cid (fnn-mux-conn-cid conn)))
        ;; Only a completed SSL_accept makes the ACL2 session protected.
        (setf (fnn-mux-conn-channel conn)
              (fnn-tls-channel-of (fnn-mux-conn-ssl conn) (fnn-mux-conn-fd conn))
              (fnn-mux-conn-ssl conn) nil
              (fnn-mux-conn-phase conn) :serving
              (fnn-mux-conn-want conn) nil
              (fnn-mux-conn-hs-deadline conn) nil)
        (decf (fnn-mux-loop-handshaking loop))
        (fnn-owner-serialized
         service cid
         (lambda ()
           (unless (eq (fnn-owner-action 'fn-owner-tls-established cid) :ok)
             (fnn-fault "owner rejected established TLS")))
         (fnn-mux-conn-class conn))
        (fnn-mux-start-waiting-handshake loop)
        (let ((greeting (fnn-mux-conn-greeting conn)))
          (setf (fnn-mux-conn-greeting conn) nil)
          (cond ((and greeting (> (length greeting) 0))
                 (fnn-mux-queue loop conn greeting :send-greeting nil))
                (t (fnn-mux-after loop conn nil))))))))

(defun fnn-mux-begin (loop conn)
  "A socket a loop adopted: the handshake pool's gate, then the admission."
  (let ((socket (fnn-mux-conn-socket conn)))
    (setf (fnn-mux-conn-fd conn) (fnn-socket-fd socket))
    ;; The handshake pool bounds handshake work, and it is bounded BEFORE the
    ;; exposure admits anything (PKT-639): an implicit-TLS connection is
    ;; admitted only when a handshake slot of its loop is free, just before
    ;; SSL_accept.  Until then it waits unadmitted -- a socket and a record,
    ;; no handshake work, no share of the capacity -- in a queue of at most
    ;; +fnn-mux-queued-per-loop+ for at most the handshake deadline; past
    ;; that it is closed and named (`tls refused reason=busy' or
    ;; `reason=timeout').  So a flood of half-open handshakes holds at most
    ;; the pool's slots of the capacity and a plaintext reader is still
    ;; admitted (hostile campaign, TLS slowloris half-open x200), while a
    ;; burst of legitimate TLS readers waits its turn instead of being
    ;; refused.  Like the kernel's accept queue, it decides no protocol
    ;; answer.
    (when (and (fnn-mux-conn-implicit-tls conn) (not (fnn-mux-slot-free-p loop)))
      (if (< (length (fnn-mux-loop-queued loop)) +fnn-mux-queued-per-loop+)
          (setf (fnn-mux-conn-phase conn) :tls-queued
                (fnn-mux-conn-hs-deadline conn)
                (fnn-mux-ticks +fnn-mux-handshake-seconds+)
                (fnn-mux-loop-queued loop)
                (append (fnn-mux-loop-queued loop) (list conn)))
        (progn (fnn-mux-tls-log loop conn :busy)
               (fnn-mux-finish loop conn)))
      (return-from fnn-mux-begin nil))
    (fnn-mux-admit loop conn)))

(defun fnn-mux-admit (loop conn)
  "The accept: the peer's address, then ACL2's admission and open in one
call (books/public-exposure.lisp fn-exp-open), as the worker did it."
  (let ((service (fnn-mux-service loop))
        (socket (fnn-mux-conn-socket conn)))
    (multiple-value-bind (family address) (fnn-owner-socket-address service socket)
      (multiple-value-bind (opened greeting peerp)
          (fnn-owner-serialized
           service nil
           (lambda ()
             ;; fn-own-open pins this reading as the connection's READER
             ;; environment (DATE, NEWGROUPS).
             (fnn-owner-advance-clock)
             (let ((peer (fnn-owner-core 'fn-owner-peer-for-socket-address
                                         family address)))
               (unless (or (null peer) (fnn-octet-list-p peer))
                 (fnn-fault "owner returned a malformed peer identity"))
               (let ((opened (fnn-owner-core 'fn-owner-exposure-open
                                             family address peer)))
                 (when opened (fnn-owner-log))
                 (values opened (fnn-owner-octets-global 'fn-owner-output)
                         (and peer t)))))
           ;; The open arrived on the served socket: a reader quantum.  The
           ;; connection's later quanta carry its class (ACL2 named a peer:
           ;; :transit).
           :reader)
        (cond
          ((not (and opened (integerp opened)))
           (cond ((fnn-mux-conn-implicit-tls conn)
                  ;; PKT-639: no handshake work for a refused connection.
                  (fnn-mux-tls-log loop conn :refused)
                  (fnn-mux-finish loop conn))
                 ((> (length greeting) 0)
                  ;; RFC 3977 5.1.1 note [2]: after a 400 greeting the server
                  ;; closes the connection.
                  (setf (fnn-mux-conn-phase conn) :serving)
                  (fnn-mux-queue loop conn greeting :send-greeting :close))
                 (t (fnn-mux-finish loop conn))))
          (t
           (setf (fnn-mux-conn-cid conn) opened
                 (fnn-mux-conn-opened-cid conn) opened
                 (fnn-mux-conn-class conn) (if peerp :transit :reader))
           (if (fnn-mux-conn-implicit-tls conn)
               ;; PRF-162: the greeting is sent once the session is protected.
               (progn (setf (fnn-mux-conn-greeting conn) greeting)
                      (fnn-mux-request-handshake loop conn))
             (progn
               (setf (fnn-mux-conn-phase conn) :serving)
               (if (> (length greeting) 0)
                   (fnn-mux-queue loop conn greeting :send-greeting nil)
                 (fnn-mux-after loop conn nil))))))))))

;;; ---------------------------------------------------------------------------
;;; The loop.

(defun fnn-mux-interest (conn)
  "The poll events CONN waits for, or 0 when it waits for nothing on its
descriptor (a timer, or a step it can take now)."
  (when (fnn-mux-conn-await conn)
    ;; Waiting for its batch's completion: nothing is read or written.
    (return-from fnn-mux-interest 0))
  (let ((want (fnn-mux-conn-want conn)))
    (flet ((bits (direction)
             (if (eq direction :output) +fnn-mux-pollout+ +fnn-mux-pollin+)))
      (case (fnn-mux-conn-phase conn)
        (:draining +fnn-mux-pollin+)
        (:handshake (bits (or want :input)))
        (:serving
         (cond ((fnn-mux-conn-out conn) (bits (or want :output)))
               ((or (fnn-mux-conn-input conn) (fnn-mux-conn-resume-at conn)) 0)
               (t (bits (or want :input)))))
        (t 0)))))

(defun fnn-mux-dispatch (loop conn)
  "CONN's descriptor is ready for what it waited for (or in trouble: the
operation then observes the error or the end of input)."
  (fnn-mux-guarded (loop conn)
    (case (fnn-mux-conn-phase conn)
      (:draining (fnn-mux-drain-readable loop conn))
      (:handshake (fnn-mux-handshake-step loop conn))
      (:serving
       (if (fnn-mux-conn-out conn)
           (fnn-mux-flush loop conn)
         (fnn-mux-readable loop conn))))))

(defun fnn-mux-timers (loop now)
  "Run each connection's due timer; answer the ticks to the next one."
  (let ((next nil) (service (fnn-mux-service loop)))
    (flet ((due (at) (and at (<= at now)))
           (note (at) (when (and at (or (null next) (< at next))) (setq next at))))
      (dolist (conn (copy-list (fnn-mux-loop-conns loop)))
        (unless (eq (fnn-mux-conn-phase conn) :done)
          (fnn-mux-guarded (loop conn)
            (cond
              ((and (fnn-mux-conn-out conn) (due (fnn-mux-conn-out-deadline conn)))
               ;; fnn-send-all's deadline, in the send's own named scope.
               (fnn-owner-connection-call
                service (fnn-mux-conn-out-op conn)
                (lambda ()
                  (if (fnn-mux-conn-channel conn)
                      (error 'fnn-tls-io-error :detail "operation timed out")
                    (fnn-os-fail sb-posix:etimedout)))))
              ((and (eq (fnn-mux-conn-phase conn) :handshake)
                    (due (fnn-mux-conn-hs-deadline conn)))
               (error 'fnn-tls-handshake-error :detail "operation timed out"))
              ((and (eq (fnn-mux-conn-phase conn) :tls-queued)
                    (due (fnn-mux-conn-hs-deadline conn)))
               (fnn-mux-tls-log loop conn :timeout)
               (fnn-mux-finish loop conn))
              ((and (eq (fnn-mux-conn-phase conn) :draining)
                    (due (fnn-mux-conn-drain-deadline conn)))
               (fnn-mux-finish loop conn))
              ((and (eq (fnn-mux-conn-phase conn) :serving)
                    (due (fnn-mux-conn-resume-at conn)))
               (setf (fnn-mux-conn-resume-at conn) nil)
               (fnn-mux-work loop conn))
              ((and (eq (fnn-mux-conn-phase conn) :serving)
                    (null (fnn-mux-conn-out conn))
                    (null (fnn-mux-conn-input conn))
                    (null (fnn-mux-conn-await conn))
                    (null (fnn-mux-conn-resume-at conn))
                    (due (fnn-mux-conn-idle-at conn)))
               (fnn-mux-idle loop conn))))
          (unless (eq (fnn-mux-conn-phase conn) :done)
            (when (fnn-mux-conn-out conn) (note (fnn-mux-conn-out-deadline conn)))
            (case (fnn-mux-conn-phase conn)
              ((:handshake :tls-queued) (note (fnn-mux-conn-hs-deadline conn)))
              (:draining (note (fnn-mux-conn-drain-deadline conn)))
              (:serving (note (fnn-mux-conn-resume-at conn))
               (unless (or (fnn-mux-conn-out conn) (fnn-mux-conn-input conn)
                           (fnn-mux-conn-await conn))
                 (note (fnn-mux-conn-idle-at conn)))))))))
    next))

(defun fnn-mux-take-inbox (loop)
  (let ((new (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
               (prog1 (nreverse (fnn-mux-loop-inbox loop))
                 (setf (fnn-mux-loop-inbox loop) nil)))))
    (dolist (conn new)
      (push conn (fnn-mux-loop-conns loop))
      (fnn-mux-guarded (loop conn)
        (fnn-mux-begin loop conn)))))

(defun fnn-mux-pending-tls (loop)
  "Connections with decrypted octets already inside OpenSSL: readable now,
whatever the descriptor says."
  (remove-if-not (lambda (conn)
                   (and (eq (fnn-mux-conn-phase conn) :serving)
                        (fnn-mux-conn-channel conn)
                        (null (fnn-mux-conn-out conn))
                        (null (fnn-mux-conn-input conn))
                        (null (fnn-mux-conn-await conn))
                        (null (fnn-mux-conn-resume-at conn))
                        (fnn-tls-pending-p (fnn-mux-conn-channel conn))))
                 (fnn-mux-loop-conns loop)))

(defun fnn-mux-take-arrived (loop)
  "Build and queue the reply of every connection whose batch completed."
  (let ((arrived (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
                   (prog1 (nreverse (fnn-mux-loop-arrived loop))
                     (setf (fnn-mux-loop-arrived loop) nil)))))
    (dolist (pair arrived)
      (let ((conn (car pair)))
        (unless (eq (fnn-mux-conn-phase conn) :done)
          (fnn-mux-guarded (loop conn)
            (fnn-mux-await-done loop conn (cdr pair))))))))

(defun fnn-mux-iterate (loop)
  (fnn-mux-take-inbox loop)
  (fnn-mux-take-arrived loop)
  (let* ((next (fnn-mux-timers loop (fnn-now)))
         (pending (fnn-mux-pending-tls loop)))
    (dolist (conn pending)
      (fnn-mux-dispatch loop conn))
    (let* ((polled (remove-if (lambda (conn) (zerop (fnn-mux-interest conn)))
                              (fnn-mux-loop-conns loop)))
           (n (1+ (length polled)))
           (fds (make-array n)) (events (make-array n))
           (timeout (if (or pending
                            (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
                              (or (fnn-mux-loop-inbox loop) (fnn-mux-loop-arrived loop))))
                        0
                      (min +fnn-mux-tick-ms+
                           (if next
                               (max 0 (ceiling (* 1000 (- next (fnn-now)))
                                               internal-time-units-per-second))
                             +fnn-mux-tick-ms+)))))
      (setf (aref fds 0) (fnn-mux-loop-wake-read loop)
            (aref events 0) +fnn-mux-pollin+)
      (loop for conn in polled for i from 1
            do (setf (aref fds i) (fnn-mux-conn-fd conn)
                     (aref events i) (fnn-mux-interest conn)))
      (let ((revents (progn (setf (fnn-mux-loop-polling loop) t)
                            ;; A committer waiting for this loop's pass sees
                            ;; it idle now (fnn-owner-loops-passed-p).
                            (fnn-mux-signal-committer loop)
                            (unwind-protect (fnn-mux-poll fds events timeout)
                              (setf (fnn-mux-loop-polling loop) nil)))))
        (unless (zerop (aref revents 0)) (fnn-mux-drain-wake loop))
        (loop for conn in polled for i from 1
              unless (or (zerop (aref revents i))
                         (eq (fnn-mux-conn-phase conn) :done))
                do (fnn-mux-dispatch loop conn)))))
  ;; PKT-875: what this loop still owes its clients, for a stop's drain.
  (let ((owed (count-if (lambda (conn)
                          (and (not (eq (fnn-mux-conn-phase conn) :done))
                               (or (fnn-mux-conn-await conn)
                                   (and (fnn-mux-conn-replying conn)
                                        (fnn-mux-conn-out conn)))))
                        (fnn-mux-loop-conns loop))))
    (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
      (setf (fnn-mux-loop-unsent loop) owed)))
  ;; A pass is complete: every connection ready in it was stepped.  A
  ;; committer waiting for the passes (format 9) looks again.
  (incf (fnn-mux-loop-passes loop))
  (fnn-mux-signal-committer loop))

(defun fnn-mux-unsent (service)
  "PKT-875: the replies the I/O loops still owe (a stop's drain observation):
per loop, its connections with output or a completion awaited at its last
pass, and the completions handed to it and not yet taken."
  (loop for loop in (fnn-owner-service-mux service)
        sum (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
              (+ (fnn-mux-loop-unsent loop)
                 (length (fnn-mux-loop-arrived loop))
                 (length (fnn-mux-loop-inbox loop))))))

(defun fnn-mux-signal-committer (loop)
  "Wake a committer waiting on this loop's pass (format 9, a submission
queued); nothing otherwise."
  (let ((service (fnn-mux-service loop)))
    (when (and (fnn-owner-service-batching service)
               (plusp (fnn-owner-service-queued service)))
      (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
        (sb-thread:condition-broadcast (fnn-owner-service-commit-ready service))))))

(defun fnn-mux-stop-loop (loop)
  "The service is stopping: deliver what a connection still has queued,
including the completions a batch's COMPLETE handed this loop before the stop
(the connections whose replies report an uncertain outcome are the sockets
the stop spared, fnn-owner-stop-service-locked), then end every connection."
  (let ((service (fnn-mux-service loop)))
    (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
      (setf (fnn-mux-loop-conns loop)
            (append (fnn-mux-loop-inbox loop) (fnn-mux-loop-conns loop))
            (fnn-mux-loop-inbox loop) nil))
    ;; A batch's COMPLETE that stops the service (books/owner-commit-steps.lisp
    ;; fn-ocs-member-releases under :stop: every member answered uncertain)
    ;; delivers each member's ACL2-rendered reply to this loop's ARRIVED list
    ;; and only then stops.  The loop may see the stop before it takes them:
    ;; build and queue them here, so the uncertain reply reaches the wire
    ;; below instead of a bare close (test_native_owner's two-client case).
    (fnn-mux-take-arrived loop)
    ;; One deadline for all of them, as the workers' sends ran in parallel
    ;; under one 10 s each: a stop never waits longer on its loops' output.
    (let ((deadline (fnn-mux-ticks +fnn-mux-send-seconds+)))
      (dolist (conn (copy-list (fnn-mux-loop-conns loop)))
        (when (and (fnn-mux-conn-out conn) (fnn-mux-conn-fd conn))
          (ignore-errors
            (fnn-owner-send (fnn-mux-conn-fd conn) (fnn-mux-conn-channel conn)
                            (subseq (fnn-mux-conn-out conn) (fnn-mux-conn-out-at conn))
                            (fnn-seconds-to-deadline deadline))))
        (fnn-mux-finish loop conn)))
    (ignore-errors (sb-posix:close (fnn-mux-loop-wake-read loop)))
    (ignore-errors (sb-posix:close (fnn-mux-loop-wake-write loop)))
    service))

(defun fnn-mux-run (loop)
  (let ((service (fnn-mux-service loop)))
    (unwind-protect
         (handler-case
             (loop
               ;; PKT-875: a SIGTERM does not end the loop: the stop's drain
               ;; (host/native/owner.lisp fnn-owner-drain-service) needs it to
               ;; deliver the replies of the batches in flight; no new input
               ;; is stepped (fnn-mux-work).  The fence ends it.
               (when (fnn-owner-service-stopping service)
                 (return))
               (fnn-mux-iterate loop))
           (serious-condition (e)
             ;; Every connection event is guarded; what reaches here is a
             ;; defect of the loop itself, which serves every connection it
             ;; holds: the whole service stops (exit 4).
             (fnn-owner-fault-service service nil e)))
      (fnn-mux-stop-loop loop)
      (fnn-with-roster (service)
        (setf (fnn-owner-service-workers service)
              (delete sb-thread:*current-thread*
                      (fnn-owner-service-workers service) :test #'eq))))))

(defun fnn-mux-start (service)
  "Start the loops; each is a worker, so the stop joins it."
  (fnn-with-roster (service)
    (unless (fnn-owner-service-mux service)
      (let ((loops
              (loop repeat +fnn-mux-loops+
                    collect (multiple-value-bind (r w) (sb-posix:pipe)
                              (fnn-set-nonblocking r)
                              (fnn-set-nonblocking w)
                              (%make-fnn-mux-loop :service service
                                                  :wake-read r :wake-write w)))))
        (setf (fnn-owner-service-mux service) loops)
        (dolist (loop loops)
          (let ((thread (sb-thread:make-thread (lambda () (fnn-mux-run loop))
                                               :name "fn owner io")))
            (setf (fnn-mux-loop-thread loop) thread)
            (push thread (fnn-owner-service-workers service))))))))

(defun fnn-mux-adopt (service socket &optional implicit-tls done)
  "Hand SOCKET to a loop (round-robin).  Registered as a client first, so a
stop shuts it down whichever thread holds it."
  (let ((loop nil))
    (fnn-with-roster (service)
      (if (or (fnn-owner-service-stopping service)
              (null (fnn-owner-service-mux service)))
          (progn (ignore-errors (fnn-socket-shut socket))
                 (when done (sb-thread:signal-semaphore done)))
        (let ((loops (fnn-owner-service-mux service)))
          (push socket (fnn-owner-service-clients service))
          (setq loop (nth (mod (fnn-owner-service-mux-next service) (length loops))
                          loops))
          (incf (fnn-owner-service-mux-next service)))))
    (when loop
      (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
        (push (%make-fnn-mux-conn :socket socket :implicit-tls implicit-tls
                                  :done done)
              (fnn-mux-loop-inbox loop)))
      (fnn-mux-wake loop))
    loop))

(defun fnn-mux-serve-once (service socket)
  "`once': serve this one client on a loop and return when it is done."
  (let ((done (sb-thread:make-semaphore :name "fn owner once")))
    (fnn-mux-adopt service socket nil done)
    (loop until (sb-thread:wait-on-semaphore done :timeout 1))))

;;; ---------------------------------------------------------------------------
;;; The connection budget (books/connection-budget.lisp): observed here,
;;; decided there, once per run after recovery and before listen.

(defun fnn-mux-thread-stack-octets ()
  (sb-alien:extern-alien "thread_control_stack_size" sb-alien:unsigned-long))

;;; The control socket's client threads.  host/native/control.lisp binds this
;;; to ACL2's ceiling (fn-native-control-host-max-active-clients) around the
;;; run it starts; an image without the control module (the DTN build), and
;;; the launcher's probe, count the most that ceiling allows.
(defvar *fnn-mux-control-clients* 64)

(defun fnn-mux-thread-count (service)
  "ACL2's count of the node's threads (books/heap-reservation.lisp
fn-heap-thread-count: the fixed threads, the I/O loops and the control
clients' ceiling), the one the launcher's reservation holds; the host's own
constants must agree with it or the budget is refused as a fault."
  (declare (ignore service))
  (let ((threads (fnn-core 'fn-heap-thread-count 0)))
    (unless (and (= +fnn-mux-loops+ (fnn-core 'fn-heap-mux-loops))
                 (>= threads (+ +fnn-mux-fixed-threads+ +fnn-mux-loops+
                                (min *fnn-mux-control-clients*
                                     (fnn-core 'fn-native-control-max-active-clients)))))
      (fnn-fault "the host's thread constants disagree with ACL2's thread count"))
    threads))

(defun fnn-mux-budget-install (service tls-context)
  "ACL2 decides whether this machine holds the live capacity; a refusal is
the run's (exit 1), named on stderr and in the service log."
  (let* ((store (fnn-owner-service-store service))
         (decision
           (fnn-owner-serialized
            service nil
            (lambda ()
              (fnn-owner-core 'fn-owner-connection-budget
                              (fnn-heap-machine-octets)
                              (sb-ext:dynamic-space-size)
                              (fnn-heap-core-octets)
                              (fnn-mux-thread-count service)
                              (fnn-mux-thread-stack-octets)
                              +fnn-gc-nursery-octets+
                              (fnn-store-config store)
                              (and tls-context t)))))
         (line (fnn-global 'fn-owner-connection-budget-line)))
    (unless (and (member decision '(:hold :refused)) (fnn-octet-list-p line))
      (fnn-fault "owner returned a malformed connection budget"))
    (fnn-log-line line)
    (when (eq decision :refused)
      (fnn-refuse "~a" (map 'string #'code-char line)))
    decision))
