;;; Shared local-control I/O primitives; no workers or owner dispatch.
;;; Extracted unchanged so NNTP and serialized BP use the same lease,
;;; credential observation, input bound and absolute I/O deadlines.
(in-package "ACL2")

(defconstant +fnn-control-io-seconds+ 10)

(defstruct (fnn-control-state (:constructor %make-fnn-control-state))
  path listener accept-thread service
  (lock (sb-thread:make-mutex :name "fn local control"))
  (workers nil) (clients nil) (stopping nil) (max-clients 0)
  (read-maximum 0)
  device inode lease-path lease-fd)

(defmacro fnn-with-control ((control) &body body)
  `(sb-thread:with-mutex ((fnn-control-state-lock ,control)) ,@body))

(defvar *fnn-control-buffer-lock*
  (sb-thread:make-mutex :name "fn local control buffer")
  "The control buffer's lock (io.lisp fnn-live-octets-ctl): a client's frame is
filled and decoded under it, before any owner work; never held across the
owner mutex.")

(defmacro fnn-with-control-buffer (() &body body)
  `(sb-thread:with-mutex (*fnn-control-buffer-lock*) ,@body))

(defun fnn-control-socket-path-p (info)
  (and info (sb-posix:s-issock (sb-posix:stat-mode info))))

(defun fnn-control-remove-stale (path)
  "Remove only an old socket node after the control-path lease is held."
  (let ((info (fnn-lstat path)))
    (when info
      (unless (fnn-control-socket-path-p info)
        (fnn-refuse "control path exists and is not a socket: ~a" path))
      (fnn-unlink path))))

(defun fnn-control-acquire-lease (control)
  "Hold the ACL2-derived adjacent lease before inspecting the socket name."
  (let ((lease-path (fnn-control-state-lease-path control))
        (fd nil))
    (unless lease-path
      (fnn-fault "ACL2 refused the control lease path"))
    (handler-case
        (progn
          (setq fd (fnn-open lease-path
                             (logior sb-posix:o-rdwr sb-posix:o-creat
                                     +fnn-o-nofollow+)
                             #o600))
          (unless (fnn-regular-p (fnn-fstat fd))
            (fnn-refuse "control lease is not regular: ~a" lease-path))
          (fnn-flock fd (logior +fnn-lock-ex+ +fnn-lock-nb+))
          (setf (fnn-control-state-lease-path control) lease-path
                (fnn-control-state-lease-fd control) fd)
          fd)
      (error (condition)
        (when fd (ignore-errors (fnn-close fd)))
        (fnn-refuse "control path is already owned: ~a (~a)"
                    (fnn-control-state-path control) condition)))))

(defun fnn-control-release-lease (control)
  (let ((fd (fnn-control-state-lease-fd control)))
    (when fd
      (setf (fnn-control-state-lease-fd control) nil)
      (ignore-errors (fnn-flock fd +fnn-lock-un+))
      (ignore-errors (fnn-close fd)))))

(defun fnn-control-remove-stale-offline (path-octets)
  "Remove a crashed owner's socket node for an offline verb (PKT-344), after
ACL2 decided :stale (fn-native-control-liveness).  Performed as
`fnn-control-listen' does: under the ACL2-derived control-path lease, so an
owner that starts meanwhile (it takes the lease before it binds) is never
unlinked; the lease is released before the verb runs."
  (let* ((lease-octets (fnn-core 'fn-native-control-host-lease-path
                                 (fnn-octet-list path-octets)))
         (lease-path (and (fnn-octet-list-p lease-octets)
                          (fnn-octets-string (fnn-octets lease-octets))))
         (control (%make-fnn-control-state
                   :path (fnn-octets-string path-octets)
                   :lease-path lease-path)))
    (unwind-protect
         (progn (fnn-control-acquire-lease control)
                (fnn-control-remove-stale (fnn-control-state-path control)))
      (fnn-control-release-lease control))))

(defun fnn-control-listen (path)
  (fnn-control-remove-stale path)
  (let ((listener (make-instance 'sb-bsd-sockets:local-socket
                                 :type :stream :protocol 0)))
    (handler-case
        (progn
          ;; S102/S143: the node is born 0600 (bind under umask 0077), so no
          ;; window exists between bind and the chmod below.
          (let ((old-umask (sb-posix:umask #o077)))
            (unwind-protect
                 (sb-bsd-sockets:socket-bind listener path)
              (sb-posix:umask old-umask)))
          (sb-bsd-sockets:socket-listen listener 16)
          ;; The accept owner polls a nonblocking listener with a one-second
          ;; ceiling.  Stop remains shutdown-only, yet close can join accept
          ;; even on platforms where shutdown does not wake a listening
          ;; accept immediately.
          (fnn-set-nonblocking (fnn-socket-fd listener))
          (fnn-chmod path #o600)
          listener)
      (error (condition)
        (fnn-socket-shut listener)
        (when (fnn-control-socket-path-p (fnn-lstat path))
          (ignore-errors (fnn-unlink path)))
        (error condition)))))

(defun fnn-control-join-chunks (chunks total)
  "Copy a reverse list of retained chunks once into its exact final vector."
  (let ((joined (fnn-make-octets total)) (offset 0))
    (dolist (chunk (nreverse chunks) joined)
      (replace joined chunk :start1 offset)
      (incf offset (length chunk)))))

(defun fnn-control-read-frame (socket maximum
                               &optional (seconds +fnn-control-io-seconds+))
  "Read one half-closed frame under one deadline and retained-input bound.
SECONDS is the deadline; a consumer wait's client allows its timeout more."
  (unless (and (integerp maximum) (>= maximum 0))
    (fnn-fault "invalid local-control frame maximum"))
  (let ((fd (fnn-socket-fd socket))
        (chunks nil) (total 0)
        (deadline (+ (fnn-now)
                     (* seconds internal-time-units-per-second))))
    (loop
      (let ((remaining-seconds (fnn-seconds-to-deadline deadline)))
        (when (<= remaining-seconds 0) (return :timeout))
        ;; The extra byte distinguishes exact-bound EOF from overbound input;
        ;; no recv buffer or retained chunk can exceed that sentinel request.
        (let* ((sentinel (1+ (- maximum total)))
               (part (fnn-recv fd remaining-seconds
                               (min +fnn-max-read+ sentinel))))
          (when (eq part :timeout) (return :timeout))
          (when (zerop (length part))
            (return (fnn-control-join-chunks chunks total)))
          (incf total (length part))
          (when (< maximum total) (return :overbound))
          (push part chunks))))))

(defun fnn-control-peer-is-owner-p (socket)
  "Bind the local-control principal to the process's effective UID.

Darwin and OpenBSD getpeereid and Linux SO_PEERCRED observe credentials on
the connected Unix socket. A failed observation refuses. The first value preserves the E2
same-owner gate; the second carries the authenticated numeric UID for ACL2's
separate local topic administrator binding. The OS supplies that observation,
not a topic or consumer authority decision."
  #+(or darwin openbsd)
  (sb-alien:with-alien ((peer-uid sb-alien:unsigned-int)
                        (peer-gid sb-alien:unsigned-int))
    (let ((result
            (sb-alien:alien-funcall
             (sb-alien:extern-alien
              "getpeereid"
              (function sb-alien:int sb-alien:int
                        (* sb-alien:unsigned-int)
                        (* sb-alien:unsigned-int)))
             (fnn-socket-fd socket)
             (sb-alien:addr peer-uid) (sb-alien:addr peer-gid))))
      (if (and (zerop result) (= peer-uid (sb-posix:geteuid)))
          (values t peer-uid)
        (values nil nil))))
  #+linux
  (handler-case
      ;; Linux ucred is three 32-bit fields: pid, uid, gid.  SOL_SOCKET=1 and
      ;; SO_PEERCRED=17 are the Linux socket ABI constants.  Check optlen so
      ;; a short or failed observation cannot authenticate a caller.  Linux
      ;; also returns the socket creator's own credentials on an unconnected
      ;; listener; getpeername must establish a connected peer first.
      (progn
        (sb-bsd-sockets:socket-peername socket)
        (sb-alien:with-alien ((credentials (sb-alien:array sb-alien:unsigned-int 3))
                            (length sb-alien:unsigned-int 12))
        (let ((result
                (sb-alien:alien-funcall
                 (sb-alien:extern-alien
                  "getsockopt"
                  (function sb-alien:int sb-alien:int sb-alien:int
                            sb-alien:int (* sb-alien:unsigned-int)
                            (* sb-alien:unsigned-int)))
                 (fnn-socket-fd socket) 1 17
                 (sb-alien:addr (sb-alien:deref credentials 0))
                 (sb-alien:addr length))))
          (if (and (zerop result) (= length 12))
              (let ((uid (sb-alien:deref credentials 1)))
                (if (= uid (sb-posix:geteuid))
                    (values t uid)
                  (values nil nil)))
            (values nil nil)))))
    (error () (values nil nil)))
  #-(or darwin linux openbsd)
  (let ((ignored socket)) (declare (ignore ignored))
    (values nil nil)))

(defun fnn-control-connect (path)
  (let ((socket (make-instance 'sb-bsd-sockets:local-socket
                               :type :stream :protocol 0)))
    (handler-case
        (progn (sb-bsd-sockets:socket-connect socket path) socket)
      (error (condition)
        (fnn-socket-shut socket)
        (error condition)))))

(defun fnn-control-send-request (socket fd octets)
  "Send one request frame and half-close.  PKT-182: when the frame is past the
owner's read bound the owner answers it (refused, `fnn-control-read-frame's
:overbound) and stops reading, so the rest of this write fails; the owner's
reply is already queued on the connection, so the failed write is not the
exchange's end: the caller reads the reply frame either way, and only a
missing or undecodable reply leaves the outcome to the transport stage
(uncertain)."
  (when (handler-case (progn (fnn-send-all fd octets +fnn-control-io-seconds+) t)
          (error () nil))
    (sb-bsd-sockets:socket-shutdown socket :direction :output))
  nil)

(defun fnn-control-transport-outcome (stage)
  (fnn-core 'fn-native-control-host-transport-outcome stage))

(defun fnn-control-exchange (path request-list &optional maximum seconds)
  "One connection: send REQUEST-LIST's octets, read the one reply frame.
Answers (values FRAME STAGE): FRAME the reply octets or NIL, STAGE the
transport stage reached (fn-native-control-transport-outcome's input).
MAXIMUM and SECONDS are the reply's bound and deadline (ACL2's command-frame
bound and ACL2's submission-sized observation policy when omitted).
This is only a client wait budget; expiry after submission remains uncertain."
  (let ((socket nil) (stage :before-submission))
    (unwind-protect
         (handler-case
             (progn
               (setq socket (fnn-control-connect path))
               (let* ((fd (fnn-socket-fd socket))
                      (request (fnn-octets request-list))
                      (reply-seconds
                        (or seconds
                            (fnn-core 'fn-native-control-host-reply-seconds
                                      (length request)))))
                 ;; Any failure from here may follow a partial write.
                 (setq stage :after-submission)
                 (fnn-control-send-request socket fd request)
                 (let ((frame (fnn-control-read-frame
                               socket
                               (or maximum
                                   (fnn-core 'fn-native-control-host-max-frame))
                               reply-seconds)))
                   (values (and (typep frame 'fnn-octets) frame) stage))))
           (error () (values nil stage)))
      (when socket (fnn-socket-shut socket)))))

(defun fnn-control-plain-status (frame stage)
  (let ((status (and frame
                     (fnn-core 'fn-native-control-host-reply-decode
                               (fnn-octet-list frame)))))
    (if (member status (fnn-core 'fn-native-control-host-statuses))
        status
      (fnn-control-transport-outcome stage))))

(defun fnn-control-reasoned-exchange (path reasoned-list plain-thunk)
  "PKT-453 (a): ask with the reasoned request; answer (values STATUS WORD).

ACL2 reads the reply and names the step (fn-native-control-reasoned-client-
step): the owner's status and reason word; a resend of the plain request once,
when an old owner refused the reasoned frame it could not decode (it acted on
nothing); or the transport outcome of the stage reached.  WORD is ACL2's
octets, or NIL.  PLAIN-THUNK encodes the plain request, only for a resend."
  (multiple-value-bind (frame stage) (fnn-control-exchange path reasoned-list)
    (let ((step (if frame
                    (fnn-core 'fn-native-control-host-lined-client-step
                              (fnn-octet-list frame))
                  '(:transport))))
      (case (first step)
        ;; LINE: the owner's sentence (kind 23), or NIL.
        (:status (values (second step) (third step) (fourth step)))
        (:resend (multiple-value-bind (plain plain-stage)
                     (let ((plain (funcall plain-thunk)))
                       (unless (fnn-octet-list-p plain)
                         (fnn-fault "ACL2 refused the plain control request"))
                       (fnn-control-exchange path plain))
                   (values (fnn-control-plain-status plain plain-stage) nil)))
        ;; No reply: ACL2's outcome of the stage reached and its word
        ;; (no-owner when the connect itself failed).
        (t (values (fnn-control-transport-outcome stage)
                   (fnn-core 'fn-native-control-host-transport-word stage)))))))

(defun fnn-control-admin (path-octets argv)
  "Send one ACL2-bounded administrative vector to the live owner.
Answers (values STATUS WORD LINE): WORD is ACL2's reason word (PKT-453 (a)),
LINE the owner's sentence when its reply carried one (kind 23), else NIL."
  (let ((reasoned (fnn-core 'fn-native-control-host-reasoned-admin-encode argv)))
    (unless (fnn-octet-list-p reasoned)
      (fnn-fault "ACL2 refused normalized live administration"))
    (fnn-control-reasoned-exchange
     (fnn-octets-string path-octets) reasoned
     (lambda () (fnn-core 'fn-native-control-host-admin-encode argv)))))
