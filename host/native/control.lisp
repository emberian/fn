;;; Native bounded local-control transport for exact article submission.
;;;
;;; ACL2 owns the FNCT request/reply grammar, bounds, status vocabulary and
;;; exit projection in books/native-control.lisp.  This raw module only moves
;;; those octets over one AF_UNIX stream and invokes the serialized owner
;;; callback.  It never opens the Store and has no direct-store fallback.

(in-package "ACL2")

(defconstant +fnn-control-io-seconds+ 10)
(defvar *fnn-hybrid-control-handler* nil)

(defstruct (fnn-control-state (:constructor %make-fnn-control-state))
  path listener accept-thread service
  (lock (sb-thread:make-mutex :name "fn local control"))
  (workers nil) (clients nil) (stopping nil) (max-clients 0)
  (read-maximum 0)
  device inode lease-path lease-fd)

(defmacro fnn-with-control ((control) &body body)
  `(sb-thread:with-mutex ((fnn-control-state-lock ,control)) ,@body))

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

(defun fnn-control-listen (path)
  (fnn-control-remove-stale path)
  (let ((listener (make-instance 'sb-bsd-sockets:local-socket
                                 :type :stream :protocol 0)))
    (handler-case
        (progn
          (sb-bsd-sockets:socket-bind listener path)
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

(defun fnn-control-read-frame (socket maximum)
  "Read one half-closed frame under one deadline and retained-input bound."
  (unless (and (integerp maximum) (>= maximum 0))
    (fnn-fault "invalid local-control frame maximum"))
  (let ((fd (fnn-socket-fd socket))
        (chunks nil) (total 0)
        (deadline (+ (fnn-now)
                     (* +fnn-control-io-seconds+
                        internal-time-units-per-second))))
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

(defun fnn-control-reply-octets (status)
  (let ((reply
          (cond
            ;; The owner's FNLS page, already sealed by ACL2
            ;; (`fn-native-live-status-host-reply').
            ((and (consp status) (eq (first status) :live-status-reply))
             (second status))
            ((and (consp status) (eq (first status) :topic-reply))
             (fnn-core 'fn-native-control-host-topic-reply-encode
                       (second status)))
            ((and (consp status) (eq (first status) :consumer-poll-reply))
             (fnn-core 'fn-native-control-host-consumer-poll-reply-encode
                       (second status) (third status) (fourth status)))
            ((and (consp status) (eq (first status) :consumer-status-reply))
             (fnn-core 'fn-native-control-host-consumer-status-reply-encode
                       (second status) (third status) (fourth status)
                       (fifth status)))
            ((and (consp status) (eq (first status) :consumer-reply))
             (fnn-core 'fn-native-control-host-consumer-reply-encode
                       (second status) (third status)))
            (t (fnn-core 'fn-native-control-host-reply-encode status)))))
    (unless (fnn-octet-list-p reply)
      (fnn-fault "ACL2 refused a local-control reply status"))
    (fnn-octets reply)))

(defun fnn-control-peer-is-owner-p (socket)
  "Bind the local-control principal to the process's effective UID.

Darwin getpeereid and Linux SO_PEERCRED observe credentials on the connected
Unix socket. A failed observation refuses. The first value preserves the E2
same-owner gate; the second carries the authenticated numeric UID for ACL2's
separate local topic administrator binding. The OS supplies that observation,
not a topic or consumer authority decision."
  #+darwin
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
  #-(or darwin linux)
  (let ((ignored socket)) (declare (ignore ignored))
    (values nil nil)))

(defun fnn-control-stop-cut-armed-p ()
  "Whether FN_NATIVE_CONTROL_TEST_STOP arms the developer stop cut.

The variable is read only through `fnn-developer-selector', which answers NIL
on a production image; a production image never gets this far with it set,
because `fnn-developer-selector-gate' refuses to start (host/native/io.lisp).
So this function has no production branch, and the reply below has no
production conversion: an earlier version faulted here, after the owner had
already made the article durable, and the caller got exit 4 for an accepted
article (campaign dabebb84, F4)."
  (let ((raw (fnn-developer-selector "FN_NATIVE_CONTROL_TEST_STOP")))
    (when raw
      (unless (string= raw "after-submit")
        (fnn-fault "unknown FN_NATIVE_CONTROL_TEST_STOP cut: ~a" raw))
      t)))

(defun fnn-control-stop-calling-thread ()
  "Stop the process with a SIGSTOP directed at the calling thread.

A process-directed kill(getpid(), SIGSTOP) is delivered to whichever thread
the kernel picks (the main thread first, when it can take it), and the group
stop reaches this worker only asynchronously: the worker could return and
send its reply before it stopped (campaign dabebb84, F3; 2 of 5 clients got
ACCEPTED by hand).  pthread_kill(pthread_self(), SIGSTOP) queues the signal
on this thread, which dequeues it on its return from the syscall and starts
the group stop itself, so no instruction after this call runs until SIGCONT."
  (let ((code (sb-alien:alien-funcall
               (sb-alien:extern-alien "pthread_kill"
                                      (function sb-alien:int sb-alien:unsigned-long
                                                sb-alien:int))
               (sb-alien:alien-funcall
                (sb-alien:extern-alien "pthread_self"
                                       (function sb-alien:unsigned-long)))
               sb-posix:sigstop)))
    ;; This runs on a client worker after the owner answered; a failed stop
    ;; is reported and the reply goes out with the owner's own status.
    (unless (zerop code)
      (fnn-err "developer stop cut: pthread_kill returned ~d" code))))

(defun fnn-control-test-after-submit (status)
  "Developer-only process-stop cut after owner completion, before the reply."
  (when (and (fnn-control-stop-cut-armed-p)
             (member status '(:accepted :duplicate :refused :clock-unusable
                              :article-exceeds-profile-bound)))
    (fnn-out "CONTROL-SUBMITTED")
    (fnn-control-stop-calling-thread)))

(defun fnn-control-send-reply (socket status)
  "Transport ACL2's sealed status; the caller retains socket ownership."
  (handler-case
      (let ((fd (fnn-socket-fd socket)))
        (fnn-send-all fd (fnn-control-reply-octets status)
                      +fnn-control-io-seconds+)
        (fnn-graceful-close fd))
    (error () nil)))

(defun fnn-control-answering (control socket)
  "Withdraw SOCKET from the set a stop wakes, once its whole frame is read.

`fnn-control-stop' shuts every socket in that set so that a worker blocked in
its read returns.  A worker that has read its frame is no longer blocked on
the socket; it is computing the reply, and the request it is answering may be
the very one whose fault or uncertain observation stops the owner.  Shutting
its socket then threw away the owner's own terminal word: on the dabebb84
image a live `group create' that faulted the owner before publishing anything
reached the operator as a closed connection, which the client can only call
uncertain (exit 3), not the fault (exit 4) the owner had classified.  The
worker still ends its I/O under the reply deadline and `fnn-control-close'
joins it before the process exits."
  (fnn-with-control (control)
    (setf (fnn-control-state-clients control)
          (delete socket (fnn-control-state-clients control) :test #'eq))))

(defun fnn-control-live-status-answer (service request)
  "The running owner's page of its status report, under the owner mutex.

ACL2 decodes the request and renders the report from the Store, the
configuration and the connection pins the owner carries
(`fn-native-live-status-host-reply'); the wrapper returns no `state', so
answering changes nothing the owner holds.  The mutex only keeps a page from
observing a half-applied transition."
  (fnn-with-owner (service)
    (when (fnn-owner-service-stopping service)
      (fnn-refuse "owner service is stopping"))
    (let ((reply (fnn-core 'fn-native-live-status-host-reply request
                           (fnn-store-observation
                            (fnn-owner-service-store service))
                           *the-live-state*)))
      (unless (fnn-octet-list-p reply)
        (fnn-fault "ACL2 returned a malformed live status page"))
      reply)))

(defun fnn-control-handle-client (control socket)
  (let* ((service (fnn-control-state-service control))
         (maximum (fnn-control-state-read-maximum control))
         (status
           (handler-case
               (let* ((frame (prog1 (fnn-control-read-frame socket maximum)
                               (fnn-control-answering control socket)))
                      (request
                        (and (typep frame 'fnn-octets)
                             (fnn-core 'fn-native-control-host-request-decode
                                       (fnn-octet-list frame))))
                      (admin
                        (and (typep frame 'fnn-octets)
                             (fnn-core 'fn-native-control-host-admin-decode
                                       (fnn-octet-list frame))))
                      (topic
                        (and (typep frame 'fnn-octets)
                             (fnn-core 'fn-native-control-host-topic-request-decode
                                       (fnn-octet-list frame))))
                      (consumer
                        (and (typep frame 'fnn-octets)
                             (fnn-core 'fn-native-control-host-consumer-request-decode
                                       (fnn-octet-list frame))))
                      (live
                        (and (typep frame 'fnn-octets)
                             (fnn-core 'fn-native-live-status-host-requestp
                                       (fnn-octet-list frame)))))
                 (cond
                   (live
                    (list :live-status-reply
                          (fnn-control-live-status-answer
                           service (fnn-octet-list frame))))
                   ((and *fnn-hybrid-control-handler*
                         (funcall *fnn-hybrid-control-handler* service frame)))
                   ((and (consp topic) (eq (first topic) :topic))
                    (multiple-value-bind (owner-p uid)
                        (fnn-control-peer-is-owner-p socket)
                      (if owner-p
                          (list :topic-reply
                                (fnn-owner-topic-local-serialized
                                 service (second topic) (third topic)
                                 (fourth topic) uid))
                        (list :topic-reply :refused))))
                   ((and (consp consumer) (eq (car consumer) :consumer))
                      (if (fnn-control-peer-is-owner-p socket)
                        (fnn-owner-consumer-local-serialized
                         service (second consumer) (third consumer)
                         (fourth consumer))
                      (case (second consumer)
                        (:poll (list :consumer-poll-reply :refused nil nil))
                        (:status (list :consumer-status-reply :refused nil nil nil))
                        (otherwise (list :consumer-reply :refused nil)))))
                   ((and (consp request) (eq (car request) :request))
                    (let ((msgid (second request))
                         (groups (third request))
                         (article (fourth request)))
                     (unless (and (fnn-octet-list-p msgid)
                                  (listp groups)
                                  (every #'fnn-octet-list-p groups)
                                  (fnn-octet-list-p article))
                       (fnn-fault "ACL2 returned a malformed control request"))
                     (fnn-owner-control-submit-serialized
                      service (fnn-octets msgid)
                      (mapcar #'fnn-octets groups) (fnn-octets article))))
                   ((and (consp admin) (eq (car admin) :admin))
                    (fnn-owner-live-admin-serialized service (second admin)))
                   (t :refused)))
             ;; The owner has already fenced itself on these two (exit 3 and
             ;; exit 4, `fnn-owner-shared-action-locked'); the reason goes to
             ;; the owner's log, and the caller gets the status word.
             (fnn-store-indeterminate (condition)
               (fnn-err "control request uncertain; owner fenced: ~a" condition)
               :uncertain)
             (fnn-store-fault (condition)
               (fnn-err "control request fault; owner stopped: ~a" condition)
               :fault)
             (fnn-store-error () :refused)
             (fnn-os-error () :refused)
             (sb-bsd-sockets:socket-error () :refused)
             (error (condition)
               (fnn-owner-fault-service service nil condition)
               :fault))))
    ;; A peer that disappears here creates no uncertainty for the owner: the
    ;; status already records its durable observation.  The client, which did
    ;; not receive it, conservatively reports :uncertain.
    (fnn-control-test-after-submit
     (if (and (consp status) (eq (first status) :live-status-reply))
         nil
     (if (and (consp status)
              (member (first status)
                      '(:topic-reply :consumer-reply :consumer-poll-reply
                        :consumer-status-reply)))
         (second status) status)))
    (fnn-control-send-reply socket status)))

(defun fnn-control-client-done (control socket)
  (fnn-with-control (control)
    (setf (fnn-control-state-clients control)
          (delete socket (fnn-control-state-clients control) :test #'eq)
          (fnn-control-state-workers control)
          (delete sb-thread:*current-thread*
                  (fnn-control-state-workers control) :test #'eq))))

(defun fnn-control-launch-client (control socket)
  (let ((disposition nil))
    (fnn-with-control (control)
      (cond ((fnn-control-state-stopping control)
             (setq disposition :stopping))
            ((>= (length (fnn-control-state-workers control))
                 (fnn-control-state-max-clients control))
             (setq disposition :busy))
            (t
             (push socket (fnn-control-state-clients control))
             (let ((worker
                     (sb-thread:make-thread
                      (lambda ()
                        (unwind-protect
                             (fnn-control-handle-client control socket)
                          (fnn-socket-shut socket)
                          (fnn-control-client-done control socket)))
                      :name "fn local control client")))
               (push worker (fnn-control-state-workers control))
               (setq disposition :launched)))))
    (case disposition
      (:stopping (fnn-socket-shut socket))
      (:busy
       ;; The accept thread owns an over-ceiling socket and can return ACL2's
       ;; bounded BUSY frame without spawning an untracked worker.
       (unwind-protect (fnn-control-send-reply socket :busy)
         (fnn-socket-shut socket))))))

(defun fnn-control-accept-loop (control)
  (let ((listener (fnn-control-state-listener control)))
    (loop
      (when (fnn-with-control (control)
              (fnn-control-state-stopping control))
        (return))
      (handler-case
          (let ((socket (fnn-accept-observe listener 1)))
            (unless (eq socket :timeout)
              (fnn-control-launch-client control socket)))
          (sb-bsd-sockets:socket-error (condition)
            (unless (fnn-with-control (control)
                      (fnn-control-state-stopping control))
              (fnn-owner-fault-service
               (fnn-control-state-service control) nil condition))
            (return))
          (error (condition)
            (fnn-owner-fault-service
             (fnn-control-state-service control) nil condition)
            (return))))))

(defun fnn-control-start (control service posting-enabledp)
  (let ((configured
          (fnn-owner-serialized
           service nil
           (lambda ()
             (fnn-owner-action 'fn-owner-posting-configure posting-enabledp)))))
    (unless (eq configured :configured)
      (fnn-fault "owner refused ACL2 posting policy")))
  ;; The read bound of one control connection, from the profile the owner
  ;; carries (fixed while it runs): ACL2's `fn-nctrl-read-bound-for' of the
  ;; profile's article and group bounds, or its hybrid twin when hybrid
  ;; control is built in.
  (let* ((bounds (fnn-owner-serialized
                  service nil
                  (lambda () (fnn-owner-core 'fn-owner-control-profile-bounds))))
         (a (first bounds)) (g (second bounds))
         (maximum (if (fboundp 'fn-native-hybrid-control-host-read-bound)
                      (fnn-core 'fn-native-hybrid-control-host-read-bound a g)
                    (fnn-core 'fn-native-control-host-read-bound a g))))
    (unless (and (integerp maximum) (> maximum 0))
      (fnn-fault "ACL2 returned no control read bound"))
    (setf (fnn-control-state-read-maximum control) maximum))
  (fnn-control-acquire-lease control)
  (let* ((path (fnn-control-state-path control))
         (listener (fnn-control-listen path))
         (info (fnn-lstat path)))
    (unless (fnn-control-socket-path-p info)
      (fnn-socket-shut listener)
      (fnn-fault "control socket did not appear at configured path"))
    (setf (fnn-control-state-service control) service
          (fnn-control-state-listener control) listener
          (fnn-control-state-device control) (sb-posix:stat-dev info)
          (fnn-control-state-inode control) (sb-posix:stat-ino info)
          (fnn-control-state-accept-thread control)
          (sb-thread:make-thread
           (lambda () (fnn-control-accept-loop control))
           :name "fn local control accept"))
    (fnn-out "CONTROL ~a" path)))

(defun fnn-control-stop (control service)
  (declare (ignore service))
  (let ((listener nil) (clients nil) (first nil))
    (fnn-with-control (control)
      (unless (fnn-control-state-stopping control)
        (setf (fnn-control-state-stopping control) t
              listener (fnn-control-state-listener control)
              clients (copy-list (fnn-control-state-clients control))
              first t)))
    (when first
      (when listener
        (ignore-errors
          (sb-bsd-sockets:socket-shutdown listener :direction :io)))
      (dolist (socket clients)
        ;; Shutdown wakes the blocked read without releasing the descriptor;
        ;; the owning worker performs the sole final close after its I/O ends.
        (ignore-errors
          (sb-bsd-sockets:socket-shutdown socket :direction :io))))))

(defun fnn-control-close (control service)
  (declare (ignore service))
  (unwind-protect
       (progn
         (let ((accept-thread (fnn-control-state-accept-thread control)))
           (when accept-thread (sb-thread:join-thread accept-thread)))
         (loop
           (let ((workers
                   (fnn-with-control (control)
                     (copy-list (fnn-control-state-workers control)))))
             (when (null workers) (return))
             (dolist (worker workers) (sb-thread:join-thread worker))))
         (let ((listener (fnn-control-state-listener control)))
           (when listener
             (setf (fnn-control-state-listener control) nil)
             (fnn-socket-shut listener)))
         (let* ((path (fnn-control-state-path control))
                (info (fnn-lstat path)))
           (when (and (fnn-control-socket-path-p info)
                      (= (sb-posix:stat-dev info)
                         (fnn-control-state-device control))
                      (= (sb-posix:stat-ino info)
                         (fnn-control-state-inode control)))
             (fnn-unlink path))))
    (fnn-control-release-lease control)))

(defun fnn-control-owner-run-normalized
    (store-octets listener-host-octets listener-port oncep max-connections
     control-path-octets posting-enabledp &optional tls-context)
  "Add composable lifecycle hooks while leaving owner normalization intact."
  (unless (and (typep control-path-octets 'fnn-octets)
               (> (length control-path-octets) 0)
               (member posting-enabledp '(t nil)))
    (fnn-fault "malformed ACL2 control run plan"))
  (let* ((max-clients
           (fnn-core 'fn-native-control-host-max-active-clients))
         (lease-octets
           (fnn-core 'fn-native-control-host-lease-path
                     (fnn-octet-list control-path-octets)))
         (lease-path
           (and (fnn-octet-list-p lease-octets)
                (fnn-octets-string (fnn-octets lease-octets))))
         (control (%make-fnn-control-state
                   :path (fnn-octets-string control-path-octets)
                   :lease-path lease-path
                   :max-clients max-clients))
         (*fnn-owner-start-hooks*
           (append *fnn-owner-start-hooks*
                   (list (lambda (service)
                           (fnn-control-start control service posting-enabledp)))))
         (*fnn-owner-stop-hooks*
           (append *fnn-owner-stop-hooks*
                   (list (lambda (service)
                           (fnn-control-stop control service)))))
         (*fnn-owner-close-hooks*
           (append *fnn-owner-close-hooks*
                   (list (lambda (service)
                           (fnn-control-close control service))))))
    (unless (and (integerp max-clients) (< 0 max-clients 65))
      (fnn-fault "ACL2 returned an invalid control client ceiling"))
    (unless lease-path
      (fnn-fault "ACL2 refused the control lease path"))
    ;; A developer image validates its control stop selector here, before
    ;; the store opens, so a malformed value never surfaces on a worker after
    ;; a durable submission.
    (fnn-control-stop-cut-armed-p)
    (fnn-owner-run-normalized store-octets listener-host-octets listener-port
                              oncep max-connections tls-context)))

(defun fnn-control-connect (path)
  (let ((socket (make-instance 'sb-bsd-sockets:local-socket
                               :type :stream :protocol 0)))
    (handler-case
        (progn (sb-bsd-sockets:socket-connect socket path) socket)
      (error (condition)
        (fnn-socket-shut socket)
        (error condition)))))

(defun fnn-control-transport-outcome (stage)
  (fnn-core 'fn-native-control-host-transport-outcome stage))

(defun fnn-control-admin (path-octets argv)
  "Send one ACL2-bounded administrative vector to the live owner."
  (let ((request-list
          (fnn-core 'fn-native-control-host-admin-encode argv))
        (socket nil) (stage :before-submission))
    (unless (fnn-octet-list-p request-list)
      (fnn-fault "ACL2 refused normalized live administration"))
    (unwind-protect
         (handler-case
             (progn
               (setq socket (fnn-control-connect
                             (fnn-octets-string path-octets)))
               (let ((fd (fnn-socket-fd socket)))
                 (setq stage :after-submission)
                 (fnn-send-all fd (fnn-octets request-list)
                               +fnn-control-io-seconds+)
                 (sb-bsd-sockets:socket-shutdown socket :direction :output)
                 (let* ((frame (fnn-control-read-frame
                                socket (fnn-core
                                        'fn-native-control-host-max-frame)))
                        (status (and (typep frame 'fnn-octets)
                                     (fnn-core
                                      'fn-native-control-host-reply-decode
                                      (fnn-octet-list frame)))))
                   (if (member status (fnn-core 'fn-native-control-host-statuses))
                       status
                     (fnn-control-transport-outcome stage)))))
           (error () (fnn-control-transport-outcome stage)))
      (when socket (fnn-socket-shut socket)))))

(defun fnn-control-topic-local (path-octets operation sequence quota)
  "Send an ACL2-framed local topic operation to the authenticated owner."
  (let ((request-list
          (fnn-core 'fn-native-control-host-topic-request-encode
                    operation sequence quota))
        (socket nil) (stage :before-submission))
    (unless (fnn-octet-list-p request-list)
      (fnn-fault "ACL2 refused local topic request"))
    (unwind-protect
         (handler-case
             (progn
               (setq socket (fnn-control-connect
                             (fnn-octets-string path-octets)))
               (let ((fd (fnn-socket-fd socket)))
                 (setq stage :after-submission)
                 (fnn-send-all fd (fnn-octets request-list)
                               +fnn-control-io-seconds+)
                 (sb-bsd-sockets:socket-shutdown socket :direction :output)
                 (let* ((frame (fnn-control-read-frame
                                socket (fnn-core
                                        'fn-native-control-host-max-frame)))
                        (reply (and (typep frame 'fnn-octets)
                                    (fnn-core
                                     'fn-native-control-host-topic-reply-decode
                                     (fnn-octet-list frame))))
                        (ordinary
                          (and (typep frame 'fnn-octets)
                               (fnn-core 'fn-native-control-host-reply-decode
                                         (fnn-octet-list frame)))))
                   (cond
                    ((and (consp reply) (eq (first reply) :topic-reply)
                          (member (second reply)
                                  '(:accepted :replayed-historical
                                    :refused :uncertain :fault)))
                     (second reply))
                    ((member ordinary '(:refused :uncertain :fault :busy))
                     (if (eq ordinary :busy) :refused ordinary))
                    (t (fnn-control-transport-outcome stage))))))
           (error () (fnn-control-transport-outcome stage)))
      (when socket (fnn-socket-shut socket)))))

(defun fnn-control-consumer-local (path-octets operation first second)
  "Exchange one ACL2-framed consumer command with the 0600 owner socket."
  (let ((request-list
          (fnn-core 'fn-native-control-host-consumer-request-encode
                    operation first second))
        (socket nil) (stage :before-submission))
    (unless (fnn-octet-list-p request-list)
      (fnn-fault "ACL2 refused local consumer request"))
    (unwind-protect
         (handler-case
             (progn
               (setq socket (fnn-control-connect
                             (fnn-octets-string path-octets)))
               (let ((fd (fnn-socket-fd socket)))
                 (setq stage :after-submission)
                 (fnn-send-all fd (fnn-octets request-list)
                               +fnn-control-io-seconds+)
                 (sb-bsd-sockets:socket-shutdown socket :direction :output)
                 (let* ((frame (fnn-control-read-frame
                                socket (fnn-core
                                        (case operation
                                          (:poll
                                           'fn-native-control-host-consumer-poll-max-frame)
                                          (:status
                                           'fn-native-control-host-consumer-status-max-frame)
                                          (otherwise
                                           'fn-native-control-host-max-frame)))))
                        (reply (and (typep frame 'fnn-octets)
                                    (fnn-core
                                     (case operation
                                       (:poll
                                        'fn-native-control-host-consumer-poll-reply-decode)
                                       (:status
                                        'fn-native-control-host-consumer-status-reply-decode)
                                       (otherwise
                                        'fn-native-control-host-consumer-reply-decode))
                                     (fnn-octet-list frame))))
                        (ordinary-status
                          (and (typep frame 'fnn-octets)
                               (fnn-core 'fn-native-control-host-reply-decode
                                         (fnn-octet-list frame)))))
                   (if (and (consp reply)
                            (eq (first reply)
                                (case operation
                                  (:poll :consumer-poll-reply)
                                  (:status :consumer-status-reply)
                                  (otherwise :consumer-reply)))
                            (member (second reply)
                                    '(:accepted :refused :uncertain :fault))
                            (if (eq operation :status)
                                (or (and (eq (second reply) :accepted)
                                         (every (lambda (value)
                                                  (and (integerp value)
                                                       (not (minusp value))))
                                                (cddr reply)))
                                    (and (eq (second reply) :refused)
                                         (null (third reply))
                                         (null (fourth reply))
                                         (null (fifth reply))))
                              (and (fnn-octet-list-p (third reply))
                                   (or (not (eq operation :poll))
                                       (fnn-octet-list-p (fourth reply)))))
                            )
                       reply
                     (list (case operation
                             (:poll :consumer-poll-reply)
                             (:status :consumer-status-reply)
                             (otherwise :consumer-reply))
                           (if (member ordinary-status
                                       '(:refused :uncertain :fault :busy))
                               (if (eq ordinary-status :busy)
                                   :refused ordinary-status)
                             (fnn-control-transport-outcome stage))
                           nil nil nil)))))
           (error ()
             (list (case operation
                     (:poll :consumer-poll-reply)
                     (:status :consumer-status-reply)
                     (otherwise :consumer-reply))
                   (fnn-control-transport-outcome stage) nil nil nil)))
      (when socket (fnn-socket-shut socket)))))

(defun fnn-control-submit (path-octets msgid-octets group-octets payload-path-octets)
  "Submit one exact bounded file; return ACL2's status keyword."
  (let* ((path (fnn-octets-string path-octets))
         (payload-path (fnn-octets-string payload-path-octets))
         (maximum-article (fnn-core 'fn-native-control-host-max-article))
         (article (fnn-read-regular-bounded payload-path maximum-article))
         (request-list
           (fnn-core 'fn-native-control-host-request-encode
                     (fnn-octet-list msgid-octets)
                     (mapcar #'fnn-octet-list group-octets)
                     (fnn-octet-list article))))
    (unless (fnn-octet-list-p request-list)
      (fnn-fault "ACL2 refused normalized control submission"))
    (let ((socket nil) (stage :before-submission))
      (unwind-protect
           (handler-case
               (progn
                 (setq socket (fnn-control-connect path))
                 (let ((fd (fnn-socket-fd socket)))
                   ;; Any failure from here may follow a partial write.
                   (setq stage :after-submission)
                   (fnn-send-all fd (fnn-octets request-list)
                                 +fnn-control-io-seconds+)
                   (sb-bsd-sockets:socket-shutdown socket :direction :output)
                   (let* ((frame
                            (fnn-control-read-frame
                             socket (fnn-core 'fn-native-control-host-max-frame)))
                          (status
                            (and (typep frame 'fnn-octets)
                                 (fnn-core 'fn-native-control-host-reply-decode
                                           (fnn-octet-list frame)))))
                     (if (member status
                                 (fnn-core 'fn-native-control-host-statuses))
                         status
                       (fnn-control-transport-outcome stage)))))
             (error () (fnn-control-transport-outcome stage)))
        (when socket (fnn-socket-shut socket))))))

(defun fnn-control-live-status-page (path-octets kind offset)
  "Ask the owner for one page of report KIND from OFFSET.

The reply octets, or the stage at which the exchange failed
(:before-submission, :after-submission), or :refused when the owner answered
an ordinary refusal (it is stopping)."
  (let ((request (fnn-core 'fn-native-live-status-host-request-encode kind offset))
        (socket nil) (stage :before-submission))
    (unless (fnn-octet-list-p request)
      (fnn-fault "ACL2 refused a live status request"))
    (unwind-protect
         (handler-case
             (progn
               (setq socket (fnn-control-connect (fnn-octets-string path-octets)))
               (let ((fd (fnn-socket-fd socket)))
                 (setq stage :after-submission)
                 (fnn-send-all fd (fnn-octets request) +fnn-control-io-seconds+)
                 (sb-bsd-sockets:socket-shutdown socket :direction :output)
                 (let ((frame (fnn-control-read-frame
                               socket (fnn-core 'fn-native-live-status-host-max-frame))))
                   (if (typep frame 'fnn-octets)
                       (let ((octets (fnn-octet-list frame)))
                         (if (member (fnn-core 'fn-native-control-host-reply-decode octets)
                                     '(:refused :busy))
                             :refused
                           octets))
                     stage))))
           (error () stage))
      (when socket (fnn-socket-shut socket)))))

(defun fnn-control-live-status (path-octets kind)
  "Join the owner's pages of report KIND through `fn-nls-client-step'.

(:done OCTETS), or an outcome keyword for `fn-nls-route'.  A page that fails
after the first was answered is :after-submission: the owner was there."
  (let ((acc nil) (total nil) (digest nil) (restarts 0)
        (limit (fnn-core 'fn-native-live-status-host-max-restarts)))
    (loop
      (let ((page (fnn-control-live-status-page path-octets kind (length acc))))
        (when (keywordp page)
          (return (if (and (eq page :before-submission)
                           (or acc (plusp restarts)))
                      :after-submission
                    page)))
        (let ((step (fnn-core 'fn-native-live-status-host-client-step
                              acc total digest page)))
          (case (first step)
            (:done (return step))
            (:next (setq acc (second step) total (third step) digest (fourth step)))
            (:restart
             (when (>= (incf restarts) limit) (return :after-submission))
             (setq acc nil total nil digest nil))
            (:refused (return :refused))
            (t (return :after-submission))))))))
