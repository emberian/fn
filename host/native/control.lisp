;;; Native bounded local-control transport for exact article submission.
;;;
;;; ACL2 owns the FNCT request/reply grammar, bounds, status vocabulary and
;;; exit projection in books/native-control.lisp.  This raw module only moves
;;; those octets over one AF_UNIX stream and invokes the serialized owner
;;; callback.  It never opens the Store and has no direct-store fallback.

(in-package "ACL2")

(defconstant +fnn-control-io-seconds+ 10)

(defstruct (fnn-control-state (:constructor %make-fnn-control-state))
  path listener accept-thread service
  (lock (sb-thread:make-mutex :name "fn local control"))
  (workers nil) (clients nil) (stopping nil)
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

(defun fnn-control-append (left right maximum)
  (let ((total (+ (length left) (length right))))
    (when (< maximum total)
      (return-from fnn-control-append :overbound))
    (let ((joined (fnn-make-octets total)))
      (replace joined left)
      (replace joined right :start1 (length left))
      joined)))

(defun fnn-control-read-frame (socket maximum)
  "Read one half-closed request/reply, bounded before each allocation."
  (let ((fd (fnn-socket-fd socket)) (all (fnn-make-octets 0)))
    (loop
      (let ((part (fnn-recv fd +fnn-control-io-seconds+)))
        (when (eq part :timeout) (return :timeout))
        (when (zerop (length part)) (return all))
        (setq all (fnn-control-append all part maximum))
        (when (eq all :overbound) (return :overbound))))))

(defun fnn-control-reply-octets (status)
  (let ((reply (fnn-core 'fn-native-control-host-reply-encode status)))
    (unless (fnn-octet-list-p reply)
      (fnn-fault "ACL2 refused a local-control reply status"))
    (fnn-octets reply)))

(defun fnn-control-test-after-submit (status)
  "Developer-only deterministic process-death cut after owner completion."
  (when (and (member status '(:accepted :duplicate :refused))
             (string= (or (sb-ext:posix-getenv
                           "FN_NATIVE_CONTROL_TEST_STOP") "")
                      "after-submit"))
    (fnn-out "CONTROL-SUBMITTED")
    (sb-posix:kill (sb-posix:getpid) sb-posix:sigstop)))

(defun fnn-control-handle-client (control socket)
  (let* ((service (fnn-control-state-service control))
         (maximum (fnn-core 'fn-native-control-host-max-frame))
         (status
           (handler-case
               (let* ((frame (fnn-control-read-frame socket maximum))
                      (request
                        (and (typep frame 'fnn-octets)
                             (fnn-core 'fn-native-control-host-request-decode
                                       (fnn-octet-list frame)))))
                 (if (not (and (consp request) (eq (car request) :request)))
                     :refused
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
                      (mapcar #'fnn-octets groups) (fnn-octets article)))))
             (fnn-store-indeterminate () :uncertain)
             (fnn-store-fault () :fault)
             (fnn-store-error () :refused)
             (fnn-os-error () :refused)
             (sb-bsd-sockets:socket-error () :refused)
             (error (condition)
               (fnn-owner-fault-service service nil condition)
               :fault))))
    (fnn-control-test-after-submit status)
    ;; A peer that disappears here creates no uncertainty for the owner: the
    ;; status already records its durable observation.  The client, which did
    ;; not receive it, conservatively reports :uncertain.
    (handler-case
        (let ((fd (fnn-socket-fd socket)))
          (fnn-send-all fd (fnn-control-reply-octets status)
                        +fnn-control-io-seconds+)
          (fnn-graceful-close fd))
      (error () nil))))

(defun fnn-control-client-done (control socket)
  (fnn-with-control (control)
    (setf (fnn-control-state-clients control)
          (delete socket (fnn-control-state-clients control) :test #'eq)
          (fnn-control-state-workers control)
          (delete sb-thread:*current-thread*
                  (fnn-control-state-workers control) :test #'eq))))

(defun fnn-control-launch-client (control socket)
  (fnn-with-control (control)
    (if (fnn-control-state-stopping control)
        (fnn-socket-shut socket)
      (progn
        (push socket (fnn-control-state-clients control))
        (let ((worker
                (sb-thread:make-thread
                 (lambda ()
                   (unwind-protect
                        (fnn-control-handle-client control socket)
                     (fnn-socket-shut socket)
                     (fnn-control-client-done control socket)))
                 :name "fn local control client")))
          (push worker (fnn-control-state-workers control)))))))

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
        ;; close(2) from another thread does not reliably interrupt its
        ;; blocked read on Linux.  Shutdown first while this socket object
        ;; still owns the descriptor, then close; the first-call guard above
        ;; prevents any later stop from touching a reused descriptor.
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
     control-path-octets posting-enabledp)
  "Add composable lifecycle hooks while leaving owner normalization intact."
  (unless (and (typep control-path-octets 'fnn-octets)
               (> (length control-path-octets) 0)
               (member posting-enabledp '(t nil)))
    (fnn-fault "malformed ACL2 control run plan"))
  (let* ((lease-octets
           (fnn-core 'fn-native-control-host-lease-path
                     (fnn-octet-list control-path-octets)))
         (lease-path
           (and (fnn-octet-list-p lease-octets)
                (fnn-octets-string (fnn-octets lease-octets))))
         (control (%make-fnn-control-state
                   :path (fnn-octets-string control-path-octets)
                   :lease-path lease-path))
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
    (unless lease-path
      (fnn-fault "ACL2 refused the control lease path"))
    (fnn-owner-run-normalized store-octets listener-host-octets listener-port
                              oncep max-connections)))

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
                                 '(:accepted :duplicate :refused :busy
                                   :uncertain :fault))
                         status
                       (fnn-control-transport-outcome stage)))))
             (error () (fnn-control-transport-outcome stage)))
        (when socket (fnn-socket-shut socket))))))
