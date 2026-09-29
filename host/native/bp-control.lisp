;;; BP's sole-writer local control: a synchronous turn, never a worker.
(in-package "ACL2")

(defstruct fnn-bpnc control model owner)
(defvar *fnn-bpnode-control-pump* nil)

(defun fnn-bpnc-step (node event)
  (setf (fnn-bpnc-model node)
        (fnn-core 'fn-bpnc-socket-step (fnn-bpnc-model node) event)))

(defun fnn-bpnc-retire (node)
  (let* ((control (fnn-bpnc-control node))
         (failure nil))
    (fnn-bpnc-step node '(:stop))
    (let ((action (fnn-core 'fn-bpnc-socket-action (fnn-bpnc-model node))))
      (when (eq (first action) :retire)
        (handler-case
            (progn
              (when (fnn-control-state-listener control)
                (fnn-socket-shut (fnn-control-state-listener control))
                (setf (fnn-control-state-listener control) nil))
              ;; Remove only the socket inode this run installed.  Retain
              ;; the path lease until that removal has finished.
              (let* ((path (fnn-octets-string (fnn-octets (second action))))
                     (info (fnn-lstat path)))
                (when (and (fnn-control-socket-path-p info)
                           (eql (sb-posix:stat-dev info)
                                (fnn-control-state-device control))
                           (eql (sb-posix:stat-ino info)
                                (fnn-control-state-inode control)))
                  (fnn-unlink path)))
              (fnn-control-release-lease control))
          (error (condition)
            (setq failure condition)
            (fnn-control-release-lease control)))
        (fnn-bpnc-step node (list :retire-result (if failure :failed :ok)))
        (when failure (error failure))))))

(defun fnn-bpnc-start (config-path store-root owner)
  (let* ((plan (fnn-core 'fn-bpnc-startup
                         (fnn-operator-read-config
                          config-path (fnn-core 'fn-bpnc-config-bound))
                         (fnn-octet-list (fnn-string-octets store-root))))
         (model (fnn-core 'fn-bpnc-socket-initial plan))
         (action (fnn-core 'fn-bpnc-socket-action model)))
    (unless (eq (first action) :bind)
      (fnn-refuse "BP control startup refused: ~a" (second plan)))
    (let* ((control (%make-fnn-control-state
                     :path (fnn-octets-string (fnn-octets (second action)))
                     :lease-path (fnn-octets-string (fnn-octets (third action)))))
           (node (make-fnn-bpnc :control control :model model :owner owner)))
      (handler-case
          (progn
            (fnn-control-acquire-lease control)
            (setf (fnn-control-state-listener control)
                  (fnn-control-listen (fnn-control-state-path control)))
            (let ((info (fnn-lstat (fnn-control-state-path control))))
              (unless (fnn-control-socket-path-p info)
                (fnn-fault "BP control bound path is not a socket"))
              (setf (fnn-control-state-device control) (sb-posix:stat-dev info)
                    (fnn-control-state-inode control) (sb-posix:stat-ino info)))
            (fnn-bpnc-step node '(:bind-result :ok))
            (let ((install (fnn-core 'fn-bpnc-socket-action (fnn-bpnc-model node))))
              (unless (eq (first install) :install)
                (fnn-fault "ACL2 refused BP control installation"))
              (setf (fnn-control-state-read-maximum control) (third install)))
            (fnn-bpnc-step node '(:install-result :ok))
            (fnn-out "BP NODE CONTROL ~a" (fnn-control-state-path control))
            node)
        (error (condition)
          (fnn-bpnc-step node '(:bind-result :failed))
          (fnn-bpnc-step node '(:install-result :failed))
          (fnn-bpnc-retire node)
          (error condition))))))

(defun fnn-bpnc-execute (node grant)
  (if (not (eq (first grant) :execute))
      (list :reason :refused (second grant))
    (let ((owner (fnn-bpnc-owner node)) (plan (second grant)))
      (if (eq (fnn-owner-disk-admit owner) :shed)
          :busy
        (fnn-owner-serialized
         owner nil
         (lambda ()
           (multiple-value-bind (word reason)
               (fnn-owner-live-reconfigure-locked
                owner
                (lambda (cid)
                  (fnn-owner-result 'fn-ores-config-result-p
                                    'fn-native-admin-host-owner-reconfigure cid plan)))
             (if (eq word :refused) (list :reason :refused reason) word))))))))

(defun fnn-bpnc-handle (node socket)
  (let ((reasoned nil) (fatal nil))
    (unwind-protect
         (let ((status
                 (handler-case
                     (let* ((ownerp (fnn-control-peer-is-owner-p socket))
                            ;; Reject credentials before consuming input.
                            ;; One bounded frame under one absolute deadline.
                            (frame (and ownerp
                                        (fnn-control-read-frame
                                         socket
                                         (fnn-control-state-read-maximum
                                          (fnn-bpnc-control node)))))
                            (decoded
                              (and (typep frame 'fnn-octets)
                                   (fnn-with-control-buffer ()
                                     (fnn-core 'fn-native-control-host-decode-frame
                                               (fnn-octets-ctl-fill frame)))))
                            (grant (fnn-core 'fn-bpnc-turn-plan ownerp (third decoded))))
                       (setq reasoned (first decoded))
                       (fnn-bpnc-execute node grant))
                   (fnn-store-indeterminate (condition)
                     (setq fatal condition) :uncertain)
                   (fnn-store-fault (condition)
                     (setq fatal condition) :fault)
                   (fnn-store-error ()
                     (list :reason :refused
                           (fnn-core 'fn-native-control-host-refusal-reason :store-error)))
                   (sb-bsd-sockets:socket-error ()
                     (list :reason :refused
                           (fnn-core 'fn-native-control-host-refusal-reason :socket-error)))
                   (error (condition)
                     (setq fatal condition)
                     (fnn-owner-fault-service (fnn-bpnc-owner node) nil condition)
                     :fault))))
           (let* ((word (if (consp status) (second status) status))
                  (reason (and (consp status) (third status)))
                  (reply (if reasoned
                             (fnn-core 'fn-native-control-host-lined-reply-encode
                                       word reason nil)
                           (fnn-core 'fn-native-control-host-reply-encode word))))
             ;; A lost answer does not change a durable admin completion.
             (ignore-errors
               (fnn-send-all (fnn-socket-fd socket) (fnn-octets reply)
                             +fnn-control-io-seconds+)))
           (when fatal (error fatal)))
      (fnn-socket-shut socket))))

(defun fnn-bpnc-pump (node &optional (timeout-ms 0))
  "At most one local request per BP scheduling boundary."
  (let ((listener (fnn-control-state-listener (fnn-bpnc-control node))))
    (when (and listener
               (fnn-poll-readable (list (fnn-socket-fd listener)) timeout-ms))
      (fnn-bpnc-handle node (sb-bsd-sockets:socket-accept listener)))))

(defun fnn-bpnc-accept-loop (node listeners handler once)
  "One writer: alternate one control turn with one accepted BP session."
  (if (null node)
      (fnn-accept-any-loop listeners handler once)
    (let ((fds (mapcar #'fnn-socket-fd listeners)))
      (loop
        (fnn-bpnc-pump node)
        (let ((index (fnn-poll-readable fds 100)))
          (when index
            (funcall handler (sb-bsd-sockets:socket-accept (nth index listeners)))
            (when once (return))))))))
