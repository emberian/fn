;;; BP's sole-writer local control: a synchronous turn, never a worker.
(in-package "ACL2")

(defstruct fnn-bpnc control model owner listeners)
(defvar *fnn-bpnode-control-pump* nil)

(defun fnn-bpnc-step (node event)
  (setf (fnn-bpnc-model node)
        (fnn-core 'fn-bpnc-socket-step (fnn-bpnc-model node) event)))

(defun fnn-bpnc-release-lease (control)
  "Observe unlock/close completion; never retry a possibly retired descriptor."
  (let ((fd (fnn-control-state-lease-fd control)))
    (when fd
      (setf (fnn-control-state-lease-fd control) nil)
      (unwind-protect (fnn-flock fd +fnn-lock-un+) (fnn-close fd)))))

(defun fnn-bpnc-retire (node)
  (let* ((control (fnn-bpnc-control node))
         (failure nil))
    (fnn-bpnc-step node '(:stop))
    (let ((action (fnn-core 'fn-bpnc-socket-action (fnn-bpnc-model node))))
      (when (eq (first action) :retire)
        (handler-case
            (progn
              (let ((listener (fnn-control-state-listener control)))
                (when listener
                  (setf (fnn-control-state-listener control) nil)
                  (sb-bsd-sockets:socket-close listener)))
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
              (fnn-bpnc-release-lease control))
          (error (condition)
            (setq failure condition)
            (ignore-errors (fnn-bpnc-release-lease control))))
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

(defun fnn-bpnc-drive-after (owner node)
  "The listener drive, off the owner mutex.  A condition leaving it is
re-signalled inside a settle quantum, so the one envelope classifies it
(fn-fs-classify over its concrete class) and fences before that mutex is
released, as it did when the drive ran in the reconfiguration's own section."
  (handler-case
      (let ((*fnn-bplc-test-change* t))
        (fnn-bplc-cut (fnn-bpnc-listeners node) :configuration-published)
        (fnn-bplc-drive (fnn-bpnc-listeners node) owner))
    (serious-condition (condition)
      (fnn-quantum-bp owner nil (lambda () (error condition))))))

(defun fnn-bpnc-execute (node grant)
  (if (not (eq (first grant) :execute))
      (list :reason :refused (second grant))
    (let ((owner (fnn-bpnc-owner node)) (plan (second grant)) (drive-after nil))
      (if (eq (fnn-owner-disk-admit owner) :shed)
          :busy
        (let ((answer
                (fnn-owner-live-reconfigure (run drive fnn-quantum-bp owner nil)
                    (word reason)
                  :stage (lambda (pcid) (fnn-owner-result 'fn-ores-config-result-p 'fn-native-admin-host-owner-reconfigure pcid plan))
                  :before (progn
                            (fnn-rc-begin run nil)
                            (drive))
                  :continue
                  (cond ((eq word :refused) (list :reason :refused reason))
                        ((eq word :accepted)
                         ;; Durable configuration is already published.  The
                         ;; model begins its change here (it reads the owner
                         ;; configuration); the drive runs after release.
                         (when (fnn-bpnc-listeners node)
                           (when *fnn-section-step*
                             (fnn-fault "BP listener drive deferred inside an open durable window"))
                           (fnn-bplc-begin-locked (fnn-bpnc-listeners node))
                           (setq drive-after t))
                         :accepted)
                        (t word)))))
          (when drive-after (fnn-bpnc-drive-after owner node))
          answer)))))

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
                            (handler (and decoded (ninth decoded))))
                       (setq reasoned (first decoded))
                       ;; The same FNCT kind table and read handlers as the
                       ;; NNTP owner, including the bounded decided-profile
                       ;; read (26). BP mutations keep their own turn plan.
                       (or (and ownerp (eq handler :read)
                                *fnn-hybrid-control-handler*
                                (let ((*fnn-control-frame-list* nil))
                                  (funcall *fnn-hybrid-control-handler*
                                           (fnn-bpnc-owner node) frame)))
                           (fnn-bpnc-execute
                            node (fnn-owner-core 'fn-owner-bplc-turn-plan
                                  ownerp (third decoded)
                                  (and (fnn-bpnc-listeners node)
                                       (fnn-bplc-model (fnn-bpnc-listeners node)))))))
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
                  ;; A read handler's reply is already sealed whole by ACL2
                  ;; (the decided profile, FNCT 27; the live status page);
                  ;; every other status is the BP turn's word, as before.
                  ;; (control.lisp's full reply dispatcher is not in the DTN
                  ;; build; this owner needs only these three shapes.)
                  (octets (cond ((and (consp status)
                                      (member (first status) '(:sealed-reply :live-status-reply)))
                                 (second status))
                                ((and (consp status) (not (eq (first status) :reason)))
                                 (fnn-fault "BP control has no encoder for reply ~s" (first status)))
                                (reasoned (fnn-core 'fn-native-control-host-lined-reply-encode
                                                    word reason nil))
                                (t (fnn-core 'fn-native-control-host-reply-encode word))))
                  (reply (if (fnn-octet-list-p octets)
                             (fnn-octets octets)
                           (fnn-fault "ACL2 refused a BP local-control reply status"))))
             ;; A lost answer does not change a durable admin completion.
             (ignore-errors
               (fnn-send-all (fnn-socket-fd socket) reply
                             +fnn-control-io-seconds+)))
           (when fatal (error fatal)))
      (sb-bsd-sockets:socket-close socket))))

(defun fnn-bpnc-pump (node &optional (timeout-ms 0))
  "At most one local request per BP scheduling boundary."
  (let ((listener (fnn-control-state-listener (fnn-bpnc-control node))))
    (when (and listener
               (fnn-poll-readable (list (fnn-socket-fd listener)) timeout-ms))
      (let ((got (fnn-accept-attempt listener)))
        (if (keywordp got)
            (fnn-accept-backoff got 1)
          (fnn-bpnc-handle node got))))))

(defun fnn-bpnc-wait-input (node fd seconds)
  "Poll BP and control under the caller's unchanged absolute read deadline."
  (let ((deadline (+ (fnn-now) (* seconds internal-time-units-per-second)))
        (zero-poll (zerop seconds)))
    (loop
      (let* ((remaining (fnn-seconds-to-deadline deadline))
             (control (fnn-control-state-listener (fnn-bpnc-control node))))
        (when (and (<= remaining 0) (not zero-poll)) (return nil))
        (setq zero-poll nil)
        ;; BP wins a tie: a stream of control requests cannot starve input.
        (let ((index (fnn-poll-readable
                      (list fd (fnn-socket-fd control))
                      (ceiling (* 1000 remaining)))))
          (cond ((eql index 0) (return t))
                ((eql index 1) (fnn-bpnc-pump node))
                (t (return nil))))))))

(defun fnn-bpnc-accept-loop (node listeners handler once &key progress pending)
  "One writer: accept only the ACL2 installed listener generation."
  (loop
    (when node (fnn-bpnc-pump node))
    (when progress (funcall progress) (sb-thread:thread-yield))
    (let* ((live (fnn-bplc-live listeners))
           (index (fnn-poll-readable
                   (mapcar #'fnn-socket-fd live)
                   (if (and pending (funcall pending)) 0 100))))
      (when index
        (let ((plan (fnn-core 'fn-bplc-accept-plan (fnn-bplc-model listeners) index)))
          (unless plan (fnn-fault "ACL2 refused BP acceptance in this listener phase"))
          ;; An attempt that took no connection (fnn-accept-attempt) is no
          ;; accept: the model is not stepped and ONCE still waits for one.
          (let ((socket (fnn-accept-attempt (nth index live))))
            (if (keywordp socket)
                (fnn-accept-backoff socket 1)
              (progn
                (fnn-bplc-step listeners (list :accept-result index :ok))
                (fnn-out "~a" (fnn-core 'fn-bplc-runtime-line (fnn-bplc-model listeners)))
                (unwind-protect (funcall handler socket)
                  (fnn-bplc-step listeners '(:session-closed)))
                (when once
                  ;; Diagnostic one-contact mode completes retained local
                  ;; work after the socket closes. Each iteration is still a
                  ;; separate turn, with control and scheduler yield.
                  (loop while (and pending (funcall pending)) do
                    (when node (fnn-bpnc-pump node))
                    (when progress (funcall progress))
                    (sb-thread:thread-yield))
                  (return))))))))))
