;;; BP listener handles follow the serialized ACL2 installation carry.
(in-package "ACL2")
(defstruct fnn-bplc model mode (owned nil) (live nil))
(defvar *fnn-bplc-test-change* nil)

(defun fnn-bplc-step (node event)
  (setf (fnn-bplc-model node)
        (fnn-core 'fn-bplc-step (fnn-bplc-model node) event)))

(defun fnn-bplc-close-all (node)
  ;; Remove ownership before each close: an ambiguous close is never retried
  ;; against a descriptor that the kernel may already have reused.
  (let ((failure nil))
    (loop while (fnn-bplc-owned node)
          for socket = (cdr (pop (fnn-bplc-owned node)))
          do (handler-case (sb-bsd-sockets:socket-close socket)
               (error (condition) (unless failure (setq failure condition)))))
    (setf (fnn-bplc-live node) nil)
    (when failure (error failure))))

(defun fnn-bplc-cut (node cut)
  (let* ((selector (and *fnn-bplc-test-change*
                        (fnn-developer-selector "FN_BP_LISTENER_TEST_PAUSE_CUT")))
         (plan (fnn-core 'fn-bplc-cut-plan (fnn-bplc-model node)
                         (and selector (fnn-octet-list (fnn-string-octets selector))) cut)))
    (when plan
      (fnn-out "~a" (second plan))
      (finish-output)
      (loop (sleep 1)))))

(defun fnn-bplc-drive (node)
  "One observed primitive per ACL2 action; accept no session while changing."
  (loop
    (let* ((action (fnn-core 'fn-bplc-action (fnn-bplc-model node)))
           (kind (first action)))
      (case kind
        (:prepare-bind (fnn-bplc-step node '(:bind-start)))
        (:bind
         (fnn-bplc-cut node :before-bind)
         (multiple-value-bind (socket port)
             (handler-case (fnn-tcl-listen (second action))
               (error (condition)
                 (fnn-bplc-step node '(:bind-result :failed))
                 (fnn-indeterminate "BP runtime listener bind failed; persisted configuration retained; recovery required: ~a" condition)))
           (push (cons (second action) socket) (fnn-bplc-owned node))
           (fnn-bplc-step node '(:bind-result :ok))
           (fnn-bplc-cut node :after-bind)
           (fnn-out "BP NODE LISTENING ~d" port)))
        (:install
         (fnn-bplc-cut node :before-install)
         (let ((live
                 (handler-case
                     (mapcar (lambda (port)
                               (or (cdr (assoc port (fnn-bplc-owned node)))
                                   (fnn-fault "ACL2 installation names no bound listener handle")))
                             (third action))
                   (error (condition)
                     (fnn-bplc-step node '(:install-result :failed))
                     (fnn-indeterminate "BP runtime listener installation failed; recovery required: ~a" condition)))))
           (setf (fnn-bplc-live node) live)
           (fnn-bplc-step node '(:install-result :ok))
           (fnn-bplc-cut node :after-install)))
        (:retire
         (fnn-bplc-cut node :before-retire)
         (let ((entry (assoc (second action) (fnn-bplc-owned node))))
           (handler-case
               (progn
                 (unless entry (fnn-fault "ACL2 retirement names no owned listener handle"))
                 (setf (fnn-bplc-owned node) (delete entry (fnn-bplc-owned node) :test #'eq))
                 (sb-bsd-sockets:socket-close (cdr entry)))
             (error (condition)
               (fnn-bplc-step node '(:retire-result :failed))
               (fnn-indeterminate "BP runtime listener retirement failed; recovery required: ~a" condition)))
           (fnn-bplc-step node '(:retire-result :ok))
           (fnn-bplc-cut node :after-retire)))
        (:refused (fnn-refuse "BP runtime startup refused: ~a" (second action)))
        (:ready
         (fnn-out "~a" (fnn-core 'fn-bplc-runtime-line (fnn-bplc-model node)))
         (return))
        (otherwise
         (fnn-indeterminate "BP runtime listener machine fenced; recovery required"))))))

(defun fnn-bplc-start (mode)
  (let ((node (make-fnn-bplc :mode mode
                            :model (fnn-owner-core 'fn-owner-bplc-recover mode))))
    (handler-case (progn (fnn-bplc-drive node) node)
      (error (condition)
        (ignore-errors (fnn-bplc-close-all node))
        (error condition)))))

(defun fnn-bplc-reconfigure (node)
  (let ((*fnn-bplc-test-change* t))
    (setf (fnn-bplc-model node)
          (fnn-owner-core 'fn-owner-bplc-begin (fnn-bplc-model node) (fnn-bplc-mode node)))
    (fnn-bplc-cut node :configuration-published)
    (fnn-bplc-drive node)))
