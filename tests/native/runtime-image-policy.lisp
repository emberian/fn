(in-package "CL-USER")
(defun fnn-image-policy-test-raw-signal (signal)
  (sb-sys:sap-ref-lispobj (sb-sys:foreign-symbol-sap "lisp_sig_handlers" t)
                        (ash signal sb-vm:word-shift)))
(let* ((pool (list :image-policy-pool))
       (gate (fnn-runtime-participants-install-for-image pool))
       (reserved (list sb-unix:sigurg sb-unix:sigusr2 sb-unix:sigvtalrm))
       (before (mapcar #'fnn-image-policy-test-raw-signal reserved))
       (policy nil) (other nil)
       (ready (sb-thread:make-semaphore))
       (release (sb-thread:make-semaphore)))
  (unwind-protect
      (progn
        (fnn-with-runtime-participants-parked (gate pool) nil)
        (setf policy (fnn-runtime-image-policy-prepare pool gate))
        (assert (equal (multiple-value-list
                         (fnn-runtime-image-policy-bootstrap-status pool gate))
                       (list :image-policy-closed policy)))
        (assert (equal before (mapcar #'fnn-image-policy-test-raw-signal reserved)))
        (assert (every #'fnn-runtime-image-policy-signal-default-p
                       *fnn-runtime-bootstrap-ordinary-signals*))
        (assert (equal (multiple-value-list
                         (fnn-runtime-image-policy-bootstrap-status (list :wrong) gate))
                       '(:image-policy-unavailable nil)))
        (fnn-runtime-image-policy-register-image-hook)
        (fnn-runtime-participants-register-image-hooks)
        ;; Actual extra thread is rejected; no pending user callback is run.
        (setf other (sb-thread:make-thread
                      (lambda () (sb-thread:signal-semaphore ready)
                        (sb-thread:wait-on-semaphore release))))
        (sb-thread:wait-on-semaphore ready)
        (assert (handler-case (progn (fnn-runtime-image-policy-restore) nil)
                  (error () t)))
        (assert (equal (multiple-value-list
                         (fnn-runtime-image-policy-bootstrap-status pool gate))
                       '(:image-policy-unavailable nil)))
        (assert (eq (fnn-runtime-image-policy-phase policy) :uncertain))
        (format t "RUNTIME-IMAGE-POLICY PASS defaults/reserved/identity/hooks/foreign-thread-fence~%"))
    (sb-thread:signal-semaphore release)
    (when other (sb-thread:join-thread other))
    (fnn-runtime-participants-stop-and-join gate)))
