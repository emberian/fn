(in-package "CL-USER")
(defvar *fnn-bootstrap-mask-order* nil)
(defun fnn-bootstrap-masked-attempt (gate pool started delivered)
 (fnn-with-runtime-participants-bootstrap (gate pool)
   (assert (not sb-sys:*interrupts-enabled*))
   (sb-thread:signal-semaphore started)
   (sb-thread:wait-on-semaphore delivered)
   (assert (null *fnn-bootstrap-mask-order*))
   (push :sample-install-complete *fnn-bootstrap-mask-order*)
   (values :sample-install-return pool)))
(let* ((pool (list :masked-pool))
       (gate (fnn-runtime-participants-install-for-image pool))
       (started (sb-thread:make-semaphore))
       (delivered (sb-thread:make-semaphore))
       (sender nil))
 (unwind-protect
  (progn
   (fnn-with-runtime-participants-parked (gate pool) nil)
   (let ((target sb-thread:*current-thread*))
    (setf sender
     (sb-thread:make-thread
      (lambda ()
       (sb-thread:wait-on-semaphore started)
       (sb-thread:interrupt-thread target
        (lambda ()
         (assert (not (sb-thread:holding-mutex-p
                       (fnn-runtime-participants-lock gate))))
         (push :pending-handler *fnn-bootstrap-mask-order*)))
       (sb-thread:signal-semaphore delivered)))))
   (assert (equal (multiple-value-list
                   (fnn-bootstrap-masked-attempt gate pool started delivered))
                  (list :sample-install-return pool)))
   (sb-thread:join-thread sender)
   (assert (equal *fnn-bootstrap-mask-order*
                  '(:pending-handler :sample-install-complete)))
   (format t "MASKED-SAMPLE-SAFE-PENDING-HANDLER-ON-EXIT-PASS~%"))
  (when (and sender (sb-thread:thread-alive-p sender))
   (sb-thread:join-thread sender))
  (fnn-runtime-participants-stop-and-join gate)))
