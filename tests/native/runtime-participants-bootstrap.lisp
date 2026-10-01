(in-package "CL-USER")
(defun fnn-bootstrap-component-attempt (gate pool marker)
  (fnn-with-runtime-participants-bootstrap (gate pool)
    (assert (eq *fnn-runtime-participant-barrier* gate))
    (assert (sb-thread:holding-mutex-p (fnn-runtime-participants-lock gate)))
    (values :sample-install-return pool marker)))
(let* ((pool (list :same-pool))
       (gate (fnn-runtime-participants-install-for-image pool))
       (hooks 0) (calls 0))
  (unwind-protect
       (progn
         ;; Setup acknowledgment uses the historical waiting helper only here.
         (fnn-with-runtime-participants-parked (gate pool) nil)
         (assert (equal (multiple-value-list
                         (fnn-bootstrap-component-attempt gate pool :marker))
                        (list :sample-install-return pool :marker)))
         (assert (sb-thread:with-mutex
                     ((fnn-runtime-participants-lock gate) :wait-p nil) t))
         (assert (equal (multiple-value-list
                         (fnn-bootstrap-component-attempt gate nil :marker))
                        '(:participant-unavailable :fenced)))
         (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
           (setf (fnn-runtime-participants-active gate) t))
         (assert (equal (multiple-value-list
                         (fnn-bootstrap-component-attempt gate pool :marker))
                        '(:participant-not-ready :refused)))
         (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
           (setf (fnn-runtime-participants-active gate) nil))
         (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
           (assert (equal (multiple-value-list
                           (fnn-bootstrap-component-attempt gate pool :marker))
                          '(:participant-reentrant :fenced))))
         (fnn-with-runtime-participants-parked (gate pool)
           (assert (equal (multiple-value-list
                           (fnn-bootstrap-component-attempt gate pool :marker))
                          '(:participant-reentrant :fenced))))
         (let* ((held (sb-thread:make-semaphore))
                (release (sb-thread:make-semaphore))
                (thread (sb-thread:make-thread
                         (lambda ()
                           (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
                             (sb-thread:signal-semaphore held)
                             (sb-thread:wait-on-semaphore release))))))
           (sb-thread:wait-on-semaphore held)
           (unwind-protect
                (assert (equal (multiple-value-list
                                (fnn-with-runtime-participants-bootstrap (gate pool)
                                  (incf calls)))
                               '(:participant-not-ready :refused)))
             (sb-thread:signal-semaphore release)
             (sb-thread:join-thread thread)))
         (assert (zerop calls))
         (push (lambda () (incf hooks)) sb-ext:*after-gc-hooks*)
         (sb-ext:gc :full t)
         (assert (equal (multiple-value-list
                         (fnn-bootstrap-component-attempt gate pool :marker))
                        (list :sample-install-return pool :marker)))
         (assert (zerop hooks))
         (assert (eq :escaped
                     (catch 'bootstrap-escape
                       (fnn-with-runtime-participants-bootstrap (gate pool)
                         (throw 'bootstrap-escape :escaped)))))
         (assert (sb-thread:with-mutex
                     ((fnn-runtime-participants-lock gate) :wait-p nil) t))
         (format t "BOOTSTRAP-NOWAIT-SAME-LOCK-MV-REFUSAL-ESCAPE-PASS~%"))
    (fnn-runtime-participants-stop-and-join gate)))
(disassemble #'fnn-bootstrap-component-attempt)
