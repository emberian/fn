(in-package "CL-USER")
(let* ((pool (list :system-cleanup-pool))
       (gate (fnn-runtime-participants-install-for-image pool))
       (receipt (list :recording-system-receipt))
       (claimed 0) (completed 0)
       (binding
        (%fnn-runtime-system-cleanup-binding
         gate :system-finalizer-one
         (lambda (subject)
           (assert (eq subject :system-finalizer-one))
           (incf claimed) (values :admitted receipt))
         (lambda (token)
           (assert (eq token receipt)) (incf completed) :completed)
         (lambda (token cause) (declare (ignore token cause))
           (error "unexpected-system-fence")))))
  (fnn-with-runtime-participants-parked (gate pool) nil)
  ;; Actual selected system primitive; core callbacks are recording mechanics,
  ;; not a real allocation grant or a claim that all pending work was drained.
  (assert (eq :completed (fnn-runtime-participant-cleanup-one binding)))
  (assert (= claimed completed 1))
  (assert (eq receipt (fnn-runtime-cleanup-binding-receipt binding)))
  (fnn-runtime-participants-stop-and-join gate)
  (format t "ACTUAL-SYSTEM-ONE-RECORDING-CLAIM-JOIN-PASS~%"))
