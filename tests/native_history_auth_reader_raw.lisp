;;; Loaded only in the coherent source/raw owner assembly, never a stub world.
;;; Reference init/post/compact produces fixture data; actual restart installs
;;; SERVICE. MAINTENANCE must be an actual operation-derived admitted token.
(in-package "ACL2")

(defun fnn-hsr-fixture-first-based-row (service maintenance)
  "Exercise the actual controller constructor, reader and decoder together.
Return the live job for the cold-span continuation; no authority is refunded."
  (let ((job (fnn-owner-snapshot-capture service maintenance)) (returned nil))
    (unwind-protect
         (loop for watchdog below 1000000
               for answer = (fnn-snapshot-job-source-step job) do
           (when (and (consp answer) (eq (first answer) :row))
             (let ((record (third answer)))
               (assert (eq (first record) :decoded))
               (assert (fnn-snapshot-job-root job))
               (assert (fnn-snapshot-job-reader job))
               (assert (eq (first (fnn-snapshot-job-completion job)) :parser-completion))
               (assert (fnn-core 'fn-omk-token-matchp
                                 (fourth answer)
                                 (second (fnn-snapshot-job-completion job))))
               (setq returned t)
               (return (values answer job))))
           (when (and (consp answer) (member (first answer) '(:refused :uncertain :done)))
             (error "actual restarted based-row path stopped: ~s" answer))
           finally (error "actual source fixture watchdog expired"))
      (unless returned
        ;; This synchronous action has returned. No fake cancellation ACK or
        ;; host Boolean can release a running source/worker.
        (fnn-snapshot-job-release-source job)
        (sb-thread:with-mutex ((fnn-owner-service-lock service))
          (when (fnn-snapshot-job-payload-view job)
            (fnn-snapshot-payload-view-release (fnn-snapshot-job-payload-view job) :joined))
          (fnn-owner-core 'fn-owner-osn-release
                          (fnn-core 'fn-osj-capture-ticket (fnn-snapshot-job-capture job))))))))

(defun fnn-hsr-fixture-provider-stale-observation (job old-observation)
  "An actually emitted prior scalar is replayed after provider advancement."
  (let ((provider (fnn-snapshot-job-provider job)))
    (assert provider)
    (assert (eq (first (fnn-core 'fn-obp-tick provider nil)) :need-byte))
    (assert (not (fnn-core 'fn-obp-byte-matchp old-observation provider)))
    (let ((answer (fnn-core 'fn-obp-tick provider old-observation)))
      ;; Invoke this at a current byte demand, not a no-byte scheduling phase.
      (assert (eq (first answer) :stale))
      (assert (equal (second answer) provider)))))
