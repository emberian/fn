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
        (fnn-snapshot-job-cleanup job)))))

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


(defun fnn-hsr-fixture-two-based-rows (service maintenance)
  "Require actual row rebinding, page recycling and joined final cleanup."
  (let ((job (fnn-owner-snapshot-capture service maintenance))
        (reader nil) (root nil) (rows nil) (pages nil)
        (released-to-idle nil) (idle-to-select nil) (cleaned nil))
    (unwind-protect
         (loop for watchdog below 2000000 do
           (let* ((r (fnn-snapshot-job-reader job))
                  (before (and r (fnn-core 'fn-hsr-field 0 (fnn-hsr-source-cursor r))))
                  (answer (fnn-snapshot-job-source-step job))
                  (next (fnn-snapshot-job-reader job))
                  (after (and next (fnn-core 'fn-hsr-field 0 (fnn-hsr-source-cursor next)))))
             (when next
               (if reader (assert (eq reader next)) (setq reader next))
               (if root (assert (eq root (fnn-snapshot-job-root job)))
                 (setq root (fnn-snapshot-job-root job)))
               (let ((verified (fnn-core 'fn-hsr-field 17 (fnn-hsr-source-cursor next))))
                 (when (eq (first verified) :verified-page)
                   (pushnew (fifth verified) pages))))
             (when (and (eq before :verified) (eq after :idle))
               (setq released-to-idle t))
             (when (and (eq before :idle) (eq after :need-read))
               (setq idle-to-select t))
             (when (and (consp answer) (eq (first answer) :row))
               (assert (eq (first (third answer)) :decoded))
               (assert (fnn-core 'fn-omk-token-matchp (fourth answer)
                                 (second (fnn-snapshot-job-completion job))))
               (when rows (assert (= (second answer) (1+ (second (first rows))))))
               (push answer rows)
               (when (= (length rows) 2)
                 (assert (>= (length pages) 2))
                 (assert released-to-idle)
                 (assert idle-to-select)
                 (assert (equal (fnn-snapshot-job-cleanup job) '(:released)))
                 (setq cleaned t)
                 (assert (eq (fnn-snapshot-job-phase job) :released))
                 (assert (not (or (fnn-snapshot-job-reader job)
                                  (fnn-snapshot-job-root job)
                                  (fnn-snapshot-job-payload-view job)
                                  (fnn-snapshot-job-capture job)
                                  (fnn-snapshot-job-maintenance job)
                                  (fnn-snapshot-job-census job)
                                  (fnn-snapshot-job-pending-row job)
                                  (fnn-snapshot-job-cold-mapping job)
                                  (fnn-snapshot-job-writer job))))
                 (return (reverse rows))))
             (when (and (consp answer) (member (first answer) '(:refused :uncertain :done)))
               (error "two-row actual source path stopped: ~s" answer)))
           finally (error "two-row actual source fixture watchdog expired"))
      (unless cleaned (fnn-snapshot-job-cleanup job)))))

(defun fnn-hsr-fixture-census-restart (service maintenance)
  "Complete the actual canonical census and retain the job for its writer.
The existing immutable reader/root must survive the core source restart."
  (multiple-value-bind (first-row job)
      (fnn-hsr-fixture-first-based-row service maintenance)
    (declare (ignore first-row))
    (let ((reader (fnn-snapshot-job-reader job))
          (root (fnn-snapshot-job-root job)) (returned nil))
      (unwind-protect
           (loop for watchdog below 2000000
                 for answer = (fnn-snapshot-job-source-step job) do
             (when (and (consp answer) (eq (first answer) :census-complete))
               (let ((serial (fnn-core 'fn-hsr-field 3
                                       (fnn-core 'fn-hsr-field 1
                                                 (fnn-hsr-source-cursor reader)))))
                 (assert (eq (first (fnn-snapshot-job-restart-source job)) :restarted))
                 (assert (eq reader (fnn-snapshot-job-reader job)))
                 (assert (eq root (fnn-snapshot-job-root job)))
                 (assert (= 1 (fnn-core 'fn-osrc-at 12 (fnn-snapshot-job-source job))))
                 (assert (equal serial
                                (fnn-core 'fn-hsr-field 3
                                          (fnn-core 'fn-hsr-field 1
                                                    (fnn-hsr-source-cursor reader)))))
                 (setq returned t)
                 (return (values (second answer) job))))
             (when (and (consp answer) (member (first answer) '(:refused :uncertain)))
               (error "actual canonical census stopped: ~s" answer))
             finally (error "actual canonical census watchdog expired"))
        (unless returned (fnn-snapshot-job-cleanup job))))))
