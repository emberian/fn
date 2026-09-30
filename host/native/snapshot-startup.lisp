; Production startup assembly WIP. Load after snapshot-producer and the HPI
; writer. The enclosing startup caller must issue INITIAL from the SAME
; installed pool before entering the private constructor below.
(in-package "ACL2")

(defstruct (fnn-snapshot-initial-workspace
             (:constructor %make-fnn-snapshot-initial-workspace))
  writer scratch receipt)

(defun %fnn-snapshot-initial-workspace-create (receipt)
  "Private allocation cut after actual INITIAL admission. No global default
page state is borrowed. The outer stage transfers SCRATCH and the writer
retains these exact five page states through publication or joined cleanup.
RECEIPT is retained custody; this constructor does not issue or validate it.
The authenticated reader separately acquires its charged physical buffers."
  (let* ((q0 (create-fn-hpq0))
         (q1 (create-fn-hpq1))
         (q2 (create-fn-hpq2))
         (q3 (create-fn-hpq3))
         (pool (create-fn-hpb))
         (digest (create-pgs-digest-state))
         (scratch (make-array 16384 :element-type '(unsigned-byte 8)
                                   :initial-element 0))
         (writer (fnn-hpi-retain nil q0 q1 q2 q3 pool digest)))
    (%make-fnn-snapshot-initial-workspace
     :writer writer :scratch scratch :receipt receipt)))

(defun fnn-snapshot-startup-open (service)
  "Startup-only caller, before feed/key mutation, SCO clear and prefix release.
The common runtime installer has already installed the same physical pool.
No writer or reader worker has been exposed. INITIAL and the recovery view
entries are coordinated production joins; absent entries are not emulated.
Returns the actual recovery job and its private workspace. Neither result is
canonical readiness or a publication capability."
  (let* ((store (fnn-owner-service-store service))
         (token (fnn-store-recovery-source store))
         (maintenance nil) (root nil) (view nil) (job nil) (workspace nil))
    (unwind-protect
         (sb-thread:with-mutex ((fnn-owner-service-lock service))
           (destructuring-bind (erp admission read-pool state)
               (fnn-call 'fn-owner-recovery-initial-admit token
                         (fnn-live-page-read-pool) *the-live-state*)
             (declare (ignore read-pool state))
             (when erp (fnn-fault "startup INITIAL core call failed"))
             (unless (eq (first admission) :admitted)
               (fnn-refuse-io "startup INITIAL unavailable: ~a" admission))
             ; NIL input requests the actual completed-open source producer;
             ; it is not authority. INITIAL returns its issued source token.
             (setq token (second admission) maintenance (third admission))
             (let* ((context (fnn-snapshot-source-context))
                    (plan (fnn-core 'fn-osj-resource-word context maintenance)))
               (unless (eq (first plan) :capture)
                 (fnn-refuse-io "startup INITIAL/source mismatch: ~a" plan))
               (when (second plan)
                 (setq root (fnn-snapshot-source-root-acquire
                             service (second plan) maintenance))))
             (multiple-value-bind (word holder)
                 (fnn-snapshot-recovery-payload-view-acquire
                  service maintenance token)
               (unless (eq word :acquired)
                 (fnn-refuse-io "startup recovery view unavailable: ~a" holder))
               (setq view holder))
             (let ((begun (fnn-core-state 'fn-owner-recovery-census-begin
                                          token (fourth admission))))
               (setq job (%fnn-snapshot-recovery-job-open
                          service begun root maintenance view)))
             (handler-case
                 (progn
                   (setq workspace (%fnn-snapshot-initial-workspace-create admission))
                   (setf (fnn-snapshot-job-writer job)
                         (fnn-snapshot-initial-workspace-writer workspace))
                   (values job workspace))
               (error (condition)
                 (error 'fnn-snapshot-capture-uncertain :job job
                        :message (format nil "startup workspace did not complete: ~a"
                                         condition))))))
      ; Once JOB exists, it owns the root/view/maintenance. Preserve it on
      ; later allocation errors for actual joined cleanup, never refund on
      ; the strength of an exception. Before JOB, no worker has been issued.
      (unless job
        (when root (fnn-snapshot-source-root-release service root))
        (when view
          (sb-thread:with-mutex ((fnn-owner-service-lock service))
            (let ((word (fnn-snapshot-recovery-payload-view-release view :joined)))
              (unless (eq (first word) :released)
                (fnn-fault "startup view cleanup retained: ~a" word)))))
        (when maintenance
          (unless (eq (first (fnn-core-page-read-pool
                              'fn-owner-maintenance-release maintenance)) :released)
            (fnn-fault "startup INITIAL cleanup retained ownership")))))))

(defun fnn-snapshot-startup-measure (service)
  "Drive the actual retained OSM/HCT collector in the exclusive startup cut.
Yield between its bounded actions. No guessed count/pool or second census is
used. Return the measured result with its still-owned job/workspace; the
internal seal/install must consume them before startup clears its source."
  (multiple-value-bind (job workspace) (fnn-snapshot-startup-open service)
    (handler-case
        (loop
          (let ((answer (fnn-snapshot-recovery-census-step job)))
            (when (and (consp answer) (eq (first answer) :measured))
              (return (values answer job workspace)))
            (when (and (consp answer)
                       (member (first answer) '(:unavailable :refused :uncertain :stale)))
              (error 'fnn-snapshot-capture-uncertain :job job
                     :message (format nil "startup census retained ownership: ~a" answer)))
            (fnn-checkpoint-yield
             "startup-canonical-census"
             (fnn-core 'fn-osrc-at 2 (fnn-snapshot-job-source job)))
            (sb-thread:thread-yield)))
      (fnn-snapshot-capture-uncertain (condition) (error condition))
      (error (condition)
        (error 'fnn-snapshot-capture-uncertain :job job
               :message (format nil "startup census did not complete: ~a" condition))))))
