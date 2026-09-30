; Production startup assembly WIP. Load after snapshot-producer and the HPI
; writer. The enclosing startup caller must issue INITIAL from the SAME
; installed pool before entering the private constructor below.
(in-package "ACL2")

(defstruct (fnn-snapshot-initial-workspace
             (:constructor %make-fnn-snapshot-initial-workspace))
  writer scratch receipt q0 q1 q2 q3 pool digest)
(define-condition fnn-snapshot-startup-retained (fnn-snapshot-capture-uncertain)
  ((workspace :initarg :workspace :reader fnn-snapshot-startup-retained-workspace)
   (source :initarg :source :initform nil :reader fnn-snapshot-startup-retained-source)
   (maintenance :initarg :maintenance :initform nil :reader fnn-snapshot-startup-retained-maintenance)
   (root :initarg :root :initform nil :reader fnn-snapshot-startup-retained-root)
   (view :initarg :view :initform nil :reader fnn-snapshot-startup-retained-view)
   (cause :initarg :cause :initform nil :reader fnn-snapshot-startup-retained-cause)))

(defun %fnn-snapshot-initial-workspace-create (receipt)
  "Private allocation cut after actual INITIAL admission. No global default
page state is borrowed. The outer stage transfers SCRATCH and the writer
retains these exact five page states through publication or joined cleanup.
RECEIPT is retained custody; this constructor does not issue or validate it.
The authenticated reader separately acquires its charged physical buffers."
  (let ((workspace (%make-fnn-snapshot-initial-workspace :receipt receipt)))
    (handler-case
        (progn
          (setf (fnn-snapshot-initial-workspace-q0 workspace) (create-fn-hpq0))
          (setf (fnn-snapshot-initial-workspace-q1 workspace) (create-fn-hpq1))
          (setf (fnn-snapshot-initial-workspace-q2 workspace) (create-fn-hpq2))
          (setf (fnn-snapshot-initial-workspace-q3 workspace) (create-fn-hpq3))
          (setf (fnn-snapshot-initial-workspace-pool workspace) (create-fn-hpb))
          (setf (fnn-snapshot-initial-workspace-digest workspace) (create-pgs-digest-state))
          (setf (fnn-snapshot-initial-workspace-scratch workspace)
                (make-array 16384 :element-type '(unsigned-byte 8) :initial-element 0))
          (setf (fnn-snapshot-initial-workspace-writer workspace)
                (fnn-hpi-retain nil
                 (fnn-snapshot-initial-workspace-q0 workspace)
                 (fnn-snapshot-initial-workspace-q1 workspace)
                 (fnn-snapshot-initial-workspace-q2 workspace)
                 (fnn-snapshot-initial-workspace-q3 workspace)
                 (fnn-snapshot-initial-workspace-pool workspace)
                 (fnn-snapshot-initial-workspace-digest workspace)))
          workspace)
      (error (condition)
        (error 'fnn-snapshot-startup-retained :job nil :workspace workspace
               :cause condition :message "startup private backing is retained")))))

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
    (handler-case
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
             ; Claim actual constructor custody before any native root/view/
             ; job/workspace creator. A partial creator keeps this row held.
             (destructuring-bind (erp entered pool state)
                 (fnn-call 'fn-owner-recovery-initial-constructor-begin
                           token maintenance (fnn-live-page-read-pool) *the-live-state*)
               (declare (ignore pool state))
               (when erp (fnn-fault "startup constructor custody core call failed"))
               (unless (eq (first entered) :entered)
                 (fnn-fault "startup constructor custody retained: ~a" entered)))
             (let* ((context (fnn-snapshot-source-context))
                    (plan (fnn-core 'fn-osj-resource-word context maintenance)))
               (unless (eq (first plan) :capture)
                 (fnn-refuse-io "startup INITIAL/source mismatch: ~a" plan))
               (when (second plan)
                 (setq root (fnn-snapshot-recovery-root-acquire
                             service (second plan) maintenance token))))
             (multiple-value-bind (word holder)
                 (fnn-snapshot-recovery-payload-view-acquire
                  service maintenance token)
               (unless (eq word :acquired)
                 (fnn-refuse-io "startup recovery view unavailable: ~a" holder))
               (setq view holder))
             (let ((begun (fnn-core-state 'fn-owner-recovery-census-begin
                                          token (fourth admission))))
               (setq job (%fnn-snapshot-recovery-job-open
                          service begun root maintenance view))
               (setf (fnn-snapshot-job-initial-source job) token))
             (handler-case
                 (progn
                   (setq workspace (%fnn-snapshot-initial-workspace-create admission))
                   (setf (fnn-snapshot-job-writer job)
                         (fnn-snapshot-initial-workspace-writer workspace))
                   (values job workspace))
               (fnn-snapshot-startup-retained (condition)
                 (setq workspace (fnn-snapshot-startup-retained-workspace condition))
                 (error condition))
               (error (condition)
                 (error 'fnn-snapshot-startup-retained :job job :workspace workspace
                        :message (format nil "startup workspace did not complete: ~a"
                                         condition))))))
      (error (condition)
        ; Actual constructor custody stays held on every partial creator.
        ; Preserve all obtained holders and the original failure. Cleanup
        ; cannot invent the missing runtime epilogue or hide a retained pin.
        (if maintenance
            (error 'fnn-snapshot-startup-retained :job job :workspace workspace
                   :source token :maintenance maintenance :root root :view view
                   :cause condition :message "startup INITIAL retains partial construction")
          (error condition))))))

(defun fnn-snapshot-startup-measure (service)
  "Drive the actual retained OSM/HCT collector in the exclusive startup cut.
Yield between its bounded actions. No guessed count/pool or second census is
used. Return the measured result with its still-owned job/workspace; the
internal seal/install must consume them before startup clears its source."
  (multiple-value-bind (job workspace) (fnn-snapshot-startup-open service)
    (handler-case
        (loop
          (sb-thread:with-mutex ((fnn-owner-service-lock service))
            (unless (fnn-snapshot-recovery-payload-view-live-p
                     (fnn-snapshot-job-payload-view job))
              (error 'fnn-snapshot-startup-retained :job job :workspace workspace
                     :message "startup recovery view is no longer current")))
          (let ((answer (fnn-snapshot-recovery-census-step job)))
            (when (and (consp answer) (eq (first answer) :measured))
              (return (values answer job workspace)))
            (when (and (consp answer)
                       (member (first answer) '(:unavailable :refused :uncertain :stale)))
              (error 'fnn-snapshot-startup-retained :job job :workspace workspace
                     :message (format nil "startup census retained ownership: ~a" answer)))
            (fnn-checkpoint-yield
             "startup-canonical-census"
             (fnn-core 'fn-osrc-at 2 (fnn-snapshot-job-source job)))
            (sb-thread:thread-yield)))
      (fnn-snapshot-capture-uncertain (condition) (error condition))
      (error (condition)
        (error 'fnn-snapshot-startup-retained :job job :workspace workspace
               :cause condition :message (format nil "startup census did not complete: ~a" condition))))))
