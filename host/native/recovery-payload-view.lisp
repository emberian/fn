; Actual startup custody boundaries; loaded after native owner/io.
; The common owner lifecycle has entered :recovering before these creators.
(in-package "ACL2")
(defun fnn-snapshot-recovery-payload-view-acquire (service maintenance source)
  (sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)
    (unless (and (eq *fnn-payload-lifecycle-phase* :recovering)
                 (eq service *fnn-payload-lifecycle-owner*))
      (return-from fnn-snapshot-recovery-payload-view-acquire
        (values :retained '(:retained :recovery-lifecycle))))
    (let ((arena *fnn-payload-lifecycle-arena*))
      (destructuring-bind (erp answer arena1 pool state)
          (fnn-call 'fn-owner-recovery-payload-view-acquire
                    source maintenance arena (fnn-live-page-read-pool) *the-live-state*)
        (declare (ignore arena1 pool state))
        (when erp (fnn-fault "recovery view core acquire failed"))
        (if (eq (first answer) :acquired)
            (values :acquired (fnn-make-snapshot-payload-view (second answer) arena))
          (values :retained answer))))))
(defun fnn-snapshot-recovery-payload-view-live-p (holder)
  (sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)
    (and (eq *fnn-payload-lifecycle-phase* :recovering)
         (eq (fnn-snapshot-payload-view-arena holder) *fnn-payload-lifecycle-arena*)
         (fnn-core 'fn-owner-recovery-payload-view-livep
                   (fnn-snapshot-payload-view-token holder)
                   (fnn-live-page-read-pool) *the-live-state*))))
(defun fnn-snapshot-recovery-payload-view-release (holder)
  ; Caller holds owner mutex. Role return derives actual child custody in the
  ; same pool; this API deliberately has no caller-supplied joined parameter.
  (sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)
    (if (not (and (eq *fnn-payload-lifecycle-phase* :recovering)
                  (eq (fnn-snapshot-payload-view-arena holder)
                      *fnn-payload-lifecycle-arena*)))
        '(:retained :recovery-view-instance)
      (destructuring-bind (erp answer pool state)
          (fnn-call 'fn-owner-recovery-payload-view-release
                    (fnn-snapshot-payload-view-token holder)
                    (fnn-live-page-read-pool) *the-live-state*)
        (declare (ignore pool state))
        (when erp (fnn-fault "recovery view core release failed"))
        answer))))
(define-condition fnn-snapshot-startup-root-retained (fnn-store-indeterminate)
  ((token :initarg :token :reader fnn-snapshot-startup-root-retained-token)
   (source :initarg :source :reader fnn-snapshot-startup-root-retained-source)
   (maintenance :initarg :maintenance :reader fnn-snapshot-startup-root-retained-maintenance)))
(defun fnn-snapshot-recovery-root-acquire (service base-handle maintenance source)
  (declare (ignore service))
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (destructuring-bind (word token &rest ignored)
        (fnn-core-page-read-pool 'fn-owner-recovery-initial-root-acquire
                                source maintenance (fnn-core 'fn-hrs-h-file base-handle))
      (declare (ignore ignored))
      (unless (eq word :admitted)
        (error 'fnn-snapshot-startup-root-retained
               :token token :source source :maintenance maintenance
               :message (format nil "startup root retained: ~a token=~a" word token)))
      token)))
(defun fnn-snapshot-recovery-root-release (service token maintenance source)
  (sb-thread:with-mutex ((fnn-owner-service-lock service))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (unless (eq (first (fnn-core-page-read-pool
                         'fn-owner-recovery-initial-root-release source maintenance token)) :released)
        (fnn-fault "startup root custody retained")))
    (fnn-owner-release-pending-extents-locked service)))
