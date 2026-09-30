; Process-local input/job holders, never account authority or allocation grants.
; The actual operator/startup source producer installs the captured request.
; Actual pool/turn admission must precede construction/installation of the job.
(in-package "ACL2")
(include-book "state-globals")

(defun fn-owner-account-adoption-request (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-account-adoption-request state)
      (f-get-global 'fn-owner-account-adoption-request state)))

(defun fn-owner-account-adoption-job (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-account-adoption-job state)
      (f-get-global 'fn-owner-account-adoption-job state)))

(defun fn-owner-account-adoption-job-install (job state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-account-adoption-job job state))

(defun fn-owner-account-adoption-input-clear (state)
 (declare (xargs :stobjs state :guard t))
 (let ((state (f-put-global 'fn-owner-account-adoption-request nil state)))
  (f-put-global 'fn-owner-account-adoption-job nil state)))

(in-theory (disable fn-owner-account-adoption-request fn-owner-account-adoption-job
                    fn-owner-account-adoption-job-install fn-owner-account-adoption-input-clear))
