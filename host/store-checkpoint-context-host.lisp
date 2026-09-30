; Fixed checkpoint metadata access for the actual loader and cold issuer.
; This includes no decoder and grants no canonical/owner readiness.
; Producer load/provenance/lifetime obligations remain at store-node-host.
(in-package "ACL2")
(defun fn-store-sco-current (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-store-sco-checkpoint state)
      (f-get-global 'fn-store-sco-checkpoint state)
    nil))

 ; This is same-load metadata, not owner/canonical readiness. These fields
 ; are invalidated at clear, decode begin, and finish begin/refusal.
(defun fn-store-sco-original-context-info (state)
 (declare (xargs :stobjs state :mode :program))
 (let ((checkpoint (fn-store-sco-current state))
       (info (and (boundp-global 'fn-store-sco-context-info state)
                  (f-get-global 'fn-store-sco-context-info state))))
  (if (and checkpoint info
           (boundp-global 'fn-store-sco-summary-region state)
           (f-get-global 'fn-store-sco-summary-region state))
      (list :summary checkpoint info)
    (list :unavailable :summary-context))))

 ; Loader replacement has a scalar incarnation distinct from owner epoch.
 ; Fault never becomes a reusable natural generation.
(defun fn-store-sco-source-invalidate (state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((state (f-put-global 'fn-store-recovery-open-origin nil state))
         (present (boundp-global 'fn-store-sco-recovery-source-generation state))
        (old (if present (f-get-global 'fn-store-sco-recovery-source-generation state) 0))
        (next (if (natp old) (+ 1 old) :fault)))
  (f-put-global 'fn-store-sco-recovery-source-generation next state)))
(defun fn-store-sco-recovery-source-generation-value (state)
 (declare (xargs :stobjs state :mode :program))
 (if (boundp-global 'fn-store-sco-recovery-source-generation state)
     (f-get-global 'fn-store-sco-recovery-source-generation state)
   :unavailable))
(defun fn-store-sco-recovery-source-generation (state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-store-sco-recovery-source-generation-value state)))

(defun fn-store-sco-recovery-source-value (state)
 (declare (xargs :stobjs state :mode :program))
 (and (fn-store-sco-current state)
      (boundp-global 'fn-store-sco-recovery-source state)
      (f-get-global 'fn-store-sco-recovery-source state)))
(defun fn-store-sco-recovery-source (state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-store-sco-recovery-source-value state)))

