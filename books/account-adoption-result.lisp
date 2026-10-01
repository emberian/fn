; Transport selectors for the actual five-MV pooled account lifecycle.
; The native caller retains every MV. These selectors make no source,
; funding, authority, durable-completion or alias-return decision.
(in-package "ACL2")
(include-book "consumer-position-fields")

(defun fn-cado-result-action (result)
 (declare (xargs :guard t))
 (list (fn-cp-nth 0 result) (fn-cp-nth 1 result)))

(defun fn-cado-status-result-action (result)
 (declare (xargs :guard t))
 (fn-cp-nth 0 result))

(defun fn-cado-result-after-status (result status-result)
 (declare (xargs :guard t))
 (let ((action (fn-cp-nth 0 status-result)))
  (list (fn-cp-nth 0 action) (fn-cp-nth 1 action)
        (fn-cp-nth 2 result) (fn-cp-nth 3 result) (fn-cp-nth 4 result))))

(in-theory (disable fn-cado-result-action fn-cado-status-result-action fn-cado-result-after-status))
