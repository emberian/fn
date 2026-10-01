; Sole process-local selection holder. Only the internal pooled selector writes
; it, and only the real durable collector/reset clears it. It never authorizes
; publication or allocation by shape. No native-supplied event is installed here.
(in-package "ACL2")
(include-book "state-globals")

(defun fn-owner-account-adoption-operation (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-account-adoption-operation state)
      (f-get-global 'fn-owner-account-adoption-operation state)))

(defun fn-owner-account-adoption-operation-clear (state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-account-adoption-operation nil state))

(in-theory (disable fn-owner-account-adoption-operation
                    fn-owner-account-adoption-operation-clear))
