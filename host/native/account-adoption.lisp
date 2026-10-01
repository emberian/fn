;;; Actual account lifecycle pool transport. The caller holds owner; these
;;; adapters acquire only extent, retain every MV and use the SAME live pool.
;;; Neither parsed config nor a returned family shape issues a turn or job.
(in-package "ACL2")

(defun fnn-account-adoption-begin (config bindings entropy slot nonce slots pool)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-call 'fn-owner-account-adoption-begin config bindings entropy
              slot nonce slots pool *the-live-state*)))

(defun fnn-account-adoption-tick (slot nonce slots pool)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-call 'fn-owner-account-adoption-tick
              slot nonce slots pool *the-live-state*)))

(defun fnn-account-adoption-status ()
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-call 'fn-owner-account-adoption-status *the-live-state*)))

;;; This STATIC callback is installed only in the enclosing actual account
;;; control binding. Owner invokes it after scheduler cleanup + explicit body
;;; callback/result/closure reference drops, before ATS finish. No caller row,
;;; charge, receipt or joined word is supplied. Unavailable/pending keeps debt.
(defun fnn-account-adoption-epilogue (slot nonce slots pool)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (values-list
      (fnn-call 'fn-owner-account-turn-return-current
                 slot nonce slots pool *the-live-state*))))

(defun fnn-account-adoption-collect (slot nonce slots pool)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-call 'fn-owner-account-adoption-collect
               slot nonce slots pool *the-live-state*)))
