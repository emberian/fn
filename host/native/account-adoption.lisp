;;; Actual account lifecycle pool transport. The caller holds owner; these
;;; adapters acquire only extent, retain every MV and use the SAME live pool.
;;; Neither parsed config nor a returned family shape issues a turn or job.
(in-package "ACL2")

;;; Retain EACH literal FnNCall result before status/next-call dispatch. This
;;; updates the actual existing installed binding under owner→extent; it is
;;; not another source association or ticket. Partial returned effects survive
;;; a malformed transport before the fixed fault fences the original receipt.
(defun fnn-account-retain-control-effects (service result)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((binding (fnn-owner-service-control-binding service))
          (slots (third result)) (pool (fourth result)) (state (fifth result)))
      (when binding
        (when slots (setf (fnn-owner-control-binding-slots binding) slots))
        (when pool (setf (fnn-owner-control-binding-pool binding) pool)))
      (when state (setf *the-live-state* state))
      (unless (and binding slots pool state)
        (fnn-fixed-callback-fail 'fn-owner-account-adoption-begin
                                :account-control-missing-effects nil))
      result)))

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

;;; No native event/graph argument, legacy store writer, or :durable word is
;;; manufactured here. The selected core source currently refuses BEFORE I/O
;;; and preserves all five effects plus the original typed turn claim.
(defun fnn-owner-account-publication-locked (service slot nonce slots pool)
  (declare (ignore service))
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-call 'fn-owner-account-adoption-publication-step
               slot nonce slots pool *the-live-state*)))

(defun fnn-owner-account-configuration-publication-locked (service slot nonce slots pool)
  (fnn-owner-account-publication-locked service slot nonce slots pool))
