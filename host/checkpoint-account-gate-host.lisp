; Include after existing owner core/Store accessors in owner-host.
(in-package "ACL2")
(include-book "../books/checkpoint-account-gate")
(include-book "../books/definterface")
(defun fn-owner-checkpoint-account-word (state)
 (declare (xargs :stobjs state :mode :program))
 (let ((cp (fn-sn-consumer (fn-own-store (fn-owner-core state)))))
  (value (fn-cpa-checkpoint-word (list :ok cp nil nil)))))
(definterface fn-owner-checkpoint-account-word :class :program)
