(in-package "ACL2")
; Environmental syscall observations only. Neither failure nor an unknown
; observation authorizes an accepted retire response using a stale report.
(defun fn-orr-reset-action (observation)
  (declare (xargs :guard t))
  (if (member-eq observation '(:removed :missing)) :continue :uncertain))
(defthm fn-orr-continue-requires-definite-reset
  (implies (equal (fn-orr-reset-action observation) :continue)
           (or (equal observation :removed) (equal observation :missing))))
