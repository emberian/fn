; Exact unchanged immutable source factoring; no issuer authority.
(in-package "ACL2")

(defun fn-irq-committed-phasep (phase)
 (declare (xargs :guard t))
 (member-eq phase '(:committed :committed-repin-released :committed-repin-held :committed-repin-aborted)))
