; Core observer provider, independent of unadmitted accounting proofs.
(in-package "ACL2")
(include-book "query-reference-predicates")
(include-book "assembly-callbacks-c")
(fn2-book-layer :c)

(defun fn2-core-query-references-accountedp (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-pool (fn2-core-pool fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))) (answer)
  (fn2-query-references-accountedp fn2-pool fn2-id-decides) answer))
