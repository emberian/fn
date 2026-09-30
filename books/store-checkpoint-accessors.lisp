; Exact total checkpoint accessor, independent of captured Store state.
(in-package "ACL2")
(include-book "consumer-position-fields")

(local
 (defthm fn-sco-cp-nth-is-nth
   (equal (fn-cp-nth n x) (nth n x))
   :hints (("Goal" :in-theory (enable fn-cp-nth)))))

(defun fn-sco-at (n x)
  (declare (xargs :guard (natp n)))
  (mbe :logic (nth n x) :exec (fn-cp-nth n x)))
