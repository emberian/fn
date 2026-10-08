; Concrete slot choice, equal to the model commit plan's slot.
(in-package "ACL2")
(include-book "pagestore")

(defun pgs-x-commit-slot (k)
  (declare (xargs :guard t))
  (if (equal k 1) 0 512))

(defthm pgs-x-commit-slot-is-the-plan-slot
  (implies (equal (car (pgs-plan-commit disk r mode dirty alloc)) :plan)
           (equal (pgs-x-commit-slot (second (pgs-open disk r mode)))
                  (* 512 (third (pgs-plan-commit disk r mode dirty alloc)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(pgs-plan-commit pgs-x-commit-slot car-cons cdr-cons (:executable-counterpart binary-*)) (theory 'minimal-theory)))))
