(in-package "ACL2")
(local (include-book "arithmetic/top" :dir :system))
; Monotone profile-only envelope; state growth is independent of success.
(defun fn-aw-budget (fuel n s)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) 1
    (+ (* 32 (+ 1 (nfix n) (nfix s)))
       (fn-aw-budget (1- fuel) (nfix n) (+ (nfix s) (* 2 (nfix n)) 4)))))
(defthm fn-aw-budget-natural
  (natp (fn-aw-budget fuel n s))
  :rule-classes :type-prescription)
(defthm fn-aw-budget-positive
  (< 0 (fn-aw-budget fuel n s))
  :rule-classes :linear)
(defun fn-aw-budget-monotone-induct (fuel n s n2 s2)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) (list n s n2 s2)
    (fn-aw-budget-monotone-induct (1- fuel) n (+ s (* 2 n) 4)
                                  n2 (+ s2 (* 2 n2) 4))))
(defthm fn-aw-budget-monotone
  (implies (and (natp n) (natp s) (natp n2) (natp s2)
                (<= n n2) (<= s s2))
           (<= (fn-aw-budget fuel n s) (fn-aw-budget fuel n2 s2)))
  :hints (("Goal" :induct (fn-aw-budget-monotone-induct fuel n s n2 s2))))
(defthm fn-aw-budget-polynomial
  (implies (and (natp fuel) (natp n) (natp s))
           (equal (fn-aw-budget fuel n s)
             (+ 1 (* 32 fuel (+ n s 1))
                  (* 32 (+ n 2) fuel (1- fuel))))))
