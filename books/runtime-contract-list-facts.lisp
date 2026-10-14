; fn: shared list decomposition for runtime correspondence proofs.
(in-package "ACL2")
(include-book "runtime-contract-pool")

; Shared list decomposition; consumers enable this fact only in local theories.
(defthm fn-rtc-nthcdr-parts
  (and (equal (car (nthcdr h l)) (nth h l))
       (equal (cdr (nthcdr h l)) (nthcdr (+ 1 (nfix h)) l))
       (implies (true-listp l) (iff (consp (nthcdr h l)) (< (nfix h) (len l)))))
  :hints (("Goal" :in-theory (enable nth nthcdr))))
(in-theory (disable fn-rtc-nthcdr-parts))
