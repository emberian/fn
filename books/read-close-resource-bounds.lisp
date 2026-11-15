; Bounds for the count the actual CLOSE preflight already returns. These are
; metadata obligations, not CPU steps or a new execution/counting model.
(in-package "ACL2")
(include-book "run-physical-park-region")
(include-book "machines-b") ; owns the actual READ's 1+8 cursor geometry
(local (include-book "arithmetic/top" :dir :system))
(fn2-book-layer :c)
(defthm fn2-run-load-region-park-check-count-natp
 (natp (mv-nth 1 (fn2-run-load-region-park-check
   i b0 n0 b1 n1 b2 n2 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn2-run-load-region-park-check
   i b0 n0 b1 n1 b2 n2 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
  :in-theory (e/d (fn2-run-load-region-park-check)
   (fn2-run-load-parkable-p fn2-checkpoint-summary-releaseable-p fn2-run-load-region-cursor)))))
(defthm fn2-run-load-region-park-check-count-bound
 (<= (mv-nth 1 (fn2-run-load-region-park-check
   i b0 n0 b1 n1 b2 n2 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
     (nfix (- (fn2-run-load-region-count n0 n1 n2) (nfix i))))
 :rule-classes :linear
 :hints (("Goal" :induct (fn2-run-load-region-park-check
   i b0 n0 b1 n1 b2 n2 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
  :in-theory (e/d (fn2-run-load-region-park-check)
   (fn2-run-load-parkable-p fn2-checkpoint-summary-releaseable-p fn2-run-load-region-cursor)))))
(defthm fn2-run-load-region-park-check-within-budget
 (implies (<= (nfix (- (fn2-run-load-region-count n0 n1 n2) (nfix i))) budget)
  (<= (mv-nth 1 (fn2-run-load-region-park-check
   i b0 n0 b1 n1 b2 n2 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)) budget))
 :rule-classes nil
 :hints (("Goal" :use fn2-run-load-region-park-check-count-bound
  :in-theory (disable fn2-run-load-region-park-check))))
; The exact preflight arguments of FN2-READ-SOURCE-CLOSE's region park.
; This does not equate nine leases or twenty-seven iterations to :steps.
(defthm fn2-read-source-close-lease-count-bound
 (<= (mv-nth 1 (fn2-run-load-region-park-check
   0 (+ transactions x) 1
   (+ transactions reads (* *fn2-b-range-source-cursors* x))
   *fn2-b-range-source-cursors* 0 0 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
     (+ 1 *fn2-b-range-source-cursors*))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn2-run-load-region-park-check-count-bound
   (i 0) (b0 (+ transactions x)) (n0 1)
   (b1 (+ transactions reads (* *fn2-b-range-source-cursors* x)))
   (n1 *fn2-b-range-source-cursors*) (b2 0) (n2 0)))
  :in-theory (e/d (fn2-run-load-region-count) (fn2-run-load-region-park-check)))))
