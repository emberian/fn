; The restart search spends at most the bit length of the initial interval,
; independently of the distribution of keys or the probe budget.
(in-package "ACL2")
(include-book "range-restart-bisection-proof")
(local (include-book "centaur/bitops/integer-length" :dir :system))

(local
 (defthm fn2-run-integer-length-monotonic
   (implies (and (natp i) (natp j) (<= i j)) (<= (integer-length i) (integer-length j)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable integer-length)))))
(local
 (defthm fn2-run-integer-length-of-half
   (implies (natp n) (equal (integer-length (floor n 2)) (if (zp n) 0 (1- (integer-length n)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable floor integer-length)))))

(local
 (defthm fn2-run-restart-half-interval
   (let* ((j (floor (+ lo hi) 2)) (low (if less (1+ j) lo)) (high (if less hi j)))
     (implies (and (natp lo) (natp hi) (< lo hi))
              (and (natp low) (natp high) (<= low high)
                   (<= (- high low) (floor (- hi lo) 2)))))
   :rule-classes nil
   :hints (("Goal" :cases ((< (floor (+ lo hi) 2) (/ (+ lo hi) 2)))))))

(local
 (defthm fn2-run-restart-half-bits
   (let* ((j (floor (+ lo hi) 2)) (low (if less (1+ j) lo)) (high (if less hi j)))
     (implies (and (natp lo) (natp hi) (< lo hi))
              (and (natp low) (natp high) (<= low high)
                   (<= (+ 1 (integer-length (- high low))) (integer-length (- hi lo))))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-run-restart-half-interval
                         (:instance fn2-run-integer-length-monotonic
                           (i (- (if less hi (floor (+ lo hi) 2)) (if less (1+ (floor (+ lo hi) 2)) lo)))
                           (j (floor (- hi lo) 2)))
                         (:instance fn2-run-integer-length-of-half (n (- hi lo))))
            :in-theory (disable integer-length floor)))))

(defthmd fn2-run-restart-search-fits-budget
  (let* ((search (fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool))
         (j (nth 0 search)) (left (nth 2 search)))
    (implies (and (natp fuel) (natp lo) (natp hi) (<= lo hi) (<= (integer-length (- hi lo)) fuel))
             (and (natp j) (<= lo j) (<= j hi) (equal (nth 1 search) j)
                  (natp left) (<= (- fuel (integer-length (- hi lo))) left) (<= left fuel))))
  :hints (("Goal" :do-not '(preprocess)
           :induct (fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool)
           :expand ((fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool))
           :in-theory (disable (:definition fn2-run-overview-restart-search) fn2-run-key-order-spec
                               fn2-run-overview-restart-fields fn2-overview-range-key-at integer-length floor))
          ("Subgoal *1/2" :use ((:instance fn2-run-restart-half-bits
                        (less (eq (fn2-run-key-order-spec *fn2-overview-range-key*
                           (nth (* *fn2-run-restart-interval* (floor (+ lo hi) 2)) rows)
                           (fn2-overview-range-key-at qbase f)) :lt)))))
          ("Subgoal *1/1" :cases ((equal lo hi))
           :expand ((:free (k low high) (fn2-run-overview-restart-search k low high offsets rows level qbase rb slot gen pk ps pg f pool)))
           :use ((:instance fn2-run-integer-length-of-half (n (- hi lo)))))))
