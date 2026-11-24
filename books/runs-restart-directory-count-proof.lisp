; The directory holds one offset for each group of sixteen entries.
(in-package "ACL2")
(include-book "runs-page")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(local
 (defthm fn2-run-ceiling-at-restart-residue
   (let ((i (+ (* 16 q) r)))
     (implies (and (integerp q) (natp r) (< r 16))
              (equal (ceiling (+ 1 i) 16) (+ (ceiling i 16) (if (equal (mod i 16) 0) 1 0)))))
   :rule-classes nil
   :hints (("Goal" :cases ((equal r 0) (equal r 1) (equal r 2) (equal r 3) (equal r 4) (equal r 5) (equal r 6) (equal r 7) (equal r 8) (equal r 9) (equal r 10) (equal r 11) (equal r 12) (equal r 13) (equal r 14) (equal r 15))))))

(local
 (defthm fn2-run-restart-count-increments-at-boundary
   (implies (natp i)
            (equal (ceiling (+ 1 i) *fn2-run-restart-interval*)
                   (+ (ceiling i *fn2-run-restart-interval*)
                      (if (equal (mod i *fn2-run-restart-interval*) 0) 1 0))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-ceiling-at-restart-residue (q (floor i 16)) (r (mod i 16))))))))

(local
 (defthm fn2-run-count-directory-groups
   (implies (natp i)
            (equal (len (fn2-run-restart-offsets-spec layout entries i off))
                   (- (ceiling (+ i (len entries)) *fn2-run-restart-interval*)
                      (ceiling i *fn2-run-restart-interval*))))
   :hints (("Goal" :induct (fn2-run-restart-offsets-spec layout entries i off)
            :expand ((fn2-run-restart-offsets-spec layout entries i off) (len entries))
            :in-theory (disable ceiling ceiling-to-floor mod fn2-layout-octets))
           ("Subgoal *1/3" :use fn2-run-restart-count-increments-at-boundary)
           ("Subgoal *1/2" :use fn2-run-restart-count-increments-at-boundary))))

(defthmd fn2-run-directory-count-matches-entries
  (equal (len (fn2-run-restart-offsets-spec layout entries 0 off))
         (ceiling (len entries) *fn2-run-restart-interval*))
  :hints (("Goal" :use ((:instance fn2-run-count-directory-groups (i 0)))
           :in-theory (disable fn2-run-count-directory-groups fn2-run-restart-offsets-spec ceiling ceiling-to-floor))))
