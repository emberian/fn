; At the end of the restart search the same cursor enters the row scan and
; returns the lower bound in the remaining suffix.
(in-package "ACL2")
(include-book "range-restart-probe-proof")

(local
 (defthm fn2-run-restart-reader-shape
   (let ((rf (mv-nth 2 (fn2-run-restart-offset j slot gen rb pk ps pg f pool))))
     (implies (and (fn2-fieldsp f) (fn2-run-readerp rb f))
              (and (fn2-fieldsp rf) (fn2-fields-wfp rf)
                   (equal (fn2-fields-rows rf) (fn2-fields-rows f)))))
   :hints (("Goal" :in-theory (e/d (fn2-run-readerp)
                                  (fn2-run-restart-offset fn2-fieldsp fn2-fields-rows fn2-fields-wfp))))))

(defthmd fn2-run-seek-enters-checked-interval
  (let* ((j (if (zp lo) 0 (1- lo))) (rf (mv-nth 2 (fn2-run-restart-offset j slot gen rb pk ps pg f pool))))
    (implies (and (posp fuel) (natp lo) (natp hi) (<= hi lo) (posp (fn2-run-page-entry-count rb f))
                  (fn2-run-page-restart-word-p j at rb slot gen pk ps pg f pool))
             (equal (fn2-run-seek 3 level fuel lo hi idx 0 qbase rb slot gen pk ps pg qk qs qg f pool)
                    (fn2-run-seek 3 level (1- fuel) lo hi (* *fn2-run-restart-interval* j) at
                                  qbase rb slot gen pk ps pg qk qs qg rf pool))))
  :hints (("Goal" :use ((:instance fn2-run-restart-offset-reads-directory-word
                         (j (if (zp lo) 0 (1- lo))) (base rb) (fn2-fields f) (v at)))
           :do-not '(preprocess)
           :expand ((:free (low high) (fn2-run-seek 3 level fuel low high idx 0 qbase rb slot gen pk ps pg qk qs qg f pool)))
           :in-theory (disable fn2-run-restart-offset fn2-run-seek fn2-run-directory fn2-run-header-value
                               fn2-run-layout-decode fn2-run-layout-compare fn2-fields-rows fn2-run-read-bytes
                               fn2-layout-le fn2-layout-range-code fn2-poolp fn2-pool-wfp fn2-pool-base))))

(defthm fn2-run-seek-checked-interval-lower-bound
  (let* ((j (if (zp lo) 0 (1- lo))) (first (* j *fn2-run-restart-interval*))
         (eb (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))
         (query (fn2-overview-range-key-at qbase f))
         (bound (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query first))
         (seek (fn2-run-seek 3 level fuel lo hi idx 0 qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (and (posp fuel) (natp lo) (natp hi) (<= hi lo) (posp (fn2-run-page-entry-count rb f))
                  (equal (fn2-run-page-entry-count rb f) (+ first (len rows)))
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (posp at) (fn2-run-page-restart-word-p j at rb slot gen pk ps pg f pool)
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (< (cadr bound) (+ first (1- fuel))) (< 1 fuel)
                  (fn2-run-overview-page-rowsp level rows eb slot gen at end pk ps pg f pool))
             (and (equal (list (car seek) (mv-nth 3 seek)) bound)
                  (equal (mv-nth 4 seek) (fn2-run-overview-lower-bound-offset level rows query at))
                  (equal (fn2-run-directory rb (mv-nth 5 seek)) end)
                  (equal (fn2-overview-range-key-at qbase (mv-nth 5 seek)) query))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-seek-enters-checked-interval
                 (:instance fn2-run-restart-keeps-header-and-query (j (if (zp lo) 0 (1- lo))))
                 (:instance fn2-run-page-rows-use-field-count (base (+ rb *fn2-run-reader-entry*))
                      (off at) (end (fn2-run-directory rb f))
                      (f2 (mv-nth 2 (fn2-run-restart-offset (if (zp lo) 0 (1- lo)) slot gen rb pk ps pg f pool))))
                 (:instance fn2-run-overview-seek-to-lower-bound (fuel (1- fuel))
                      (idx (* *fn2-run-restart-interval* (if (zp lo) 0 (1- lo)))) (off at)
                      (f (mv-nth 2 (fn2-run-restart-offset (if (zp lo) 0 (1- lo)) slot gen rb pk ps pg f pool)))))
           :in-theory (e/d (fn2-overview-range-key-at)
               (fn2-run-seek fn2-run-directory fn2-run-page-restart-word-p fn2-run-header-value
                fn2-fields-rows fn2-fields-value fn2-fieldsp fn2-run-readerp fn2-fields-wfp
                fn2-run-overview-page-rowsp fn2-run-lower-bound-spec fn2-run-overview-lower-bound-offset
                fn2-run-restart-offset)))))
