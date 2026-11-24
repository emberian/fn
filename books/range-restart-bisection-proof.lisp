; Account for the comparisons made by the served binary search, including
; the updated reader fields and the precise remaining scan budget.
(in-package "ACL2")
(include-book "range-restart-table-proof")

(defun-nx fn2-run-overview-restart-search (fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (<= hi lo)) (list lo hi fuel f)
    (let* ((j (floor (+ lo hi) 2)) (at (nth j offsets))
           (row (nth (* j *fn2-run-restart-interval*) rows))
           (less (eq (fn2-run-key-order-spec *fn2-overview-range-key* row (fn2-overview-range-key-at qbase f)) :lt))
           (after (fn2-run-overview-restart-fields level j at rb slot gen pk ps pg f pool)))
      (fn2-run-overview-restart-search (1- fuel) (if less (1+ j) lo) (if less hi j)
            offsets rows level qbase rb slot gen pk ps pg after pool))))

(local
 (defthm fn2-run-restart-midpoint-in-range
   (let ((j (floor (+ lo hi) 2)))
     (implies (and (natp lo) (natp hi) (< lo hi)) (and (natp j) (<= lo j) (< j hi))))
   :rule-classes :rewrite))

(local
 (defthmd fn2-run-restart-one-comparison
   (let* ((j (floor (+ lo hi) 2)) (at (nth j offsets)) (row (nth (* j *fn2-run-restart-interval*) rows))
          (after (fn2-run-overview-restart-fields level j at rb slot gen pk ps pg f pool))
          (less (eq (fn2-run-key-order-spec *fn2-overview-range-key* row (fn2-overview-range-key-at qbase f)) :lt)))
     (implies (and (posp fuel) (natp lo) (natp hi) (< lo hi) (natp n) (<= hi n)
                   (posp (fn2-run-page-entry-count rb f)) (fn2-fieldsp f) (fn2-run-readerp rb f)
                   (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                   (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool))
              (equal (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
                     (fn2-run-seek 3 level (1- fuel) (if less (1+ j) lo) (if less hi j) idx off qbase rb
                                   slot gen pk ps pg qk qs qg after pool))))
   :hints (("Goal" :use ((:instance fn2-run-overview-restart-table-lookup (j (floor (+ lo hi) 2)))
                         (:instance fn2-run-seek-narrows-at-checked-restart (at (nth (floor (+ lo hi) 2) offsets))
                          (row (nth (* *fn2-run-restart-interval* (floor (+ lo hi) 2)) rows))))
            :in-theory (e/d (fn2-run-overview-restart-fields)
                      (floor nth fn2-run-seek fn2-run-overview-restart-tablep fn2-run-readerp fn2-fieldsp
                       fn2-run-header-value fn2-run-directory fn2-run-key-order-spec fn2-overview-range-key-at
                       fn2-run-overview-row-atp fn2-run-page-restart-word-p fn2-run-layout-decode fn2-run-restart-offset))))))

(defthm fn2-run-seek-executes-restart-search
  (let* ((end (fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool))
         (low (nth 0 end)) (high (nth 1 end)) (left (nth 2 end)) (rf (nth 3 end)))
    (implies (and (natp fuel) (natp lo) (natp hi) (<= lo hi) (natp n) (<= hi n)
                  (posp (fn2-run-page-entry-count rb f)) (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool))
             (and (equal (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
                         (fn2-run-seek 3 level left low high idx off qbase rb slot gen pk ps pg qk qs qg rf pool))
                  (equal (fn2-overview-range-key-at qbase rf) (fn2-overview-range-key-at qbase f))
                  (equal (fn2-run-page-entry-count rb rf) (fn2-run-page-entry-count rb f))
                  (equal (fn2-run-page-restart-count rb rf) (fn2-run-page-restart-count rb f))
                  (equal (fn2-run-directory rb rf) (fn2-run-directory rb f))
                  (equal (fn2-fields-rows rf) (fn2-fields-rows f))
                  (fn2-fieldsp rf) (fn2-run-readerp rb rf)
                  (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg rf pool))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :induct (fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool)
           :expand ((fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool))
           :in-theory (disable fn2-run-key-order-spec fn2-overview-range-key-at fn2-run-directory fn2-fields-rows
                               fn2-fieldsp fn2-run-readerp fn2-run-seek fn2-run-header-value
                               (:definition fn2-run-overview-restart-search) fn2-run-overview-restart-fields
                               fn2-run-overview-restart-tablep floor))
          ("Subgoal *1/2" :use (fn2-run-restart-one-comparison
                                (:instance fn2-run-midpoint-keeps-restart-table (j (floor (+ lo hi) 2)))))))
