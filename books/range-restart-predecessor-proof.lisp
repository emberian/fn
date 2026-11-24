; The lower restart bound has already passed only keys below the query.
(in-package "ACL2")
(include-book "range-restart-count-proof")
(include-book "range-page-prefix-proof")

(local
 (defthm fn2-run-predecessor-midpoint
   (let ((j (floor (+ lo hi) 2)))
     (implies (and (natp lo) (natp hi) (< lo hi))
              (and (natp j) (<= lo j) (< j hi))))
   :rule-classes nil))

(defthmd fn2-run-restart-search-retains-predecessor
  (let* ((search (fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool))
         (low (car search)))
    (implies (and (natp fuel) (natp lo) (natp hi) (<= lo hi) (natp n) (<= hi n)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (equal query (fn2-overview-range-key-at qbase f))
                  (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool)
                  (or (zp lo)
                      (eq (fn2-run-key-order-spec *fn2-overview-range-key*
                              (nth (* (1- lo) *fn2-run-restart-interval*) rows) query) :lt)))
             (or (zp low)
                 (eq (fn2-run-key-order-spec *fn2-overview-range-key*
                          (nth (* (1- low) *fn2-run-restart-interval*) rows) query) :lt))))
  :hints (("Goal" :do-not '(preprocess)
           :induct (fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool)
           :expand ((fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool))
           :in-theory (disable fn2-run-key-order-spec fn2-overview-range-key-at fn2-run-overview-restart-fields
                  (:definition fn2-run-overview-restart-search) fn2-run-overview-restart-tablep
                  fn2-run-readerp fn2-fieldsp fn2-run-directory fn2-run-header-value fn2-fields-rows nth floor))
          ("Subgoal *1/2" :cases ((eq (fn2-run-key-order-spec *fn2-overview-range-key*
                                  (nth (* 16 (floor (+ lo hi) 2)) rows)
                                  (fn2-overview-range-key-at qbase f)) :lt))
           :use (fn2-run-predecessor-midpoint (:instance fn2-run-midpoint-keeps-restart-table (j (floor (+ lo hi) 2)))))))

(defmacro fn2-run-preceding-restart (n)
  `(if (zp ,n) 0 (1- ,n)))

(local
 (defthm fn2-run-preceding-rows-below-query
   (let* ((offsets (fn2-run-restart-offsets-spec layout rows 0 *fn2-run-entries-base*))
          (j (fn2-run-preceding-restart low)) (idx (* j *fn2-run-restart-interval*)))
     (implies (and (natp low) (<= low (len offsets)) (posp (len offsets))
                   (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                   (or (zp low) (eq (fn2-run-key-order-spec *fn2-overview-range-key* (nth idx rows) query) :lt)))
              (and (natp j) (< j (len offsets)) (< idx (len rows))
                   (fn2-run-overview-prefix-below-p idx rows query))))
   :rule-classes nil
   :hints (("Goal" :cases ((zp low))
            :use ((:instance fn2-run-page-restart-names-row (off *fn2-run-entries-base*) (j (fn2-run-preceding-restart low)))
                  (:instance fn2-run-overview-predecessor-bounds-prefix
                             (i (* *fn2-run-restart-interval* (fn2-run-preceding-restart low)))))
            :expand ((fn2-run-overview-prefix-below-p 0 rows query))
            :in-theory (disable fn2-run-restart-offsets-spec fn2-run-key-order-spec fn2-run-sorted-spec
                                fn2-run-overview-prefix-below-p fn2-run-row-offset nth)))))

(defthmd fn2-run-restart-search-selects-earlier-prefix
  (let* ((n (len offsets))
         (search (fn2-run-overview-restart-search fuel 0 n offsets rows level qbase rb slot gen pk ps pg f pool))
         (low (car search)) (j (if (zp low) 0 (1- low))) (idx (* j *fn2-run-restart-interval*))
         (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
         (query (fn2-overview-range-key-at qbase f)))
    (implies (and (natp fuel) (<= (integer-length n) fuel) (consp rows) (posp (len offsets))
                  (equal offsets (fn2-run-restart-offsets-spec layout rows 0 *fn2-run-entries-base*))
                  (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool))
             (and (natp j) (< j n) (< idx (len rows))
                  (fn2-run-overview-prefix-below-p idx rows query))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-restart-search-fits-budget (lo 0) (hi (len offsets)))
                 (:instance fn2-run-restart-search-retains-predecessor
                            (query (fn2-overview-range-key-at qbase f)) (lo 0) (n (len offsets)) (hi (len offsets)))
                 (:instance fn2-run-preceding-rows-below-query
                     (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
                     (query (fn2-overview-range-key-at qbase f))
                     (low (car (fn2-run-overview-restart-search fuel 0 (len offsets) offsets rows level qbase rb slot gen pk ps pg f pool)))))
           :in-theory (disable fn2-run-overview-restart-search fn2-run-key-order-spec fn2-run-overview-restart-tablep
                               fn2-run-sorted-spec fn2-run-restart-offsets-spec fn2-run-row-offset
                               fn2-overview-range-key-at fn2-run-readerp fn2-fieldsp fn2-run-overview-prefix-below-p
                               len integer-length))))
