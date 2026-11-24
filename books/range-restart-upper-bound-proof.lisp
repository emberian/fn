; The high restart bound is either the end of the page or a row at or
; above the query. The scan from the preceding restart crosses at most one
; interval even when there are many more rows on the page.
(in-package "ACL2")
(include-book "range-restart-predecessor-proof")

(local
 (defthm fn2-run-upper-midpoint
   (let ((j (floor (+ lo hi) 2)))
     (implies (and (natp lo) (natp hi) (< lo hi))
              (and (natp j) (<= lo j) (< j hi))))))

(local
 (defthm fn2-run-restart-search-retains-upper-bound
   (let* ((search (fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool))
          (high (nth 1 search)))
     (implies (and (natp fuel) (natp lo) (natp hi) (<= lo hi) (natp n) (<= hi n)
                   (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                   (fn2-fieldsp f) (fn2-run-readerp rb f)
                   (equal query (fn2-overview-range-key-at qbase f))
                   (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool)
                   (or (equal hi n)
                       (not (eq (fn2-run-key-order-spec *fn2-overview-range-key*
                                  (nth (* hi *fn2-run-restart-interval*) rows) query) :lt))))
              (or (equal high n)
                  (not (eq (fn2-run-key-order-spec *fn2-overview-range-key*
                             (nth (* high *fn2-run-restart-interval*) rows) query) :lt)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :induct (fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool)
            :expand ((fn2-run-overview-restart-search fuel lo hi offsets rows level qbase rb slot gen pk ps pg f pool))
            :in-theory (disable fn2-run-key-order-spec fn2-overview-range-key-at fn2-run-overview-restart-fields
                   (:definition fn2-run-overview-restart-search) fn2-run-overview-restart-tablep
                   fn2-run-readerp fn2-fieldsp fn2-run-directory fn2-run-header-value fn2-fields-rows floor))
           ("Subgoal *1/2" :cases ((eq (fn2-run-key-order-spec *fn2-overview-range-key*
                                   (nth (* 16 (floor (+ lo hi) 2)) rows)
                                   (fn2-overview-range-key-at qbase f)) :lt))
            :use ((:instance fn2-run-midpoint-keeps-restart-table (j (floor (+ lo hi) 2))))))))

(defthmd fn2-run-restart-search-bounds-scan-distance
  (let* ((n (len offsets)) (search (fn2-run-overview-restart-search fuel 0 n offsets rows level qbase rb slot gen pk ps pg f pool))
         (low (nth 0 search)) (first (* *fn2-run-restart-interval* (fn2-run-preceding-restart low)))
         (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
         (query (fn2-overview-range-key-at qbase f)))
    (implies (and (natp fuel) (<= (integer-length n) fuel)
                  (equal offsets (fn2-run-restart-offsets-spec layout rows 0 *fn2-run-entries-base*))
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool))
             (<= (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0))
                 (+ first *fn2-run-restart-interval*))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-restart-search-fits-budget (lo 0) (hi (len offsets)))
                 (:instance fn2-run-restart-search-retains-upper-bound (lo 0) (hi (len offsets)) (n (len offsets))
                            (query (fn2-overview-range-key-at qbase f)))
                 (:instance fn2-run-page-restarts-cover-rows
                            (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
                            (off *fn2-run-entries-base*))
                 (:instance fn2-run-lower-bound-reached-by-row (idx 0) (key *fn2-overview-range-key*)
                            (query (fn2-overview-range-key-at qbase f))
                            (n (* *fn2-run-restart-interval*
                                (nth 1 (fn2-run-overview-restart-search fuel 0 (len offsets) offsets rows level qbase rb slot gen pk ps pg f pool))))))
           :in-theory (disable fn2-run-lower-bound-spec fn2-run-key-order-spec fn2-run-restart-offsets-spec
                     fn2-run-overview-restart-search fn2-run-overview-restart-tablep fn2-overview-range-key-at
                     integer-length fn2-run-readerp fn2-fieldsp nth len))))
