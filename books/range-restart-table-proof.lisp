; Every restart in an overview page names the first row of its interval.
(in-package "ACL2")
(include-book "range-restart-state-proof")

(defun-nx fn2-run-overview-restart-tablep (n offsets rows level rb slot gen pk ps pg f pool)
  (if (zp n) t
    (let* ((j (1- n)) (at (nth j offsets))
           (row (nth (* j *fn2-run-restart-interval*) rows))
           (eb (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)))
      (and (fn2-run-page-restart-word-p j at rb slot gen pk ps pg f pool)
           (fn2-run-overview-row-atp level row eb slot gen at end pk ps pg f pool)
           (fn2-run-overview-restart-tablep (1- n) offsets rows level rb slot gen pk ps pg f pool)))))

(defthmd fn2-run-overview-restart-table-lookup
  (let ((at (nth j offsets)) (row (nth (* j *fn2-run-restart-interval*) rows)))
    (implies (and (natp j) (natp n) (< j n)
                  (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool))
             (and (fn2-run-page-restart-word-p j at rb slot gen pk ps pg f pool)
                  (fn2-run-overview-row-atp level row (+ rb *fn2-run-reader-entry*) slot gen at
                                            (fn2-run-directory rb f) pk ps pg f pool))))
  :hints (("Goal" :induct (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool)
           :in-theory (disable fn2-run-page-restart-word-p fn2-run-overview-row-atp
                               fn2-run-directory nth))
          ("Subgoal *1/2" :cases ((equal j (1- n))))))

(defthmd fn2-run-restart-table-uses-header-and-field-count
  (implies (and (equal (fn2-fields-rows f2) (fn2-fields-rows f))
                (equal (fn2-run-directory rb f2) (fn2-run-directory rb f))
                (equal (fn2-run-page-restart-count rb f2) (fn2-run-page-restart-count rb f)))
           (equal (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f2 pool)
                  (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool)))
  :hints (("Goal" :induct (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool)
           :in-theory (disable fn2-fields-rows fn2-run-directory fn2-run-header-value
                               fn2-run-values-layoutp fn2-run-read-bytes fn2-layout-range-code fn2-layout-le
                               fn2-poolp fn2-pool-wfp fn2-pool-base unsigned-byte-p fn2-layout-octets nth))))

(defthmd fn2-run-midpoint-keeps-restart-table
  (let* ((at (nth j offsets))
         (out (fn2-run-overview-restart-fields level j at rb slot gen pk ps pg f pool)))
    (implies (and (natp j) (natp n) (< j n) (natp rb) (natp qbase)
                  (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool))
             (and (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg out pool)
                  (equal (fn2-run-page-entry-count rb out) (fn2-run-page-entry-count rb f))
                  (equal (fn2-run-directory rb out) (fn2-run-directory rb f))
                  (equal (fn2-run-page-restart-count rb out) (fn2-run-page-restart-count rb f))
                  (equal (fn2-overview-range-key-at qbase out) (fn2-overview-range-key-at qbase f))
                  (equal (fn2-fields-rows out) (fn2-fields-rows f))
                  (fn2-fieldsp out) (fn2-run-readerp rb out))))
  :hints (("Goal" :use (fn2-run-overview-restart-table-lookup
                  (:instance fn2-run-restart-comparison-keeps-search-state (at (nth j offsets))
                             (row (nth (* j *fn2-run-restart-interval*) rows)))
                  (:instance fn2-run-restart-table-uses-header-and-field-count
                             (f2 (fn2-run-overview-restart-fields level j (nth j offsets) rb slot gen pk ps pg f pool))))
           :in-theory (theory 'minimal-theory))))
