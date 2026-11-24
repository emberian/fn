; Once the restart bounds meet, the scan returns the lower bound for the
; entire stored page, including its byte offset and the unchanged query.
(in-package "ACL2")
(include-book "range-stored-restarts-proof")
(include-book "range-restart-scan-proof")
(include-book "range-restart-predecessor-proof")

(defmacro fn2-run-overview-layout-at (level)
  `(if (and (integerp ,level) (< 0 ,level)) *fn2-overview-index* *fn2-overview-entry*))

(local
 (defthm fn2-run-suffix-row-count
   (implies (and (natp i) (<= i (len rows)))
            (equal (len (nthcdr i rows)) (- (len rows) i)))
   :hints (("Goal" :induct (nthcdr i rows)))))

(defthm fn2-run-stored-scan-input
   (let* ((layout (fn2-run-overview-layout-at level))
          (offsets (fn2-run-restart-offsets-spec layout rows 0 *fn2-run-entries-base*))
          (i (* j *fn2-run-restart-interval*))
          (at (fn2-run-row-offset i layout rows *fn2-run-entries-base*)))
     (implies (and (natp j) (< j (len offsets))
                   (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
              (and (posp at) (< i (len rows))
                   (equal (fn2-run-page-entry-count rb f) (+ i (len (nthcdr i rows))))
                   (posp (fn2-run-page-entry-count rb f))
                   (fn2-run-page-restart-word-p j at rb slot gen pk ps pg f pool)
                   (fn2-run-overview-page-rowsp level (nthcdr i rows) (+ rb *fn2-run-reader-entry*) slot gen at
                                                (fn2-run-directory rb f) pk ps pg f pool))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-run-stored-overview-restart
                  (:instance fn2-run-page-restart-names-row (layout (fn2-run-overview-layout-at level))
                             (off *fn2-run-entries-base*))
                  (:instance fn2-run-overview-page-suffix (i (* j *fn2-run-restart-interval*))
                             (base (+ rb *fn2-run-reader-entry*)) (off *fn2-run-entries-base*) (end (fn2-run-directory rb f))))
            :in-theory (e/d (fn2-run-stored-overview-page-p)
                 (fn2-run-page-restart-word-p fn2-run-overview-row-atp fn2-run-overview-page-rowsp
                  fn2-run-directory fn2-run-header-value fn2-run-restart-offsets-spec fn2-run-row-offset
                  fn2-layout-range-code fn2-poolp fn2-pool-wfp fn2-pool-base fn2-fields-rows
                  fn2-run-read-bytes fn2-run-directory-octets nth nthcdr)))))

(defthmd fn2-run-seek-scans-stored-page
  (let* ((j (fn2-run-preceding-restart low)) (i (* j *fn2-run-restart-interval*))
         (offsets (fn2-run-restart-offsets-spec (fn2-run-overview-layout-at level) rows 0 *fn2-run-entries-base*))
         (query (fn2-overview-range-key-at qbase f))
         (bound (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0))
         (seek (fn2-run-seek 3 level fuel low low idx 0 qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (and (posp fuel) (< 1 fuel) (< (cadr bound) (+ i (1- fuel)))
                  (natp low) (< j (len offsets))
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool)
                  (fn2-run-overview-prefix-below-p i rows query))
             (and (equal (list (car seek) (mv-nth 3 seek)) bound)
                  (equal (mv-nth 4 seek) (fn2-run-overview-lower-bound-offset level rows query *fn2-run-entries-base*))
                  (equal (fn2-run-directory rb (mv-nth 5 seek)) (fn2-run-directory rb f))
                  (equal (fn2-overview-range-key-at qbase (mv-nth 5 seek)) query))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-stored-scan-input (j (fn2-run-preceding-restart low)))
                 (:instance fn2-run-overview-lower-bound-skips-prefix (i 0)
                   (n (* *fn2-run-restart-interval* (fn2-run-preceding-restart low)))
                   (query (fn2-overview-range-key-at qbase f)) (off *fn2-run-entries-base*))
                 (:instance fn2-run-seek-checked-interval-lower-bound (hi low) (lo low)
                   (rows (nthcdr (* *fn2-run-restart-interval* (fn2-run-preceding-restart low)) rows))
                   (at (fn2-run-row-offset (* *fn2-run-restart-interval* (fn2-run-preceding-restart low))
                              (fn2-run-overview-layout-at level) rows *fn2-run-entries-base*))))
           :in-theory (disable fn2-run-seek fn2-run-stored-overview-page-p fn2-run-overview-prefix-below-p
                       fn2-run-page-restart-word-p fn2-run-row-offset fn2-run-restart-offsets-spec
                       fn2-run-overview-page-rowsp fn2-run-lower-bound-spec fn2-run-overview-lower-bound-offset
                       fn2-run-directory fn2-run-header-value fn2-overview-range-key-at fn2-run-readerp fn2-fieldsp nthcdr))))
