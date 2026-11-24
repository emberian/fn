; Derive the search table from the on-page rows, serialized directory and
; decoded header, so callers need no per-probe read or comparison hypothesis.
(in-package "ACL2")
(include-book "range-stored-page-rows-proof")
(include-book "range-restart-table-proof")
(include-book "runs-restart-lookup-proof")

(defun-nx fn2-run-stored-overview-page-p (rows level rb slot gen pk ps pg f pool)
  (let* ((layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
         (offsets (fn2-run-restart-offsets-spec layout rows 0 *fn2-run-entries-base*))
         (dir (fn2-run-directory rb f)) (end (+ dir (* 4 (len offsets)))))
    (and (natp rb) (< (+ rb *fn2-run-reader-restart*) (fn2-fields-rows f))
         (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
         (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
         (natp dir) (unsigned-byte-p 32 end)
         (equal (fn2-run-page-entry-count rb f) (len rows))
         (equal (fn2-run-page-restart-count rb f) (len offsets))
         (fn2-run-overview-page-rowsp level rows (+ rb *fn2-run-reader-entry*) slot gen
                                      *fn2-run-entries-base* dir pk ps pg f pool)
         (equal (fn2-layout-range-code slot gen dir end nil pk ps pg pool) :ok)
         (equal (fn2-run-read-bytes (* 4 (len offsets)) slot gen dir pk ps pg pool)
                (fn2-run-directory-octets offsets)))))

(local
 (defthm fn2-run-readable-directory-subrange
   (implies (and (natp start) (natp end) (natp lo) (natp hi)
                 (<= start lo) (<= lo hi) (<= hi end)
                 (equal (fn2-layout-range-code slot gen start end nil pk ps pg pool) :ok))
            (equal (fn2-layout-range-code slot gen lo hi nil pk ps pg pool) :ok))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code)
                                    (fn2-pool-readable-code fn2-pool-slot-fill fn2-pool-slot-base
                                     fn2-pool-capacity-bytes))))))

(defthm fn2-run-stored-overview-restart
  (let* ((layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
         (offsets (fn2-run-restart-offsets-spec layout rows 0 *fn2-run-entries-base*))
         (at (nth j offsets)) (idx (* j *fn2-run-restart-interval*)) (dir (fn2-run-directory rb f)))
    (implies (and (natp j) (< j (len offsets))
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
             (and (fn2-run-page-restart-word-p j at rb slot gen pk ps pg f pool)
                  (fn2-run-overview-row-atp level (nth idx rows) (+ rb *fn2-run-reader-entry*)
                                            slot gen at dir pk ps pg f pool))))
  :rule-classes nil
  :hints (("Goal" :use
           ((:instance fn2-run-page-restart-names-row
               (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
               (off *fn2-run-entries-base*))
            (:instance fn2-run-overview-page-suffix (i (* j *fn2-run-restart-interval*))
               (base (+ rb *fn2-run-reader-entry*)) (off *fn2-run-entries-base*) (end (fn2-run-directory rb f)))
            (:instance fn2-run-read-directory-index (at (fn2-run-directory rb f))
               (offsets (fn2-run-restart-offsets-spec
                  (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*)
                  rows 0 *fn2-run-entries-base*)))
            (:instance fn2-run-readable-directory-subrange
               (start (fn2-run-directory rb f))
               (end (+ (fn2-run-directory rb f) (* 4 (fn2-run-page-restart-count rb f))))
               (lo (+ (fn2-run-directory rb f) (* 4 j))) (hi (+ 4 (fn2-run-directory rb f) (* 4 j)))))
           :in-theory (e/d (fn2-run-stored-overview-page-p fn2-run-page-restart-word-p)
                          (fn2-run-overview-page-rowsp fn2-run-overview-row-atp fn2-run-directory fn2-run-header-value
                           fn2-run-read-bytes fn2-run-directory-octets fn2-run-restart-offsets-spec fn2-layout-le
                           fn2-run-row-offset fn2-layout-range-code fn2-fields-rows fn2-poolp fn2-pool-wfp
                           fn2-pool-base nth nthcdr)))))

(defthmd fn2-run-stored-page-supplies-restart-table
  (let* ((layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
         (offsets (fn2-run-restart-offsets-spec layout rows 0 *fn2-run-entries-base*)))
    (implies (and (natp n) (<= n (len offsets))
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
             (fn2-run-overview-restart-tablep n offsets rows level rb slot gen pk ps pg f pool)))
  :hints (("Goal" :induct (fn2-layout-le n 0) :do-not '(preprocess)
           :expand ((:free (xs) (fn2-run-overview-restart-tablep n xs rows level rb slot gen pk ps pg f pool)))
           :in-theory (disable fn2-run-stored-overview-page-p fn2-run-page-restart-word-p
                               fn2-run-overview-row-atp fn2-run-restart-offsets-spec fn2-run-directory nth))
          ("Subgoal *1/2" :use ((:instance fn2-run-stored-overview-restart (j (1- n)))))))
