; The scan costs one comparison past the keys below the query.
(in-package "ACL2")
(include-book "range-page-scan-state-proof")

(local
 (defthm fn2-run-overview-seek-after-last-row
 (implies (and (posp fuel) (natp idx) (equal idx (fn2-run-page-entry-count rb f)) (posp off)
               (natp lo) (natp hi) (<= hi lo))
          (equal (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
                 (list :absent lo hi idx off f)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (idx) (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
          :in-theory (disable fn2-run-restart-offset fn2-run-layout-decode fn2-run-layout-compare fn2-run-directory fn2-run-header-value fn2-run-seek)))))

(local
 (defthm fn2-overview-key-order-cases
 (member-eq (fn2-run-key-order-spec *fn2-overview-range-key* row query) '(:eq :lt :gt))
 :hints (("Goal" :in-theory (disable nfix)))))

(local
 (defun-nx fn2-run-overview-page-walk (rows level fuel idx off rb slot gen pk ps pg f pool)
 (if (atom rows) (list fuel idx off f)
   (let* ((read (fn2-run-layout-decode 3 level (+ rb *fn2-run-reader-entry*) slot gen off
                         (fn2-run-directory rb f) pk ps pg f pool)))
     (fn2-run-overview-page-walk (cdr rows) level (1- fuel) (1+ idx)
                         (fn2-run-overview-next-offset level (car rows) off) rb
                         slot gen pk ps pg (mv-nth 2 read) pool)))))

(defun-nx fn2-run-overview-lower-bound-offset (level rows query off)
 (if (and (consp rows) (eq (fn2-run-key-order-spec *fn2-overview-range-key* (car rows) query) :lt))
     (fn2-run-overview-lower-bound-offset level (cdr rows) query (fn2-run-overview-next-offset level (car rows) off))
   off))

(local
 (defthm fn2-run-lower-bound-index-limits
 (let ((index (cadr (fn2-run-lower-bound-spec key rows query idx))))
  (implies (natp idx) (and (natp index) (<= idx index) (<= index (+ idx (len rows))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-run-lower-bound-spec key rows query idx)
          :in-theory (disable fn2-run-key-order-spec)))))

(defthm fn2-run-overview-seek-to-lower-bound
 (let* ((base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)) (query (fn2-overview-range-key-at qbase f))
        (seek (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))
        (rf (mv-nth 5 seek)))
  (implies (and (natp rb) (natp qbase) (< (1+ qbase) base) (natp lo) (natp hi) (<= hi lo)
                (natp idx) (posp off) (posp fuel)
                (< (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query idx)) (+ idx fuel))
                (equal (fn2-run-page-entry-count rb f) (+ idx (len rows)))
                (fn2-fieldsp f) (fn2-fields-wfp f)
                (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool))
           (and (equal (list (car seek) (mv-nth 3 seek)) (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query idx))
                (equal (mv-nth 4 seek) (fn2-run-overview-lower-bound-offset level rows query off))
                (equal (fn2-run-page-entry-count rb rf) (fn2-run-page-entry-count rb f))
                (equal (fn2-run-directory rb rf) end) (equal (fn2-overview-range-key-at qbase rf) query))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-run-overview-page-walk rows level fuel idx off rb slot gen pk ps pg f pool)
          :do-not '(preprocess generalize fertilize eliminate-destructors)
          :expand ((len rows) (:free (query) (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query idx))
                   (:free (query) (fn2-run-overview-lower-bound-offset level rows query off)))
          :in-theory (e/d (fn2-run-overview-next-offset)
                    (fn2-run-overview-page-rowsp fn2-run-overview-row-atp fn2-run-layout-decode fn2-run-seek
                     fn2-layout-octets fn2-run-key-order-spec fn2-run-lower-bound-spec
                     fn2-run-overview-lower-bound-offset fn2-fields-rows fn2-fieldsp fn2-fields-wfp
                     fn2-run-header-value fn2-run-directory fn2-overview-range-key-at)))
         ("Subgoal *1/1" :use (fn2-run-overview-seek-after-last-row))
         ("Subgoal *1/2" :use ((:instance fn2-run-lower-bound-index-limits (key *fn2-overview-range-key*) (rows (cdr rows)) (idx (1+ idx)) (query (fn2-overview-range-key-at qbase f)))
                    fn2-run-overview-page-scan-tail
                    (:instance fn2-run-overview-seek-first-row (row (car rows)))
                    (:instance fn2-overview-key-order-cases (row (car rows)) (query (fn2-overview-range-key-at qbase f)))))))

(defthm fn2-run-overview-seek-page-lower-bound
 (let* ((base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)) (query (fn2-overview-range-key-at qbase f))
        (seek (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))
        (rf (mv-nth 5 seek)))
  (implies (and (natp rb) (natp qbase) (< (1+ qbase) base) (natp lo) (natp hi) (<= hi lo)
                (natp idx) (posp off) (natp fuel) (< (len rows) fuel)
                (equal (fn2-run-page-entry-count rb f) (+ idx (len rows)))
                (fn2-fieldsp f) (fn2-fields-wfp f)
                (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool))
           (and (equal (list (car seek) (mv-nth 3 seek)) (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query idx))
                (equal (mv-nth 4 seek) (fn2-run-overview-lower-bound-offset level rows query off))
                (equal (fn2-run-page-entry-count rb rf) (fn2-run-page-entry-count rb f))
                (equal (fn2-run-directory rb rf) end) (equal (fn2-overview-range-key-at qbase rf) query))))
 :rule-classes nil
 :hints (("Goal" :use (fn2-run-overview-seek-to-lower-bound
                (:instance fn2-run-lower-bound-index-limits (key *fn2-overview-range-key*)
                   (query (fn2-overview-range-key-at qbase f))))
          :in-theory (disable fn2-run-overview-page-rowsp fn2-run-lower-bound-spec
                     fn2-run-overview-lower-bound-offset fn2-run-seek fn2-run-directory
                     fn2-run-header-value fn2-overview-range-key-at fn2-fieldsp fn2-fields-wfp))))

(local
 (defun fn2-run-restart-distance-induct (n rows idx)
 (declare (xargs :verify-guards nil))
 (if (or (zp n) (atom rows)) idx (fn2-run-restart-distance-induct (1- n) (cdr rows) (1+ idx)))))

(local
 (defthm fn2-run-lower-bound-reached-by-row
 (implies (and (natp idx) (natp n)
               (or (<= (len rows) n) (not (eq (fn2-run-key-order-spec key (nth n rows) query) :lt))))
          (<= (cadr (fn2-run-lower-bound-spec key rows query idx)) (+ idx n)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-run-restart-distance-induct n rows idx)
          :expand ((fn2-run-lower-bound-spec key rows query idx) (nth n rows) (len rows))
          :in-theory (disable fn2-run-key-order-spec)))))

(defthm fn2-run-overview-seek-restart-interval
 (let* ((base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)) (query (fn2-overview-range-key-at qbase f))
        (seek (fn2-run-seek 3 level (1+ *fn2-run-restart-interval*) lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))
        (rf (mv-nth 5 seek)))
  (implies (and (natp rb) (natp qbase) (< (1+ qbase) base) (natp lo) (natp hi) (<= hi lo)
                (natp idx) (posp off) (or (<= (len rows) *fn2-run-restart-interval*)
                    (not (eq (fn2-run-key-order-spec *fn2-overview-range-key*
                               (nth *fn2-run-restart-interval* rows) query) :lt)))
                (equal (fn2-run-page-entry-count rb f) (+ idx (len rows)))
                (fn2-fieldsp f) (fn2-fields-wfp f)
                (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool))
           (and (equal (list (car seek) (mv-nth 3 seek)) (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query idx))
                (equal (mv-nth 4 seek) (fn2-run-overview-lower-bound-offset level rows query off))
                (equal (fn2-run-page-entry-count rb rf) (fn2-run-page-entry-count rb f))
                (equal (fn2-run-directory rb rf) end) (equal (fn2-overview-range-key-at qbase rf) query))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-overview-seek-to-lower-bound (fuel (1+ *fn2-run-restart-interval*)))
                (:instance fn2-run-lower-bound-reached-by-row (key *fn2-overview-range-key*) (n *fn2-run-restart-interval*)
                   (query (fn2-overview-range-key-at qbase f))))
          :in-theory (disable fn2-run-overview-page-rowsp fn2-run-lower-bound-spec fn2-run-key-order-spec nth
                     fn2-run-overview-lower-bound-offset fn2-run-seek fn2-run-directory
                     fn2-run-header-value fn2-overview-range-key-at fn2-fieldsp fn2-fields-wfp))))
