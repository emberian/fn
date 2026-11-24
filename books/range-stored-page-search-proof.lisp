; A fresh seek on the encoded overview page executes both the restart
; search and a scan of at most one restart interval.
(in-package "ACL2")
(include-book "range-stored-page-scan-proof")
(include-book "range-restart-upper-bound-proof")

(local
 (defthm fn2-run-stored-page-frame
   (implies (and (equal (fn2-fields-rows f2) (fn2-fields-rows f))
                 (equal (fn2-run-directory rb f2) (fn2-run-directory rb f))
                 (equal (fn2-run-page-entry-count rb f2) (fn2-run-page-entry-count rb f))
                 (equal (fn2-run-page-restart-count rb f2) (fn2-run-page-restart-count rb f)))
            (equal (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f2 pool)
                   (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-page-rows-use-field-count (base (+ rb *fn2-run-reader-entry*))
                  (off *fn2-run-entries-base*) (end (fn2-run-directory rb f))))
            :in-theory (e/d (fn2-run-stored-overview-page-p)
                 (fn2-run-overview-page-rowsp fn2-run-directory fn2-run-header-value fn2-run-restart-offsets-spec
                  fn2-layout-range-code fn2-poolp fn2-pool-wfp fn2-pool-base fn2-fields-rows
                  fn2-run-read-bytes fn2-run-directory-octets))))))

(local
 (defthm fn2-run-stored-page-counts
   (let ((offsets (fn2-run-restart-offsets-spec (fn2-run-overview-layout-at level) rows 0 *fn2-run-entries-base*)))
     (implies (and (consp rows) (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
              (and (posp (len offsets))
                   (equal (fn2-run-page-restart-count rb f) (len offsets))
                   (posp (fn2-run-page-entry-count rb f)))))
   :rule-classes nil
   :hints (("Goal" :expand ((:free (layout) (fn2-run-restart-offsets-spec layout rows 0 *fn2-run-entries-base*)))
            :in-theory (e/d (fn2-run-stored-overview-page-p)
                 (fn2-run-restart-offsets-spec fn2-layout-octets fn2-run-overview-page-rowsp
                  fn2-run-directory fn2-run-header-value fn2-layout-range-code fn2-poolp fn2-pool-wfp
                  fn2-pool-base fn2-fields-rows fn2-run-read-bytes fn2-run-directory-octets))))))

(local
 (defmacro fn2-run-stored-page-search ()
   '(fn2-run-overview-restart-search fuel 0 (len offsets) offsets rows level qbase rb slot gen pk ps pg f pool)))

(local
 (defun-nx fn2-run-fresh-stored-search-p (offsets rows level fuel rb qbase slot gen pk ps pg f pool)
   (and (equal offsets (fn2-run-restart-offsets-spec (fn2-run-overview-layout-at level) rows 0 *fn2-run-entries-base*))
        (natp fuel) (< (+ (integer-length (len offsets)) *fn2-run-restart-interval* 1) fuel)
        (consp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
        (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
        (fn2-fieldsp f) (fn2-run-readerp rb f)
        (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))))

(local
 (defthm fn2-run-fresh-stored-search-table
   (implies (fn2-run-fresh-stored-search-p offsets rows level fuel rb qbase slot gen pk ps pg f pool)
            (and (posp (len offsets)) (posp (fn2-run-page-entry-count rb f))
                 (fn2-run-overview-restart-tablep (len offsets) offsets rows level rb slot gen pk ps pg f pool)))
   :rule-classes nil
   :hints (("Goal" :use (fn2-run-stored-page-counts
                       (:instance fn2-run-stored-page-supplies-restart-table (n (len offsets))))
            :in-theory (union-theories (theory 'minimal-theory)
                            '(fn2-run-fresh-stored-search-p natp (:type-prescription len)))))))

(local
 (defthm fn2-run-fresh-stored-search-position
   (let* ((result (fn2-run-stored-page-search)) (low (nth 0 result)) (rf (nth 3 result)))
     (implies (fn2-run-fresh-stored-search-p offsets rows level fuel rb qbase slot gen pk ps pg f pool)
              (and (equal (fn2-run-seek 3 level fuel 0 (len offsets) 0 0 qbase rb slot gen pk ps pg qk qs qg f pool)
                          (fn2-run-seek 3 level (nth 2 result) low (nth 1 result) 0 0 qbase rb slot gen pk ps pg qk qs qg rf pool))
                   (equal (fn2-run-directory rb rf) (fn2-run-directory rb f))
                   (equal (fn2-overview-range-key-at qbase rf) (fn2-overview-range-key-at qbase f))
                   (fn2-fieldsp rf) (fn2-run-readerp rb rf)
                   (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg rf pool))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-run-fresh-stored-search-table
                  (:instance fn2-run-seek-executes-restart-search (lo 0) (hi (len offsets))
                             (idx 0) (off 0) (n (len offsets)))
                  (:instance fn2-run-stored-page-frame (f2 (nth 3 (fn2-run-stored-page-search)))))
            :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-run-fresh-stored-search-p natp (:e natp) (:type-prescription len)))))))

(local
 (defthm fn2-run-fresh-stored-search-bracket
   (let* ((result (fn2-run-stored-page-search)) (low (nth 0 result)) (left (nth 2 result))
          (j (fn2-run-preceding-restart low)) (i (* j *fn2-run-restart-interval*))
          (query (fn2-overview-range-key-at qbase f)))
     (implies (fn2-run-fresh-stored-search-p offsets rows level fuel rb qbase slot gen pk ps pg f pool)
              (and (equal (nth 1 result) low) (natp low) (< j (len offsets))
                   (posp left) (< 1 left) (< (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0)) (+ i (1- left)))
                   (fn2-run-overview-prefix-below-p i rows query))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-fresh-stored-search-table
                  (:instance fn2-run-restart-search-fits-budget (lo 0) (hi (len offsets)))
                  fn2-run-restart-search-selects-earlier-prefix
                  fn2-run-restart-search-bounds-scan-distance)
            :in-theory (e/d (fn2-run-fresh-stored-search-p)
                          (integer-length len fn2-run-restart-offsets-spec fn2-run-overview-restart-search
                           fn2-run-overview-restart-tablep fn2-run-stored-overview-page-p fn2-run-sorted-spec
                           fn2-run-overview-prefix-below-p fn2-run-lower-bound-spec
                           fn2-run-readerp fn2-fieldsp fn2-run-header-value fn2-overview-range-key-at))))))

(local
 (defthm fn2-run-stored-overview-page-search-with-offsets
  (let* ((n (len offsets))
         (query (fn2-overview-range-key-at qbase f))
         (seek (fn2-run-seek 3 level fuel 0 n 0 0 qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (fn2-run-fresh-stored-search-p offsets rows level fuel rb qbase slot gen pk ps pg f pool)
             (and (equal (list (car seek) (mv-nth 3 seek)) (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0))
                  (equal (mv-nth 4 seek) (fn2-run-overview-lower-bound-offset level rows query *fn2-run-entries-base*))
                  (equal (fn2-run-directory rb (mv-nth 5 seek)) (fn2-run-directory rb f))
                  (equal (fn2-overview-range-key-at qbase (mv-nth 5 seek)) query))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-fresh-stored-search-position fn2-run-fresh-stored-search-bracket
                  (:instance fn2-run-seek-scans-stored-page (idx 0) (low (nth 0 (fn2-run-stored-page-search)))
                             (fuel (nth 2 (fn2-run-stored-page-search))) (f (nth 3 (fn2-run-stored-page-search)))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-fresh-stored-search-p))))))

(defthmd fn2-run-stored-overview-page-lower-bound
  (let* ((n (fn2-run-page-restart-count rb f))
         (query (fn2-overview-range-key-at qbase f))
         (seek (fn2-run-seek 3 level fuel 0 n 0 0 qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (and (natp fuel) (< (+ (integer-length n) *fn2-run-restart-interval* 1) fuel)
                  (consp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
             (and (equal (list (car seek) (mv-nth 3 seek)) (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0))
                  (equal (mv-nth 4 seek) (fn2-run-overview-lower-bound-offset level rows query *fn2-run-entries-base*))
                  (equal (fn2-run-directory rb (mv-nth 5 seek)) (fn2-run-directory rb f))
                  (equal (fn2-overview-range-key-at qbase (mv-nth 5 seek)) query))))
  :hints (("Goal" :use ((:instance fn2-run-stored-overview-page-search-with-offsets
              (offsets (fn2-run-restart-offsets-spec (fn2-run-overview-layout-at level) rows 0 *fn2-run-entries-base*)))
             fn2-run-stored-page-counts)
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-fresh-stored-search-p)))))
