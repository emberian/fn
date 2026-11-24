; Connect the complete lower-bound search to the concrete leaf delivery.
; Both a key match and a gap before a row name that row's stored bytes.
(in-package "ACL2")
(include-book "range-stored-page-search-proof")
(include-book "runs-overview-cursor-id-proof")

(local
 (defun-nx fn2-run-lower-bound-offset-walk (rows key query level off idx)
   (if (and (consp rows) (eq (fn2-run-key-order-spec key (car rows) query) :lt))
       (fn2-run-lower-bound-offset-walk (cdr rows) key query level
                 (fn2-run-overview-next-offset level (car rows) off) (1+ idx))
     idx)))

(local
 (defthm fn2-run-lower-bound-row-address
   (let* ((result (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query idx))
          (n (- (cadr result) idx)))
     (implies (natp idx)
              (and (natp n) (<= n (len rows))
                   (equal (fn2-run-row-offset n (fn2-run-overview-layout-at level) rows off)
                          (fn2-run-overview-lower-bound-offset level rows query off)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-run-lower-bound-offset-walk rows *fn2-overview-range-key* query level off idx)
            :do-not '(preprocess)
            :expand ((fn2-run-lower-bound-spec *fn2-overview-range-key* rows query idx)
                     (fn2-run-overview-lower-bound-offset level rows query off)
                     (:free (n layout) (fn2-run-row-offset n layout rows off)) (len rows))
            :in-theory (e/d (fn2-run-overview-next-offset)
                     (fn2-layout-octets fn2-run-key-order-spec fn2-run-lower-bound-spec
                      fn2-run-row-offset fn2-run-overview-lower-bound-offset))))))

(local
 (defthm fn2-run-stored-row-after-field-change
   (let ((at (fn2-run-row-offset i *fn2-overview-entry* rows *fn2-run-entries-base*)))
     (implies (and (natp i) (< i (len rows)) (equal (fn2-fields-rows f2) (fn2-fields-rows f))
                   (equal (fn2-run-directory rb f2) (fn2-run-directory rb f))
                   (fn2-run-stored-overview-page-p rows 0 rb slot gen pk ps pg f pool))
              (and (posp at)
                   (fn2-run-overview-row-atp 0 (nth i rows) (+ rb *fn2-run-reader-entry*) slot gen at
                                              (fn2-run-directory rb f2) pk ps pg f2 pool))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-overview-page-suffix (level 0) (base (+ rb *fn2-run-reader-entry*))
                            (off *fn2-run-entries-base*) (end (fn2-run-directory rb f)) (f f2))
                         (:instance fn2-run-page-rows-use-field-count (level 0) (base (+ rb *fn2-run-reader-entry*))
                            (off *fn2-run-entries-base*) (end (fn2-run-directory rb f))))
            :in-theory (e/d (fn2-run-stored-overview-page-p)
                      (fn2-run-overview-row-atp fn2-run-overview-page-rowsp fn2-run-row-offset
                       fn2-run-directory fn2-run-header-value fn2-run-restart-offsets-spec fn2-run-directory-octets
                       fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code fn2-run-read-bytes fn2-fields-rows))))))

(local
 (defthm fn2-run-bound-selectors
   (implies (equal (list code index) result)
            (and (equal (car result) code) (equal (cadr result) index)))
   :rule-classes nil))

(local
 (defmacro fn2-run-fresh-leaf-seek ()
   '(fn2-run-seek 3 0 fuel 0 (fn2-run-page-restart-count rb f) 0 0 qbase rb slot gen pk ps pg qk qs qg f pool)))

(local
 (defthm fn2-run-leaf-index-natural
   (implies (natp idx) (natp (cadr (fn2-run-lower-bound-spec key rows query idx))))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (fn2-run-lower-bound-spec key rows query idx)
            :in-theory (disable fn2-run-key-order-spec)))))

(defthmd fn2-run-stored-leaf-locates-head
  (let* ((n (fn2-run-page-restart-count rb f)) (query (fn2-overview-range-key-at qbase f))
         (i (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0)))
         (seek (fn2-run-seek 3 0 fuel 0 n 0 0 qbase rb slot gen pk ps pg qk qs qg f pool))
         (after (mv-nth 5 seek)) (at (mv-nth 4 seek)))
    (implies (and (natp fuel) (< (+ (integer-length n) *fn2-run-restart-interval* 1) fuel)
                  (consp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows) (< i (len rows))
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows 0 rb slot gen pk ps pg f pool))
             (and (equal (mv-nth 3 seek) i) (natp i) (posp at)
                  (fn2-run-overview-row-atp 0 (nth i rows) (+ rb *fn2-run-reader-entry*) slot gen at
                                            (fn2-run-directory rb after) pk ps pg after pool))))
  :hints (("Goal" :use ((:instance fn2-run-bound-selectors
                          (code (car (fn2-run-fresh-leaf-seek))) (index (mv-nth 3 (fn2-run-fresh-leaf-seek)))
                          (result (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0)))
                       (:instance fn2-run-seek-shape (sid 3) (lv 0) (lo 0) (hi (fn2-run-page-restart-count rb f)) (steps fuel)
                             (idx 0) (off 0) (fn2-fields f) (fn2-pool pool))
                       (:instance fn2-run-stored-overview-page-lower-bound (level 0))
                       (:instance fn2-run-lower-bound-row-address (idx 0) (level 0) (off *fn2-run-entries-base*)
                                  (query (fn2-overview-range-key-at qbase f)))
                       (:instance fn2-run-stored-row-after-field-change
                            (i (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0)))
                            (f2 (mv-nth 5 (fn2-run-seek 3 0 fuel 0 (fn2-run-page-restart-count rb f) 0 0 qbase rb slot gen pk ps pg qk qs qg f pool)))))
           :in-theory (disable fn2-run-seek fn2-run-directory fn2-run-header-value fn2-run-readerp
                     fn2-run-stored-overview-page-p fn2-fieldsp fn2-fields-rows fn2-run-overview-row-atp fn2-run-sorted-spec
                     fn2-run-lower-bound-spec fn2-run-row-offset fn2-run-overview-lower-bound-offset fn2-overview-range-key-at nth integer-length))))

(local
 (defthm fn2-run-leaf-delivers-stored-field
   (let* ((step (fn2-run-step-deliver c 3 i at slot gen unit counter rb pk ps pg curs paths f pool))
          (base (+ rb *fn2-run-reader-entry*)) (path (fn2-run-path-row c 0)))
     (implies (and (natp rb) (natp c) (< c (fn2-run-cursors-rows curs)) (< path (fn2-run-paths-rows paths))
                   (natp i) (< i (fn2-run-paths-entries path paths)) (unsigned-byte-p 32 (1+ i))
                   (posp at) (natp j) (< j 4) (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                   (fn2-run-overview-row-atp 0 row base slot gen at (fn2-run-directory rb f) pk ps pg f pool))
              (and (equal (car step) :entry)
                   (equal (fn2-run-cursors-idx c (mv-nth 1 step)) (1+ i))
                   (equal (fn2-fields-value (+ base j) (mv-nth 2 step)) (nth j row)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-overview-cursor-supplies-source-id (idx i) (off at)))
            :in-theory (e/d (fn2-run-overview-row-atp)
                        (fn2-run-step-deliver fn2-fields-value fn2-run-cursors-idx fn2-run-directory fn2-fields-rows
                         fn2-run-cursors-rows fn2-run-path-row fn2-run-paths-rows fn2-run-paths-entries
                         fn2-run-values-layoutp fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-octets
                         fn2-run-read-bytes fn2-layout-range-code unsigned-byte-p nth))))))

(defthmd fn2-run-stored-leaf-supplies-source-head
  (let* ((n (fn2-run-page-restart-count rb f)) (query (fn2-overview-range-key-at qbase f))
         (i (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0)))
         (seek (fn2-run-seek 3 0 fuel 0 n 0 0 qbase rb slot gen pk ps pg qk qs qg f pool)) (path (fn2-run-path-row c 0))
         (step (fn2-run-step-deliver c 3 (mv-nth 3 seek) (mv-nth 4 seek) slot gen unit counter rb pk ps pg
                                     curs paths (mv-nth 5 seek) pool)))
    (implies (and (natp fuel) (< (+ (integer-length n) *fn2-run-restart-interval* 1) fuel)
                  (consp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (unsigned-byte-p 32 (len rows)) (< i (len rows)) (natp j) (< j 4)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (natp c) (< c (fn2-run-cursors-rows curs)) (< path (fn2-run-paths-rows paths))
                  (equal (fn2-run-paths-entries path paths) (len rows))
                  (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows 0 rb slot gen pk ps pg f pool))
             (and (equal (car step) :entry)
                  (equal (fn2-run-cursors-idx c (mv-nth 1 step)) (1+ i))
                  (equal (fn2-fields-value (+ rb *fn2-run-reader-entry* j) (mv-nth 2 step)) (nth j (nth i rows))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-stored-leaf-locates-head
                 (:instance fn2-run-leaf-delivers-stored-field
                       (i (mv-nth 3 (fn2-run-fresh-leaf-seek))) (at (mv-nth 4 (fn2-run-fresh-leaf-seek)))
                       (row (nth (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0)) rows))
                       (f (mv-nth 5 (fn2-run-fresh-leaf-seek)))))
           :in-theory (disable fn2-run-seek fn2-run-step-deliver fn2-run-cursors-idx fn2-fields-value
                     fn2-run-directory fn2-run-header-value fn2-run-readerp fn2-run-cursors-rows fn2-run-path-row
                     fn2-run-paths-rows fn2-run-paths-entries fn2-run-stored-overview-page-p fn2-fieldsp
                     fn2-run-overview-row-atp fn2-run-sorted-spec fn2-run-lower-bound-spec fn2-overview-range-key-at nth
                     integer-length len))))
