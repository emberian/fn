; Select the index row whose child can contain the first key at the query.
(in-package "ACL2")
(include-book "range-page-cursor-bounds-proof")
(include-book "range-stored-page-search-proof")
(include-book "runs-seek-budget-proof")

(defun fn2-range-index-child-number (lower)
  (let ((i (nfix (cadr lower))))
    (if (or (equal (car lower) :found) (zp i)) i (1- i))))

(local
 (defthmd fn2-range-stored-search-widths
   (let* ((n (fn2-run-page-restart-count rb f))
          (off (fn2-run-overview-lower-bound-offset level rows query *fn2-run-entries-base*)))
     (implies (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool)
              (and (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (unsigned-byte-p 32 n) (unsigned-byte-p 32 off))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-page-selected-offset-fits
                    (base (+ rb *fn2-run-reader-entry*)) (off *fn2-run-entries-base*) (end (fn2-run-directory rb f))))
            :in-theory (e/d (fn2-run-stored-overview-page-p)
                        (fn2-run-overview-page-rowsp fn2-run-overview-lower-bound-offset fn2-run-directory
                         fn2-run-restart-offsets-spec fn2-run-header-value fn2-fields-rows fn2-run-directory-octets
                         fn2-run-read-bytes fn2-poolp fn2-pool-wfp fn2-layout-range-code fn2-pool-base len))))))

(local
 (defthmd fn2-range-page-search-saves-child
   (let* ((seek (fn2-run-seek 3 level fuel 0 n 0 0 qbase rb slot gen pk ps pg qk qs qg f pool))
          (lower (list (car seek) (mv-nth 3 seek)))
          (step (fn2-run-step-seek c 3 nil level fuel 0 n 0 0 qbase slot gen unit counter
                          rb pk ps pg qk qs qg curs f pool))
          (after (mv-nth 1 step)))
     (implies (and (natp c) (< c (fn2-run-cursors-rows curs)) (posp level) (unsigned-byte-p 8 level)
                   (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                   (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 n)
                   (member-eq (car seek) '(:found :absent))
                   (unsigned-byte-p 32 (mv-nth 3 seek)) (unsigned-byte-p 32 (mv-nth 4 seek)))
              (and (equal (car step) :more)
                   (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-child*)
                   (equal (fn2-run-cursors-idx c after) (fn2-range-index-child-number lower))
                   (equal (mv-nth 2 step) (mv-nth 5 seek)))))
   :hints (("Goal" :use ((:instance fn2-range-page-search-keeps-interval-width
                             (sid 3) (lo 0) (hi n) (idx 0) (off 0)))
            :in-theory (e/d (fn2-run-step-seek fn2-range-index-child-number fn2-run-saved-cursor-position)
                       (fn2-run-seek fn2-run-cursor-save fn2-run-cursors-phase fn2-run-cursors-idx fn2-run-cursors-rows))))))

(local
 (defthmd fn2-range-child-number-in-bounds
   (let ((result (fn2-run-lower-bound-spec key rows query 0)))
     (implies (and (consp rows) (unsigned-byte-p 32 (len rows)))
              (and (member-eq (car result) '(:found :absent))
                   (unsigned-byte-p 32 (cadr result))
                   (natp (fn2-range-index-child-number result))
                   (< (fn2-range-index-child-number result) (len rows)))))
   :hints (("Goal" :expand ((len rows)) :use ((:instance fn2-range-lower-bound-result-limits (idx 0)))
            :in-theory (e/d (fn2-range-index-child-number)
                            (fn2-run-lower-bound-spec))))))

(local
 (defthm fn2-range-page-search-result-parts
   (implies (equal (list code idx) result)
            (and (equal code (car result)) (equal idx (cadr result))))
   :rule-classes nil))

(defthmd fn2-range-stored-index-selects-lower-bound-child
  (let* ((n (fn2-run-page-restart-count rb f)) (query (fn2-overview-range-key-at qbase f))
         (lower (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0))
         (step (fn2-run-step-seek c 3 nil level fuel 0 n 0 0 qbase slot gen unit counter
                                  rb pk ps pg qk qs qg curs f pool))
         (after (mv-nth 1 step)) (k (fn2-run-cursors-idx c after)))
    (implies (and (natp c) (< c (fn2-run-cursors-rows curs)) (posp level) (unsigned-byte-p 8 level)
                  (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                  (consp rows) (unsigned-byte-p 32 (len rows)) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (natp fuel) (< (+ (integer-length n) *fn2-run-restart-interval* 1) fuel)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
             (and (equal (car step) :more) (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-child*)
                  (equal k (fn2-range-index-child-number lower)) (natp k) (< k (len rows))
                  (equal (fn2-overview-range-key-at qbase (mv-nth 2 step)) query))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-stored-overview-page-lower-bound
                 (:instance fn2-range-stored-search-widths (query (fn2-overview-range-key-at qbase f)))
                 (:instance fn2-range-page-search-saves-child (n (fn2-run-page-restart-count rb f)))
                 (:instance fn2-range-child-number-in-bounds (key *fn2-overview-range-key*)
                             (query (fn2-overview-range-key-at qbase f)))
                 (:instance fn2-range-page-search-result-parts
                    (result (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0))
                    (code (car (fn2-run-seek 3 level fuel 0 (fn2-run-page-restart-count rb f) 0 0 qbase rb slot gen
                                             pk ps pg qk qs qg f pool)))
                    (idx (mv-nth 3 (fn2-run-seek 3 level fuel 0 (fn2-run-page-restart-count rb f) 0 0 qbase rb slot gen
                                                pk ps pg qk qs qg f pool)))))
           :in-theory (union-theories (theory 'minimal-theory) '(eq not (:e equal) (:e unary--) (:e binary-+))))))
