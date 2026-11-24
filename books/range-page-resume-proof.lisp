; A successful page search can be interrupted at any fuel boundary.
; Resume all four coordinates and the decoder's field rows together.
(in-package "ACL2")
(include-book "range-stored-page-search-proof")

(include-book "runs-seek-budget-proof")

(defun-nx fn2-run-page-seek-slices (calls budget sid lv lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
  (if (zp calls) (list :more lo hi idx off f)
    (let ((step (fn2-run-seek sid lv budget lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
      (if (eq (car step) :more)
          (fn2-run-page-seek-slices (1- calls) budget sid lv (mv-nth 1 step) (mv-nth 2 step)
                      (mv-nth 3 step) (mv-nth 4 step) qbase rb slot gen pk ps pg qk qs qg (mv-nth 5 step) pool)
        step))))

(defthmd fn2-run-page-seek-resumes-to-completion
  (let ((whole (fn2-run-seek sid lv (* calls budget) lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (and (natp calls) (natp budget) (not (equal (car whole) :more)))
             (equal (fn2-run-page-seek-slices calls budget sid lv lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
                    whole)))
  :hints (("Goal" :do-not '(preprocess)
           :induct (fn2-run-page-seek-slices calls budget sid lv lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
           :expand ((fn2-run-page-seek-slices calls budget sid lv lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))
           :in-theory (e/d ((:induction fn2-run-page-seek-slices)) (fn2-run-seek (:definition fn2-run-page-seek-slices))))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use ((:instance fn2-run-seek-resumes-with-remaining-budget (steps budget) (extra (* (1- calls) budget))))
                 :expand ((fn2-run-page-seek-slices calls budget sid lv lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
                          (fn2-run-seek sid lv 0 lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))))))

(local
 (defthm fn2-run-page-bound-returns-position
   (member-eq (car (fn2-run-lower-bound-spec key rows query i)) '(:found :absent))
   :hints (("Goal" :induct (fn2-run-lower-bound-spec key rows query i)
            :in-theory (disable fn2-run-key-order-spec)))))

(defthmd fn2-run-stored-page-lower-bound-by-slices
  (let* ((n (fn2-run-page-restart-count rb f)) (query (fn2-overview-range-key-at qbase f))
         (seek (fn2-run-page-seek-slices calls budget 3 level 0 n 0 0 qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (and (natp calls) (posp budget)
                  (< (+ (integer-length n) *fn2-run-restart-interval* 1) (* calls budget))
                  (consp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
             (and (equal (list (car seek) (mv-nth 3 seek))
                         (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0))
                  (equal (mv-nth 4 seek) (fn2-run-overview-lower-bound-offset level rows query *fn2-run-entries-base*))
                  (equal (fn2-run-directory rb (mv-nth 5 seek)) (fn2-run-directory rb f))
                  (equal (fn2-overview-range-key-at qbase (mv-nth 5 seek)) query))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-page-seek-resumes-to-completion (sid 3) (lv level) (lo 0)
                            (hi (fn2-run-page-restart-count rb f)) (idx 0) (off 0))
                 (:instance fn2-run-stored-overview-page-lower-bound (fuel (* calls budget)))
                 (:instance fn2-run-page-bound-returns-position (key *fn2-overview-range-key*)
                            (query (fn2-overview-range-key-at qbase f)) (i 0)))
           :in-theory (disable fn2-run-page-bound-returns-position fn2-run-seek fn2-run-page-seek-slices
                        fn2-run-header-value fn2-run-stored-overview-page-p fn2-run-readerp fn2-fieldsp
                        fn2-run-lower-bound-spec fn2-run-sorted-spec fn2-run-directory fn2-overview-range-key-at
                        fn2-run-overview-lower-bound-offset integer-length))))

(defthmd fn2-run-saved-page-search-returns-lower-bound
  (let* ((n (fn2-run-page-restart-count rb f)) (query (fn2-overview-range-key-at qbase f))
         (first (fn2-run-seek 3 level steps 0 n 0 0 qbase rb slot gen pk ps pg qk qs qg f pool))
         (step (fn2-run-step-seek c 3 nil level steps 0 n 0 0 qbase slot gen unit counter
                                  rb pk ps pg qk qs qg curs f pool)) (after (mv-nth 1 step))
         (resume (fn2-run-seek 3 level extra (fn2-run-cursors-lo c after) (fn2-run-cursors-hi c after)
                               (fn2-run-cursors-idx c after) (fn2-run-cursors-off c after)
                               qbase rb slot gen pk ps pg qk qs qg (mv-nth 2 step) pool)))
    (implies (and (posp steps) (natp extra) (< (+ (integer-length n) *fn2-run-restart-interval* 1) (+ steps extra))
                  (consp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool)
                  (natp c) (< c (fn2-run-cursors-rows curs)) (unsigned-byte-p 8 level)
                  (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (equal (car first) :more) (unsigned-byte-p 32 (mv-nth 1 first)) (unsigned-byte-p 32 (mv-nth 2 first))
                  (unsigned-byte-p 32 (mv-nth 3 first)) (unsigned-byte-p 32 (mv-nth 4 first)))
             (and (equal (car step) :more) (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-seek*)
                  (equal (list (car resume) (mv-nth 3 resume)) (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0))
                  (equal (mv-nth 4 resume) (fn2-run-overview-lower-bound-offset level rows query *fn2-run-entries-base*))
                  (equal (fn2-overview-range-key-at qbase (mv-nth 5 resume)) query))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-yielded-cursor-preserves-page-search (sid 3) (lo 0)
                            (hi (fn2-run-page-restart-count rb f)) (idx 0) (off 0))
                 (:instance fn2-run-stored-overview-page-lower-bound (fuel (+ steps extra)))
                 (:instance fn2-run-page-bound-returns-position (key *fn2-overview-range-key*)
                            (query (fn2-overview-range-key-at qbase f)) (i 0)))
           :in-theory (disable fn2-run-page-bound-returns-position fn2-run-seek fn2-run-step-seek
                        fn2-run-cursors-rows fn2-run-cursors-phase fn2-run-cursors-lo fn2-run-cursors-hi
                        fn2-run-cursors-idx fn2-run-cursors-off fn2-run-header-value fn2-run-stored-overview-page-p
                        fn2-run-readerp fn2-fieldsp fn2-run-lower-bound-spec fn2-run-sorted-spec fn2-run-directory
                        fn2-overview-range-key-at fn2-run-overview-lower-bound-offset unsigned-byte-p integer-length))))
