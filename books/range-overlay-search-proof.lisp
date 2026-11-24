; The bounded binary search of an indexed overlay returns the lower bound
; of the stored rows. The comparisons may overwrite the decoded entry.
(in-package "ACL2")
(include-book "range-overlay-row-proof")
(include-book "range-sorted-lower-bound-proof")
(include-book "range-restart-count-proof")

(local
 (defthm fn2-ov-midpoint-bounds
   (let ((j (floor (+ lo hi) 2)))
     (implies (and (natp lo) (natp hi) (< lo hi))
              (and (natp j) (<= lo j) (< j hi))))
   :rule-classes nil))

(local
 (defthmd fn2-ov-search-retains-cut
   (let* ((search (fn2-ov-search steps lo hi o eb qbase qk qs qg ov ix f pool)) (rf (mv-nth 2 search))
          (n (len rows)))
     (implies (and (natp steps) (natp lo) (natp hi) (natp cut) (<= lo cut) (<= cut hi) (<= hi n)
                   (<= (integer-length (- hi lo)) steps) (equal (fn2-overlays-count o ov) n)
                   (fn2-run-sorted-spec *fn2-overview-range-key* rows) (equal query (fn2-overview-range-key-at qbase f))
                   (equal cut (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0)))
                   (fn2-ov-overview-reader-p o eb qbase ov ix f) (fn2-ov-indexed-rows-p n rows o eb ov ix f pool))
              (and (equal (car search) :ok) (equal (mv-nth 1 search) cut)
                   (equal (fn2-overview-range-key-at qbase rf) query)
                   (fn2-ov-overview-reader-p o eb qbase ov ix rf) (fn2-ov-indexed-rows-p n rows o eb ov ix rf pool))))
   :hints (("Goal" :induct (fn2-ov-search steps lo hi o eb qbase qk qs qg ov ix f pool)
            :do-not '(preprocess)
            :expand ((fn2-ov-search steps lo hi o eb qbase qk qs qg ov ix f pool))
            :in-theory (e/d ((:induction fn2-ov-search))
                          ((:definition fn2-ov-search) fn2-ov-order fn2-run-key-order-spec fn2-run-lower-bound-spec
                           fn2-ov-indexed-rows-p fn2-ov-overview-reader-p fn2-run-sorted-spec fn2-overview-range-key-at
                           fn2-overlays-count floor integer-length len nth)))
           (and (equal (access clause-id id :pool-lst) '(1))
                (equal (len (access clause-id id :case-lst)) 1)
                (equal (access clause-id id :primes) 0)
                '(:use (fn2-ov-midpoint-bounds
                        (:instance fn2-ov-search-reads-indexed-row (pos (floor (+ lo hi) 2)) (n (len rows)))
                        (:instance fn2-overview-row-before-lower-bound (j (floor (+ lo hi) 2)) (i 0))
                        (:instance fn2-run-restart-half-bits (less (< (floor (+ lo hi) 2) cut)))))))))

(local
 (defthm fn2-ov-order-past-last
   (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f)
                 (natp pos) (<= (fn2-overlays-count o ov) pos))
            (equal (fn2-ov-order o pos eb qbase qk qs qg ov ix f pool) (list :ok :end f)))
   :hints (("Goal" :in-theory (e/d (fn2-ov-overview-reader-p fn2-ov-order fn2-ov-okp)
                 (fn2-ov-entry fn2-run-layout-compare fn2-overlays-wfp fn2-overlay-index-wfp fn2-overlays-count
                  fn2-overlays-rows fn2-fields-rows fn2-overlays-schema fn2-overlays-icap fn2-overlays-ibase
                  fn2-overlay-index-rows fn2-fieldsp fn2-fields-wfp))))))

(defthmd fn2-ov-locates-stored-lower-bound
  (let* ((query (fn2-overview-range-key-at qbase f))
         (i (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0)))
         (locate (fn2-ov-locate o eb qbase qk qs qg ov ix f pool)) (rf (mv-nth 3 locate)))
    (implies (and (equal (fn2-overlays-count o ov) (len rows))
                  (<= (integer-length (len rows)) *fn2-ov-search-steps*)
                  (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (fn2-ov-overview-reader-p o eb qbase ov ix f)
                  (fn2-ov-indexed-rows-p (len rows) rows o eb ov ix f pool))
             (and (equal (car locate) :ok) (equal (mv-nth 1 locate) i)
                  (equal (mv-nth 2 locate) (if (< i (len rows))
                         (fn2-run-key-order-spec *fn2-overview-range-key* (nth i rows) query) :end))
                  (equal (fn2-overview-range-key-at qbase rf) query)
                  (fn2-ov-overview-reader-p o eb qbase ov ix rf)
                  (fn2-ov-indexed-rows-p (len rows) rows o eb ov ix rf pool))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-overview-bound-index-in-range (i 0) (query (fn2-overview-range-key-at qbase f)))
                 (:instance fn2-ov-search-retains-cut (steps *fn2-ov-search-steps*) (lo 0) (hi (len rows))
                            (query (fn2-overview-range-key-at qbase f))
                            (cut (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0))))
                 (:instance fn2-ov-search-reads-indexed-row (n (len rows))
                        (pos (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0)))
                        (f (mv-nth 2 (fn2-ov-search *fn2-ov-search-steps* 0 (len rows) o eb qbase qk qs qg ov ix f pool)))))
           :in-theory (e/d (fn2-ov-locate fn2-ov-overview-reader-p fn2-ov-okp)
                     (fn2-ov-search fn2-ov-order fn2-ov-indexed-rows-p fn2-run-key-order-spec fn2-run-lower-bound-spec
                      fn2-run-sorted-spec fn2-overview-range-key-at fn2-overlays-count fn2-overlays-rows
                      fn2-overlay-index-rows fn2-overlays-ibase fn2-overlays-icap fn2-fieldsp fn2-fields-wfp
                      fn2-overlays-wfp fn2-overlay-index-wfp fn2-overlays-schema fn2-fields-rows integer-length len nth)))))
