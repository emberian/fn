; The range's overlay source exposes the first row at or above the query,
; and after consumption advances to the following row.
(in-package "ACL2")
(include-book "range-overlay-search-proof")

(local
 (defthm fn2-range-saved-overlay-position
   (let* ((state (if (< pos n) *fn2-range-state-head* *fn2-range-state-end*))
          (after (fn2-range-sources-put s (state state) (pos pos) (count n))))
     (implies (and (natp s) (< s (fn2-range-sources-rows fn2-range-sources))
                   (unsigned-byte-p 32 pos) (unsigned-byte-p 32 n))
              (and (equal (fn2-range-sources-state s after) state)
                   (equal (fn2-range-sources-pos s after) pos)
                   (equal (fn2-range-sources-count s after) n))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-range-sources-set-state fn2-range-sources-set-pos fn2-range-sources-set-count
                    update-fn2-range-sources-state$ai update-fn2-range-sources-pos$ai update-fn2-range-sources-count$ai
                    fn2-range-sources-state fn2-range-sources-pos fn2-range-sources-count nth-update-nth)
                   (fn2-range-sources-rows nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-range-overlay-advance-prepared
   (let* ((eb (+ (fn2-range-sources-rb s rs) *fn2-run-reader-entry*)) (o (fn2-range-sources-src s rs))
          (n (fn2-overlays-count o ov)) (fresh (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*))
          (loc (fn2-ov-locate o eb qbase qk qs qg ov ix f pool))
          (start (if fresh (mv-nth 3 loc) f)) (at (if fresh (mv-nth 1 loc) (1+ (nfix (fn2-range-sources-pos s rs))))))
     (implies (and (natp s) (< s (fn2-range-sources-rows rs)) (< o (fn2-overlays-rows ov)) (natp qbase)
                   (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f)) (unsigned-byte-p 32 at) (unsigned-byte-p 32 n)
                   (implies fresh (equal (car loc) :ok))
                   (implies (< at n) (equal (car (fn2-ov-entry o at eb ov ix start pool)) :ok)))
              (let* ((res (fn2-range-advance-overlay s qbase qk qs qg rs ov ix f pool)) (after (mv-nth 1 res)))
                (and (equal (car res) :ok)
                     (equal (mv-nth 2 res) (if (< at n) (mv-nth 2 (fn2-ov-entry o at eb ov ix start pool)) start))
                     (equal (fn2-range-sources-state s after) (if (< at n) *fn2-range-state-head* *fn2-range-state-end*))
                     (equal (fn2-range-sources-pos s after) at) (equal (fn2-range-sources-count s after) n)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-range-saved-overlay-position (fn2-range-sources rs)
                        (n (fn2-overlays-count (fn2-range-sources-src s rs) ov))
                        (pos (if (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*)
                           (mv-nth 1 (fn2-ov-locate (fn2-range-sources-src s rs) (+ (fn2-range-sources-rb s rs) *fn2-run-reader-entry*)
                                                     qbase qk qs qg ov ix f pool))
                           (1+ (nfix (fn2-range-sources-pos s rs)))))))
            :in-theory (e/d (fn2-range-advance-overlay)
                  (fn2-ov-entry fn2-ov-locate fn2-fields-rows fn2-range-sources-rows fn2-overlays-rows fn2-overlays-count
                   fn2-range-sources-rb fn2-range-sources-src fn2-range-sources-state fn2-range-sources-pos fn2-range-sources-count
                   fn2-range-sources-set-state fn2-range-sources-set-pos fn2-range-sources-set-count))))))

(local
 (defthm fn2-range-overlay-reader-space
   (implies (fn2-ov-overview-reader-p o eb qbase ov ix f)
            (and (natp qbase) (< o (fn2-overlays-rows ov))
                 (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-ov-overview-reader-p fn2-ov-okp)
                  (fn2-fields-rows fn2-overlays-rows fn2-ov-indexed-rows-p fn2-overlays-wfp fn2-overlay-index-wfp
                   fn2-fieldsp fn2-fields-wfp fn2-overlays-schema fn2-overlays-ibase fn2-overlays-icap
                   fn2-overlay-index-rows fn2-overlays-count))))))

(defthmd fn2-range-overlay-supplies-selected-row
  (let* ((step (fn2-range-advance-overlay s qbase qk qs qg rs ov ix f pool))
         (after (mv-nth 1 step))
         (at (if (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*)
                 (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows
                              (fn2-overview-range-key-at qbase f) 0))
               (1+ (nfix (fn2-range-sources-pos s rs))))))
    (implies (and (natp s) (< s (fn2-range-sources-rows rs)) (natp j) (< j 4)
                  (equal o (fn2-range-sources-src s rs))
                  (equal eb (+ (fn2-range-sources-rb s rs) *fn2-run-reader-entry*))
                  (equal (len rows) (fn2-overlays-count o ov)) (<= (len rows) 48)
                  (implies (not (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*))
                           (< (nfix (fn2-range-sources-pos s rs)) (len rows)))
                  (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (fn2-ov-overview-reader-p o eb qbase ov ix f)
                  (fn2-ov-indexed-rows-p (len rows) rows o eb ov ix f pool))
             (and (equal (car step) :ok) (equal (fn2-range-sources-pos s after) at)
                  (equal (fn2-range-sources-count s after) (len rows))
                  (equal (fn2-range-sources-state s after)
                         (if (< at (len rows)) *fn2-range-state-head* *fn2-range-state-end*))
                  (implies (< at (len rows))
                           (equal (fn2-fields-value (+ eb j) (mv-nth 2 step)) (nth j (nth at rows)))))))
  :hints (("Goal" :do-not '(preprocess)
           :cases ((equal (fn2-range-sources-state s rs) *fn2-range-state-seek*))
           :use (fn2-range-overlay-reader-space fn2-range-overlay-advance-prepared
                 fn2-ov-locates-stored-lower-bound
                 (:instance fn2-overview-bound-index-in-range (i 0) (query (fn2-overview-range-key-at qbase f)))
                 (:instance fn2-run-integer-length-monotonic (i (len rows)) (j 48))
                 (:instance fn2-ov-indexed-row-supplies-field (n (len rows)) (pos (1+ (nfix (fn2-range-sources-pos s rs)))))
                 (:instance fn2-ov-indexed-row-supplies-field (n (len rows))
                            (pos (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0)))
                            (f (mv-nth 3 (fn2-ov-locate o eb qbase qk qs qg ov ix f pool)))))
           :in-theory (disable fn2-range-advance-overlay fn2-range-sources-state fn2-range-sources-src
                       fn2-range-sources-rb fn2-range-sources-pos fn2-range-sources-count fn2-range-sources-rows
                       fn2-overlays-count fn2-overlays-rows fn2-fields-rows fn2-fields-value
                       fn2-ov-locate fn2-ov-entry fn2-ov-overview-reader-p fn2-ov-indexed-rows-p
                       fn2-run-sorted-spec fn2-run-lower-bound-spec fn2-run-key-order-spec fn2-overview-range-key-at
                       len nth integer-length))))
