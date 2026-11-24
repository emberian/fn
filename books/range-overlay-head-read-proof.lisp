; The overlay source supplies the complete stored row at its lower bound,
; or the following row when the previous head has been consumed.
(in-package "ACL2")
(include-book "range-indexed-overlay-read-proof")
(include-book "range-overlay-head-proof")

(local
 (defthm fn2-range-overlay-returns-entry-fields
   (let* ((advance (fn2-range-advance-overlay s qbase qk qs qg rs ov ix f pool))
          (o (fn2-range-sources-src s rs)) (eb (+ (fn2-range-sources-rb s rs) *fn2-run-reader-entry*))
          (fresh (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*))
          (loc (fn2-ov-locate o eb qbase qk qs qg ov ix f pool))
          (at (if fresh (mv-nth 1 loc) (1+ (nfix (fn2-range-sources-pos s rs)))))
          (ready (if fresh (mv-nth 3 loc) f)))
     (implies (and (equal (car advance) :ok) (< at (fn2-overlays-count o ov)))
              (equal (mv-nth 2 advance) (mv-nth 2 (fn2-ov-entry o at eb ov ix ready pool)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-range-advance-overlay)
                 (fn2-ov-entry fn2-ov-locate fn2-fields-rows fn2-range-sources-rows fn2-overlays-rows
                  fn2-overlays-count fn2-range-sources-rb fn2-range-sources-src fn2-range-sources-state
                  fn2-range-sources-pos fn2-range-sources-count fn2-range-sources-set-state fn2-range-sources-set-pos
                  fn2-range-sources-set-count unsigned-byte-p))))))

(local
 (defthm fn2-range-overlay-locates-readable-row
   (let* ((at (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0)))
          (loc (fn2-ov-locate o eb qbase qk qs qg ov ix f pool))
          (read (fn2-ov-entry o (mv-nth 1 loc) eb ov ix (mv-nth 3 loc) pool)))
     (implies (and (equal (len rows) (fn2-overlays-count o ov)) (<= (len rows) 48)
                   (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                   (equal (fn2-overlays-okind o ov) 9) (equal (fn2-overlays-oslot o ov) 0) (equal (fn2-overlays-ogen o ov) 1)
                   (fn2-ov-overview-reader-p o eb qbase ov ix f) (fn2-ov-indexed-rows-p (len rows) rows o eb ov ix f pool))
              (and (equal (mv-nth 1 loc) at)
                   (implies (< at (len rows))
                            (equal (fn2-run-unload-values *fn2-overview-entry* eb (mv-nth 2 read) pool) (nth at rows))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-ov-locates-stored-lower-bound
                 (:instance fn2-overview-bound-index-in-range (i 0) (query (fn2-overview-range-key-at qbase f)))
                 (:instance fn2-run-integer-length-monotonic (i (len rows)) (j 48))
                 (:instance fn2-ov-reads-indexed-overview (n (len rows))
                   (i (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0)))
                   (f (mv-nth 3 (fn2-ov-locate o eb qbase qk qs qg ov ix f pool)))))
            :in-theory (disable fn2-ov-entry fn2-ov-locate fn2-run-unload-values fn2-run-sorted-spec fn2-run-lower-bound-spec
                      fn2-run-key-order-spec fn2-ov-indexed-rows-p fn2-ov-overview-reader-p fn2-overview-range-key-at
                      fn2-overlays-count fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen nth len integer-length)))))

(defthm fn2-range-overlay-reads-lower-bound
  (let* ((step (fn2-range-advance-overlay s qbase qk qs qg rs ov ix f pool))
         (after (mv-nth 1 step))
         (at (if (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*)
                 (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0))
               (1+ (nfix (fn2-range-sources-pos s rs))))))
    (implies (and (natp s) (< s (fn2-range-sources-rows rs))
                  (equal o (fn2-range-sources-src s rs)) (equal eb (+ (fn2-range-sources-rb s rs) *fn2-run-reader-entry*))
                  (equal (len rows) (fn2-overlays-count o ov)) (<= (len rows) 48)
                  (implies (not (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*))
                           (< (nfix (fn2-range-sources-pos s rs)) (len rows)))
                  (equal (fn2-overlays-okind o ov) 9) (equal (fn2-overlays-oslot o ov) 0) (equal (fn2-overlays-ogen o ov) 1)
                  (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (fn2-ov-overview-reader-p o eb qbase ov ix f) (fn2-ov-indexed-rows-p (len rows) rows o eb ov ix f pool))
             (and (equal (car step) :ok) (equal (fn2-range-sources-pos s after) at)
                  (equal (fn2-range-sources-state s after) (if (< at (len rows)) *fn2-range-state-head* *fn2-range-state-end*))
                  (implies (< at (len rows))
                           (equal (fn2-run-unload-values *fn2-overview-entry* eb (mv-nth 2 step) pool) (nth at rows))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :cases ((equal (fn2-range-sources-state s rs) *fn2-range-state-seek*))
           :use ((:instance fn2-range-overlay-supplies-selected-row (j 0))
                 fn2-range-overlay-returns-entry-fields fn2-range-overlay-locates-readable-row
                 (:instance fn2-ov-reads-indexed-overview (n (len rows)) (i (1+ (nfix (fn2-range-sources-pos s rs))))))
           :in-theory (disable fn2-range-advance-overlay fn2-range-sources-state fn2-range-sources-src fn2-range-sources-rb
                      fn2-range-sources-pos fn2-range-sources-count fn2-range-sources-rows fn2-overlays-count
                      fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen fn2-fields-value fn2-run-unload-values
                      fn2-ov-entry fn2-ov-locate fn2-ov-overview-reader-p fn2-ov-indexed-rows-p fn2-run-sorted-spec
                      fn2-run-lower-bound-spec fn2-run-key-order-spec fn2-overview-range-key-at len nth integer-length))))
