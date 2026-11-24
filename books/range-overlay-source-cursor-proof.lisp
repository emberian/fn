; A range cursor over the fully loaded overlay reaches the requested
; lower bound, or END, in one actual overlay advance.
(in-package "ACL2")
(include-book "range-overlay-fresh-source-proof")
(include-book "range-overlay-head-read-proof")

(local
 (defthmd fn2-ov-move-reader-base
   (implies (and (fn2-ov-overview-reader-p 0 old query ov ix old-fields)
                 (natp qbase) (natp eb) (< (1+ qbase) eb)
                 (fn2-fieldsp f) (fn2-fields-wfp f) (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f)))
            (fn2-ov-overview-reader-p 0 eb qbase ov ix f))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-ov-overview-reader-p))))))

(local
 (defthmd fn2-ov-loaded-arena-reads-bound
  (let* ((step (fn2-range-advance-overlay s qbase qk qs qg rs ov ix f p))
         (at (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0))))
    (implies (and (fn2-range-inputp *fn2-overview-entry* *fn2-overview-range-key* (list rows) budget)
                  (fn2-ov-contiguous-arena-p rows 0 ov ix p)
                  (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* ov ix old-fields)
                  (fn2-fieldsp f) (fn2-fields-wfp f) (natp qbase) (natp eb) (< (1+ qbase) eb)
                  (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
                  (natp s) (< s (fn2-range-sources-rows rs)) (equal (fn2-range-sources-src s rs) 0)
                  (equal eb (+ (fn2-range-sources-rb s rs) *fn2-run-reader-entry*))
                  (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*))
             (and (equal (car step) :ok) (equal (fn2-range-sources-pos s (mv-nth 1 step)) at)
                  (equal (fn2-range-sources-state s (mv-nth 1 step))
                         (if (< at (len rows)) *fn2-range-state-head* *fn2-range-state-end*))
                  (implies (< at (len rows))
                           (equal (fn2-run-unload-values *fn2-overview-entry* eb (mv-nth 2 step) p) (nth at rows))))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-contiguous-arena-supplies-reader (o 0) (pool p))
                 (:instance fn2-ov-move-reader-base (old *fn2-run-adapter-reader*) (query *fn2-run-adapter-entry*))
                 (:instance fn2-range-overlay-reads-lower-bound (o 0) (pool p)))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-range-inputp fn2-range-listsp fn2-ov-contiguous-arena-p car-cons cdr-cons (:e consp)
                         (:e equal) (:e not) (:e len) (:e binary-+) (:e unary--) (:e <)))))))

(defthm fn2-range-fresh-overlay-reads-lower-bound
  (let* ((run (fn2-range-overlay-source-from-setup rows))
         (ov (mv-nth 3 run)) (ix (mv-nth 4 run)) (p (mv-nth 13 run))
         (step (fn2-range-advance-overlay s qbase qk qs qg rs ov ix f p))
         (at (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0))))
    (implies (and (fn2-range-inputp *fn2-overview-entry* *fn2-overview-range-key* (list rows) budget)
                  (equal fn2-pool (create-fn2-pool)) (fn2-overlaysp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
                  (fn2-fieldsp fn2-fields) (fn2-fieldsp f) (fn2-fields-wfp f) (natp qbase) (natp eb) (< (1+ qbase) eb)
                  (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
                  (natp s) (< s (fn2-range-sources-rows rs)) (equal (fn2-range-sources-src s rs) 0)
                  (equal eb (+ (fn2-range-sources-rb s rs) *fn2-run-reader-entry*))
                  (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*))
             (and (equal (car run) :ok) (equal (car step) :ok)
                  (equal (fn2-range-sources-pos s (mv-nth 1 step)) at)
                  (equal (fn2-range-sources-state s (mv-nth 1 step))
                         (if (< at (len rows)) *fn2-range-state-head* *fn2-range-state-end*))
                  (implies (< at (len rows))
                           (equal (fn2-run-unload-values *fn2-overview-entry* eb (mv-nth 2 step) p) (nth at rows))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-fresh-setup-installs-overlay-source
                 (:instance fn2-ov-loaded-arena-reads-bound
                   (ov (mv-nth 3 (fn2-range-overlay-source-from-setup rows))) (ix (mv-nth 4 (fn2-range-overlay-source-from-setup rows)))
                   (old-fields (mv-nth 12 (fn2-range-overlay-source-from-setup rows))) (p (mv-nth 13 (fn2-range-overlay-source-from-setup rows)))))
           :in-theory (theory 'minimal-theory))))
