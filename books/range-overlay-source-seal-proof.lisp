; At any delivery cut the field bank may have changed. Freezing and
; reading the installed overlay still supplies every original row to the
; seal builder, provided the bank has its reader region.
(in-package "ACL2")
(include-book "range-overlay-fresh-source-proof")
(include-book "range-sealed-catalog-proof")

(local
 (defthm fn2-ov-loaded-phase-is-active
   (let ((run (fn2-rga-call fn2-rga-overlay sid layout entries)))
     (implies (equal (car run) :ok)
              (equal (fn2-overlays-phase 0 (mv-nth 3 run)) *fn2-overlay-phase-active*)))
   :hints (("Goal" :use fn2-range-loaded-overlay-source
            :in-theory (e/d (fn2-range-overlay-descriptor)
                         (fn2-rga-overlay fn2-overlays-rows fn2-overlays-phase fn2-overlays-schema
                          fn2-overlays-cov fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))))))

(local
 (defthmd fn2-ov-contiguous-input-freezes-exactly
   (let* ((freeze (fn2-ov-freeze 0 ov)) (frozen (mv-nth 1 freeze))
          (read (fn2-ov-adapter-read (fn2-overlays-count 0 frozen) 0 *fn2-overview-entry* frozen ix f p)))
     (implies (and (true-listp rows) (fn2-run-entries-layoutp *fn2-overview-entry* rows)
                   (fn2-ov-contiguous-arena-p rows 0 ov ix p)
                   (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-active*)
                   (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* ov ix old)
                   (fn2-fieldsp f) (fn2-fields-wfp f) (<= (+ *fn2-run-adapter-reader* *fn2-run-entry-rows*) (fn2-fields-rows f)))
              (and (equal (car freeze) :ok) (equal (car read) rows))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-ov-contiguous-arena-supplies-reader (eb *fn2-run-adapter-reader*) (o 0) (pool p))
                  (:instance fn2-range-seal-reads-indexed-overlay (qbase *fn2-run-adapter-entry*) (pool p)))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-ov-contiguous-arena-p fn2-ov-overview-reader-p (:e natp) (:e binary-+) (:e <) (:e equal) (:e not)))))))

(defthm fn2-range-seal-reads-fresh-input-source
  (let* ((run (fn2-range-overlay-source-from-setup rows))
         (freeze (fn2-ov-freeze 0 (mv-nth 3 run))) (frozen (mv-nth 1 freeze))
         (read (fn2-ov-adapter-read (fn2-overlays-count 0 frozen) 0 *fn2-overview-entry* frozen (mv-nth 4 run) f (mv-nth 13 run))))
    (implies (and (fn2-range-inputp *fn2-overview-entry* *fn2-overview-range-key* (list rows) budget)
                  (equal fn2-pool (create-fn2-pool)) (fn2-overlaysp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
                  (fn2-fieldsp fn2-fields) (fn2-fieldsp f) (fn2-fields-wfp f)
                  (<= (+ *fn2-run-adapter-reader* *fn2-run-entry-rows*) (fn2-fields-rows f)))
             (and (equal (car run) :ok) (equal (car freeze) :ok) (equal (car read) rows))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn2-range-fresh-setup-installs-overlay-source
                 (:instance fn2-ov-contiguous-input-freezes-exactly
                    (ov (mv-nth 3 (fn2-range-overlay-source-from-setup rows))) (ix (mv-nth 4 (fn2-range-overlay-source-from-setup rows)))
                    (old (mv-nth 12 (fn2-range-overlay-source-from-setup rows))) (p (mv-nth 13 (fn2-range-overlay-source-from-setup rows)))))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-ov-loaded-phase-is-active fn2-range-inputp fn2-range-listsp car-cons cdr-cons
                         (:e equal) (:e not) (:e consp) (:e binary-+) (:e <))))))
