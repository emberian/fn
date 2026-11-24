; The actual caller reserves both slots, creates the overlay, and installs
; the complete sorted source. The final arena is independently readable.
(in-package "ACL2")
(include-book "range-overlay-source-load-proof")
(include-book "range-overlay-first-input-proof")

(local
 (defthm fn2-ov-start-keeps-table-type
   (implies (and (fn2-overlaysp ov) (fn2-overlays-wfp ov))
            (fn2-overlaysp (mv-nth 1 (fn2-ov-start 0 3 dst dg 0 256 9 0 1 0 ov ix p))))
   :hints (("Goal" :in-theory (e/d (fn2-ov-start)
                      (fn2-overlaysp fn2-overlays-wfp fn2-poolp fn2-pool-wfp fn2-pool-reset fn2-pool-slot-cap
                       fn2-pool-rows fn2-overlay-index-rows fn2-overlays-rows fn2-overlays-phase unsigned-byte-p))))))

(local
 (defthmd fn2-ov-empty-load-finishes
   (let ((run (fn2-ov-adapter-load 3 *fn2-overview-entry* rows src sg 0 ov ix f pool)))
     (implies (and (fn2-ov-physical-prefix-p nil src sg ov ix f pool) (true-listp rows) (<= (len rows) 48)
                   (fn2-run-entries-layoutp *fn2-overview-entry* rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows))
              (and (subsetp-eq (car run) '(:ok))
                   (fn2-ov-contiguous-arena-p rows 0 (mv-nth 1 run) (mv-nth 2 run) (mv-nth 4 run))
                   (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry*
                                             (mv-nth 1 run) (mv-nth 2 run) (mv-nth 3 run)))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-ov-adapter-loads-complete-source (rows nil) (tail rows)))
            :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-ov-physical-prefix-p fn2-ov-load-workspaces-p binary-append (:e fn2-run-entries-layoutp)
                          (:e fn2-range-line-bytes) (:e true-listp) (:e consp) (:e equal) (:e not)))))))

(defthm fn2-range-overlay-installs-admitted-source
  (let ((run (fn2-rga-call fn2-rga-overlay 3 *fn2-overview-entry* rows)))
    (implies (and (true-listp rows) (<= (len rows) 48) (fn2-run-entries-layoutp *fn2-overview-entry* rows)
                  (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (fn2-range-pool-available-p n fn2-pool) (natp n) (<= 2 n) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                  (fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (< 0 (fn2-overlays-rows fn2-overlays))
                  (equal (fn2-overlays-phase 0 fn2-overlays) *fn2-overlay-phase-free*)
                  (fn2-overlay-indexp fn2-overlay-index) (fn2-overlay-index-wfp fn2-overlay-index)
                  (<= 256 (fn2-overlay-index-rows fn2-overlay-index)) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
                  (<= (+ *fn2-run-adapter-reader* *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields)))
             (and (equal (car run) :ok)
                  (fn2-ov-contiguous-arena-p rows 0 (mv-nth 3 run) (mv-nth 4 run) (mv-nth 13 run))
                  (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry*
                                            (mv-nth 3 run) (mv-nth 4 run) (mv-nth 12 run)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-reserved-start-prepares-empty-prefix (p fn2-pool) (ov fn2-overlays) (ix fn2-overlay-index) (f fn2-fields))
                 (:instance fn2-ov-empty-load-finishes
                   (src (mv-nth 1 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 fn2-pool)))))
                   (sg (mv-nth 2 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 fn2-pool)))))
                   (ov (mv-nth 1 (fn2-ov-input-start))) (ix fn2-overlay-index) (f fn2-fields) (pool (mv-nth 2 (fn2-ov-input-start)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-ov-physical-prefix-p fn2-ov-start-keeps-table-type fn2-rga-overlay eq
                       (:t fn2-ov-adapter-load) (:t fn2-pool-reserve) (:t fn2-ov-start)
                       mv-nth car-cons cdr-cons (:e equal) (:e mv-nth) (:e zp) (:e not)
                       (:e unary--) (:e binary-+) (:e consp))))))
