; Fresh range setup installs the complete source represented by the overlay.
; Its bytes and offsets supply physical cursors at any fitting field base.
(in-package "ACL2")
(include-book "range-overlay-setup-input-proof")
(include-book "range-overlay-installed-source-proof")

(local
 (defthm fn2-ov-single-source-admission
   (implies (fn2-range-inputp *fn2-overview-entry* *fn2-overview-range-key* (list rows) budget)
            (and (true-listp rows) (<= (len rows) 48) (fn2-run-entries-layoutp *fn2-overview-entry* rows)
                 (fn2-run-sorted-spec *fn2-overview-range-key* rows)))
   :hints (("Goal" :in-theory (e/d (fn2-range-inputp fn2-range-listsp)
                            (fn2-run-entries-layoutp fn2-run-sorted-spec fn2-layoutp true-listp len))))))

(defthmd fn2-range-fresh-setup-installs-overlay-source
  (let ((run (fn2-range-overlay-source-from-setup rows)))
    (implies (and (fn2-range-inputp *fn2-overview-entry* *fn2-overview-range-key* (list rows) budget)
                  (equal fn2-pool (create-fn2-pool)) (fn2-overlaysp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
                  (fn2-fieldsp fn2-fields))
             (and (equal (car run) :ok)
                  (fn2-ov-contiguous-arena-p rows 0 (mv-nth 3 run) (mv-nth 4 run) (mv-nth 13 run))
                  (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry*
                                            (mv-nth 3 run) (mv-nth 4 run) (mv-nth 12 run)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-ov-single-source-admission fn2-range-setup-has-all-reservations fn2-range-setup-overlay-geometry
                 (:instance fn2-range-overlay-installs-admitted-source (n 327)
                    (fn2-ranges (mv-nth 1 (fn2-rga-call fn2-rga-setup)))
                    (fn2-range-sources (mv-nth 2 (fn2-rga-call fn2-rga-setup)))
                    (fn2-overlays (mv-nth 3 (fn2-rga-call fn2-rga-setup)))
                    (fn2-overlay-index (mv-nth 4 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-installed (mv-nth 5 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-builds (mv-nth 6 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-cursors (mv-nth 7 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-paths (mv-nth 8 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-cache (mv-nth 9 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-writers (mv-nth 10 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-restarts (mv-nth 11 (fn2-rga-call fn2-rga-setup)))
                    (fn2-fields (mv-nth 12 (fn2-rga-call fn2-rga-setup)))
                    (fn2-pool (mv-nth 13 (fn2-rga-call fn2-rga-setup)))
                    (fn2-fc (mv-nth 14 (fn2-rga-call fn2-rga-setup)))
                    (fn2-fc-context (mv-nth 15 (fn2-rga-call fn2-rga-setup)))
                    (fn2-b3 (mv-nth 16 (fn2-rga-call fn2-rga-setup)))
                    (fn2-digests (mv-nth 17 (fn2-rga-call fn2-rga-setup)))))
           :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-range-created-pool-has-type (:e natp) (:e <) (:e equal) (:e not) (:e binary-+) (:e unary--))))))

(defthm fn2-range-fresh-overlay-supplies-cursor
  (let ((run (fn2-range-overlay-source-from-setup rows)))
    (implies (and (fn2-range-inputp *fn2-overview-entry* *fn2-overview-range-key* (list rows) budget)
                  (equal fn2-pool (create-fn2-pool)) (fn2-overlaysp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
                  (fn2-fieldsp fn2-fields) (natp eb) (<= (+ eb 5) (fn2-fields-rows f)))
             (and (equal (car run) :ok)
                  (fn2-ov-indexed-rows-p (len rows) rows 0 eb (mv-nth 3 run) (mv-nth 4 run) f (mv-nth 13 run)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn2-ov-single-source-admission fn2-range-fresh-setup-installs-overlay-source
                 (:instance fn2-ov-contiguous-arena-supplies-reader (o 0)
                       (ov (mv-nth 3 (fn2-range-overlay-source-from-setup rows)))
                       (ix (mv-nth 4 (fn2-range-overlay-source-from-setup rows)))
                       (pool (mv-nth 13 (fn2-range-overlay-source-from-setup rows)))))
           :in-theory (theory 'minimal-theory))))
