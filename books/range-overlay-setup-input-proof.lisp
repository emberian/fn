; A fresh range image with one overview in its overlay reaches physical
; storage without any successful-operation premise.
(in-package "ACL2")
(include-book "range-overlay-first-input-proof")

(local
 (defthmd fn2-range-setup-overlay-geometry
   (let* ((setup (fn2-rga-call fn2-rga-setup)) (ov (mv-nth 3 setup))
          (ix (mv-nth 4 setup)) (f (mv-nth 12 setup)) (p (mv-nth 13 setup)))
     (implies (and (fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool))
              (and (fn2-overlays-wfp ov) (equal (fn2-overlays-rows ov) 1)
                   (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-free*)
                   (fn2-overlay-index-wfp ix) (equal (fn2-overlay-index-rows ix) 256)
                   (fn2-fieldsp f) (fn2-fields-wfp f)
                   (<= (+ *fn2-run-adapter-reader* *fn2-run-entry-rows*) (fn2-fields-rows f))
                   (fn2-poolp p) (fn2-pool-wfp p))))
   :hints (("Goal" :in-theory (e/d (fn2-rga-setup fn2-overlays-phase)
                      (fn2-overlays-init fn2-overlay-index-init fn2-fields-init fn2-pool-init
                       fn2-fieldsp fn2-poolp fn2-overlays-wfp fn2-overlay-index-wfp fn2-fields-wfp fn2-pool-wfp))))))

(defmacro fn2-range-overlay-single-from-setup (row)
  `(b* (((mv & ,@*fn2-rga-stobjs*) (fn2-rga-call fn2-rga-setup)))
     (fn2-rga-call fn2-rga-overlay 3 *fn2-overview-entry* (list ,row))))

(local
 (defthm fn2-range-created-pool-has-type
   (fn2-poolp (create-fn2-pool))
   :hints (("Goal" :in-theory (enable create-fn2-pool fn2-poolp)))))

(defthm fn2-range-setup-stores-single-overview
  (let* ((run (fn2-range-overlay-single-from-setup row))
         (bytes (fn2-layout-octets *fn2-overview-entry* row)))
    (implies (and (equal fn2-pool (create-fn2-pool)) (fn2-fieldsp fn2-fields)
                  (fn2-run-values-layoutp *fn2-overview-entry* row))
             (and (equal (car run) :ok) (equal (fn2-overlays-count 0 (mv-nth 3 run)) 1)
                  (equal (fn2-overlays-fill 0 (mv-nth 3 run)) (len bytes))
                  (equal (fn2-overlay-index-off 0 (mv-nth 4 run)) 0)
                  (equal (fn2-run-read-bytes (len bytes) 0 1 0 9 0 1 (mv-nth 13 run)) bytes))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-setup-has-all-reservations fn2-range-setup-overlay-geometry
                 (:instance fn2-range-overlay-loads-single-input
                    (n 327)
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
                    '(fn2-range-created-pool-has-type (:e natp) (:e <) (:e equal)
                      (:e binary-+) (:e unary--) (:e not))))))
