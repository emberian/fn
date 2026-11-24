; After copying the active overlay, the seal retires it and installs the
; copied rows as the newest run. An empty overlay requires no run build.
(in-package "ACL2")
(include-book "range-indexed-overlay-read-proof")
(include-book "range-setup-cursors-proof")

(defmacro fn2-range-build-copied-overlay (rows k)
  `(b* (((mv & fn2-overlays) (fn2-ov-freeze 0 fn2-overlays))
        ((mv & fn2-fields) (fn2-ov-adapter-read (fn2-overlays-count 0 fn2-overlays) 0 *fn2-overview-entry*
                                  fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
     (fn2-rga-call fn2-rga-build 3 *fn2-overview-entry* ,rows ,k)))

(local
 (defthm fn2-range-retire-after-freeze
   (let* ((freeze (fn2-ov-freeze 0 ov)) (retire (fn2-ov-retire 0 (mv-nth 1 freeze))))
     (implies (equal (car freeze) :ok)
              (and (equal (car retire) :ok) (equal (fn2-overlays-phase 0 (mv-nth 1 retire)) *fn2-overlay-phase-free*)
                   (equal (fn2-overlays-rows (mv-nth 1 retire)) (fn2-overlays-rows ov)))))
   :hints (("Goal" :in-theory (e/d (fn2-ov-retire fn2-ov-freeze fn2-ov-advance fn2-overlays-phase fn2-overlays-rows
                        fn2-overlays-set-phase update-fn2-overlays-phase$ai nth-update-nth)
                       (nth update-nth))))))

(local
 (defthmd fn2-range-seal-follows-copy
   (let* ((freeze (fn2-ov-freeze 0 fn2-overlays)) (frozen (mv-nth 1 freeze))
          (read (fn2-ov-adapter-read (fn2-overlays-count 0 frozen) 0 *fn2-overview-entry*
                                    frozen fn2-overlay-index fn2-fields fn2-pool))
          (build (fn2-range-build-copied-overlay rows k))
          (seal (fn2-rga-call fn2-rga-seal 3 *fn2-overview-entry* k)))
     (implies (and (equal (car freeze) :ok) (equal (car read) rows))
              (and (equal (car seal) (car build)) (equal (mv-nth 5 seal) (mv-nth 5 build))
                   (equal (mv-nth 1 seal) fn2-ranges) (equal (mv-nth 2 seal) fn2-range-sources)
                   (implies (equal (car build) :ok)
                            (and (equal (fn2-overlays-phase 0 (mv-nth 3 seal)) *fn2-overlay-phase-free*)
                                 (equal (fn2-overlays-rows (mv-nth 3 seal)) (fn2-overlays-rows fn2-overlays)))))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (union-theories (theory 'minimal-theory)
                          '(fn2-rga-seal fn2-range-retire-after-freeze fn2-range-build-preserves-reader-tables
                            (:t fn2-ov-freeze) (:t fn2-ov-adapter-read) (:t fn2-rga-build) (:t fn2-ov-retire)
                            eq mv-nth car-cons cdr-cons (:e mv-nth) (:e consp) (:e equal) (:e zp) (:e unary--) (:e binary-+)))))))

(defthm fn2-range-seal-installs-indexed-overlay
  (let* ((build (fn2-range-build-copied-overlay rows k))
         (seal (fn2-rga-call fn2-rga-seal 3 *fn2-overview-entry* k)) (inst (mv-nth 5 seal)))
    (implies (and (true-listp rows) (equal (fn2-overlays-count 0 fn2-overlays) (len rows))
                  (equal (fn2-overlays-phase 0 fn2-overlays) *fn2-overlay-phase-active*)
                  (equal (fn2-overlays-okind 0 fn2-overlays) 9) (equal (fn2-overlays-oslot 0 fn2-overlays) 0)
                  (equal (fn2-overlays-ogen 0 fn2-overlays) 1)
                  (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* qbase fn2-overlays fn2-overlay-index fn2-fields)
                  (fn2-ov-indexed-rows-p (len rows) rows 0 *fn2-run-adapter-reader*
                                       fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
                  (natp r) (< r (fn2-run-installed-rows fn2-run-installed)))
             (and (equal (car seal) (car build)) (equal (mv-nth 1 seal) fn2-ranges)
                  (equal (mv-nth 2 seal) fn2-range-sources)
                  (implies (equal (car build) :ok)
                           (and (equal (fn2-overlays-phase 0 (mv-nth 3 seal)) *fn2-overlay-phase-free*)
                                (equal (fn2-overlays-rows (mv-nth 3 seal)) (fn2-overlays-rows fn2-overlays))
                                (equal (fn2-run-installed-rows inst) (fn2-run-installed-rows fn2-run-installed))
                                (equal (fn2-run-installed-source r inst)
                                       (if (and (consp rows) (equal r k))
                                           (list *fn2-run-installed-state-live* 3 (1+ k) (len rows) 9 0 1)
                                         (fn2-run-installed-source r fn2-run-installed))))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-seal-follows-copy
                 (:instance fn2-range-seal-reads-indexed-overlay (ov fn2-overlays) (ix fn2-overlay-index)
                    (f fn2-fields) (pool fn2-pool)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn2-range-build-records-input-source (:e equal) (:e not))))))

(defthm fn2-range-seals-empty-overlay
  (let ((seal (fn2-rga-call fn2-rga-seal 3 *fn2-overview-entry* k)))
    (implies (and (< 0 (fn2-overlays-rows fn2-overlays)) (equal (fn2-overlays-count 0 fn2-overlays) 0)
                  (equal (fn2-overlays-phase 0 fn2-overlays) *fn2-overlay-phase-active*))
             (and (equal (car seal) :ok)
                  (equal (fn2-overlays-phase 0 (mv-nth 3 seal)) *fn2-overlay-phase-free*)
                  (equal (mv-nth 1 seal) fn2-ranges) (equal (mv-nth 2 seal) fn2-range-sources)
                  (equal (mv-nth 5 seal) fn2-run-installed) (equal (mv-nth 12 seal) fn2-fields)
                  (equal (mv-nth 13 seal) fn2-pool))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-rga-seal fn2-ov-freeze fn2-ov-retire fn2-ov-advance fn2-ov-adapter-read fn2-rga-build
                            fn2-overlays-phase fn2-overlays-count fn2-overlays-rows fn2-overlays-set-phase
                            update-fn2-overlays-phase$ai nth-update-nth)
                      (fn2-pool-reserve fn2-run-build-start fn2-run-run-loop fn2-rga-install-pages
                       fn2-ov-entry fn2-run-unload-values nth update-nth)))))
