; When the next overview does not fit, leave it pending and start closing
; the current page. An empty page always fits an admitted overview row.
(in-package "ACL2")
(include-book "runs-builder-input-step-proof")
(include-book "runs-page-row-budget-proof")

(defthmd fn2-run-admitted-overview-fits-first-page
  (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row)
                (equal (fn2-run-writers-cursor w writers) *fn2-run-entries-base*)
                (equal (fn2-run-writers-entries w writers) 0) (equal (fn2-run-writers-restarts w writers) 0)
                (equal (fn2-run-writers-limit w writers) 2048))
           (car (fn2-run-leaf-packed-end row w writers)))
  :hints (("Goal" :use ((:instance fn2-run-overview-admission-fits-decoder (layout *fn2-overview-entry*)))
           :in-theory (e/d (fn2-run-pack-bound)
                      (fn2-run-writers-cursor fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-limit
                       fn2-layout-octets fn2-run-values-layoutp len)))))

(local
 (defthm fn2-run-nonfitting-page-has-entries
   (let* ((w (fn2-run-builds-wbase 0 builds)) (idx (fn2-run-writers-entries w writers)))
     (implies (and (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                   (equal (fn2-run-writers-limit w writers) 2048) (not (car (fn2-run-leaf-packed-end row w writers))))
              (posp idx)))
   :rule-classes nil
   :hints (("Goal" :cases ((consp rows)) :use ((:instance fn2-run-admitted-overview-fits-first-page (w (fn2-run-builds-wbase 0 builds))))
            :expand ((len rows) (fn2-run-restart-offsets-spec *fn2-overview-entry* rows 0 *fn2-run-entries-base*)
                     (fn2-run-entries-octets *fn2-overview-entry* rows))
            :in-theory (e/d (fn2-run-open-overview-contents-p fn2-run-next-overview-row-p)
                 (fn2-run-overview-append-workspace-p fn2-run-values-layoutp fn2-run-key-order-spec fn2-overview-range-key-at
                  fn2-run-entries-octets fn2-run-restart-offsets-spec fn2-run-saved-offsets fn2-run-read-bytes
                  fn2-run-builds-wbase fn2-run-builds-entries fn2-run-builds-schema fn2-run-writers-fields fn2-run-writers-prev
                  fn2-run-writers-cursor fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-limit fn2-run-writers-slot
                  fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-layout-octets fn2-run-pack-bound
                  fn2-layout-range-code fn2-poolp fn2-pool-wfp fn2-pool-base len unsigned-byte-p nth))))))

(local
 (defthm fn2-run-full-leaf-closes
   (let* ((w (fn2-run-builds-wbase 0 builds))
          (build (fn2-run-build-add 0 base builds writers restarts f pool)))
     (implies (and (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-adding*)
                   (posp (fn2-run-builds-height 0 builds)) (equal (fn2-run-builds-schema 0 builds) 3)
                   (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-open*)
                   (posp (fn2-run-writers-entries w writers)) (equal (fn2-run-add-ready w 3 base writers restarts f pool) :full))
              (equal build (list :more builds (fn2-run-writers-set-phase w *fn2-run-writer-phase-closing*
                                                  (fn2-run-writers-set-pos w 0 writers)) restarts f pool))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-build-add fn2-run-add fn2-run-close-full fn2-run-close)
                    (fn2-run-builds-phase fn2-run-builds-height fn2-run-builds-schema fn2-run-builds-wbase
                     fn2-run-writers-entries fn2-run-writers-phase fn2-run-writers-set-phase fn2-run-writers-set-pos
                     fn2-run-add-ready fn2-run-add-write))))))

(local (defthm fn2-run-input-byte-offset-natural (implies (unsigned-byte-p 32 at) (natp at)) :rule-classes nil))

(local
 (defthm fn2-run-oversized-next-append-starts-close
   (let* ((w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*)
          (load (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))
          (build (fn2-run-build-add 0 base builds writers restarts (mv-nth 2 load) (mv-nth 3 load))))
     (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                   (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                   (equal (fn2-run-writers-limit w writers) 2048) (not (car (fn2-run-leaf-packed-end row w writers))))
              (and (equal (car load) :ok)
                   (equal build (list :more builds (fn2-run-writers-set-phase w *fn2-run-writer-phase-closing*
                                                  (fn2-run-writers-set-pos w 0 writers)) restarts (mv-nth 2 load) (mv-nth 3 load))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-input-byte-offset-natural fn2-run-nonfitting-page-has-entries
                  (:instance fn2-run-sorted-overview-admission (w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*))
                  (:instance fn2-run-full-leaf-closes (base *fn2-run-run-entry*)
                    (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool)))
                    (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool)))))
            :in-theory (union-theories (theory 'minimal-theory)
                   '(fn2-run-build-awaits-input-p fn2-run-next-overview-row-p fn2-run-overview-append-workspace-p eq not (:e equal)))))))

(defthmd fn2-run-idle-build-retries-unconsumed-overview
  (let* ((w (fn2-run-builds-wbase 0 builds))
         (step (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg at unit pages builds curs paths cache
                                    writers restarts f pool fc ctx b3 ds)))
    (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                  (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                  (equal (fn2-run-writers-limit w writers) 2048) (not (car (fn2-run-leaf-packed-end row w writers))))
             (and (not (car step)) (equal (mv-nth 1 step) :more)
                  (equal (mv-nth 2 step) (cons row tail)) (equal (mv-nth 3 step) at)
                  (equal (mv-nth 4 step) unit) (equal (mv-nth 5 step) pages) (equal (mv-nth 6 step) builds)
                  (equal (mv-nth 10 step) (fn2-run-writers-set-phase w *fn2-run-writer-phase-closing* (fn2-run-writers-set-pos w 0 writers)))
                  (equal (mv-nth 11 step) restarts))))
  :hints (("Goal" :use (fn2-run-oversized-next-append-starts-close
                   (:instance fn2-run-idle-build-consumes-accepted-row (layout *fn2-overview-entry*)))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(mv-nth car-cons cdr-cons member-equal eq not (:e mv-nth) (:e equal) (:e consp) (:e zp) (:e binary-+))))))
