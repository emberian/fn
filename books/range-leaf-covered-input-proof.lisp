; A leaf accepts the next row or closes for retry. At either yield the
; rows represented by the builder followed by its pending input are the
; same sequence as before the call.
(in-package "ACL2")
(include-book "range-writer-coverage-update-proof")
(include-book "range-leaf-published-pages-proof")
(local (include-book "columns-observation-frames"))

(local (defcolumns-observation-frame fn2-range-added-row-keeps-height fn2-run-builds height entries))
(local (defcolumns-observation-frame fn2-range-added-row-keeps-writer-base fn2-run-builds wbase entries))

(local
 (defthmd fn2-range-build-append-keeps-levels
   (let* ((add (fn2-run-build-add 0 base builds writers restarts f pool))
          (after (mv-nth 1 add)) (wbase (fn2-run-builds-wbase 0 builds)) (height (fn2-run-builds-height 0 builds)))
     (implies (equal (car add) :ok)
              (equal (fn2-range-builder-input (fn2-run-builds-height 0 after) (fn2-run-builds-wbase 0 after) leaves children
                                               records (mv-nth 2 add) pending)
                     (fn2-range-builder-input height wbase leaves children records writers pending))))
   :hints (("Goal" :use ((:instance fn2-range-appending-row-keeps-builder-selection
                             (w (fn2-run-builds-wbase 0 builds)) (sid (fn2-run-builds-schema 0 builds))
                             (wbase (fn2-run-builds-wbase 0 builds)) (height (fn2-run-builds-height 0 builds))))
            :in-theory (e/d (fn2-run-build-add fn2-run-close-full fn2-run-close)
                     (fn2-range-builder-input fn2-run-add fn2-run-builds-wbase fn2-run-builds-height
                      fn2-run-builds-schema fn2-run-builds-entries fn2-run-builds-phase fn2-run-writers-phase
                      fn2-run-writers-entries fn2-run-builds-set-height fn2-run-builds-set-entries
                      fn2-run-writers-set-phase fn2-run-writers-set-pos unsigned-byte-p))))))

(local
 (defthmd fn2-range-accepted-row-moves-from-input-to-leaf
   (implies (and (posp height) (natp base) (equal (fn2-run-writers-phase base writers) *fn2-run-writer-phase-open*))
            (equal (fn2-range-builder-input height base (append leaves (list row)) children records writers pending)
                   (fn2-range-builder-input height base leaves children records writers (cons row pending))))
   :hints (("Goal" :induct (fn2-range-builder-input height base leaves children records writers pending)
            :in-theory (e/d (fn2-range-builder-input fn2-range-writer-covered-rows)
                       (fn2-run-writers-phase fn2-range-writer-page-address fn2-range-child-entry-lists append-lst assoc-equal nth)))
           ("Subgoal *1/2" :cases ((equal height 1))))))

(local
 (defthmd fn2-range-ready-leaf-is-active
   (let ((base (fn2-run-builds-wbase 0 builds)))
     (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                   (fn2-run-next-overview-row-p leaves row src sg at builds writers restarts f pool))
              (and (natp base) (posp (fn2-run-builds-height 0 builds))
                   (equal (fn2-run-writers-phase base writers) *fn2-run-writer-phase-open*))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-build-awaits-input-p
                                  fn2-run-next-overview-row-p fn2-run-overview-append-workspace-p))))))

(defmacro fn2-range-leaf-input-after-step (step leaves)
  `(fn2-range-builder-input (fn2-run-builds-height 0 (mv-nth 6 ,step)) (fn2-run-builds-wbase 0 (mv-nth 6 ,step))
                            ,leaves children records (mv-nth 10 ,step) (mv-nth 2 ,step)))

(defmacro fn2-range-leaf-input-step ()
  '(fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg at unit pages builds curs paths cache
                        writers restarts f pool fc ctx b3 ds))

(local
 (defthmd fn2-range-fitting-leaf-keeps-builder-input
   (let* ((w (fn2-run-builds-wbase 0 builds)) (step (fn2-range-leaf-input-step)))
     (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                   (fn2-run-next-overview-row-p leaves row src sg at builds writers restarts f pool)
                   (car (fn2-run-leaf-packed-end row w writers)))
              (equal (fn2-range-leaf-input-after-step step (append leaves (list row)))
                     (fn2-range-builder-input (fn2-run-builds-height 0 builds) w leaves children records writers (cons row tail)))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-range-ready-leaf-is-active (:instance fn2-range-fitting-leaf-build-pool (rows leaves))
                  (:instance fn2-run-idle-build-consumes-accepted-row (layout *fn2-overview-entry*))
                  (:instance fn2-range-build-append-keeps-levels (base *fn2-run-run-entry*) (pending tail)
                    (leaves (append leaves (list row)))
                    (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool)))
                    (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool))))
                  (:instance fn2-range-accepted-row-moves-from-input-to-leaf (height (fn2-run-builds-height 0 builds))
                    (base (fn2-run-builds-wbase 0 builds)) (pending tail)))
            :in-theory (union-theories (theory 'minimal-theory)
                    '(mv-nth car-cons cdr-cons (:e member-equal) (:e mv-nth) (:e binary-+) (:e equal) (:e consp) (:e zp)))))))

(defthmd fn2-range-leaf-step-keeps-complete-input
  (let* ((w (fn2-run-builds-wbase 0 builds)) (fits (car (fn2-run-leaf-packed-end row w writers)))
         (step (fn2-range-leaf-input-step)))
    (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                  (fn2-run-next-overview-row-p leaves row src sg at builds writers restarts f pool)
                  (equal (fn2-run-writers-limit w writers) 2048))
             (and (not (car step)) (equal (mv-nth 1 step) :more)
                  (equal (mv-nth 2 step) (if fits tail (cons row tail)))
                  (equal (fn2-range-leaf-input-after-step step (if fits (append leaves (list row)) leaves))
                         (fn2-range-builder-input (fn2-run-builds-height 0 builds) w leaves children records writers (cons row tail))))))
  :hints (("Goal" :do-not '(preprocess) :cases ((car (fn2-run-leaf-packed-end row (fn2-run-builds-wbase 0 builds) writers)))
           :use (fn2-range-fitting-leaf-keeps-builder-input fn2-range-ready-leaf-is-active
                 (:instance fn2-run-idle-build-appends-fitting-overview (rows leaves))
                 (:instance fn2-run-idle-build-retries-unconsumed-overview (rows leaves))
                 (:instance fn2-range-starting-leaf-close-keeps-builder-input (w (fn2-run-builds-wbase 0 builds))
                   (wbase (fn2-run-builds-wbase 0 builds)) (height (fn2-run-builds-height 0 builds)) (pending (cons row tail))))
           :in-theory (theory 'minimal-theory))))
