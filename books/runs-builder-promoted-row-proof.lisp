; Promotion submits the first key and sealed child reference to the actual
; parent writer, then applies its append or full-page result.
(in-package "ACL2")
(include-book "runs-promoted-first-key-proof")

(defun-nx fn2-run-overview-promotion-ready-p (level builds writers)
  (and (natp level) (< (1+ level) *fn2-run-max-levels*) (< (1+ level) (fn2-run-builds-height 0 builds))
       (equal (fn2-run-builds-wbase 0 builds) 0) (equal (fn2-run-builds-fields 0 builds) 0)
       (equal (fn2-run-builds-schema 0 builds) 3) (< (1+ level) (fn2-run-writers-rows writers))
       (equal (fn2-run-writers-phase level writers) *fn2-run-writer-phase-sealed*)
       (equal (fn2-run-writers-phase (1+ level) writers) *fn2-run-writer-phase-open*)
       (equal (fn2-run-builds-hbase 0 builds) 136)
       (equal (fn2-run-builds-okind 0 builds) 9) (equal (fn2-run-builds-oslot 0 builds) 0) (equal (fn2-run-builds-ogen 0 builds) 1)))

(defmacro fn2-run-overview-promote-bindings (body)
  `(let* ((ib *fn2-run-build-index*) (end (fn2-run-writers-cursor level writers))
          (hslot (fn2-run-builds-hslot 0 builds)) (hgen (fn2-run-builds-hgen 0 builds)) (hrow (+ 136 level))
          (ref (fn2-run-promotion-input level level ib end hrow hslot hgen writers f pool ds))
          (parent (fn2-run-add (1+ level) 3 ib writers restarts (mv-nth 1 ref) (mv-nth 2 ref)))
          (commit (fn2-run-promote-commit level (car parent) (mv-nth 1 parent)))
          (promote (fn2-run-build-promote 0 level builds writers restarts f pool ds)))
     ,body))

(local
 (defthm fn2-run-concrete-promotion-submits-reference
   (fn2-run-overview-promote-bindings
     (implies (and (fn2-run-overview-promotion-ready-p level builds writers)
                   (<= (+ ib *fn2-run-entry-rows*) (fn2-fields-rows f))
                   (equal (car (fn2-run-layout-decode 3 level ib (fn2-run-writers-slot level writers) (fn2-run-writers-gen level writers)
                               *fn2-run-entries-base* end 9 0 1 f pool)) :ok) (equal (car ref) :ok))
              (equal promote (list (car commit) builds (mv-nth 1 commit) (mv-nth 2 parent)
                                   (mv-nth 3 parent) (mv-nth 4 parent) ds))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-build-promote fn2-run-promote-check fn2-run-overview-promotion-ready-p)
                 (fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-fields fn2-run-builds-schema fn2-run-writers-rows
                  fn2-run-writers-phase fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-cursor fn2-run-builds-hbase
                  fn2-run-builds-hslot fn2-run-builds-hgen fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen
                  fn2-fields-rows fn2-run-layout-decode fn2-run-child-ref fn2-run-add fn2-run-promote-commit))))))

(defthmd fn2-run-builder-promotes-encoded-child
  (fn2-run-overview-promote-bindings
   (implies (and (fn2-run-overview-promotion-ready-p level builds writers) (consp rows)
                 (fn2-run-encoded-overview-page-p rows level bvals cvals (fn2-run-writers-slot level writers)
                           (fn2-run-writers-gen level writers) 9 0 1 pool)
                 (equal end (fn2-run-overview-directory-offset level rows))
                 (fn2-fieldsp f) (fn2-fields-wfp f) (<= (+ ib *fn2-run-entry-rows*) (fn2-fields-rows f))
                 (fn2-run-child-reference-room-p level level ib hrow hslot hgen writers f pool ds))
            (and (equal (fn2-run-unload-values *fn2-overview-index* ib (mv-nth 1 ref) (mv-nth 2 ref))
                        (fn2-run-overview-child-row (list (nth 0 (car rows)) (nth 1 (car rows))) level hrow writers ds))
                 (equal promote (list (car commit) builds (mv-nth 1 commit) (mv-nth 2 parent)
                                      (mv-nth 3 parent) (mv-nth 4 parent) ds)))))
  :hints (("Goal" :use (fn2-run-concrete-promotion-submits-reference
                    (:instance fn2-run-encoded-child-supplies-promotion-input (w level) (ib *fn2-run-build-index*) (hrow (+ 136 level))
                      (hslot (fn2-run-builds-hslot 0 builds)) (hgen (fn2-run-builds-hgen 0 builds))))
           :in-theory (theory 'minimal-theory))))
