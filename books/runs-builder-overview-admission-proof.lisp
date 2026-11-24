; For a sorted overview input the append decision is exactly the packing
; bound, including the four bytes reserved for each restart offset.
(in-package "ACL2")
(include-book "runs-loaded-overview-order-proof")
(include-book "runs-builder-open-page-proof")

(defun-nx fn2-run-overview-append-workspace-p (w base writers restarts f)
  (and (natp w) (< w (fn2-run-writers-rows writers))
       (<= (* (1+ w) *fn2-run-restart-capacity*) (fn2-run-restarts-rows restarts))
       (natp base) (<= (+ base *fn2-run-entry-rows*) (fn2-fields-rows f))
       (natp (fn2-run-writers-fields w writers))
       (<= (+ (fn2-run-writers-fields w writers) *fn2-run-writer-fields*) (fn2-fields-rows f))
       (< (+ (fn2-run-writers-fields w writers) *fn2-run-prev-fields* 1) base)
       (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-open*)
       (equal (fn2-run-writers-schema w writers) 3) (equal (fn2-run-writers-level w writers) 0)))

(local
 (defthm fn2-run-overview-key-prefix-for-order
   (equal (fn2-run-key-order-spec *fn2-overview-range-key* (list (nfix (car row)) (nfix (cadr row))) prev)
          (fn2-run-key-order-spec *fn2-overview-range-key* row prev))
   :hints (("Goal" :in-theory (enable fn2-run-key-order-spec)))))

(local (defthm fn2-run-append-natural-index (implies (natp i) (equal (nfix i) i))))

(defthmd fn2-run-sorted-overview-admission
  (let* ((prev (+ (fn2-run-writers-fields w writers) *fn2-run-prev-fields*))
         (load (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))
         (sf (mv-nth 2 load)) (sp (mv-nth 3 load))
         (packed (fn2-run-pack-bound (len (fn2-layout-octets *fn2-overview-entry* row))
                      (fn2-run-writers-cursor w writers) (fn2-run-writers-entries w writers)
                      (fn2-run-writers-restarts w writers) (fn2-run-writers-limit w writers))))
    (implies (and (fn2-run-overview-append-workspace-p w base writers restarts f)
                  (fn2-run-values-layoutp *fn2-overview-entry* row) (natp at) (natp (fn2-pool-base src pool))
                  (equal (fn2-layout-range-code src sg at (+ at (len (nth 4 row))) t 9 0 1 pool) :ok)
                  (or (not (equal (fn2-run-writers-prev w writers) 1))
                      (equal (fn2-run-key-order-spec *fn2-overview-range-key* row (fn2-overview-range-key-at prev f)) :gt)))
             (and (equal (car load) :ok)
                  (equal (fn2-run-add-ready w 3 base writers restarts sf sp) (if (car packed) :ok :full)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-loaded-keys-and-field-count (slot src) (gen sg) (off at)
                        (prev (+ (fn2-run-writers-fields w writers) *fn2-run-prev-fields*)))
                 (:instance fn2-run-loaded-overview-wire-size (slot src) (gen sg) (off at) (cap (+ at (len (nth 4 row))))))
           :in-theory (e/d (fn2-run-add-ready fn2-run-add-check fn2-run-roomp)
                     (nfix fn2-run-roomp-by-definition fn2-run-pack-bound fn2-run-load-values fn2-run-unload-values
                      fn2-layout-range-code fn2-layout-octets fn2-run-values-layoutp fn2-overview-range-key-at fn2-run-key-order-spec
                      fn2-run-layout-size fn2-pool-base fn2-run-writers-fields fn2-run-writers-phase fn2-run-writers-schema
                      fn2-run-writers-rows fn2-run-writers-level fn2-run-writers-prev fn2-run-writers-cursor fn2-run-writers-restarts
                      fn2-run-writers-entries fn2-run-writers-limit fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen
                      fn2-run-restarts-rows fn2-fields-rows nth)))))
