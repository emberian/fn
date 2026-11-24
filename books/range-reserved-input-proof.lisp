; Allocating a page preserves the writable extent of a separate input slot.
(in-package "ACL2")
(include-book "layout")

(defthm fn2-range-reserve-keeps-writable-slot
   (let* ((r (fn2-pool-reserve 0 9 0 1 p)) (after (mv-nth 3 r)))
     (implies (and (equal (car r) :ok) (natp i) (natp (mv-nth 1 r)) (not (equal i (mv-nth 1 r))))
              (and (equal (fn2-layout-range-code i g 0 65536 t 9 0 1 after)
                          (fn2-layout-range-code i g 0 65536 t 9 0 1 p))
                   (equal (fn2-pool-base i after) (fn2-pool-base i p)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-layout-range-code fn2-pool-reserve fn2-pool-reserve-body fn2-pool-workspace-code
                    fn2-pool-handle-code fn2-pool-ownerp fn2-pool-slot-base fn2-pool-slot-cap fn2-pool-slot-fill
                    fn2-pool-capacity-bytes fn2-pool-data-length fn2-pool-rows fn2-pool-gen fn2-pool-state
                    fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen fn2-pool-query-ref-count
                    fn2-pool-base fn2-pool-cap fn2-pool-fill fn2-pool-out-count fn2-pool-set-state
                    fn2-pool-set-owner-kind fn2-pool-set-owner-slot fn2-pool-set-owner-gen
                    fn2-pool-set-out-count fn2-pool-set-query-ref-count fn2-pool-set-fill
                    update-fn2-pool-state$ai update-fn2-pool-owner-kind$ai update-fn2-pool-owner-slot$ai
                    update-fn2-pool-owner-gen$ai update-fn2-pool-out-count$ai update-fn2-pool-query-ref-count$ai update-fn2-pool-fill$ai
                    update-fn2-pool-class-headsi update-fn2-pool-class-countsi nth-update-nth)
                  (fn2-pool-reservable-count fn2-pool-mrefp fn2-pool-nclasses fn2-pool-class-headsi
                   fn2-pool-class-countsi fn2-pool-next-free fn2-pool-class nth update-nth)))))
