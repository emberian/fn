; Resetting a writable run workspace and reserving its header bytes leaves
; the rest of the page available for entries and their restart directory.
(in-package "ACL2")
(include-book "runs-close-padding-proof")

(defthmd fn2-run-reset-writable-page
  (let* ((reset (fn2-pool-reset slot gen pk ps pg pool)) (after (mv-nth 1 reset)))
    (implies (and (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen 0 *fn2-run-page-size* t pk ps pg pool) :ok))
             (and (natp slot) (< slot (fn2-pool-rows pool))
                  (<= *fn2-run-page-size* (fn2-pool-slot-cap slot pool))
                  (equal (car reset) :ok) (equal (fn2-pool-base slot after) (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen 0 *fn2-run-page-size* t pk ps pg after) :ok))))
  :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-reset fn2-pool-workspace-code
                        fn2-pool-handle-code fn2-pool-ownerp fn2-pool-set-fill update-fn2-pool-fill$ai
                        fn2-pool-slot-cap fn2-pool-slot-fill fn2-pool-slot-base fn2-pool-capacity-bytes nth-update-nth)
                       (nth update-nth)))))

(defthmd fn2-run-reserves-page-header-space
  (let* ((reset (fn2-pool-reset slot gen pk ps pg pool))
         (zero (fn2-run-zero *fn2-run-entries-base* slot gen 0 pk ps pg (mv-nth 1 reset)))
         (after (mv-nth 1 zero)))
    (implies (and (natp (fn2-pool-base slot pool)) (natp (fn2-pool-slot-cap slot pool))
                  (equal (fn2-layout-range-code slot gen 0 *fn2-run-page-size* t pk ps pg pool) :ok))
             (and (equal (car reset) :ok) (equal (car zero) :ok)
                  (equal (fn2-pool-base slot after) (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen *fn2-run-entries-base* *fn2-run-page-size* t pk ps pg after) :ok))))
  :hints (("Goal" :use (fn2-run-reset-writable-page
                       (:instance fn2-run-padding-keeps-page-prefix (off 0) (at 0) (size 0)
                          (cap *fn2-run-page-size*) (n *fn2-run-entries-base*)
                          (pool (mv-nth 1 (fn2-pool-reset slot gen pk ps pg pool)))))
           :in-theory (disable fn2-run-zero fn2-pool-reset fn2-pool-base fn2-pool-rows fn2-pool-slot-cap
                               fn2-layout-range-code fn2-run-read-bytes))))
