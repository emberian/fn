; A run page's BLAKE3 update consumes its full span in any allocated slot.
(in-package "ACL2")
(include-book "runs-page-hash-handle-proof")
(include-book "ribbon-false-neg-hash-proof")
(include-book "runs-seal-hash-progress-proof")

(local (defthm fn2-run-hash-first-result (equal (mv-nth 0 x) (car x))
         :hints (("Goal" :in-theory (enable mv-nth)))))

(defthmd fn2-run-filled-page-hash-consumes-range
  (let ((r (fn2-b3-update 0 slot gen off len pk ps pg ds b3 pool)))
    (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool)
                  (natp off) (natp len) (<= len 4096) (<= (+ off len) 65536)
                  (natp bytes) (<= (+ bytes len) 70000) (fn2-ribbon-hash-cursor-p bytes b3))
             (and (equal (car r) :ok) (equal (mv-nth 1 r) len)
                  (fn2-ribbon-hash-cursor-p (+ bytes len) (mv-nth 3 r)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-hash-view-covers-page (:instance fn2-run-hash-update-through-page-view (row 0))
                 (:instance fn2-ribbon-hash-update-consumes-page-range (fn2-pool (fn2-run-hash-page-view slot pool))
                            (fn2-b3 b3) (fn2-digests ds)))
           :in-theory (e/d (fn2-ribbon-arena-p)
                     (fn2-run-hash-page-view fn2-pool-base fn2-pool-fill fn2-pool-cap fn2-pool-workspace-code
                      fn2-pool-data-length fn2-layout-range-code fn2-b3-update fn2-ribbon-hash-cursor-p)))))

(local
 (defthmd fn2-run-hash-span-address
   (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp pos) (natp n) (<= (+ pos n) 65536))
            (and (natp slot) (< slot (fn2-pool-rows pool)) (natp (fn2-pool-slot-base slot pool))
                 (equal (fn2-pool-slot-base slot pool) (fn2-pool-base slot pool))
                 (<= (+ (fn2-pool-base slot pool) pos n) (fn2-pool-data-length pool))
                 (equal (fn2-layout-range-code slot gen pos (+ pos n) nil pk ps pg pool) :ok)))
   :hints (("Goal" :use ((:instance fn2-run-filled-page-allows-subrange (start pos) (end (+ pos n)) (writep nil)))
            :in-theory (e/d (fn2-layout-range-code fn2-pool-slot-base fn2-pool-capacity-bytes
                             fn2-pool-workspace-code fn2-pool-handle-code)
                       (fn2-pool-rows fn2-pool-base fn2-pool-data-length fn2-pool-slot-fill fn2-pool-slot-cap
                        fn2-pool-state fn2-pool-gen fn2-pool-ownerp fn2-pool-query-ref-count))))))

(local
 (defthmd fn2-run-used-hash-bytes-natural
   (implies (fn2-ribbon-hash-cursor-p bytes b3) (natp (fn2-run-hash-used 0 b3)))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-hash-cursor-p) (fn2-b3-pos fn2-b3-blocks))))))

(local
 (defthmd fn2-run-span-capped-by-budget
   (implies (and (natp pos) (natp pad) (natp used))
            (<= (fn2-fc-span-size 4096 pos pad 65536 used) 4096))
   :hints (("Goal" :in-theory (e/d (fn2-fc-span-size) (fn2-fc-aligned-count))))))

(defun-nx fn2-run-hash-page-input-p (slot gen pk ps pg fc b3 pool)
  (let ((pos (fn2-fc-pos 0 fc)) (pad (fn2-fc-pad 0 fc)))
    (and (natp pos) (< pos 65536) (natp pad) (<= pad 2048)
         (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pad-end 0 fc) 65536)
         (fn2-run-filled-page-p slot gen pk ps pg pool)
         (fn2-ribbon-zero-region-p (- 65536 pad) pad slot gen pool)
         (fn2-ribbon-hash-cursor-p (+ 20 pos) b3))))

(defmacro fn2-run-hash-page-span-length ()
  '(fn2-fc-span-size 4096 (fn2-fc-pos 0 fc) (fn2-fc-pad 0 fc) 65536 (fn2-run-hash-used 0 b3)))

(defthmd fn2-run-hash-page-accepts-next-span
  (let* ((pos (fn2-fc-pos 0 fc)) (n (fn2-run-hash-page-span-length))
         (s (fn2-fc-page-span 4096 0 slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds)))
    (implies (fn2-run-hash-page-input-p slot gen pk ps pg fc b3 pool)
             (and (posp n) (equal (car s) :yield) (equal (mv-nth 1 s) n)
                  (equal (mv-nth 2 s) (fn2-fc-set-pos 0 (+ pos n) fc))
                  (fn2-ribbon-hash-cursor-p (+ 20 pos n) (mv-nth 3 s)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-used-hash-bytes-natural (bytes (+ 20 (fn2-fc-pos 0 fc))))
                 (:instance fn2-run-hash-span-address (pos (fn2-fc-pos 0 fc)) (n (fn2-run-hash-page-span-length)))
                 (:instance fn2-run-page-hash-span-size (pos (fn2-fc-pos 0 fc)) (pad (fn2-fc-pad 0 fc)) (used (fn2-run-hash-used 0 b3)))
                 (:instance fn2-run-span-capped-by-budget (pos (fn2-fc-pos 0 fc)) (pad (fn2-fc-pad 0 fc)) (used (fn2-run-hash-used 0 b3)))
                 (:instance fn2-ribbon-checker-accepts-padding-span (pos (fn2-fc-pos 0 fc)) (pad (fn2-fc-pad 0 fc))
                            (span (fn2-run-hash-page-span-length)) (fn2-pool pool))
                 (:instance fn2-run-filled-page-hash-consumes-range (off (fn2-fc-pos 0 fc)) (len (fn2-run-hash-page-span-length))
                            (bytes (+ 20 (fn2-fc-pos 0 fc)))))
           :in-theory (e/d (fn2-fc-page-span fn2-run-hash-page-input-p)
                       (fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-phase fn2-fc-zero-prefix fn2-fc-set-pos fn2-fc-span-size
                        fn2-pool-base fn2-pool-data-length fn2-pool-rows fn2-pool-slot-base fn2-layout-range-code fn2-b3-update
                        fn2-b3-blocks fn2-b3-pos fn2-ribbon-hash-cursor-p fn2-ribbon-zero-region-p)))))
