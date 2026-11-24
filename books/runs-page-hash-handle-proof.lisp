; Two handles for the same filled page produce the same hash update,
; including the digest words and resumable BLAKE3 state.
(in-package "ACL2")
(include-book "blake3-page-storage-proof")
(include-book "runs-header-overwrite-proof")

(defun-nx fn2-run-hash-page-view (slot pool)
  (update-nth *fn2-pool-datai* (nth *fn2-pool-datai* pool)
    (fn2-pool-set-base 0 (fn2-pool-base slot pool)
      (let ((fn2-pool (fn2-pool-columns-init 1 (create-fn2-pool))))
        (fn2-pool-put 0 (gen 1) (state *fn2-pool-state-workspace*) (owner-kind 9) (owner-slot 0)
                    (owner-gen 1) (out-count 0) (query-ref-count 0) (fill 65536) (cap 65536))))))

(local
 (defthm fn2-run-hash-page-view-layout
   (let ((view (fn2-run-hash-page-view slot pool)))
     (and (fn2-pool-same-bytes-p view pool)
          (equal (fn2-pool-base 0 view) (fn2-pool-base slot pool))
          (equal (fn2-pool-data-length view) (fn2-pool-data-length pool))
          (equal (fn2-pool-rows view) 1)
          (equal (fn2-pool-fill 0 view) 65536) (equal (fn2-pool-cap 0 view) 65536)
          (equal (fn2-pool-workspace-code 0 1 9 0 1 view) :ok)))
   :hints (("Goal" :in-theory (e/d (fn2-run-hash-page-view fn2-pool-same-bytes-p fn2-pool-workspace-code
                   fn2-pool-handle-code fn2-pool-ownerp fn2-pool-base fn2-pool-rows fn2-pool-cap
                   fn2-pool-fill fn2-pool-gen fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen fn2-pool-out-count
                   fn2-pool-query-ref-count fn2-pool-state fn2-pool-data-length fn2-pool-set-base update-fn2-pool-base$ai nth-update-nth)
                    (nth update-nth))))))

(defthmd fn2-run-hash-view-covers-page
  (let ((view (fn2-run-hash-page-view slot pool)))
    (implies (fn2-run-filled-page-p slot gen pk ps pg pool)
             (and (natp slot) (< slot (fn2-pool-rows pool))
                  (equal (fn2-pool-workspace-code 0 1 9 0 1 view) :ok)
                  (natp (fn2-pool-base 0 view))
                  (equal (fn2-pool-fill 0 view) 65536) (equal (fn2-pool-cap 0 view) 65536)
                  (<= (+ (fn2-pool-base 0 view) 65536) (fn2-pool-data-length view))
                  (fn2-run-filled-page-p 0 1 9 0 1 view))))
  :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-workspace-code fn2-pool-handle-code
                                    fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-slot-base fn2-pool-capacity-bytes)
                            (fn2-run-hash-page-view fn2-pool-base fn2-pool-rows fn2-pool-data-length
                             fn2-pool-state fn2-pool-ownerp fn2-pool-gen fn2-pool-fill fn2-pool-cap
                             fn2-pool-out-count fn2-pool-query-ref-count)))))

(local
 (defthmd fn2-run-filled-page-read-address
   (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp off) (< off 65536))
            (equal (fn2-b3-read slot gen off pk ps pg pool)
                   (list :ok (fn2-pool-datai (+ (fn2-pool-base slot pool) off) pool))))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-b3-read fn2-pool-read fn2-pool-readable-code
                         fn2-pool-workspace-code fn2-pool-slot-fill fn2-pool-slot-base fn2-pool-capacity-bytes)
                      (fn2-pool-handle-code fn2-pool-base fn2-pool-fill fn2-pool-datai fn2-pool-data-length
                       fn2-pool-ownerp fn2-pool-state fn2-pool-query-ref-count fn2-pool-out-count))))))

(local
 (defthm fn2-run-hash-page-view-read
   (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp off) (< off 65536))
            (equal (fn2-b3-read 0 1 off 9 0 1 (fn2-run-hash-page-view slot pool))
                   (fn2-b3-read slot gen off pk ps pg pool)))
   :rule-classes nil
   :hints (("Goal" :use (fn2-run-filled-page-read-address fn2-run-hash-view-covers-page
                  (:instance fn2-run-filled-page-read-address (slot 0) (gen 1) (pk 9) (ps 0) (pg 1)
                             (pool (fn2-run-hash-page-view slot pool))))
            :in-theory (e/d (fn2-pool-datai fn2-run-hash-page-view)
                            (fn2-b3-read fn2-pool-base fn2-layout-range-code nth update-nth))))))

(local
 (defthm fn2-run-hash-page-view-span-choice
   (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp off) (natp left) (<= (+ off left) 65536))
            (equal (fn2-b3-can-span row 0 1 off left used 9 0 1 b3 (fn2-run-hash-page-view slot pool))
                   (fn2-b3-can-span row slot gen off left used pk ps pg b3 pool)))
   :rule-classes nil
   :hints (("Goal" :use (fn2-run-hash-view-covers-page
                  (:instance fn2-run-filled-page-allows-subrange (start off) (end (+ 1024 off)) (writep nil))
                  (:instance fn2-run-filled-page-allows-subrange (start off) (end (+ 1024 off)) (writep nil)
                             (slot 0) (gen 1) (pk 9) (ps 0) (pg 1) (pool (fn2-run-hash-page-view slot pool))))
            :in-theory (e/d (fn2-b3-can-span fn2-pool-slot-base)
                      (fn2-run-hash-page-view fn2-layout-range-code fn2-pool-base fn2-pool-rows fn2-pool-data-length
                       fn2-b3-flags fn2-b3-blocks fn2-b3-pos fn2-b3-next-counter unsigned-byte-p))))))

(local
 (defthm fn2-run-hash-from-page-view-span
   (equal (fn2-b3-span row off counter lastp ds b3 (fn2-run-hash-page-view slot pool))
          (fn2-b3-span row off counter lastp ds b3 pool))
   :hints (("Goal" :use ((:instance fn2-pool-same-bytes-p-implies-equal-fn2-b3-span-7
                         (pool (fn2-run-hash-page-view slot pool)) (pool-equiv pool)))
            :in-theory (disable fn2-run-hash-page-view fn2-pool-same-bytes-p fn2-b3-span)))))

(local
 (defthmd fn2-run-hash-from-page-view-feed
   (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp off) (natp left) (natp used) (<= (+ off left) 65536))
            (equal (fn2-b3-feed row 0 1 off left used 9 0 1 ds b3 (fn2-run-hash-page-view slot pool))
                   (fn2-b3-feed row slot gen off left used pk ps pg ds b3 pool)))
   :hints (("Goal" :induct (fn2-b3-feed row slot gen off left used pk ps pg ds b3 pool)
            :do-not '(preprocess)
            :expand ((fn2-b3-feed row 0 1 off left used 9 0 1 ds b3 (fn2-run-hash-page-view slot pool))
                     (fn2-b3-feed row slot gen off left used pk ps pg ds b3 pool))
            :in-theory (e/d ((:i fn2-b3-feed) fn2-pool-slot-base)
                       ((:d fn2-b3-feed) fn2-b3-span fn2-b3-can-span fn2-b3-roomp fn2-b3-read fn2-b3-next-counter
                        fn2-b3-byte fn2-pool-base fn2-run-hash-page-view fn2-layout-range-code)))
           ("Subgoal *1/1" :in-theory (enable fn2-b3-feed))
           ("Subgoal *1/3" :use (fn2-run-hash-page-view-span-choice (:instance fn2-b3-can-span-bounds (consumed used)
                                  (fn2-b3 b3) (fn2-pool pool) (okind pk) (oslot ps) (ogen pg))))
           ("Subgoal *1/4" :use (fn2-run-hash-page-view-span-choice fn2-run-hash-page-view-read))
           ("Subgoal *1/5" :use (fn2-run-hash-page-view-span-choice fn2-run-hash-page-view-read)))))

(local
 (defmacro fn2-run-hash-fragment-size ()
   '(min len (nfix (- 1024 (+ (* 64 (fn2-b3-blocks row b3)) (fn2-b3-pos row b3)))))))

(local
 (defthm fn2-run-hash-page-view-fragment-count
   (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp off) (natp len) (<= (+ off len) 65536))
            (equal (fn2-b3-fragment-count row 0 1 off len 9 0 1 b3 (fn2-run-hash-page-view slot pool))
                   (fn2-b3-fragment-count row slot gen off len pk ps pg b3 pool)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-hash-view-covers-page
                  (:instance fn2-run-filled-page-allows-subrange (start off) (end (+ off (fn2-run-hash-fragment-size))) (writep nil))
                  (:instance fn2-run-filled-page-allows-subrange (start off) (end (+ off (fn2-run-hash-fragment-size))) (writep nil)
                             (slot 0) (gen 1) (pk 9) (ps 0) (pg 1) (pool (fn2-run-hash-page-view slot pool))))
            :in-theory (e/d (fn2-b3-fragment-count fn2-pool-slot-base)
                      (fn2-run-hash-page-view fn2-layout-range-code fn2-pool-base fn2-pool-rows fn2-pool-data-length
                       fn2-b3-flags fn2-b3-blocks fn2-b3-pos fn2-b3-roomp unsigned-byte-p))))))

(local
 (defthm fn2-run-hash-from-page-view-fragment
   (equal (fn2-b3-fragment-into row off n ds b3 (fn2-run-hash-page-view slot pool))
          (fn2-b3-fragment-into row off n ds b3 pool))
   :hints (("Goal" :use ((:instance fn2-pool-same-bytes-p-implies-equal-fn2-b3-fragment-into-6
                         (pool (fn2-run-hash-page-view slot pool)) (pool-equiv pool)))
            :in-theory (disable fn2-run-hash-page-view fn2-pool-same-bytes-p fn2-b3-fragment-into)))))

(defthmd fn2-run-hash-update-through-page-view
  (let ((view (fn2-run-hash-page-view slot pool)))
    (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp off) (natp len)
                  (<= len 4096) (<= (+ off len) 65536))
             (equal (fn2-b3-update row slot gen off len pk ps pg ds b3 pool)
                    (fn2-b3-update row 0 1 off len 9 0 1 ds b3 view))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-hash-page-view-fragment-count
                 (:instance fn2-run-hash-from-page-view-feed (used 0) (left len))
                 (:instance fn2-run-hash-from-page-view-feed
                   (used (fn2-b3-fragment-count row slot gen off len pk ps pg b3 pool))
                   (off (+ off (fn2-b3-fragment-count row slot gen off len pk ps pg b3 pool)))
                   (left (- len (fn2-b3-fragment-count row slot gen off len pk ps pg b3 pool)))
                   (ds (mv-nth 0 (fn2-b3-fragment-into row (+ (nfix (fn2-pool-base slot pool)) off)
                                    (fn2-b3-fragment-count row slot gen off len pk ps pg b3 pool) ds b3 pool)))
                   (b3 (mv-nth 1 (fn2-b3-fragment-into row (+ (nfix (fn2-pool-base slot pool)) off)
                                    (fn2-b3-fragment-count row slot gen off len pk ps pg b3 pool) ds b3 pool)))))
           :cases ((posp (fn2-b3-fragment-count row slot gen off len pk ps pg b3 pool)))
           :in-theory (e/d (fn2-b3-update fn2-pool-slot-base)
                     (fn2-run-hash-page-view fn2-b3-fragment-into fn2-b3-feed fn2-b3-fragment-count
                      fn2-pool-base fn2-layout-range-code)))))
