; Loading octets preserves pool extents and other handles' checked ranges.
(in-package "ACL2")
(include-book "runs-load-bytes-proof")

(local
 (defthm fn2-run-other-range-after-byte-update
 (implies (and (natp slot) (natp dst) (not (equal slot dst))
               (natp addr) (< addr (fn2-pool-data-length pool)))
          (equal (fn2-layout-range-code dst dg at end writep pk ps pg
                  (fn2-pool-set-fill slot new-fill (update-fn2-pool-datai addr byte pool)))
                 (fn2-layout-range-code dst dg at end writep pk ps pg pool)))
 :hints (("Goal" :in-theory
           (e/d (fn2-layout-range-code fn2-pool-slot-fill fn2-pool-slot-base fn2-pool-slot-cap
                 fn2-pool-capacity-bytes fn2-pool-workspace-code fn2-pool-readable-code
                 fn2-pool-handle-code fn2-pool-ownerp fn2-pool-set-fill
                 update-fn2-pool-fill$ai update-fn2-pool-datai nth-update-nth)
                (nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-run-write-frames-other-range
 (implies (and (natp slot) (natp dst) (not (equal slot dst)) (natp (fn2-pool-base slot pool)))
          (equal (fn2-layout-range-code dst dg at end writep pk ps pg
                         (mv-nth 1 (fn2-pool-write slot gen off byte pk ps pg pool)))
                 (fn2-layout-range-code dst dg at end writep pk ps pg pool)))
 :hints (("Goal" :in-theory (e/d (fn2-pool-write)
                          (fn2-pool-workspace-code fn2-layout-range-code fn2-pool-base fn2-pool-cap
                           fn2-pool-fill fn2-pool-data-length fn2-pool-set-fill update-fn2-pool-datai
                           unsigned-byte-p))))))

(defthm fn2-run-load-preserves-other-range
 (implies (and (natp slot) (natp dst) (not (equal slot dst)) (natp (fn2-pool-base slot pool)))
          (equal (fn2-layout-range-code dst dg at end writep pk ps pg
                         (mv-nth 1 (fn2-run-load-bytes bytes slot gen off pk ps pg pool)))
                 (fn2-layout-range-code dst dg at end writep pk ps pg pool)))
 :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg pool)
          :in-theory (e/d (fn2-run-load-bytes fn2-pool-write-keeps-extents)
                          (fn2-pool-base fn2-pool-write fn2-layout-range-code)))))

(defthm fn2-run-load-preserves-base
 (equal (fn2-pool-base i (mv-nth 1 (fn2-run-load-bytes bytes slot gen off pk ps pg pool)))
        (fn2-pool-base i pool))
 :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg pool)
          :in-theory (e/d (fn2-run-load-bytes fn2-pool-write-keeps-extents)
                          (fn2-pool-base fn2-pool-write)))))

(defthm fn2-run-load-preserves-pool
 (implies (and (fn2-poolp pool) (fn2-pool-wfp pool))
          (let ((after (mv-nth 1 (fn2-run-load-bytes bytes slot gen off pk ps pg pool))))
            (and (fn2-poolp after) (fn2-pool-wfp after))))
 :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg pool)
          :in-theory (e/d (fn2-run-load-bytes) (fn2-poolp fn2-pool-wfp fn2-pool-write)))))

(defthm fn2-run-writable-end-readable-prefix
 (implies (and (unsigned-byte-p 32 off) (<= off end)
               (equal (fn2-layout-range-code slot gen end cap t pk ps pg pool) :ok))
          (equal (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok))
 :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-workspace-code fn2-pool-readable-code)
                                 (fn2-pool-slot-base fn2-pool-slot-fill fn2-pool-slot-cap
                                  fn2-pool-capacity-bytes fn2-pool-handle-code fn2-pool-ownerp fn2-pool-state)))))
