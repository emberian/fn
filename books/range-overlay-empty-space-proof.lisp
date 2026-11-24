; Starting the overlay resets its own arena and leaves its separate input workspace writable.
(in-package "ACL2")
(include-book "range-served")

(defthmd fn2-ov-reset-keeps-source-space
   (let ((p (mv-nth 1 (fn2-pool-reset dst 1 9 0 1 pool))))
     (implies (and (natp src) (natp dst) (not (equal src dst)))
              (and (equal (fn2-pool-base src p) (fn2-pool-base src pool))
                   (equal (fn2-layout-range-code src 1 0 65536 t 9 0 1 p)
                          (fn2-layout-range-code src 1 0 65536 t 9 0 1 pool)))))
   :hints (("Goal" :in-theory (e/d (fn2-pool-reset fn2-layout-range-code fn2-pool-workspace-code
                        fn2-pool-handle-code fn2-pool-ownerp fn2-pool-slot-fill fn2-pool-slot-base fn2-pool-slot-cap
                        fn2-pool-base fn2-pool-cap fn2-pool-fill fn2-pool-set-fill update-fn2-pool-fill$ai
                        fn2-pool-capacity-bytes fn2-pool-data-length fn2-pool-rows fn2-pool-state fn2-pool-gen
                        fn2-pool-query-ref-count fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen nth-update-nth)
                       (nth update-nth)))))

(defthmd fn2-ov-empty-workspace-readable
   (implies (equal (fn2-layout-range-code dst 1 0 65536 t 9 0 1 pool) :ok)
            (equal (fn2-layout-range-code dst 1 0 0 nil 9 0 1 pool) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-workspace-code fn2-pool-readable-code)
                        (fn2-pool-handle-code fn2-pool-ownerp fn2-pool-slot-base fn2-pool-slot-cap fn2-pool-slot-fill
                         fn2-pool-capacity-bytes fn2-pool-state fn2-pool-query-ref-count)))))

(defthm fn2-ov-arena-after-start
   (let* ((start (fn2-ov-start 0 3 dst 1 0 256 9 0 1 0 ov ix pool)) (after (mv-nth 1 start)))
     (implies (and (natp dst) (unsigned-byte-p 32 dst) (< dst (fn2-pool-rows pool))
                   (< 0 (fn2-overlays-rows ov)) (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-free*)
                   (<= 256 (fn2-overlay-index-rows ix)) (fn2-overlays-wfp ov)
                   (equal (fn2-pool-slot-cap dst pool) 65536) (equal (car (fn2-pool-reset dst 1 9 0 1 pool)) :ok))
              (and (equal (car start) :ok) (equal (mv-nth 2 start) (mv-nth 1 (fn2-pool-reset dst 1 9 0 1 pool)))
                   (fn2-overlays-wfp after) (equal (fn2-overlays-rows after) (fn2-overlays-rows ov))
                   (equal (fn2-overlays-slot 0 after) dst) (equal (fn2-overlays-gen 0 after) 1)
                   (equal (fn2-overlays-fill 0 after) 0) (equal (fn2-overlays-count 0 after) 0)
                   (equal (fn2-overlays-cap 0 after) 65536) (equal (fn2-overlays-icap 0 after) 256)
                   (equal (fn2-overlays-ibase 0 after) 0) (equal (fn2-overlays-schema 0 after) 3)
                   (equal (fn2-overlays-phase 0 after) *fn2-overlay-phase-active*)
                   (equal (fn2-overlays-okind 0 after) 9) (equal (fn2-overlays-oslot 0 after) 0) (equal (fn2-overlays-ogen 0 after) 1))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-ov-start fn2-overlays-rows fn2-overlays-phase fn2-overlays-schema fn2-overlays-slot
                         fn2-overlays-gen fn2-overlays-fill fn2-overlays-count fn2-overlays-cap fn2-overlays-icap fn2-overlays-ibase
                         fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen nth-update-nth)
                        (fn2-pool-reset fn2-overlays-wfp fn2-overlay-index-rows fn2-pool-rows
                         fn2-pool-slot-cap unsigned-byte-p nth update-nth)))))
