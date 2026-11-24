; The range adapter's overlay starts with an empty, readable arena and a
; separate writable source. Both pointers come from class-zero reservations.
(in-package "ACL2")
(include-book "range-overlay-prefix-insert-proof")
(include-book "range-build-workspace-proof")
(include-book "range-overlay-empty-space-proof")
(local (include-book "runs-open-workspace-proof"))

(local
 (defthm fn2-ov-zero-bytes-in-new-arena
   (equal (fn2-run-read-bytes 0 s g off pk ps pg p) nil)
   :hints (("Goal" :expand ((fn2-run-read-bytes 0 s g off pk ps pg p))))))

(defthm fn2-ov-start-prepares-empty-prefix
  (let* ((start (fn2-ov-start 0 3 dst 1 0 256 9 0 1 0 ov ix pool)) (after (mv-nth 1 start)) (p (mv-nth 2 start)))
    (implies (and (fn2-poolp pool) (fn2-pool-wfp pool) (fn2-overlays-wfp ov) (< 0 (fn2-overlays-rows ov))
                  (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-free*) (fn2-overlay-index-wfp ix) (<= 256 (fn2-overlay-index-rows ix))
                  (fn2-fieldsp f) (fn2-fields-wfp f) (<= (+ *fn2-run-adapter-reader* *fn2-run-entry-rows*) (fn2-fields-rows f))
                  (natp dst) (unsigned-byte-p 32 dst) (natp src) (unsigned-byte-p 32 src) (not (equal src dst))
                  (equal (fn2-pool-slot-cap dst pool) 65536) (natp (fn2-pool-base dst pool)) (natp (fn2-pool-base src pool))
                  (<= (+ 65536 (fn2-pool-base dst pool)) (fn2-pool-base src pool))
                  (equal (fn2-layout-range-code src 1 0 65536 t 9 0 1 pool) :ok)
                  (equal (fn2-layout-range-code dst 1 0 65536 t 9 0 1 pool) :ok))
             (and (equal (car start) :ok) (fn2-ov-load-workspaces-p nil src 1 after ix f p))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :expand ((fn2-ov-prefix-offsets-p 0 nil 0 ix))
           :use (fn2-ov-arena-after-start (:instance fn2-run-reset-writable-page (slot dst) (gen 1) (pk 9) (ps 0) (pg 1)))
           :in-theory (e/d (fn2-ov-reset-keeps-source-space fn2-ov-empty-workspace-readable fn2-ov-load-workspaces-p fn2-ov-contiguous-arena-p fn2-ov-overview-reader-p fn2-ov-okp)
                       (fn2-ov-start fn2-pool-reset fn2-layout-range-code fn2-run-read-bytes fn2-run-entries-octets
                        fn2-ov-prefix-offsets-p fn2-range-line-bytes fn2-overlays-wfp fn2-overlay-index-wfp fn2-overlay-index-rows
                        fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-poolp fn2-pool-wfp fn2-pool-base fn2-pool-slot-cap fn2-pool-rows
                        fn2-overlays-rows fn2-overlays-phase fn2-overlays-schema fn2-overlays-slot fn2-overlays-gen fn2-overlays-fill
                        fn2-overlays-count fn2-overlays-cap fn2-overlays-icap fn2-overlays-ibase fn2-overlays-okind fn2-overlays-oslot
                        fn2-overlays-ogen unsigned-byte-p)))))

(local
 (defthm fn2-ov-reserve-keeps-slot-capacity
   (equal (fn2-pool-slot-cap j (mv-nth 3 (fn2-pool-reserve 0 9 0 1 p))) (fn2-pool-slot-cap j p))
   :hints (("Goal" :in-theory (e/d (fn2-pool-reserve fn2-pool-reserve-body fn2-pool-slot-cap fn2-pool-cap)
                         (fn2-pool-reservable-count fn2-pool-nclasses fn2-pool-class-headsi fn2-pool-class-countsi
                          fn2-pool-next-free fn2-pool-class fn2-pool-rows fn2-pool-state fn2-pool-gen nth update-nth))))))

(defthm fn2-ov-reserved-start-prepares-empty-prefix
  (let* ((arena (fn2-pool-reserve 0 9 0 1 p)) (dst (mv-nth 1 arena))
         (src-res (fn2-pool-reserve 0 9 0 1 (mv-nth 3 arena))) (src (mv-nth 1 src-res))
         (start (fn2-ov-start 0 3 dst (mv-nth 2 arena) 0 256 9 0 1 0 ov ix (mv-nth 3 src-res))))
    (implies (and (fn2-range-pool-available-p n p) (natp n) (<= 2 n) (fn2-poolp p) (fn2-pool-wfp p)
                  (fn2-overlays-wfp ov) (< 0 (fn2-overlays-rows ov)) (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-free*)
                  (fn2-overlay-index-wfp ix) (<= 256 (fn2-overlay-index-rows ix))
                  (fn2-fieldsp f) (fn2-fields-wfp f) (<= (+ *fn2-run-adapter-reader* *fn2-run-entry-rows*) (fn2-fields-rows f)))
             (and (equal (car arena) :ok) (equal (car src-res) :ok) (equal (car start) :ok)
                  (fn2-ov-load-workspaces-p nil src (mv-nth 2 src-res) (mv-nth 1 start) ix f (mv-nth 2 start)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-build-reserves-workspaces
                 (:instance fn2-range-reservation-provides-workspace (pk 9) (ps 0) (pg 1))
                 (:instance fn2-ov-start-prepares-empty-prefix (dst (- 327 n)) (src (- 328 n))
                        (pool (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 p)))))))
           :in-theory (e/d (fn2-range-pool-available-p)
                       (fn2-ov-start fn2-pool-reserve fn2-ov-load-workspaces-p fn2-range-free-suffix-p
                        fn2-layout-range-code fn2-pool-slot-cap fn2-poolp fn2-pool-wfp fn2-pool-base fn2-pool-rows
                        fn2-pool-class-headsi fn2-pool-class-countsi fn2-pool-nclasses fn2-pool-credit-configured fn2-pool-capacity-bytes
                        fn2-overlays-wfp fn2-overlays-rows fn2-overlays-phase fn2-overlay-index-wfp fn2-overlay-index-rows
                        fn2-fieldsp fn2-fields-wfp fn2-fields-rows)))))
