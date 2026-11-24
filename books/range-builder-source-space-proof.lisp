; Initializing the builder writes only its hash slot. The distinct input
; slot retains its complete writable interval.
(in-package "ACL2")
(include-book "runs")
(local (include-book "runs-load-frame-proof"))

(local
 (defthm fn2-range-fill-preserves-other-workspace
   (let ((p (fn2-pool-set-fill dst v pool)))
     (implies (and (natp src) (natp dst) (not (equal src dst)))
              (and (equal (fn2-pool-base j p) (fn2-pool-base j pool))
                   (equal (fn2-layout-range-code src sg at cap t 9 0 1 p)
                          (fn2-layout-range-code src sg at cap t 9 0 1 pool)))))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-workspace-code
                        fn2-pool-handle-code fn2-pool-ownerp fn2-pool-slot-fill fn2-pool-slot-base fn2-pool-slot-cap
                        fn2-pool-base fn2-pool-cap fn2-pool-fill fn2-pool-set-fill update-fn2-pool-fill$ai
                        fn2-pool-capacity-bytes fn2-pool-data-length fn2-pool-rows fn2-pool-state fn2-pool-gen
                        fn2-pool-query-ref-count fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen nth-update-nth)
                       (nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-range-reset-preserves-other-workspace
   (let ((p (mv-nth 1 (fn2-pool-reset dst dg 9 0 1 pool))))
     (implies (and (natp src) (natp dst) (not (equal src dst)))
              (and (equal (fn2-pool-base j p) (fn2-pool-base j pool))
                   (equal (fn2-layout-range-code src sg at cap t 9 0 1 p)
                          (fn2-layout-range-code src sg at cap t 9 0 1 pool)))))
   :hints (("Goal" :in-theory (e/d (fn2-pool-reset)
                              (fn2-pool-workspace-code fn2-pool-base fn2-pool-set-fill fn2-layout-range-code))))))

(local
 (defthm fn2-range-writing-zero-preserves-other-workspace
   (implies (and (natp src) (natp dst) (not (equal src dst)) (natp (fn2-pool-base dst pool)))
            (equal (fn2-layout-range-code src sg at cap t 9 0 1 (mv-nth 1 (fn2-pool-write dst dg off 0 9 0 1 pool)))
                   (fn2-layout-range-code src sg at cap t 9 0 1 pool)))
   :hints (("Goal" :use ((:instance fn2-run-load-preserves-other-range (bytes '(0)) (slot dst) (gen dg) (dst src) (dg sg)
                                   (end cap) (writep t) (pk 9) (ps 0) (pg 1)))
            :expand ((fn2-run-load-bytes '(0) dst dg off 9 0 1 pool)
                     (:free (x y) (fn2-run-load-bytes nil dst dg x 9 0 1 y)))
            :in-theory (disable fn2-run-load-preserves-other-range fn2-run-load-bytes fn2-pool-write fn2-pool-base fn2-layout-range-code)))))

(local
 (defthm fn2-range-zeroing-preserves-other-workspace
   (let ((p (mv-nth 1 (fn2-run-zero n dst dg off 9 0 1 pool))))
     (implies (and (natp src) (natp dst) (not (equal src dst)) (natp (fn2-pool-base dst pool)))
              (and (equal (fn2-pool-base j p) (fn2-pool-base j pool))
                   (equal (fn2-layout-range-code src sg at cap t 9 0 1 p) (fn2-layout-range-code src sg at cap t 9 0 1 pool)))))
   :hints (("Goal" :induct (fn2-run-zero n dst dg off 9 0 1 pool)
            :in-theory (e/d (fn2-run-zero fn2-pool-write-keeps-extents) (fn2-pool-write fn2-pool-base fn2-layout-range-code))))))

(defthmd fn2-range-start-keeps-input-slot
  (let ((p (mv-nth 3 (fn2-run-build-start 0 3 run 0 0 136 dst dg 0 2048 1 1 9 0 1 b w pool))))
    (implies (and (natp src) (natp dst) (not (equal src dst)) (natp (fn2-pool-base dst pool)))
             (and (equal (fn2-pool-base j p) (fn2-pool-base j pool))
                  (equal (fn2-layout-range-code src sg at cap t 9 0 1 p) (fn2-layout-range-code src sg at cap t 9 0 1 pool)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-run-build-start)
                      (fn2-run-reset-writers fn2-run-zero fn2-pool-reset fn2-run-builds-rows fn2-run-builds-phase
                       fn2-pool-base fn2-layout-range-code unsigned-byte-p)))))

(defthmd fn2-range-opening-page-keeps-input-slot
  (let* ((r (fn2-run-open w dst dg sid version level run ordinal kind unit epoch counter history incarnation
                          9 0 1 fields limit writers pool))
         (p (mv-nth 2 r)))
    (implies (and (natp src) (natp dst) (not (equal src dst)) (natp (fn2-pool-base dst pool)))
             (and (equal (fn2-pool-base j p) (fn2-pool-base j pool))
                  (equal (fn2-layout-range-code src sg at cap t 9 0 1 p)
                         (fn2-layout-range-code src sg at cap t 9 0 1 pool)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-run-open)
                      (fn2-run-zero fn2-pool-reset fn2-pool-base fn2-pool-rows fn2-pool-slot-cap
                       fn2-run-writers-phase fn2-layout-range-code unsigned-byte-p)))))
