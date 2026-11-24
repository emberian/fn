; The page checker yields at the end of a consumed hash span. Its returned
; cursor measures the remaining calls for every slot and generation.
(in-package "ACL2")
(include-book "runs-page-hash-step-count-proof")

(local
 (defthm fn2-run-hash-reader-returns-no-control-code
   (implies (member-eq tag '(:yield :byte :more))
            (not (equal (car (fn2-b3-read slot gen off pk ps pg pool)) tag)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-b3-read fn2-pool-read fn2-pool-readable-code fn2-pool-handle-code
                         member-equal eq eql car-cons (:e equal) (:e member-equal)))))))

(local
 (defthm fn2-run-hash-feed-returns-no-control-code
   (implies (member-eq tag '(:yield :byte :more))
            (not (equal (car (fn2-b3-feed row slot gen off left consumed pk ps pg ds b3 pool)) tag)))
   :hints (("Goal" :induct (fn2-b3-feed row slot gen off left consumed pk ps pg ds b3 pool)
            :expand ((fn2-b3-feed row slot gen off left consumed pk ps pg ds b3 pool))
            :in-theory (e/d ((:induction fn2-b3-feed))
                        ((:definition fn2-b3-feed) fn2-b3-read fn2-b3-roomp fn2-b3-can-span fn2-b3-span fn2-b3-byte
                         fn2-pool-slot-base fn2-b3-next-counter))))))

(local
 (defthm fn2-run-successful-hash-feed-used-all-bytes
   (let ((r (fn2-b3-feed row slot gen off left consumed pk ps pg ds b3 pool)))
     (implies (and (natp left) (natp consumed) (equal (car r) :ok)) (equal (mv-nth 1 r) (+ consumed left))))
   :hints (("Goal" :induct (fn2-b3-feed row slot gen off left consumed pk ps pg ds b3 pool)
            :expand ((fn2-b3-feed row slot gen off left consumed pk ps pg ds b3 pool))
            :in-theory (e/d ((:induction fn2-b3-feed)) ((:definition fn2-b3-feed) fn2-b3-read fn2-b3-roomp fn2-b3-can-span
                                        fn2-b3-span fn2-b3-byte fn2-pool-slot-base fn2-b3-next-counter)))
           ("Subgoal *1/3" :use fn2-b3-can-span-bounds))))

(local
 (defthm fn2-run-bounded-hash-update-status
   (let ((r (fn2-b3-update row slot gen off n pk ps pg ds b3 pool)))
     (implies (and (natp off) (natp n) (<= n 4096))
              (and (not (equal (car r) :yield)) (not (equal (car r) :more)) (not (equal (car r) :byte))
                   (implies (equal (car r) :ok) (equal (mv-nth 1 r) n)))))
   :hints (("Goal" :do-not '(preprocess) :cases ((posp (fn2-b3-fragment-count row slot gen off n pk ps pg b3 pool)))
            :use ((:instance fn2-run-successful-hash-feed-used-all-bytes (left n) (consumed 0))
                  (:instance fn2-run-successful-hash-feed-used-all-bytes
                     (off (+ off (fn2-b3-fragment-count row slot gen off n pk ps pg b3 pool)))
                     (left (- n (fn2-b3-fragment-count row slot gen off n pk ps pg b3 pool)))
                     (consumed (fn2-b3-fragment-count row slot gen off n pk ps pg b3 pool))
                     (ds (mv-nth 0 (fn2-b3-fragment-into row (+ (nfix (fn2-pool-slot-base slot pool)) off)
                                         (fn2-b3-fragment-count row slot gen off n pk ps pg b3 pool) ds b3 pool)))
                     (b3 (mv-nth 1 (fn2-b3-fragment-into row (+ (nfix (fn2-pool-slot-base slot pool)) off)
                                         (fn2-b3-fragment-count row slot gen off n pk ps pg b3 pool) ds b3 pool)))))
            :in-theory (e/d (fn2-b3-update)
                        (fn2-b3-fragment-count fn2-b3-fragment-into fn2-b3-feed fn2-pool-slot-base))))))

(local
 (defthm fn2-run-yielded-span-consumed-its-prefix
   (let ((r (fn2-b3-update row slot gen off prefix pk ps pg ds b3 pool)))
     (implies (and (natp off) (natp n) (<= n 4096) (natp prefix) (<= prefix n)
                   (equal (if (eq (car r) :ok) (if (< prefix n) :nonzero-padding :yield) (car r)) :yield))
              (equal (mv-nth 1 r) n)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn2-b3-update)))))

(defmacro fn2-run-full-page-span ()
  '(fn2-fc-page-span 4096 row slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds))

(defthmd fn2-run-page-hash-yield-advances-to-span-end
  (let* ((pos (fn2-fc-pos row fc)) (pad (fn2-fc-pad row fc)) (used (+ (* 64 (fn2-b3-blocks row b3)) (fn2-b3-pos row b3)))
         (n (fn2-fc-span-size 4096 pos pad 65536 used)) (span (fn2-run-full-page-span)))
    (implies (and (natp pos) (< pos 65536) (natp pad) (<= pad 2048) (natp used) (equal (car span) :yield))
             (and (equal (mv-nth 1 span) n) (equal (mv-nth 2 span) (fn2-fc-set-pos row (+ pos n) fc)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-yielded-span-consumed-its-prefix (off (fn2-fc-pos row fc))
                    (n (fn2-fc-span-size 4096 (fn2-fc-pos row fc) (fn2-fc-pad row fc) 65536
                                         (+ (* 64 (fn2-b3-blocks row b3)) (fn2-b3-pos row b3))))
                    (prefix (let* ((pos (fn2-fc-pos row fc)) (pad (fn2-fc-pad row fc))
                                   (size (fn2-fc-span-size 4096 pos pad 65536 (+ (* 64 (fn2-b3-blocks row b3)) (fn2-b3-pos row b3)))))
                              (if (< pos pad) size (fn2-fc-zero-prefix (+ (nfix (fn2-pool-slot-base slot pool)) pos) size pool))))))
           :in-theory (e/d (fn2-fc-page-span)
                         (fn2-b3-update fn2-fc-set-pos fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-span-size
                          fn2-b3-blocks fn2-b3-pos fn2-layout-range-code fn2-fc-zero-prefix fn2-pool-slot-base
                          fn2-pool-data-length fn2-pool-rows nfix)))))

(defthmd fn2-run-readable-hash-span-returns-a-result
  (let* ((pos (fn2-fc-pos row fc)) (pad (fn2-fc-pad row fc)) (used (+ (* 64 (fn2-b3-blocks row b3)) (fn2-b3-pos row b3)))
         (n (fn2-fc-span-size 4096 pos pad 65536 used)) (code (car (fn2-run-full-page-span))))
    (implies (and (natp pos) (< pos 65536) (natp pad) (<= pad 2048) (natp used) (natp slot) (< slot (fn2-pool-rows pool))
                  (equal (fn2-fc-pad-end row fc) 65536)
                  (<= (+ (nfix (fn2-pool-slot-base slot pool)) pos n) (fn2-pool-data-length pool))
                  (equal (fn2-layout-range-code slot gen pos (+ pos n) nil pk ps pg pool) :ok))
             (and (not (equal code :byte)) (not (equal code :more)) (not (equal code :ok)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-fc-page-span)
                         (fn2-b3-update fn2-fc-set-pos fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-span-size
                          fn2-b3-blocks fn2-b3-pos fn2-layout-range-code fn2-fc-zero-prefix fn2-pool-slot-base
                          fn2-pool-data-length fn2-pool-rows nfix)))))
