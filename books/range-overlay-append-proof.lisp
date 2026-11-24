; Appending a sorted input to the overlay records its arena address,
; advances the fill, and leaves every earlier index position intact.
(in-package "ACL2")
(include-book "range-served")
(local (include-book "runs-overview-emit-proof"))

(local
 (defthm fn2-ov-append-index-update
   (let* ((n (fn2-overlays-count o ov)) (b (fn2-overlays-ibase o ov))
          (r (fn2-ov-place o n off end ov ix)))
     (implies (and (fn2-ov-okp o ov ix) (natp n) (natp b)
                   (< n (fn2-overlays-icap o ov))
                   (unsigned-byte-p 32 off) (unsigned-byte-p 32 end))
              (and (equal (car r) :ok)
                   (equal (mv-nth 1 r) (fn2-overlays-set-fill o end (fn2-overlays-set-count o (+ 1 n) ov)))
                   (equal (mv-nth 2 r) (fn2-overlay-index-set-off (+ b n) off ix)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-ov-okp fn2-ov-place fn2-ov-insert-at)
                           (fn2-overlays-wfp fn2-overlay-index-wfp fn2-overlays-rows fn2-overlay-index-rows
                            fn2-overlays-count fn2-overlays-icap fn2-overlays-ibase
                            fn2-overlays-set-count fn2-overlays-set-fill fn2-overlay-index-set-off unsigned-byte-p))))))

(defthm fn2-ov-append-records-row-offset
  (let* ((n (fn2-overlays-count o ov)) (b (fn2-overlays-ibase o ov))
         (r (fn2-ov-place o n off end ov ix)) (after (mv-nth 1 r)) (index (mv-nth 2 r)))
    (implies (and (fn2-ov-okp o ov ix) (natp n) (natp b) (< n (fn2-overlays-icap o ov))
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (natp j))
             (and (equal (car r) :ok) (equal (fn2-overlays-count o after) (1+ n))
                  (equal (fn2-overlays-fill o after) end)
                  (equal (fn2-overlay-index-off (+ b j) index)
                         (if (equal j n) off (fn2-overlay-index-off (+ b j) ix))))))
  :rule-classes nil
  :hints (("Goal" :use fn2-ov-append-index-update
           :in-theory (e/d (fn2-overlays-count fn2-overlays-fill fn2-overlays-set-count fn2-overlays-set-fill
                    fn2-overlay-index-off fn2-overlay-index-set-off update-fn2-overlay-index-off$ai
                    update-fn2-overlays-count$ai update-fn2-overlays-fill$ai nth-update-nth)
                  (fn2-overlays-ibase fn2-overlays-icap fn2-ov-okp fn2-ov-place nth update-nth unsigned-byte-p)))))

(local
 (defthm fn2-ov-overview-write-size
   (implies (and (natp base) (natp (fn2-fields-ref-len (+ base 4) f)) (natp (fn2-fields-value base f))
                 (natp (fn2-fields-value (+ base 1) f)) (natp (fn2-fields-value (+ base 2) f))
                 (natp (fn2-fields-value (+ base 3) f)))
            (equal (fn2-run-layout-size 3 0 base f) (fn2-overview-entry-size base f)))
   :hints (("Goal" :use ((:instance fn2-run-overview-wire-size (pool nil)))
            :in-theory (e/d (fn2-run-layout-size) (fn2-overview-entry-size fn2-run-unload-values fn2-layout-octets
                       fn2-fields-value fn2-fields-ref-len natp len))))))

(defthm fn2-ov-append-indexes-encoded-overview
  (let* ((off (fn2-overlays-fill o ov)) (dst (fn2-overlays-slot o ov)) (dg (fn2-overlays-gen o ov))
         (n (fn2-overlays-count o ov)) (b (fn2-overlays-ibase o ov))
         (i (+ base 4)) (src (fn2-fields-ref-slot i f)) (sg (fn2-fields-ref-gen i f))
         (at (fn2-fields-ref-off i f)) (size (fn2-overview-entry-size base f))
         (k (fn2-fields-ref-len i f)) (end (+ off size))
         (from (+ at (fn2-pool-base src pool))) (to (+ off (fn2-pool-base dst pool)))
         (bytes (fn2-layout-octets *fn2-overview-entry* (fn2-run-unload-values *fn2-overview-entry* base f pool)))
         (r (fn2-ov-write o n base nil ov ix f pool)) (after (mv-nth 1 r)) (index (mv-nth 2 r)) (p (mv-nth 3 r)))
    (implies (and (fn2-ov-okp o ov ix) (natp n) (natp b) (< n (fn2-overlays-icap o ov))
                  (equal (fn2-overlays-schema o ov) 3) (equal (fn2-overlays-okind o ov) 9)
                  (equal (fn2-overlays-oslot o ov) 0) (equal (fn2-overlays-ogen o ov) 1)
                  (natp base) (<= (+ base *fn2-run-entry-rows*) (fn2-fields-rows f))
                  (natp (fn2-fields-value base f)) (natp (fn2-fields-value (+ base 1) f))
                  (natp (fn2-fields-value (+ base 2) f)) (natp (fn2-fields-value (+ base 3) f))
                  (fn2-poolp pool) (fn2-pool-wfp pool) (natp src) (natp dst) (not (equal src dst))
                  (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= end (fn2-overlays-cap o ov))
                  (unsigned-byte-p 32 at) (natp k) (<= k 1024) (or (<= (+ from k) to) (<= (+ to size) from))
                  (equal (fn2-layout-range-code src sg at (+ at k) nil 9 0 1 pool) :ok)
                  (equal (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok) (natp j))
             (and (equal (car r) :ok) (equal (fn2-overlays-count o after) (1+ n))
                  (equal (fn2-overlays-fill o after) end)
                  (equal (fn2-overlay-index-off (+ b j) index)
                         (if (equal j n) off (fn2-overlay-index-off (+ b j) ix)))
                  (equal p (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)))
                  (equal (fn2-run-read-bytes size dst dg off 9 0 1 p) bytes))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-overview-leaf-encode-writes-layout
                     (off (fn2-overlays-fill o ov)) (dst (fn2-overlays-slot o ov)) (dg (fn2-overlays-gen o ov)))
                 (:instance fn2-ov-append-records-row-offset (off (fn2-overlays-fill o ov))
                     (end (+ (fn2-overlays-fill o ov) (fn2-overview-entry-size base f)))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-ov-overview-write-size fn2-ov-write eq not mv-nth car-cons cdr-cons
                          (:e mv-nth) (:e equal) (:e consp) (:e zp) (:e unary--) (:e binary-+))))))
