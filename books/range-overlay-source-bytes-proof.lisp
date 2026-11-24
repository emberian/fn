; After inserting an admitted row, the entire new logical prefix is
; physically readable and both reservations admit the next write.
(in-package "ACL2")
(include-book "range-overlay-prefix-step-proof")
(include-book "range-overlay-prefix-bytes-proof")

(local (include-book "range-overview-admitted-octets-proof"))

(local
 (defthm fn2-ov-encoded-length-of-append
   (equal (len (append x y)) (+ (len x) (len y)))))

(defthm fn2-ov-source-line-length-after-append
  (equal (fn2-range-line-bytes (append rows (list row))) (+ (fn2-range-line-bytes rows) (len (nth 4 row))))
  :hints (("Goal" :induct (len rows) :in-theory (disable nth))))

(local
 (defthmd fn2-ov-physical-prefix-inputs
   (let* ((dst (fn2-overlays-slot 0 ov)) (dg (fn2-overlays-gen 0 ov))
          (off (fn2-overlays-fill 0 ov)) (at (fn2-range-line-bytes rows)))
     (implies (fn2-ov-prefix-step-p rows row src sg ov ix f pool)
              (and (natp src) (natp dst) (not (equal src dst)) (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                   (<= (+ (fn2-pool-base dst pool) 65536) (fn2-pool-base src pool)) (natp off) (natp at)
                   (equal (fn2-run-read-bytes off dst dg 0 9 0 1 pool) (fn2-run-entries-octets *fn2-overview-entry* rows))
                   (equal off (len (fn2-run-entries-octets *fn2-overview-entry* rows)))
                   (equal (fn2-layout-range-code src sg at 65536 t 9 0 1 pool) :ok)
                   (equal (fn2-layout-range-code dst dg off 65536 t 9 0 1 pool) :ok)
                   (unsigned-byte-p 32 (+ off (len (fn2-layout-octets *fn2-overview-entry* row))))
                   (<= (+ off (len (fn2-layout-octets *fn2-overview-entry* row))) 65536)
                   (<= (+ at (len (nth 4 row))) 65536))))
   :hints (("Goal" :do-not '(preprocess) :use fn2-range-next-row-fits-both-workspaces
            :in-theory (e/d (fn2-ov-prefix-step-p fn2-ov-load-workspaces-p fn2-ov-contiguous-arena-p)
                        (fn2-ov-overview-reader-p fn2-ov-prefix-offsets-p fn2-run-entries-layoutp fn2-run-values-layoutp
                         fn2-run-sorted-spec fn2-range-line-bytes fn2-run-read-bytes fn2-run-entries-octets fn2-layout-octets
                         fn2-layout-range-code fn2-poolp fn2-pool-wfp fn2-pool-base fn2-overlays-slot fn2-overlays-gen
                         fn2-overlays-count fn2-overlays-fill fn2-overlays-ibase fn2-overlays-icap fn2-overlays-cap
                         fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen fn2-overlays-phase nth binary-append len))))))

(defthmd fn2-ov-source-insert-extends-physical-bytes
  (let* ((r (fn2-ov-source-insert rows row src sg ov ix f pool)) (p (mv-nth 4 r))
         (all (append rows (list row))) (wire (fn2-run-entries-octets *fn2-overview-entry* all))
         (dst (fn2-overlays-slot 0 ov)) (dg (fn2-overlays-gen 0 ov)))
    (implies (fn2-ov-prefix-step-p rows row src sg ov ix f pool)
             (and (equal (fn2-overlays-fill 0 (mv-nth 1 r)) (len wire)) (unsigned-byte-p 32 (len wire))
                  (equal (fn2-run-read-bytes (len wire) dst dg 0 9 0 1 p) wire)
                  (equal (fn2-layout-range-code dst dg 0 (len wire) nil 9 0 1 p) :ok)
                  (equal (fn2-layout-range-code dst dg (len wire) 65536 t 9 0 1 p) :ok)
                  (equal (fn2-layout-range-code src sg (fn2-range-line-bytes all) 65536 t 9 0 1 p) :ok)
                  (fn2-poolp p) (fn2-pool-wfp p) (equal (fn2-pool-base j p) (fn2-pool-base j pool)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-ov-physical-prefix-inputs (:instance fn2-ov-inserts-next-prefix-row (j 0))
                 (:instance fn2-ov-complete-appended-pool-bytes
                        (at (fn2-range-line-bytes rows)) (off (fn2-overlays-fill 0 ov))
                        (dst (fn2-overlays-slot 0 ov)) (dg (fn2-overlays-gen 0 ov))
                        (line (nth 4 row)) (bytes (fn2-layout-octets *fn2-overview-entry* row)))
                 (:instance fn2-ov-appended-pool-windows
                        (at (fn2-range-line-bytes rows)) (off (fn2-overlays-fill 0 ov))
                        (dst (fn2-overlays-slot 0 ov)) (dg (fn2-overlays-gen 0 ov))
                        (line (nth 4 row)) (bytes (fn2-layout-octets *fn2-overview-entry* row))))
           :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-ov-prefix-step-p fn2-ov-load-workspaces-p fn2-ov-contiguous-arena-p
                      fn2-ov-entries-plus-one fn2-ov-checked-row-contains-octets fn2-ov-encoded-length-of-append
                      fn2-ov-source-line-length-after-append fn2-run-load-preserves-base fn2-run-load-preserves-pool
                      (:e natp) (:e equal) (:e not))))))
