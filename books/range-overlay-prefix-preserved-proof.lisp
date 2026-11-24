; The complete invariant for continuing the real loader after the next
; admitted input. All evidence about the index and pool is derived from
; the state before the load.
(in-package "ACL2")
(include-book "range-overlay-source-reader-proof")
(include-book "range-overlay-source-bytes-proof")

(defun-nx fn2-ov-physical-prefix-p (rows src sg ov ix f p)
  (and (fn2-overlaysp ov) (fn2-overlay-indexp ix) (fn2-ov-load-workspaces-p rows src sg ov ix f p)))

(local
 (defthm fn2-ov-next-list-length
   (equal (len (append x (list row))) (1+ (len x)))))

(local
 (defthm fn2-ov-components-of-equal-records
   (equal (equal (cons a b) (cons c d)) (and (equal a c) (equal b d)))))

(local
 (defthmd fn2-ov-next-physical-prefix
   (let* ((b (fn2-overlays-ibase 0 ov)) (dst (fn2-overlays-slot 0 ov)) (dg (fn2-overlays-gen 0 ov))
          (wire (fn2-run-entries-octets *fn2-overview-entry* all)) (end (len wire)))
     (implies (and (fn2-ov-physical-prefix-p rows src sg ov ix f p)
                   (fn2-overlaysp ov2) (fn2-overlay-indexp ix2)
                   (equal (fn2-ov-arena-geometry 0 ov2) (fn2-ov-arena-geometry 0 ov))
                   (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* ov2 ix2 f2)
                   (equal (fn2-overlays-count 0 ov2) (len all)) (equal (fn2-overlays-fill 0 ov2) end)
                   (unsigned-byte-p 32 end) (fn2-ov-prefix-offsets-p (len all) all b ix2)
                   (fn2-poolp p2) (fn2-pool-wfp p2)
                   (equal (fn2-pool-base src p2) (fn2-pool-base src p)) (equal (fn2-pool-base dst p2) (fn2-pool-base dst p))
                   (equal (fn2-run-read-bytes end dst dg 0 9 0 1 p2) wire)
                   (equal (fn2-layout-range-code dst dg 0 end nil 9 0 1 p2) :ok)
                   (equal (fn2-layout-range-code dst dg end 65536 t 9 0 1 p2) :ok)
                   (equal (fn2-layout-range-code src sg (fn2-range-line-bytes all) 65536 t 9 0 1 p2) :ok))
              (fn2-ov-physical-prefix-p all src sg ov2 ix2 f2 p2)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-ov-physical-prefix-p fn2-ov-load-workspaces-p fn2-ov-contiguous-arena-p
                         fn2-ov-arena-geometry fn2-ov-components-of-equal-records car-cons cdr-cons (:e equal) (:e not)))))))

(defthmd fn2-ov-source-insert-preserves-physical-prefix
  (let* ((r (fn2-ov-source-insert rows row src sg ov ix f pool)) (all (append rows (list row))))
    (implies (and (fn2-ov-physical-prefix-p rows src sg ov ix f pool)
                  (fn2-run-entries-layoutp *fn2-overview-entry* rows) (fn2-run-values-layoutp *fn2-overview-entry* row)
                  (fn2-run-sorted-spec *fn2-overview-range-key* all) (< (len rows) 48))
             (and (equal (car (fn2-ov-source-load rows row src sg f pool)) :ok)
                  (equal (mv-nth 1 (fn2-ov-source-load rows row src sg f pool)) (fn2-range-line-bytes all))
                  (equal (car r) :ok)
                  (fn2-ov-physical-prefix-p all src sg (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-inserts-next-prefix-row (j 0))
                 fn2-ov-source-insert-keeps-reader fn2-ov-source-insert-extends-index
                 (:instance fn2-ov-source-insert-extends-physical-bytes (j src))
                 (:instance fn2-ov-source-insert-extends-physical-bytes (j (fn2-overlays-slot 0 ov)))
                 (:instance fn2-ov-next-physical-prefix (p pool) (all (append rows (list row)))
                       (ov2 (mv-nth 1 (fn2-ov-source-insert rows row src sg ov ix f pool)))
                       (ix2 (mv-nth 2 (fn2-ov-source-insert rows row src sg ov ix f pool)))
                       (f2 (mv-nth 3 (fn2-ov-source-insert rows row src sg ov ix f pool)))
                       (p2 (mv-nth 4 (fn2-ov-source-insert rows row src sg ov ix f pool)))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-ov-prefix-step-p fn2-ov-physical-prefix-p fn2-ov-next-list-length
                          fn2-ov-source-line-length-after-append (:e natp) (:e equal) (:e not))))))
