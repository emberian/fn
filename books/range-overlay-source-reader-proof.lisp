; The next input uses the same arena and the same reader region. Its
; updated count still fits the allocated offset table.
(in-package "ACL2")
(include-book "range-overlay-prefix-step-proof")
(include-book "range-overlay-insert-geometry-proof")

(local
 (defthmd fn2-ov-reader-from-matching-geometry
   (implies (and (fn2-ov-overview-reader-p 0 eb base ov ix f)
                 (equal (fn2-ov-arena-geometry 0 ov2) (fn2-ov-arena-geometry 0 ov))
                 (fn2-overlays-wfp ov2) (fn2-overlay-index-wfp ix2)
                 (equal (fn2-overlays-rows ov2) (fn2-overlays-rows ov))
                 (equal (fn2-overlay-index-rows ix2) (fn2-overlay-index-rows ix))
                 (fn2-fieldsp f2) (fn2-fields-wfp f2) (equal (fn2-fields-rows f2) (fn2-fields-rows f))
                 (<= (fn2-overlays-count 0 ov2) (fn2-overlays-icap 0 ov)))
            (fn2-ov-overview-reader-p 0 eb base ov2 ix2 f2))
   :hints (("Goal" :in-theory (e/d (fn2-ov-overview-reader-p fn2-ov-okp fn2-ov-arena-geometry)
                      (fn2-overlays-wfp fn2-overlay-index-wfp fn2-fieldsp fn2-fields-wfp fn2-fields-rows
                       fn2-overlays-rows fn2-overlay-index-rows fn2-overlays-ibase fn2-overlays-icap
                       fn2-overlays-count fn2-overlays-phase fn2-overlays-schema fn2-overlays-slot fn2-overlays-gen
                       fn2-overlays-cap fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))))))

(local
 (defthmd fn2-ov-source-reader-after-load
   (let* ((load (fn2-ov-source-load rows row src sg f pool)) (base *fn2-run-adapter-entry*) (eb *fn2-run-adapter-reader*))
     (implies (fn2-ov-prefix-step-p rows row src sg ov ix f pool)
              (fn2-ov-overview-reader-p 0 eb base ov ix (mv-nth 2 load))))
   :hints (("Goal" :do-not '(preprocess) :use (fn2-range-next-row-fits-both-workspaces
                 (:instance fn2-ov-load-preserves-reader (at (fn2-range-line-bytes rows))))
            :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-ov-prefix-step-p fn2-ov-load-workspaces-p (:e equal) (:e not)))))))

(local
 (defthmd fn2-ov-next-index-count-fits
   (let ((r (fn2-ov-source-insert rows row src sg ov ix f pool)))
     (implies (fn2-ov-prefix-step-p rows row src sg ov ix f pool)
              (<= (fn2-overlays-count 0 (mv-nth 1 r)) (fn2-overlays-icap 0 ov))))
   :hints (("Goal" :do-not '(preprocess) :use ((:instance fn2-ov-inserts-next-prefix-row (j 0)))
            :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-ov-prefix-step-p fn2-ov-load-workspaces-p (:e natp) (:t len)
                        (:e equal) (:e not) (:e <) (:e binary-+)))))))

(defthmd fn2-ov-source-insert-keeps-reader
  (let* ((r (fn2-ov-source-insert rows row src sg ov ix f pool)) (ov2 (mv-nth 1 r)) (ix2 (mv-nth 2 r)))
    (implies (and (fn2-overlaysp ov) (fn2-overlay-indexp ix) (fn2-ov-prefix-step-p rows row src sg ov ix f pool))
             (and (fn2-overlaysp ov2) (fn2-overlay-indexp ix2)
                  (equal (fn2-ov-arena-geometry 0 ov2) (fn2-ov-arena-geometry 0 ov))
                  (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* ov2 ix2 (mv-nth 3 r)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-ov-source-reader-after-load fn2-ov-next-index-count-fits
                 (:instance fn2-ov-inserting-retains-geometry (j 0) (o 0) (base *fn2-run-adapter-entry*) (eb *fn2-run-adapter-reader*)
                        (f (mv-nth 2 (fn2-ov-source-load rows row src sg f pool))) (p (mv-nth 3 (fn2-ov-source-load rows row src sg f pool))))
                 (:instance fn2-ov-inserting-retains-tables (o 0) (base *fn2-run-adapter-entry*) (eb *fn2-run-adapter-reader*)
                        (f (mv-nth 2 (fn2-ov-source-load rows row src sg f pool))) (p (mv-nth 3 (fn2-ov-source-load rows row src sg f pool))))
                 (:instance fn2-ov-reader-from-matching-geometry (base *fn2-run-adapter-entry*) (eb *fn2-run-adapter-reader*)
                        (f (mv-nth 2 (fn2-ov-source-load rows row src sg f pool)))
                        (ov2 (mv-nth 1 (fn2-ov-source-insert rows row src sg ov ix f pool)))
                        (ix2 (mv-nth 2 (fn2-ov-source-insert rows row src sg ov ix f pool)))
                        (f2 (mv-nth 3 (fn2-ov-source-insert rows row src sg ov ix f pool)))))
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-ov-overview-reader-p fn2-ov-okp (:e equal) (:e not))))))
