; The source and arena are distinct pool slots. Loading the next line in
; the source workspace preserves all bytes and read permissions in the arena.
(in-package "ACL2")
(include-book "range-overlay-arena-proof")
(local (include-book "runs-loaded-overview-order-proof"))

(local
 (defthm fn2-ov-source-octets-preserve-arena
   (let* ((dst (fn2-overlays-slot o ov)) (end (fn2-overlays-fill o ov))
          (after (mv-nth 1 (fn2-run-load-bytes line src sg at 9 0 1 pool))))
     (implies (and (fn2-ov-contiguous-arena-p rows o ov ix pool) (natp src) (natp dst) (not (equal src dst))
                   (natp at) (natp (fn2-pool-base src pool))
                   (<= (+ (fn2-pool-base dst pool) end) (+ (fn2-pool-base src pool) at)))
              (fn2-ov-contiguous-arena-p rows o ov ix after)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-load-preserves-earlier-bytes (bytes line) (dst src) (dg sg) (off at)
                         (src (fn2-overlays-slot o ov)) (sg (fn2-overlays-gen o ov)) (at 0)
                         (n (fn2-overlays-fill o ov)) (pk 9) (ps 0) (pg 1)))
            :in-theory (e/d (fn2-ov-contiguous-arena-p)
                       (fn2-ov-prefix-offsets-p fn2-run-load-bytes fn2-run-read-bytes fn2-layout-range-code fn2-run-entries-octets
                        fn2-poolp fn2-pool-wfp fn2-pool-base fn2-overlays-slot fn2-overlays-gen fn2-overlays-fill fn2-overlays-count
                        fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen fn2-overlays-ibase len unsigned-byte-p))))))

(local
 (defthm fn2-ov-fifth-field-is-line
   (equal (nth 4 row) (car (cddddr row)))
   :hints (("Goal" :expand ((:free (x) (nth 4 x)) (:free (x) (nth 3 x)) (:free (x) (nth 2 x))
                            (:free (x) (nth 1 x)) (:free (x) (nth 0 x)))))))

(defthm fn2-ov-load-keeps-indexed-prefix
  (let* ((load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg at 9 0 1 f pool))
         (sf (mv-nth 2 load)) (sp (mv-nth 3 load)) (dst (fn2-overlays-slot 0 ov)) (end (fn2-overlays-fill 0 ov)))
    (implies (and (fn2-ov-contiguous-arena-p rows 0 ov ix pool) (fn2-run-entries-layoutp *fn2-overview-entry* rows)
                  (natp src) (natp dst) (not (equal src dst)) (natp at) (natp (fn2-pool-base src pool))
                  (<= (+ (fn2-pool-base dst pool) end) (+ (fn2-pool-base src pool) at))
                  (natp eb) (<= (+ eb 5) (fn2-fields-rows f)))
             (and (fn2-ov-contiguous-arena-p rows 0 ov ix sp)
                  (fn2-ov-indexed-rows-p (len rows) rows 0 eb ov ix sf sp))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-source-octets-preserve-arena (o 0) (line (nth 4 row)))
                 (:instance fn2-run-overview-source-fields (base *fn2-run-adapter-entry*) (slot src) (gen sg) (off at))
                 (:instance fn2-run-loaded-keys-and-field-count (base *fn2-run-adapter-entry*) (slot src) (gen sg) (off at) (prev 0))
                 (:instance fn2-ov-contiguous-arena-supplies-reader (o 0)
                      (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg at 9 0 1 f pool)))
                      (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg at 9 0 1 f pool)))))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-ov-fifth-field-is-line (:e natp) (:e <) (:e equal) (:e binary-+) (:e not))))))

(local
 (defthm fn2-ov-input-id-widths
   (implies (fn2-run-values-layoutp *fn2-overview-entry* row)
            (and (unsigned-byte-p 60 (car row)) (unsigned-byte-p 60 (cadr row))
                 (unsigned-byte-p 60 (caddr row)) (unsigned-byte-p 60 (cadddr row))
                 (unsigned-byte-p 32 (len (car (cddddr row))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 0) (id 'group))
                         (:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 1) (id 'group-number))
                         (:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 2) (id 'article))
                         (:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 3) (id 'position))
                         fn2-run-admitted-line-fits-source)
            :expand ((:free (x) (nth 0 x)) (:free (x) (nth 1 x)) (:free (x) (nth 2 x)) (:free (x) (nth 3 x)))
            :in-theory (disable fn2-run-values-layoutp len)))))

(defthm fn2-ov-load-preserves-reader
  (let* ((load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg at 9 0 1 f pool))
         (sf (mv-nth 2 load)))
    (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row)
                  (unsigned-byte-p 32 src) (unsigned-byte-p 60 sg) (unsigned-byte-p 32 at)
                  (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* ov ix f))
             (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* ov ix sf)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use fn2-ov-input-id-widths
           :in-theory (e/d (fn2-ov-overview-reader-p fn2-run-load-values fn2-run-load-ref)
                       (fn2-ov-okp fn2-run-values-layoutp fn2-overlays-schema fn2-fields-rows fn2-fieldsp fn2-fields-wfp
                        fn2-fields-set-value fn2-fields-set-ref-slot fn2-fields-set-ref-gen fn2-fields-set-ref-off
                        fn2-fields-set-ref-len fn2-run-load-bytes len)))))
