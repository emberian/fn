; Promotion already prepares and owns the digest. Check the parent
; destination against its original page window before either write.
(in-package "ACL2")
(include-book "runs-promoted-index-input-proof")
(include-book "runs-index-encode-proof")

(local
 (defthm fn2-run-digest-source-bytes
   (let ((bytes (fn2-page-parent-octets k n words)))
     (and (fn-b3-octet-listp bytes) (equal (true-list-fix bytes) bytes) (equal (len bytes) (nfix n))))
   :hints (("Goal" :induct (fn2-page-parent-octets k n words)
            :in-theory (e/d (fn2-page-parent-octets) (fn2-fc-word-byte floor mod nth))))))

(local
 (defthm fn2-run-stored-reference-readable
   (let* ((bytes (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds)))
          (end (+ at 32)) (after (mv-nth 1 (fn2-run-load-bytes bytes hslot hgen at 9 0 1 pool))))
     (implies (and (unsigned-byte-p 32 at) (natp (fn2-pool-base hslot pool))
                   (equal (fn2-layout-range-code hslot hgen at end t 9 0 1 pool) :ok))
              (and (equal (fn2-layout-range-code hslot hgen at end nil 9 0 1 after) :ok)
                   (equal (fn2-run-read-bytes 32 hslot hgen at 9 0 1 after) bytes))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-load-bytes-roundtrip (bytes (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds)))
                                     (slot hslot) (gen hgen) (off at) (cap (+ at 32)) (pk 9) (ps 0) (pg 1))
                         (:instance fn2-run-writable-end-readable-prefix (slot hslot) (gen hgen) (off at) (end (+ at 32)) (cap (+ at 32))
                           (pk 9) (ps 0) (pg 1)
                           (pool (mv-nth 1 (fn2-run-load-bytes (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds)) hslot hgen at 9 0 1 pool)))))
            :in-theory (disable fn2-layout-range-code fn2-run-load-bytes fn2-run-read-bytes fn2-pool-base
                                fn2-page-parent-octets fn2-digest-list true-list-fix fn-b3-octet-listp len)))))

(local
 (defthm fn2-run-reference-scalar-fields-fit
   (implies (and (natp ib) (fn2-run-writersp writers) (fn2-run-writers-wfp writers) (natp w) (< w (fn2-run-writers-rows writers))
                 (< (fn2-run-writers-page-kind w writers) (len (caddr *fn2-format-page-kind*)))
                 (unsigned-byte-p 60 (car key)) (unsigned-byte-p 60 (cadr key))
                 (equal (fn2-run-unload-values *fn2-overview-index* ib rf rp)
                        (fn2-run-overview-child-row key w hrow writers ds)))
            (and (fn2-run-index-prefix-values-p ib rf)
                 (natp (fn2-fields-value (+ ib *fn2-overview-index-field-child-entries*) rf))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn2-run-unload-values fn2-run-overview-child-row)
                      (fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows fn2-run-writers-entries
                       fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-page-kind
                       fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                       fn2-run-read-bytes fn2-page-parent-octets fn2-digest-list))))))

(defmacro fn2-run-child-index-bytes (rows w hrow writers ds)
  `(fn2-layout-octets *fn2-overview-index* (fn2-run-overview-child-row
          (list (nth 0 (car ,rows)) (nth 1 (car ,rows))) ,w ,hrow ,writers ,ds)))

(defun-nx fn2-run-child-index-destination-p (size level hslot dst dg off pool)
  (let ((source (+ (* 32 level) (fn2-pool-base hslot pool))) (target (+ off (fn2-pool-base dst pool))) (end (+ off size)))
    (and (natp dst) (not (equal dst hslot)) (natp (fn2-pool-base dst pool))
         (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)
         (or (<= (+ 32 source) target) (<= (+ size target) source))
         (equal (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok))))

(local (defthm fn2-run-reference-segment-length (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn2-run-prepared-reference-fits-destination
   (let* ((bytes (fn2-layout-octets *fn2-overview-index* (fn2-run-unload-values *fn2-overview-index* ib rf rp)))
          (i (fn2-run-index-digest-field ib)) (at (* 32 level)) (digest (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds))))
     (implies (and (natp ib) (fn2-run-index-prefix-values-p ib rf)
                   (natp (fn2-fields-value (+ ib *fn2-overview-index-field-child-entries*) rf))
                   (equal (fn2-fields-value i rf) 1) (equal (fn2-fields-ref-len i rf) 32)
                   (equal (fn2-fields-ref-slot i rf) hslot) (equal (fn2-fields-ref-gen i rf) hgen) (equal (fn2-fields-ref-off i rf) at)
                   (natp hslot) (natp (fn2-pool-base hslot pool)) (unsigned-byte-p 32 at)
                   (equal (fn2-layout-range-code hslot hgen at (+ 32 at) t 9 0 1 pool) :ok)
                   (equal rp (mv-nth 1 (fn2-run-load-bytes digest hslot hgen at 9 0 1 pool)))
                   (fn2-run-child-index-destination-p (len bytes) level hslot dst dg off pool))
              (fn2-run-overview-index-write-room-p ib dst dg off rf rp)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess) :do-not-induct t
            :use ((:instance fn2-run-index-wire-segments (base ib) (f rf) (pool rp))
                  (:instance fn2-run-stored-reference-readable (at (* 32 level))))
            :in-theory (e/d (fn2-run-overview-index-write-room-p fn2-run-child-index-destination-p fn2-run-index-digest-octets)
                      (fn2-run-unload-values fn2-layout-octets fn2-overview-index-size fn2-run-read-bytes
                       fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-len fn2-fields-ref-off
                       fn2-run-index-prefix-octets fn2-run-index-count-octets fn2-page-parent-octets fn2-digest-list
                       fn2-pool-base fn2-run-load-bytes fn2-layout-range-code fn-b3-octet-listp binary-append unsigned-byte-p len))))))

(local
 (defthm fn2-run-child-prepares-fitting-scalars
   (let* ((ref (fn2-run-promotion-input level w ib (fn2-run-writers-cursor w writers) hrow hslot hgen writers f pool ds))
          (rf (mv-nth 1 ref)))
     (implies (fn2-run-encoded-child-input-p w level ib hrow hslot hgen rows bvals cvals writers f pool ds)
              (and (fn2-run-index-prefix-values-p ib rf)
                   (natp (fn2-fields-value (+ ib *fn2-overview-index-field-child-entries*) rf)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-encoded-child-supplies-promotion-input
                  fn2-run-promoted-key-width
                  (:instance fn2-run-reference-scalar-fields-fit (key (list (nth 0 (car rows)) (nth 1 (car rows))))
                   (rf (mv-nth 1 (fn2-run-promotion-input level w ib (fn2-run-writers-cursor w writers) hrow hslot hgen writers f pool ds)))
                   (rp (mv-nth 2 (fn2-run-promotion-input level w ib (fn2-run-writers-cursor w writers) hrow hslot hgen writers f pool ds)))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-child-reference-room-p fn2-run-encoded-overview-page-p car-cons cdr-cons (:e car) (:e cdr) (:e len)))))))

(local
 (defthm fn2-run-child-workspace-offset-bounds
   (implies (fn2-run-child-reference-room-p w level ib hrow hslot hgen writers f pool ds)
            (and (natp ib) (natp hslot) (natp (fn2-pool-base hslot pool)) (unsigned-byte-p 32 (* 32 level))
                 (equal (fn2-layout-range-code hslot hgen (* 32 level) (+ 32 (* 32 level)) t 9 0 1 pool) :ok)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-child-reference-room-p)
                      (fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows fn2-fields-rows
                       fn2-digest-rowp fn2-pool-base fn2-layout-range-code))))))

(defthm fn2-run-child-prepares-parent-destination
  (let* ((ref (fn2-run-promotion-input level w ib (fn2-run-writers-cursor w writers) hrow hslot hgen writers f pool ds))
         (size (len (fn2-run-child-index-bytes rows w hrow writers ds))))
    (implies (and (fn2-run-encoded-child-input-p w level ib hrow hslot hgen rows bvals cvals writers f pool ds)
                  (fn2-run-child-index-destination-p size level hslot dst dg off pool))
             (fn2-run-overview-index-write-room-p ib dst dg off (mv-nth 1 ref) (mv-nth 2 ref))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-child-workspace-offset-bounds fn2-run-encoded-child-supplies-promotion-input
                 fn2-run-promoted-index-row-is-admitted fn2-run-child-prepares-fitting-scalars
                 (:instance fn2-run-prepared-reference-fits-destination
                  (rf (mv-nth 1 (fn2-run-promotion-input level w ib (fn2-run-writers-cursor w writers) hrow hslot hgen writers f pool ds)))
                  (rp (mv-nth 2 (fn2-run-promotion-input level w ib (fn2-run-writers-cursor w writers) hrow hslot hgen writers f pool ds)))))
           :in-theory (theory 'minimal-theory))))
