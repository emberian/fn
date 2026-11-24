; The adapter loads the input into its source slot and inserts it through
; the sorted index. The new index position addresses the entire input row.
(in-package "ACL2")
(include-book "range-overlay-insert-write-proof")
(local (include-book "runs-loaded-overview-order-proof"))

(local
 (defthm fn2-ov-next-appended-row
   (equal (car (append xs (list x))) (if (consp xs) (car xs) x))))

(local (defthm fn2-ov-fixed-input-id (equal (nfix (nfix x)) (nfix x))))

(local
 (defthm fn2-ov-order-input-key-fields
   (equal (fn2-run-key-order-spec *fn2-overview-range-key* prev (list (nfix (car row)) (nfix (cadr row))))
          (fn2-run-key-order-spec *fn2-overview-range-key* prev row))
   :hints (("Goal" :in-theory (disable nfix)))))

(local
 (defthm fn2-ov-sorted-next-key
   (equal (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list (list (nfix (car row)) (nfix (cadr row))))))
          (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list row))))
   :hints (("Goal" :induct (len rows) :do-not '(preprocess)
            :in-theory (disable fn2-run-key-order-spec nfix)))))

(local (defthm fn2-ov-natural-offset (implies (unsigned-byte-p 32 at) (natp at))))

(local
 (defthm fn2-ov-projection-of-cons
   (equal (mv-nth i (cons a b)) (if (zp i) a (mv-nth (1- i) b)))))

(local (defthm fn2-ov-natural-index-length (natp (len rows))))

(local
 (defthmd fn2-ov-sorted-insertion-records-encoding
   (let* ((n (len rows)) (b (fn2-overlays-ibase 0 ov)) (off (fn2-overlays-fill 0 ov))
          (base *fn2-run-adapter-entry*) (eb *fn2-run-adapter-reader*) (dst (fn2-overlays-slot 0 ov))
          (dg (fn2-overlays-gen 0 ov)) (enc (fn2-run-layout-encode 3 0 base dst dg off 9 0 1 f pool))
          (end (mv-nth 1 enc)) (ins (fn2-ov-insert 0 base eb ov ix f pool)))
     (implies (and (< n 48) (equal (fn2-overlays-count 0 ov) n) (< n (fn2-overlays-icap 0 ov)) (natp b) (natp j)
                   (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-active*)
                   (equal (fn2-overlays-okind 0 ov) 9) (equal (fn2-overlays-oslot 0 ov) 0) (equal (fn2-overlays-ogen 0 ov) 1)
                   (fn2-ov-overview-reader-p 0 eb base ov ix f) (fn2-ov-indexed-rows-p n rows 0 eb ov ix f pool)
                   (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list (fn2-overview-range-key-at base f))))
                   (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (equal (car enc) :ok)
                   (<= (+ off (fn2-run-layout-size 3 0 base f)) (fn2-overlays-cap 0 ov)))
              (and (equal (car ins) :ok) (equal (mv-nth 4 ins) (mv-nth 2 enc))
                   (equal (fn2-overlays-count 0 (mv-nth 1 ins)) (1+ n))
                   (equal (fn2-overlays-fill 0 (mv-nth 1 ins)) end)
                   (equal (fn2-overlay-index-off (+ b j) (mv-nth 2 ins))
                          (if (equal j n) off (fn2-overlay-index-off (+ b j) ix))))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-ov-sorted-insert-writes-input fn2-ov-append-reaches-encoded-index)
            :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-ov-overview-reader-p fn2-ov-projection-of-cons fn2-ov-natural-index-length (:t len) (:e binary-+) (:e natp)
                          (:e <) (:e not) (:e equal) (:e zp) (:e unary--) car-cons))))))

(defthm fn2-ov-loaded-input-is-stored-at-fill
  (let* ((base *fn2-run-adapter-entry*) (eb *fn2-run-adapter-reader*)
         (n (len rows)) (b (fn2-overlays-ibase 0 ov)) (off (fn2-overlays-fill 0 ov))
         (dst (fn2-overlays-slot 0 ov)) (dg (fn2-overlays-gen 0 ov))
         (line (nth 4 row)) (bytes (fn2-layout-octets *fn2-overview-entry* row)) (size (len bytes)) (end (+ off size))
         (load (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))
         (sf (mv-nth 2 load)) (sp (mv-nth 3 load)) (ins (fn2-ov-insert 0 base eb ov ix sf sp))
         (after (mv-nth 1 ins)) (index (mv-nth 2 ins)) (p (mv-nth 4 ins)))
    (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row)
                  (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list row)))
                  (< n 48) (equal (fn2-overlays-count 0 ov) n) (< n (fn2-overlays-icap 0 ov)) (natp b)
                  (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-active*)
                  (equal (fn2-overlays-okind 0 ov) 9) (equal (fn2-overlays-oslot 0 ov) 0) (equal (fn2-overlays-ogen 0 ov) 1)
                  (fn2-ov-overview-reader-p 0 eb base ov ix sf) (fn2-ov-indexed-rows-p n rows 0 eb ov ix sf sp)
                  (fn2-poolp pool) (fn2-pool-wfp pool) (natp src) (natp dst) (not (equal src dst))
                  (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 at) (unsigned-byte-p 32 end)
                  (<= end (fn2-overlays-cap 0 ov))
                  (or (<= (+ (+ at (fn2-pool-base src pool)) (len line)) (+ off (fn2-pool-base dst pool)))
                      (<= (+ (+ off (fn2-pool-base dst pool)) size) (+ at (fn2-pool-base src pool))))
                  (equal (fn2-layout-range-code src sg at (+ at (len line)) t 9 0 1 pool) :ok)
                  (equal (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok) (natp j))
             (and (equal (car load) :ok) (equal (mv-nth 1 load) (+ at (len line)))
                  (equal (car ins) :ok) (equal (fn2-overlays-count 0 after) (1+ n))
                  (equal (fn2-overlays-fill 0 after) end)
                  (equal (fn2-overlay-index-off (+ b j) index) (if (equal j n) off (fn2-overlay-index-off (+ b j) ix)))
                  (equal p (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1
                                         (mv-nth 1 (fn2-run-load-bytes line src sg at 9 0 1 pool)))))
                  (equal (fn2-layout-range-code dst dg off end nil 9 0 1 p) :ok)
                  (equal (fn2-run-read-bytes size dst dg off 9 0 1 p) bytes))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-loaded-keys-and-field-count (base *fn2-run-adapter-entry*) (slot src) (gen sg) (off at) (prev 0))
                 (:instance fn2-run-loaded-overview-wire-size (base *fn2-run-adapter-entry*) (slot src) (gen sg) (off at)
                            (cap (+ at (len (nth 4 row)))))
                 (:instance fn2-run-load-overview-roundtrip (base *fn2-run-adapter-entry*) (slot src) (gen sg) (off at)
                            (cap (+ at (len (nth 4 row)))))
                 (:instance fn2-run-adapter-source-wire-readback (base *fn2-run-adapter-entry*) (rb *fn2-run-adapter-reader*)
                            (rf (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg at 9 0 1 f pool)))
                            (dst (fn2-overlays-slot 0 ov)) (dg (fn2-overlays-gen 0 ov)) (off (fn2-overlays-fill 0 ov)))
                 (:instance fn2-ov-sorted-insertion-records-encoding
                            (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg at 9 0 1 f pool)))
                            (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg at 9 0 1 f pool)))))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-ov-overview-reader-p fn2-ov-sorted-next-key fn2-ov-natural-offset
                         (:t len) (:t fn2-ov-insert) (:t fn2-ov-write) (:t fn2-ov-locate)
                         fn2-ov-projection-of-cons car-cons cdr-cons eq not (:e equal) (:e consp) (:e zp) (:e natp) (:e not)
                         (:e mv-nth) (:e <) (:e len) (:e unary--) (:e binary-+))))))
