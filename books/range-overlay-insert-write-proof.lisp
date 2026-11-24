; On a sorted input the actual insert performs the same append as writing
; the original input fields directly, including its pool and index effects.
(in-package "ACL2")
(include-book "range-overlay-insert-position-proof")
(include-book "range-overlay-input-fields-proof")
(include-book "range-overlay-append-proof")

(local
 (defthmd fn2-ov-same-input-same-write
   (implies (and (equal (fn2-overlays-schema o ov) 3) (natp base)
                 (fn2-ov-same-input-p base f f2) (equal (fn2-fields-rows f) (fn2-fields-rows f2)))
            (equal (fn2-ov-write o pos base nil ov ix f pool) (fn2-ov-write o pos base nil ov ix f2 pool)))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-ov-same-input-encodes-identically
                   (dst (fn2-overlays-slot o ov)) (dg (fn2-overlays-gen o ov)) (off (fn2-overlays-fill o ov))
                   (pk (fn2-overlays-okind o ov)) (ps (fn2-overlays-oslot o ov)) (pg (fn2-overlays-ogen o ov))))
            :in-theory (e/d (fn2-ov-write) (fn2-ov-same-input-p fn2-ov-okp fn2-run-layout-size fn2-run-layout-encode
                        fn2-ov-place fn2-fields-rows fn2-overlays-fill fn2-overlays-cap fn2-overlays-schema fn2-overlays-slot
                        fn2-overlays-gen fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))))))

(defthmd fn2-ov-sorted-insert-writes-input
  (let* ((base *fn2-run-adapter-entry*) (eb *fn2-run-adapter-reader*) (n (len rows))
         (query (fn2-overview-range-key-at base f))
         (write (fn2-ov-write 0 n base nil ov ix f pool))
         (loc (fn2-ov-locate 0 eb base 9 0 1 ov ix f pool)) (ins (fn2-ov-insert 0 base eb ov ix f pool)))
    (implies (and (< n 48) (< n (fn2-overlays-icap 0 ov)) (equal (fn2-overlays-count 0 ov) n)
                  (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-active*)
                  (equal (fn2-overlays-okind 0 ov) 9) (equal (fn2-overlays-oslot 0 ov) 0) (equal (fn2-overlays-ogen 0 ov) 1)
                  (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list query)))
                  (fn2-ov-overview-reader-p 0 eb base ov ix f) (fn2-ov-indexed-rows-p n rows 0 eb ov ix f pool))
             (equal ins (list (car write) (mv-nth 1 write) (mv-nth 2 write) (mv-nth 3 loc) (mv-nth 3 write)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-locates-sorted-append (o 0) (eb *fn2-run-adapter-reader*) (base *fn2-run-adapter-entry*) (j 0))
                 (:instance fn2-ov-search-preserves-input-for-encode (o 0) (eb *fn2-run-adapter-reader*) (base *fn2-run-adapter-entry*))
                 (:instance fn2-ov-same-input-same-write (o 0) (pos (len rows)) (base *fn2-run-adapter-entry*) (f2 f)
                    (f (mv-nth 3 (fn2-ov-locate 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* 9 0 1 ov ix f pool)))))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-ov-insert fn2-ov-overview-reader-p eq eql not member-equal
                         (:t fn2-ov-locate) (:t fn2-ov-write) mv-nth car-cons cdr-cons (:e mv-nth) (:e equal)
                         (:e consp) (:e zp) (:e natp) (:e <) (:e not) (:e binary-+) (:e unary--))))))

(defthmd fn2-ov-append-reaches-encoded-index
  (let* ((n (fn2-overlays-count 0 ov)) (base *fn2-run-adapter-entry*)
         (dst (fn2-overlays-slot 0 ov)) (dg (fn2-overlays-gen 0 ov)) (off (fn2-overlays-fill 0 ov))
         (enc (fn2-run-layout-encode 3 0 base dst dg off 9 0 1 f pool)) (end (mv-nth 1 enc))
         (write (fn2-ov-write 0 n base nil ov ix f pool)) (index (mv-nth 2 write)) (b (fn2-overlays-ibase 0 ov)))
    (implies (and (fn2-ov-okp 0 ov ix) (natp n) (natp b) (< n (fn2-overlays-icap 0 ov))
                  (equal (fn2-overlays-schema 0 ov) 3) (equal (fn2-overlays-okind 0 ov) 9)
                  (equal (fn2-overlays-oslot 0 ov) 0) (equal (fn2-overlays-ogen 0 ov) 1)
                  (<= (+ base *fn2-run-entry-rows*) (fn2-fields-rows f))
                  (<= (+ off (fn2-run-layout-size 3 0 base f)) (fn2-overlays-cap 0 ov))
                  (equal (car enc) :ok) (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (natp j))
             (and (equal (car write) :ok) (equal (mv-nth 3 write) (mv-nth 2 enc))
                  (equal (fn2-overlays-count 0 (mv-nth 1 write)) (1+ n))
                  (equal (fn2-overlays-fill 0 (mv-nth 1 write)) end)
                  (equal (fn2-overlay-index-off (+ b j) index)
                         (if (equal j n) off (fn2-overlay-index-off (+ b j) ix))))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-append-records-row-offset (o 0) (off (fn2-overlays-fill 0 ov))
                  (end (mv-nth 1 (fn2-run-layout-encode 3 0 *fn2-run-adapter-entry* (fn2-overlays-slot 0 ov)
                                  (fn2-overlays-gen 0 ov) (fn2-overlays-fill 0 ov) 9 0 1 f pool)))))
           :in-theory (union-theories (theory 'minimal-theory)
                  '(fn2-ov-write eq not (:t fn2-ov-place) (:t fn2-run-layout-encode) mv-nth car-cons cdr-cons
                    (:e mv-nth) (:e equal) (:e consp) (:e zp) (:e natp) (:e unary--) (:e binary-+))))))
