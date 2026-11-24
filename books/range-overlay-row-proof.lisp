; Each overlay index position selects a physical row. Decoding and
; comparing it preserves the query and the remaining index entries.
(in-package "ACL2")
(include-book "range-page-search-proof")

(defun-nx fn2-ov-indexed-row-p (o pos row eb ov ix f pool)
  (fn2-run-overview-row-atp 0 row eb (fn2-overlays-slot o ov) (fn2-overlays-gen o ov)
    (fn2-overlay-index-off (+ (fn2-overlays-ibase o ov) pos) ix) (fn2-overlays-fill o ov)
    (fn2-overlays-okind o ov) (fn2-overlays-oslot o ov) (fn2-overlays-ogen o ov) f pool))

(defun-nx fn2-ov-indexed-rows-p (n rows o eb ov ix f pool)
  (if (zp n) t
    (and (fn2-ov-indexed-row-p o (1- n) (nth (1- n) rows) eb ov ix f pool)
         (fn2-ov-indexed-rows-p (1- n) rows o eb ov ix f pool))))

(defun-nx fn2-ov-overview-reader-p (o eb qbase ov ix f)
  (and (fn2-ov-okp o ov ix) (equal (fn2-overlays-schema o ov) 3) (natp eb) (natp qbase)
       (< (1+ qbase) eb) (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
       (fn2-fieldsp f) (fn2-fields-wfp f)))

(local
 (defthm fn2-ov-indexed-position
   (implies (and (natp pos) (natp n) (< pos n) (fn2-ov-indexed-rows-p n rows o eb ov ix f pool))
            (fn2-ov-indexed-row-p o pos (nth pos rows) eb ov ix f pool))
   :hints (("Goal" :induct (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)
            :in-theory (disable fn2-ov-indexed-row-p nth)))))

(local
 (defthm fn2-ov-indexed-rows-use-capacity
   (implies (equal (fn2-fields-rows f2) (fn2-fields-rows f))
            (equal (fn2-ov-indexed-rows-p n rows o eb ov ix f2 pool) (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)
            :in-theory (e/d (fn2-ov-indexed-row-p fn2-run-overview-row-atp)
                      (fn2-run-values-layoutp fn2-layout-octets fn2-run-read-bytes fn2-layout-range-code fn2-fields-rows
                       fn2-poolp fn2-pool-wfp fn2-pool-base fn2-overlays-slot fn2-overlays-gen fn2-overlays-fill
                       fn2-overlays-ibase fn2-overlay-index-off fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen nth))))))

(local
 (defthm fn2-ov-readable-position
   (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f) (natp pos) (< pos (fn2-overlays-count o ov)))
            (and (fn2-ov-okp o ov ix) (natp o) (< o (fn2-overlays-rows ov)) (natp eb) (natp qbase)
                 (< (1+ qbase) eb) (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
                 (<= (+ qbase *fn2-run-entry-rows*) (fn2-fields-rows f))
                 (< (+ (fn2-overlays-ibase o ov) pos) (fn2-overlay-index-rows ix))
                 (equal (fn2-overlays-schema o ov) 3)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-ov-overview-reader-p fn2-ov-okp)
             (fn2-overlays-rows fn2-overlay-index-rows fn2-overlays-ibase fn2-overlays-count fn2-overlays-icap
              fn2-fields-rows fn2-overlays-schema fn2-overlays-wfp fn2-overlay-index-wfp fn2-fields-wfp fn2-fieldsp))))))

(local
 (defthm fn2-ov-reads-selected-position
   (let ((read (fn2-run-layout-decode 3 0 eb (fn2-overlays-slot o ov) (fn2-overlays-gen o ov)
              (fn2-overlay-index-off (+ (fn2-overlays-ibase o ov) pos) ix) (fn2-overlays-fill o ov)
              (fn2-overlays-okind o ov) (fn2-overlays-oslot o ov) (fn2-overlays-ogen o ov) f pool)))
     (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f) (natp pos) (< pos (fn2-overlays-count o ov)))
              (equal (fn2-ov-entry o pos eb ov ix f pool) read)))
   :rule-classes nil
   :hints (("Goal" :use fn2-ov-readable-position
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-ov-entry eq not (:e equal)))))))

(local
 (defthm fn2-ov-index-row-compares-query
   (let* ((read (fn2-ov-entry o pos eb ov ix f pool)) (rf (mv-nth 2 read))
          (ord (fn2-ov-order o pos eb qbase qk qs qg ov ix f pool)))
     (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f) (natp pos) (< pos (fn2-overlays-count o ov))
                   (fn2-ov-indexed-row-p o pos row eb ov ix f pool))
              (and (equal (car read) :ok) (equal (car ord) :ok)
                   (equal (mv-nth 1 ord) (fn2-run-key-order-spec *fn2-overview-range-key* row (fn2-overview-range-key-at qbase f)))
                   (equal (mv-nth 2 ord) rf)
                   (equal (fn2-overview-range-key-at qbase rf) (fn2-overview-range-key-at qbase f)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-ov-readable-position fn2-ov-reads-selected-position
                  (:instance fn2-run-overview-page-key-order (level 0) (base eb)
                   (slot (fn2-overlays-slot o ov)) (gen (fn2-overlays-gen o ov))
                   (off (fn2-overlay-index-off (+ (fn2-overlays-ibase o ov) pos) ix)) (end (fn2-overlays-fill o ov))
                   (pk (fn2-overlays-okind o ov)) (ps (fn2-overlays-oslot o ov)) (pg (fn2-overlays-ogen o ov)))
                  (:instance fn2-run-overview-decoded-key-pair (level 0) (base eb)
                   (slot (fn2-overlays-slot o ov)) (gen (fn2-overlays-gen o ov))
                   (off (fn2-overlay-index-off (+ (fn2-overlays-ibase o ov) pos) ix)) (end (fn2-overlays-fill o ov))
                   (pk (fn2-overlays-okind o ov)) (ps (fn2-overlays-oslot o ov)) (pg (fn2-overlays-ogen o ov))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-ov-indexed-row-p fn2-ov-order eq not mv-nth car-cons cdr-cons
                           (:e mv-nth) (:e zp) (:e equal) (:e consp) (:e unary--) (:e binary-+)))))))

(defthmd fn2-ov-search-reads-indexed-row
  (let* ((ord (fn2-ov-order o pos eb qbase qk qs qg ov ix f pool)) (rf (mv-nth 2 ord))
         (query (fn2-overview-range-key-at qbase f)))
    (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f) (natp pos) (natp n) (< pos n)
                  (<= n (fn2-overlays-count o ov)) (fn2-ov-indexed-rows-p n rows o eb ov ix f pool))
             (and (equal (car ord) :ok) (equal (mv-nth 1 ord) (fn2-run-key-order-spec *fn2-overview-range-key* (nth pos rows) query))
                  (equal (fn2-overview-range-key-at qbase rf) query)
                  (fn2-ov-overview-reader-p o eb qbase ov ix rf)
                  (fn2-ov-indexed-rows-p n rows o eb ov ix rf pool))))
  :hints (("Goal" :use ((:instance fn2-ov-index-row-compares-query (row (nth pos rows)))
                       (:instance fn2-ov-indexed-rows-use-capacity (f2 (mv-nth 2 (fn2-ov-order o pos eb qbase qk qs qg ov ix f pool)))))
           :in-theory (e/d (fn2-ov-overview-reader-p)
                     (fn2-ov-indexed-row-p fn2-ov-indexed-rows-p fn2-ov-order fn2-ov-entry fn2-ov-okp fn2-overlays-schema
                      fn2-overview-range-key-at fn2-run-key-order-spec fn2-overlays-count fn2-fields-rows fn2-fieldsp fn2-fields-wfp nth)))))

(defthmd fn2-ov-indexed-row-supplies-field
  (let ((read (fn2-ov-entry o pos eb ov ix f pool)))
    (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f) (natp pos) (natp n) (< pos n)
                  (<= n (fn2-overlays-count o ov)) (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)
                  (natp j) (< j 4))
             (and (equal (car read) :ok)
                  (equal (fn2-fields-value (+ eb j) (mv-nth 2 read)) (nth j (nth pos rows))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-ov-readable-position fn2-ov-reads-selected-position
                 (:instance fn2-ov-index-row-compares-query (row (nth pos rows)))
                 (:instance fn2-ov-indexed-position)
                 (:instance fn2-run-overview-page-row-id (level 0) (base eb) (row (nth pos rows))
                   (slot (fn2-overlays-slot o ov)) (gen (fn2-overlays-gen o ov))
                   (off (fn2-overlay-index-off (+ (fn2-overlays-ibase o ov) pos) ix)) (end (fn2-overlays-fill o ov))
                   (pk (fn2-overlays-okind o ov)) (ps (fn2-overlays-oslot o ov)) (pg (fn2-overlays-ogen o ov))))
           :in-theory (e/d (fn2-ov-indexed-row-p fn2-run-overview-row-atp)
                    (fn2-ov-indexed-position fn2-ov-indexed-rows-p fn2-ov-entry fn2-ov-order fn2-ov-overview-reader-p
                     fn2-run-layout-decode fn2-layout-octets fn2-layout-range-code fn2-run-read-bytes fn2-run-values-layoutp
                     fn2-poolp fn2-pool-wfp fn2-pool-base fn2-fields-value fn2-fields-rows fn2-overview-range-key-at
                     fn2-run-key-order-spec fn2-overlays-slot fn2-overlays-gen fn2-overlays-fill fn2-overlays-ibase
                     fn2-overlay-index-off fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen fn2-overlays-count
                     unsigned-byte-p nth)))))
