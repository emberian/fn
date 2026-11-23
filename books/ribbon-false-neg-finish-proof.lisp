(in-package "ACL2")
(include-book "ribbon-false-neg-proof")
(include-book "owed-discharge")

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(defun fn2-ribbon-query-slot-free-p (fn2-pool)
   (declare (xargs :stobjs fn2-pool :verify-guards nil))
   (and (equal (fn2-pool-nclasses fn2-pool) 1) (equal (fn2-pool-rows fn2-pool) 3)
        (equal (fn2-pool-credit-configured fn2-pool) 0)
        (equal (fn2-pool-class-countsi 0 fn2-pool) 1) (equal (fn2-pool-class-headsi 0 fn2-pool) 2)
        (equal (fn2-pool-state 2 fn2-pool) *fn2-pool-state-free*) (equal (fn2-pool-class 2 fn2-pool) 0)
        (equal (fn2-pool-out-count 2 fn2-pool) 0) (equal (fn2-pool-query-ref-count 2 fn2-pool) 0)
        (equal (fn2-pool-gen 2 fn2-pool) 1)
        (equal (fn2-pool-base 0 fn2-pool) 0) (equal (fn2-pool-base 2 fn2-pool) 131072)
        (equal (fn2-pool-cap 2 fn2-pool) 65536) (<= 196608 (fn2-pool-data-length fn2-pool))))

(defthm fn2-ribbon-octet-write-leaves-query-slot-free
   (implies (fn2-ribbon-query-slot-free-p fn2-pool)
            (fn2-ribbon-query-slot-free-p (mv-nth 1 (fn2-pool-write slot gen off byte pk ps pg fn2-pool))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-query-slot-free-p fn2-pool-write fn2-pool-set-fill
                 update-fn2-pool-fill$ai update-fn2-pool-datai fn2-pool-nclasses fn2-pool-rows fn2-pool-credit-configured fn2-pool-class-countsi fn2-pool-class-headsi fn2-pool-state fn2-pool-class fn2-pool-out-count fn2-pool-query-ref-count fn2-pool-gen fn2-pool-base fn2-pool-cap fn2-pool-data-length)
               (nth update-nth fn2-pool-workspace-code unsigned-byte-p)))))

(local
 (defthm fn2-ribbon-load-leaves-query-slot-free
   (implies (fn2-ribbon-query-slot-free-p fn2-pool) (fn2-ribbon-query-slot-free-p (mv-nth 1 (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool) :in-theory (e/d (fn2-run-load-bytes) (fn2-ribbon-query-slot-free-p fn2-pool-write fn2-ribbon-band-z))))))

(local
 (defthm fn2-ribbon-key-load-leaves-query-slot-free
   (implies (fn2-ribbon-query-slot-free-p fn2-pool)
            (fn2-ribbon-query-slot-free-p (mv-nth 3 (fn2-ribbon-key-load bytes 300 slot gen off))))
   :hints (("Goal" :in-theory (e/d (fn2-run-load-values fn2-run-load-ref) (fn2-run-load-bytes fn2-ribbon-query-slot-free-p))))))

; The generated emitter for each scalar field writes the corresponding layout octets.
(local
 (defun fn2-ribbon-write-header-octets (bytes slot gen next fn2-pool)
   (declare (xargs :stobjs fn2-pool :verify-guards nil))
   (if (atom bytes) (mv :ok next fn2-pool)
     (mv-let (code fn2-pool) (fn2-pool-write slot gen next (car bytes) 9 0 1 fn2-pool)
       (if (eq code :ok) (fn2-ribbon-write-header-octets (cdr bytes) slot gen (1+ next) fn2-pool)
         (mv code next fn2-pool))))))

(local
 (defthm fn2-ribbon-fixed-emitter-octets
   (implies (natp v)
            (equal (fn2-codec-emit-fixed n v slot gen next 9 0 1 fn2-pool)
                   (fn2-ribbon-write-header-octets (fn2-layout-le n v) slot gen next fn2-pool)))
   :hints (("Goal" :induct (fn2-codec-emit-fixed n v slot gen next 9 0 1 fn2-pool)
            :expand (fn2-layout-le n v) :in-theory (e/d (fn2-codec-emit-fixed fn2-layout-le) (fn2-pool-write))))))

(local
 (defthm fn2-ribbon-varint-emitter-octets
   (implies (natp v)
            (equal (fn2-codec-emit-varint v slot gen next 9 0 1 fn2-pool)
                   (fn2-ribbon-write-header-octets (fn2-layout-varoctets v) slot gen next fn2-pool)))
   :hints (("Goal" :induct (fn2-codec-emit-varint v slot gen next 9 0 1 fn2-pool)
            :in-theory (e/d (fn2-codec-emit-varint fn2-layout-varoctets) (fn2-pool-write))))))

(local
 (defthm fn2-ribbon-write-header-append
   (let ((prefix (fn2-ribbon-write-header-octets a slot gen next fn2-pool)))
     (equal (fn2-ribbon-write-header-octets (append a b) slot gen next fn2-pool)
            (if (eq (mv-nth 0 prefix) :ok)
                (fn2-ribbon-write-header-octets b slot gen (mv-nth 1 prefix) (mv-nth 2 prefix))
              prefix)))
   :hints (("Goal" :induct (fn2-ribbon-write-header-octets a slot gen next fn2-pool)
            :in-theory (disable fn2-pool-write)))))

(local
 (defthm fn2-ribbon-write-header-in-arena
   (let* ((wr (fn2-ribbon-write-header-octets bytes slot gen off fn2-pool))
          (loaded (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)))
     (implies (and (natp off) (<= (+ off (len bytes)) cap) (fn2-ribbon-bytesp bytes)
                   (fn2-ribbon-arena-p slot gen 9 0 1 off cap fn2-pool))
              (equal wr (list :ok (+ off (len bytes)) (mv-nth 1 loaded)))))
   :hints (("Goal" :induct (fn2-ribbon-write-header-octets bytes slot gen off fn2-pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-ribbon-arena-p fn2-pool-write unsigned-byte-p)))
           ("Subgoal *1/3" :use ((:instance fn2-ribbon-arena-write-progress (pk 9) (ps 0) (pg 1) (v (car bytes)))))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-arena-write-progress (pk 9) (ps 0) (pg 1) (v (car bytes))))))))

(local
 (defthm fn2-ribbon-written-octets-next
   (let ((wr (fn2-ribbon-write-header-octets bytes slot gen next fn2-pool)))
     (implies (and (natp next) (equal (mv-nth 0 wr) :ok))
              (equal (mv-nth 1 wr) (+ next (len bytes)))))
   :hints (("Goal" :induct (fn2-ribbon-write-header-octets bytes slot gen next fn2-pool)
            :in-theory (disable fn2-pool-write)))))

(local
 (defthm fn2-ribbon-written-octets-triple
   (let ((wr (fn2-ribbon-write-header-octets bytes slot gen off fn2-pool)))
     (equal (list (mv-nth 0 wr) (mv-nth 1 wr) (mv-nth 2 wr)) wr))
   :hints (("Goal" :induct (fn2-ribbon-write-header-octets bytes slot gen off fn2-pool)
            :in-theory (disable fn2-pool-write)))))

(local
 (defthm fn2-ribbon-len-le
   (equal (len (fn2-layout-le n v)) (nfix n))
   :hints (("Goal" :induct (fn2-layout-le n v) :in-theory (enable fn2-layout-le)))))

(local
 (defthm fn2-ribbon-varint-next-size
   (implies (natp v) (equal (len (fn2-layout-varoctets v)) (fn2-layout-varsize v)))
   :hints (("Goal" :induct (fn2-layout-varoctets v)
            :in-theory (enable fn2-layout-varoctets fn2-layout-varsize)))))

(local
 (defthm fn2-ribbon-pack-write-result
   (let ((wr (fn2-ribbon-write-header-octets bytes slot gen off fn2-pool)))
     (implies (and (equal code (mv-nth 0 wr)) (equal next (mv-nth 1 wr)))
              (equal (list code next (mv-nth 2 wr)) wr)))
   :hints (("Goal" :use fn2-ribbon-written-octets-triple
            :in-theory (disable fn2-ribbon-written-octets-triple fn2-ribbon-write-header-octets)))))

(local
 (defun fn2-ribbon-emit-field-terms (layout i)
   (if (atom layout) nil
     (cons `(fn2-fields-value (+ base ,i) fn2-fields)
           (fn2-ribbon-emit-field-terms (cdr layout) (1+ i))))))

(local
 (defun fn2-ribbon-emit-field-hyps (layout terms)
   (if (atom layout) nil
     (cons (if (equal (fn2-layout-kind-code (cadar layout)) 9)
               `(unsigned-byte-p 8 ,(car terms))
             `(natp ,(car terms)))
           (fn2-ribbon-emit-field-hyps (cdr layout) (cdr terms))))))

(local
 (defun fn2-ribbon-emitter-lemmas (name layout i fixed)
   (declare (xargs :verify-guards nil))
   (if (atom layout) nil
     (let* ((step (fn2-codec-emitter-name name (caar layout)))
            (terms (fn2-ribbon-emit-field-terms layout i))
            (bytes `(fn2-layout-octets ',layout (list ,@terms)))
            (width (fn2-layout-width (cadar layout))))
       (append (fn2-ribbon-emitter-lemmas name (cdr layout) (1+ i) (and fixed width (+ fixed width)))
         (list
           `(defthm ,(fn2-codec-symbol step "-WRITES-OCTETS")
              (implies (and (natp base) (natp off) (natp next) ,@(fn2-ribbon-emit-field-hyps layout terms))
                       (equal (,step base slot gen off next 9 0 1 fn2-fields fn2-pool)
                              (fn2-ribbon-write-header-octets ,bytes slot gen ,(if fixed `(+ off ,fixed) 'next) fn2-pool)))
              :hints (("Goal" :use ((:instance fn2-ribbon-written-octets-triple
                                 (bytes ,(if width `(fn2-layout-le ,width ,(car terms))
                                                   `(fn2-layout-varoctets ,(car terms))))
                                 (off ,(if fixed `(+ off ,fixed) 'next))))
                       :expand ((:free (values) (fn2-layout-octets ',layout values)))
                       :in-theory (e/d (,step fn2-layout-field-octets)
                          (fn2-layout-le fn2-layout-varoctets fn2-layout-octets fn2-ribbon-write-header-octets
                           fn2-ribbon-write-header-in-arena fn2-codec-emit-fixed fn2-codec-emit-varint
                           fn2-pool-write fn2-fields-value nth binary-append)))))))))))

(local (make-event (cons 'progn (fn2-ribbon-emitter-lemmas 'fn2-ribbon-header *fn2-ribbon-header* 0 0))))

(local
 (defthm fn2-ribbon-one-octet-le
   (implies (unsigned-byte-p 8 v) (equal (fn2-layout-le 1 v) (list v)))
   :hints (("Goal" :in-theory (enable fn2-layout-le)))))

(local (make-event (cons 'progn (fn2-ribbon-emitter-lemmas 'fn2-format-page-header *fn2-format-page-header* 0 0))))

(defthm fn2-ribbon-complete-page-range
   (implies (and (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)
                 (natp start) (natp end) (<= start end) (<= end 65536))
            (equal (fn2-layout-range-code slot gen start end writep 9 0 1 fn2-pool) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-arena-p fn2-layout-range-code fn2-pool-workspace-code
                        fn2-pool-readable-code fn2-pool-slot-base fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-capacity-bytes)
                        (nth update-nth fn2-pool-handle-code fn2-pool-ownerp)))))

(local
 (defun fn2-ribbon-scalar-size (layout vals)
   (if (atom layout) 0
     (+ (or (fn2-layout-width (cadar layout)) (fn2-layout-varsize (car vals)))
        (fn2-ribbon-scalar-size (cdr layout) (cdr vals))))))

(local
 (defun fn2-ribbon-header-sizes-p (n)
   (let* ((b (fn2-ribbon-page-values n)) (c (fn2-ribbon-filter-values n))
          (bb (fn2-layout-octets *fn2-format-page-header* b)) (cb (fn2-layout-octets *fn2-ribbon-header* c)))
     (and (fn2-ribbon-bytesp bb) (fn2-ribbon-bytesp cb)
          (equal (fn2-ribbon-scalar-size *fn2-format-page-header* b) (len bb))
          (equal (fn2-ribbon-scalar-size *fn2-ribbon-header* c) (len cb))
          (<= (len bb) *fn2-run-header-area*) (<= (+ *fn2-run-header-area* (len cb)) *fn2-ribbon-base*)))))

(local
 (defun fn2-ribbon-sizes-through (limit)
   (if (zp limit) t
     (and (fn2-ribbon-header-sizes-p limit) (fn2-ribbon-sizes-through (1- limit))))))

(local
 (defthm fn2-ribbon-sizes-at-key-count
   (implies (and (fn2-ribbon-sizes-through limit) (posp n) (natp limit) (<= n limit))
            (fn2-ribbon-header-sizes-p n))
   :hints (("Goal" :induct (fn2-ribbon-row-induct limit) :in-theory (disable fn2-ribbon-header-sizes-p)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-header-sizes-for-admitted-key-counts
   (implies (and (posp n) (<= n 256)) (fn2-ribbon-header-sizes-p n))
   :hints (("Goal" :use ((:instance fn2-ribbon-sizes-at-key-count (limit 256)))
            :in-theory (disable fn2-ribbon-header-sizes-p fn2-ribbon-sizes-through)))
   :rule-classes nil))

(local
 (defun fn2-ribbon-encoder-definitions (name layout)
   (if (atom layout) nil
     (list* (fn2-codec-sizer-name name (caar layout)) (fn2-codec-checker-name name (caar layout))
            (fn2-ribbon-encoder-definitions name (cdr layout))))))

(local
 (defun fn2-ribbon-field-equalities (terms i vals)
   (if (atom terms) nil
     (cons `(equal ,(car terms) (nth ,i ,vals))
           (fn2-ribbon-field-equalities (cdr terms) (1+ i) vals)))))

(local
 (defun fn2-ribbon-encoder-event (name layout vals off)
   (let* ((encode (fn2-codec-symbol name "-ENCODE")) (bytes `(fn2-layout-octets ',layout (,vals n))))
     `(defthm ,(fn2-codec-symbol name "-SERIALIZES-RIBBON-HEADER")
        (implies (and (posp n) (<= n 256) (natp base)
                      (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)
                      ,@(fn2-ribbon-field-equalities (fn2-ribbon-emit-field-terms layout 0) 0 `(,vals n)))
                 (equal (,encode base slot gen ,off 9 0 1 fn2-fields fn2-pool)
                        (list :ok (+ ,off (len ,bytes))
                              (mv-nth 1 (fn2-run-load-bytes ,bytes slot gen ,off 9 0 1 fn2-pool)))))
        :hints (("Goal"
                 :use (fn2-ribbon-header-sizes-for-admitted-key-counts
                       (:instance fn2-ribbon-arena-rewind (pk 9) (ps 0) (pg 1) (off 65536) (new ,off) (cap 65536))
                       (:instance fn2-ribbon-write-header-in-arena (off ,off) (bytes ,bytes) (cap 65536)))
                 :in-theory (e/d (,encode ,(fn2-codec-symbol name "-SIZE") ,(fn2-codec-symbol name "-CHECK-VALUES")
                                  ,@(fn2-ribbon-encoder-definitions name layout))
                                 (fn2-ribbon-arena-p fn2-fields-value fn2-ribbon-slots fn2-layout-range-code
                                  fn2-layout-octets fn2-ribbon-bytesp fn2-layout-varsize fn2-run-load-bytes
                                  fn2-ribbon-write-header-octets fn2-ribbon-write-header-in-arena))))
        :rule-classes nil))))

(local (make-event (fn2-ribbon-encoder-event 'fn2-ribbon-header *fn2-ribbon-header* 'fn2-ribbon-filter-values *fn2-run-header-area*)))

(local (make-event (fn2-ribbon-encoder-event 'fn2-format-page-header *fn2-format-page-header* 'fn2-ribbon-page-values 0)))

(local
 (defthm fn2-ribbon-overwrite-in-full-page
   (let ((wr (fn2-pool-write slot gen off byte 9 0 1 fn2-pool)))
     (implies (and (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)
                   (natp off) (< off 65536) (unsigned-byte-p 8 byte))
              (and (equal (mv-nth 0 wr) :ok)
                   (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 (mv-nth 1 wr)))))
   :hints (("Goal" :in-theory (e/d (fn2-pool-write fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp
                            fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai)
                          (nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-ribbon-overwrite-header-in-full-page
   (let ((wr (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)))
     (implies (and (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)
                   (natp off) (<= (+ off (len bytes)) 65536) (fn2-ribbon-bytesp bytes))
              (and (equal (mv-nth 0 wr) :ok)
                   (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 (mv-nth 1 wr)))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-write fn2-ribbon-arena-p unsigned-byte-p))))))

(local
 (defthm fn2-ribbon-read-beyond-header-write
   (let ((wr (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool))
         (before (fn2-pool-read slot gen i 9 0 1 fn2-pool)))
     (implies (and (natp (fn2-pool-base slot fn2-pool)) (natp off) (natp i)
                   (or (< i off) (<= (+ off (len bytes)) i)) (equal (mv-nth 0 before) :ok)
                   (equal (mv-nth 0 wr) :ok))
              (equal (fn2-pool-read slot gen i 9 0 1 (mv-nth 1 wr)) before)))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-write fn2-pool-read fn2-pool-base))))))

(local
 (defthm fn2-ribbon-bytes-before-header-write
   (let ((wr (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)))
     (implies (and (natp (fn2-pool-base slot fn2-pool)) (natp off) (natp start)
                   (<= (+ start (len prior)) off) (equal (mv-nth 0 wr) :ok)
                   (fn2-ribbon-bytes-at-p prior slot gen start 9 0 1 fn2-pool))
              (fn2-ribbon-bytes-at-p prior slot gen start 9 0 1 (mv-nth 1 wr))))
   :hints (("Goal" :induct (fn2-ribbon-bytes-at-p prior slot gen start 9 0 1 fn2-pool)
            :in-theory (disable fn2-run-load-bytes fn2-pool-read fn2-pool-base)))))

(local
 (defthm fn2-ribbon-header-write-keeps-solution
   (let ((wr (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)))
     (implies (and (fn2-ribbon-solution-page-p n slot gen fn2-ribbon-band fn2-pool)
                   (natp (fn2-pool-base slot fn2-pool)) (natp off) (<= (+ off (len bytes)) *fn2-ribbon-base*)
                   (equal (mv-nth 0 wr) :ok))
              (fn2-ribbon-solution-page-p n slot gen fn2-ribbon-band (mv-nth 1 wr))))
   :hints (("Goal" :induct (fn2-ribbon-row-induct n)
            :in-theory (disable fn2-pool-read fn2-pool-base fn2-ribbon-band-z fn2-run-load-bytes unsigned-byte-p)))))

(local
 (defthm fn2-ribbon-header-at-offset
   (let ((after (mv-nth 1 (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool))))
     (implies (and (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)
                   (fn2-ribbon-bytesp bytes) (natp off) (<= (+ off (len bytes)) 65536))
              (fn2-ribbon-bytes-at-p bytes slot gen off 9 0 1 after)))
   :hints (("Goal" :use ((:instance fn2-ribbon-loaded-prefix-matches (n 0) (pk 9) (ps 0) (pg 1))
                         (:instance fn2-ribbon-arena-base-natural (pk 9) (ps 0) (pg 1) (off 65536) (cap 65536)))
            :in-theory (disable fn2-run-load-bytes fn2-ribbon-arena-p fn2-ribbon-bytes-at-p fn2-ribbon-bytesp fn2-pool-base)))))

; Padding writes extend a readable zero region. The checker's raw span scan accepts each subrange.
(defun fn2-ribbon-zero-region-p (count start slot gen fn2-pool)
   (declare (xargs :stobjs fn2-pool :measure (nfix count) :verify-guards nil))
   (if (zp count) t
     (mv-let (code byte) (fn2-pool-read slot gen start 9 0 1 fn2-pool)
       (and (equal code :ok) (equal byte 0)
          (fn2-ribbon-zero-region-p (1- count) (1+ start) slot gen fn2-pool)))))

(local
 (defun fn2-ribbon-padding-induct (count start)
   (declare (xargs :measure (nfix count)))
   (if (zp count) start (fn2-ribbon-padding-induct (1- count) (1+ start)))))

(defthm fn2-ribbon-headers-preserve-padding
   (let ((wr (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)))
     (implies (and (fn2-ribbon-zero-region-p count start slot gen fn2-pool)
                   (natp (fn2-pool-base slot fn2-pool)) (natp start) (natp off) (<= (+ off (len bytes)) start)
                   (equal (mv-nth 0 wr) :ok))
              (fn2-ribbon-zero-region-p count start slot gen (mv-nth 1 wr))))
   :hints (("Goal" :induct (fn2-ribbon-padding-induct count start)
            :in-theory (disable fn2-pool-read fn2-run-load-bytes fn2-pool-base))))

(local
 (defthm fn2-ribbon-two-headers-on-solution
   (let* ((b (fn2-layout-octets *fn2-format-page-header* (fn2-ribbon-page-values n)))
          (c (fn2-layout-octets *fn2-ribbon-header* (fn2-ribbon-filter-values n)))
          (p (mv-nth 1 (fn2-run-load-bytes b slot gen 0 9 0 1 fn2-pool)))
          (after (mv-nth 1 (fn2-run-load-bytes c slot gen *fn2-run-header-area* 9 0 1 p))))
     (implies (and (posp n) (<= n 256) (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)
                   (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band fn2-pool))
              (and (fn2-ribbon-physical-headers-p n slot gen after)
                   (implies (and (natp start) (<= *fn2-ribbon-base* start)
                                 (fn2-ribbon-zero-region-p count start slot gen fn2-pool))
                            (fn2-ribbon-zero-region-p count start slot gen after))
                   (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band after)
                   (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 after))))
   :hints (("Goal" :use (fn2-ribbon-header-sizes-for-admitted-key-counts
                         (:instance fn2-ribbon-arena-base-natural (pk 9) (ps 0) (pg 1) (off 65536) (cap 65536)))
            :in-theory (disable fn2-layout-range-code fn2-layout-octets fn2-ribbon-page-values fn2-ribbon-filter-values
                  fn2-ribbon-scalar-size fn2-ribbon-bytesp fn2-ribbon-bytes-at-p fn2-ribbon-arena-p
                  fn2-ribbon-zero-region-p fn2-ribbon-solution-page-p fn2-run-load-bytes fn2-pool-base)))
   :rule-classes nil))

; The seal records the computed digest. The independent check compares all 32 bytes.
(local
 (defmacro fn2-ribbon-page-call (op prefix sealp)
   (append (list op) prefix (list 0 :page sealp)
           '(slot gen 0 *fn2-run-page-size* 0 9 0 1)
           '(fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))

(local
 (defthm fn2-ribbon-matching-digest-byte
   (implies (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) (fn2-fc-context-hash 0 fn2-fc-context) fn2-digests)
            (equal (fn2-fc-digest-byte 0 i fn2-fc fn2-digests)
                   (fn2-fc-word-byte (fn2-fc-context-hash-word 0 (floor i 4) fn2-fc-context fn2-digests) (mod i 4))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-digest-byte fn2-fc-context-hash-word fn2-digest-equal fn2-digest-word)
                       (nth floor mod fn2-fc-word-byte fn2-fc-context-hash))))))

(local
 (defthm fn2-ribbon-compare-page-hash-byte
   (let ((pos (fn2-fc-pos 0 fn2-fc)) (step (fn2-ribbon-page-call fn2-fc-advance (fuel) nil)))
     (implies (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                   (natp pos) (< pos 32)
                   (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) (fn2-fc-context-hash 0 fn2-fc-context) fn2-digests))
              (equal step (list (if (equal pos 31) :ok :more) 1 (fn2-fc-set-pos 0 (+ 1 pos) fn2-fc)
                                fn2-b3 fn2-pool fn2-digests))))
   :hints (("Goal" :use ((:instance fn2-ribbon-matching-digest-byte (i (fn2-fc-pos 0 fn2-fc)))) :in-theory (e/d (fn2-fc-advance fn2-fc-byte)
                       (fn2-ribbon-matching-digest-byte nth fn2-fc-phase fn2-fc-pos fn2-fc-set-pos fn2-fc-context-hash fn2-digest-equal
                        fn2-fc-word-byte fn2-fc-context-hash-word fn2-fc-digest-byte fn2-fc-page-span))))))

(local
 (defthm fn2-ribbon-fc-position-update
   (and (equal (fn2-fc-pos 0 (fn2-fc-set-pos 0 i fn2-fc)) i)
        (equal (fn2-fc-phase 0 (fn2-fc-set-pos 0 i fn2-fc)) (fn2-fc-phase 0 fn2-fc)))
   :hints (("Goal" :in-theory (e/d (fn2-fc-pos fn2-fc-phase fn2-fc-set-pos update-fn2-fc-pos$ai)
                                   (nth update-nth))))))

(local
 (defun fn2-ribbon-digest-induct (fuel fn2-fc)
   (declare (xargs :stobjs fn2-fc :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) fn2-fc
     (let ((fn2-fc (fn2-fc-set-pos 0 (1+ (fn2-fc-pos 0 fn2-fc)) fn2-fc)))
       (fn2-ribbon-digest-induct (1- fuel) fn2-fc)))))

(local
 (defthm fn2-ribbon-page-check-matching-digest
   (let ((pos (fn2-fc-pos 0 fn2-fc)) (run (fn2-ribbon-page-call fn2-fc-run-bytes (fuel) nil)))
     (implies (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                   (natp pos) (< pos 32) (natp fuel) (<= (- 32 pos) fuel)
                   (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) (fn2-fc-context-hash 0 fn2-fc-context) fn2-digests))
              (and (equal (mv-nth 0 run) :ok) (equal (mv-nth 2 run) fn2-b3)
                   (equal (mv-nth 3 run) fn2-pool) (equal (mv-nth 4 run) fn2-digests))))
   :hints (("Goal" :induct (fn2-ribbon-digest-induct fuel fn2-fc)
            :expand ((fn2-ribbon-page-call fn2-fc-run-bytes (fuel) nil))
            :in-theory (disable nth fn2-fc-run-bytes fn2-fc-advance fn2-fc-set-pos fn2-fc-phase fn2-fc-pos
                                fn2-digest-equal fn2-fc-context-hash)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-seal-copies-computed-digest
   (implies (and (natp dest) (not (equal dest (fn2-digest-slot 0 *fn2-fc-result*))))
            (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) dest
              (fn2-digest-copy dest (fn2-digest-slot 0 *fn2-fc-result*) fn2-digests)))
   :hints (("Goal" :in-theory (e/d (fn2-digest-equal fn2-digest-copy
                            fn2-digests-w0 fn2-digests-set-w0 update-fn2-digests-w0$ai fn2-digests-w1 fn2-digests-set-w1 update-fn2-digests-w1$ai fn2-digests-w2 fn2-digests-set-w2 update-fn2-digests-w2$ai fn2-digests-w3 fn2-digests-set-w3 update-fn2-digests-w3$ai fn2-digests-w4 fn2-digests-set-w4 update-fn2-digests-w4$ai fn2-digests-w5 fn2-digests-set-w5 update-fn2-digests-w5$ai fn2-digests-w6 fn2-digests-set-w6 update-fn2-digests-w6$ai fn2-digests-w7 fn2-digests-set-w7 update-fn2-digests-w7$ai )
                           (nth update-nth))))))

(local
 (defthm fn2-ribbon-finish-sealer-digest
   (let ((run (fn2-ribbon-page-call fn2-fc-run-bytes (fuel) t)))
     (implies (and (posp fuel) (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                   (equal (fn2-fc-context-hash 0 fn2-fc-context) 136))
              (and (equal (mv-nth 0 run) :ok)
                   (equal (mv-nth 1 run) fn2-fc) (equal (mv-nth 2 run) fn2-b3) (equal (mv-nth 3 run) fn2-pool)
                   (equal (mv-nth 4 run) (fn2-digest-copy 136 (fn2-digest-slot 0 *fn2-fc-result*) fn2-digests))
                   (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) 136 (mv-nth 4 run)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-seal-copies-computed-digest (dest 136))) :expand ((fn2-ribbon-page-call fn2-fc-run-bytes (fuel) t))
            :in-theory (e/d (fn2-fc-advance fn2-fc-byte)
                         (nth fn2-fc-phase fn2-fc-context-hash fn2-fc-pos fn2-digest-copy fn2-digest-equal))))
   :rule-classes nil))

(defthm fn2-ribbon-check-returns-ok-after-hash
   (let ((pos (fn2-fc-pos 0 fn2-fc)))
     (implies (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                   (natp pos) (< pos 32)
                   (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) (fn2-fc-context-hash 0 fn2-fc-context) fn2-digests))
              (equal (mv-nth 0 (fn2-rba-call fn2-rba-check slot gen)) :ok)))
   :hints (("Goal" :use ((:instance fn2-ribbon-page-check-matching-digest (fuel 4096)))
            :expand ((:free (ticks) (fn2-format-drive ticks 0 :page nil slot gen 0
                           *fn2-run-page-size* 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
            :in-theory (e/d (fn2-rba-check fn2-format-run fn2-fc-step)
                         (fn2-format-drive fn2-fc-phase fn2-fc-pos fn2-fc-run-bytes fn2-digest-equal fn2-fc-context-hash))))
   :rule-classes nil)

; The real heading phase writes both headers and installs the writer's seal context.
(local
 (defun fn2-ribbon-put-values (vals base fn2-fields)
   (declare (xargs :stobjs fn2-fields :verify-guards nil))
   (if (atom vals) fn2-fields
     (let ((fn2-fields (fn2-fields-set-value base (car vals) fn2-fields)))
       (fn2-ribbon-put-values (cdr vals) (1+ base) fn2-fields)))))

(local
 (defthm fn2-ribbon-read-set-field
   (implies (and (natp i) (natp j))
            (equal (fn2-fields-value i (fn2-fields-set-value j val fn2-fields))
                   (if (equal i j) val (fn2-fields-value i fn2-fields))))
   :hints (("Goal" :in-theory (e/d (fn2-fields-set-value fn2-fields-value update-fn2-fields-value$ai)
                                   (nth update-nth))))))

(defun fn2-ribbon-writer-identity-p (slot gen fn2-run-writers)
   (declare (xargs :stobjs fn2-run-writers :verify-guards nil))
   (and (< 0 (fn2-run-writers-rows fn2-run-writers))
        (equal (fn2-run-writers-slot 0 fn2-run-writers) slot)
        (equal (fn2-run-writers-gen 0 fn2-run-writers) gen)
        (equal (fn2-run-writers-okind 0 fn2-run-writers) 9)
        (equal (fn2-run-writers-oslot 0 fn2-run-writers) 0)
        (equal (fn2-run-writers-ogen 0 fn2-run-writers) 1)
        (equal (fn2-run-writers-fields 0 fn2-run-writers) 0)
        (equal (fn2-run-writers-page-kind 0 fn2-run-writers) *page-kind-partitioned-filter*)
        (equal (fn2-run-writers-schema 0 fn2-run-writers) 1)
        (equal (fn2-run-writers-run 0 fn2-run-writers) 7)
        (equal (fn2-run-writers-unit 0 fn2-run-writers) 5)
        (equal (fn2-run-writers-epoch 0 fn2-run-writers) 2)
        (equal (fn2-run-writers-counter 0 fn2-run-writers) 3)
        (equal (fn2-run-writers-history 0 fn2-run-writers) 1)
        (equal (fn2-run-writers-incarnation 0 fn2-run-writers) 1)
        (equal (fn2-run-writers-restarts 0 fn2-run-writers) 0)))

(local
 (defthm fn2-ribbon-adapter-page-header
   (let* ((bytes (fn2-layout-octets *fn2-format-page-header* (fn2-ribbon-page-values n)))
          (result (fn2-run-head-b 0 0 fn2-run-writers fn2-fields fn2-pool)))
     (implies (and (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
                   (equal (fn2-run-writers-cursor 0 fn2-run-writers) (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))
                   (posp n) (<= n 256) (< 301 (fn2-fields-rows fn2-fields))
                   (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool))
              (and (equal (mv-nth 0 result) :ok)
                   (equal (mv-nth 1 result) (fn2-ribbon-put-values (fn2-ribbon-page-values n) 0 fn2-fields))
                   (equal (fn2-fields-rows (mv-nth 1 result)) (fn2-fields-rows fn2-fields))
                   (equal (mv-nth 2 result) (mv-nth 1 (fn2-run-load-bytes bytes slot gen 0 9 0 1 fn2-pool)))
                   (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 (mv-nth 2 result)))))
   :hints (("Goal" :use (fn2-ribbon-header-sizes-for-admitted-key-counts
                         (:instance fn2-format-page-header-serializes-ribbon-header (base 0)
                           (fn2-fields (fn2-ribbon-put-values (fn2-ribbon-page-values n) 0 fn2-fields))))
            :do-not '(preprocess) :in-theory (e/d (fn2-run-head-b fn2-run-payload-length fn2-ribbon-put-values)
                         (fn2-run-writers-rows fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-page-kind fn2-run-writers-schema fn2-run-writers-run fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-restarts fn2-ribbon-builds-rows fn2-ribbon-builds-keys fn2-ribbon-builds-schema fn2-ribbon-builds-run fn2-ribbon-builds-seed fn2-ribbon-builds-slots fn2-ribbon-builds-base fn2-ribbon-builds-w fn2-ribbon-builds-crow fn2-ribbon-builds-hrow fn2-run-writers-cursor nth fn2-fields-rows fn2-fields-value fn2-fields-set-value fn2-format-page-header-encode
                          fn2-run-load-bytes fn2-layout-octets fn2-ribbon-scalar-size fn2-ribbon-bytesp
                          fn2-ribbon-arena-p fn2-ribbon-slots))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-write-filter-header
   (let* ((vals (fn2-ribbon-filter-values n)) (fields (fn2-ribbon-put-values vals 10 fn2-fields))
          (bytes (fn2-layout-octets *fn2-ribbon-header* vals)))
     (implies (and (posp n) (<= n 256) (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool))
              (equal (fn2-ribbon-header-encode 10 slot gen *fn2-run-header-area* 9 0 1 fields fn2-pool)
                     (list :ok (+ *fn2-run-header-area* (len bytes))
                           (mv-nth 1 (fn2-run-load-bytes bytes slot gen *fn2-run-header-area* 9 0 1 fn2-pool))))))
   :hints (("Goal" :use ((:instance fn2-ribbon-header-serializes-ribbon-header (base 10)
                           (fn2-fields (fn2-ribbon-put-values (fn2-ribbon-filter-values n) 10 fn2-fields))))
            :in-theory (disable fn2-fields-value fn2-fields-set-value fn2-ribbon-header-encode fn2-layout-octets
                                fn2-run-load-bytes fn2-ribbon-arena-p fn2-ribbon-slots)))
   :rule-classes nil))

(defun fn2-ribbon-build-identity-p (n fn2-ribbon-builds)
   (declare (xargs :stobjs fn2-ribbon-builds :verify-guards nil))
   (and (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
        (equal (fn2-ribbon-builds-keys 0 fn2-ribbon-builds) n)
        (equal (fn2-ribbon-builds-schema 0 fn2-ribbon-builds) 1)
        (equal (fn2-ribbon-builds-run 0 fn2-ribbon-builds) 7)
        (equal (fn2-ribbon-builds-seed 0 fn2-ribbon-builds) (fn2-ribbon-seed 7))
        (equal (fn2-ribbon-builds-slots 0 fn2-ribbon-builds) (fn2-ribbon-slots n))
        (equal (fn2-ribbon-builds-base 0 fn2-ribbon-builds) 0)
        (equal (fn2-ribbon-builds-w 0 fn2-ribbon-builds) 0)
        (equal (fn2-ribbon-builds-crow 0 fn2-ribbon-builds) 0)
        (equal (fn2-ribbon-builds-hrow 0 fn2-ribbon-builds) 136)))

(local
 (defun-nx fn2-ribbon-header-stage (n slot gen builds writers fields pool context)
   (let* ((b (fn2-run-head-b 0 0 writers fields pool))
          (fields (fn2-ribbon-put-values (fn2-ribbon-filter-values n) 10 (mv-nth 1 b)))
          (c (fn2-ribbon-header-encode 10 slot gen *fn2-run-header-area* 9 0 1 fields (mv-nth 2 b)))
          (sealed-writer (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-sealing* writers)))
     (cond ((not (equal (mv-nth 0 b) :ok)) (list (mv-nth 0 b) builds writers (mv-nth 1 b) (mv-nth 2 b) context))
           ((not (equal (mv-nth 0 c) :ok)) (list (mv-nth 0 c) builds writers fields (mv-nth 2 c) context))
           (t (list :more (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-sealing* builds)
                    sealed-writer fields (mv-nth 2 c) (fn2-run-seal-context 0 0 136 sealed-writer context)))))))

(local
 (defthm fn2-ribbon-heading-phase-result
   (implies (and (fn2-ribbon-build-identity-p n fn2-ribbon-builds) (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
                 (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-heading*)
                 (< 0 (fn2-fc-context-rows fn2-fc-context)) (< 301 (fn2-fields-rows fn2-fields)))
            (equal (fn2-ribbon-head 0 fn2-ribbon-builds fn2-run-writers fn2-fields fn2-pool fn2-fc-context)
                   (fn2-ribbon-header-stage n slot gen fn2-ribbon-builds fn2-run-writers fn2-fields fn2-pool fn2-fc-context)))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-head)
                        (fn2-run-writers-rows fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-page-kind fn2-run-writers-schema fn2-run-writers-run fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-restarts fn2-ribbon-builds-rows fn2-ribbon-builds-keys fn2-ribbon-builds-schema fn2-ribbon-builds-run fn2-ribbon-builds-seed fn2-ribbon-builds-slots fn2-ribbon-builds-base fn2-ribbon-builds-w fn2-ribbon-builds-crow fn2-ribbon-builds-hrow nth fn2-fields-rows fn2-fields-set-value fn2-run-seal-context fn2-run-head-b
                        fn2-run-writers-phase fn2-ribbon-builds-set-phase fn2-run-writers-set-phase fn2-ribbon-header-encode fn2-ribbon-slots))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-put-values-rows
   (equal (fn2-fields-rows (fn2-ribbon-put-values vals base fn2-fields)) (fn2-fields-rows fn2-fields))
   :hints (("Goal" :induct (fn2-ribbon-put-values vals base fn2-fields)
                :in-theory (e/d (fn2-ribbon-put-values) (fn2-fields-rows fn2-fields-set-value))))))

(defthm fn2-ribbon-heading-establishes-serialized-solution
   (let* ((step (fn2-ribbon-head 0 fn2-ribbon-builds fn2-run-writers fn2-fields fn2-pool fn2-fc-context))
          (writer (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-sealing* fn2-run-writers))
          (after (mv-nth 4 step)))
     (implies (and (fn2-ribbon-build-identity-p n fn2-ribbon-builds) (posp n) (<= n 256)
                   (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
                   (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-heading*)
                   (equal (fn2-run-writers-cursor 0 fn2-run-writers) (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))
                   (< 0 (fn2-fc-context-rows fn2-fc-context)) (< 301 (fn2-fields-rows fn2-fields))
                   (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)
                   (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band fn2-pool))
              (and (equal (mv-nth 0 step) :more)
                   (equal after
                     (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-ribbon-header* (fn2-ribbon-filter-values n))
                       slot gen *fn2-run-header-area* 9 0 1
                       (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-format-page-header* (fn2-ribbon-page-values n))
                          slot gen 0 9 0 1 fn2-pool)))))
                   (equal (mv-nth 1 step) (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-sealing* fn2-ribbon-builds))
                   (equal (mv-nth 2 step) writer)
                   (equal (mv-nth 5 step) (fn2-run-seal-context 0 0 136 writer fn2-fc-context))
                   (equal (fn2-fields-rows (mv-nth 3 step)) (fn2-fields-rows fn2-fields))
                   (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 after)
                   (fn2-ribbon-physical-headers-p n slot gen after)
                   (implies (and (natp start) (<= *fn2-ribbon-base* start)
                                 (fn2-ribbon-zero-region-p count start slot gen fn2-pool))
                            (fn2-ribbon-zero-region-p count start slot gen after))
                   (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band after))))
   :hints (("Goal" :use (fn2-ribbon-heading-phase-result fn2-ribbon-adapter-page-header fn2-ribbon-two-headers-on-solution
                         (:instance fn2-ribbon-write-filter-header
                           (fn2-fields (mv-nth 1 (fn2-run-head-b 0 0 fn2-run-writers fn2-fields fn2-pool)))
                           (fn2-pool (mv-nth 2 (fn2-run-head-b 0 0 fn2-run-writers fn2-fields fn2-pool)))))
            :do-not '(preprocess)
            :in-theory (union-theories '(fn2-ribbon-header-stage fn2-ribbon-put-values-rows
                            mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil)

; Starting and clearing establish the initial band used by key insertion.
(local
 (defthm fn2-ribbon-clear-row-count-preserved
   (equal (fn2-ribbon-band-rows (mv-nth 1 (fn2-ribbon-clear-rows k i base fn2-ribbon-band)))
          (fn2-ribbon-band-rows fn2-ribbon-band))
   :hints (("Goal" :induct (fn2-ribbon-clear-rows k i base fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-clear-rows fn2-ribbon-band-rows fn2-ribbon-band-set-lo
                          fn2-ribbon-band-set-hi fn2-ribbon-band-set-z update-fn2-ribbon-band-lo$ai
                          update-fn2-ribbon-band-hi$ai update-fn2-ribbon-band-z$ai) (nth update-nth))))))

(local
 (defthm fn2-ribbon-adapter-starts-clearing
   (let ((start (fn2-ribbon-start 0 0 0 136 0 n fn2-ribbon-builds fn2-ribbon-band fn2-run-writers)))
     (implies (and (posp n) (<= n 256) (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
                   (<= (fn2-ribbon-slots n) (fn2-ribbon-band-rows fn2-ribbon-band))
                   (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
                   (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-open*)
                   (equal (fn2-run-writers-cursor 0 fn2-run-writers) *fn2-ribbon-base*)
                   (equal (fn2-run-writers-entries 0 fn2-run-writers) 0))
              (let ((b (mv-nth 1 start)))
                (and (equal (mv-nth 0 start) :ok) (fn2-ribbon-build-identity-p n b)
                     (equal (fn2-ribbon-builds-phase 0 b) *fn2-ribbon-phase-clearing*)
                     (equal (fn2-ribbon-builds-pending 0 b) 0)
                     (equal (fn2-ribbon-builds-added 0 b) 0) (equal (fn2-ribbon-builds-i 0 b) 0)))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-start fn2-ribbon-builds-rows fn2-ribbon-builds-phase fn2-ribbon-builds-set-phase update-fn2-ribbon-builds-phase$ai
                          fn2-ribbon-builds-schema fn2-ribbon-builds-set-schema update-fn2-ribbon-builds-schema$ai
                          fn2-ribbon-builds-run fn2-ribbon-builds-set-run update-fn2-ribbon-builds-run$ai
                          fn2-ribbon-builds-seed fn2-ribbon-builds-set-seed update-fn2-ribbon-builds-seed$ai
                          fn2-ribbon-builds-base fn2-ribbon-builds-set-base update-fn2-ribbon-builds-base$ai
                          fn2-ribbon-builds-slots fn2-ribbon-builds-set-slots update-fn2-ribbon-builds-slots$ai
                          fn2-ribbon-builds-keys fn2-ribbon-builds-set-keys update-fn2-ribbon-builds-keys$ai
                          fn2-ribbon-builds-added fn2-ribbon-builds-set-added update-fn2-ribbon-builds-added$ai
                          fn2-ribbon-builds-i fn2-ribbon-builds-set-i update-fn2-ribbon-builds-i$ai
                          fn2-ribbon-builds-w fn2-ribbon-builds-set-w update-fn2-ribbon-builds-w$ai
                          fn2-ribbon-builds-crow fn2-ribbon-builds-set-crow update-fn2-ribbon-builds-crow$ai
                          fn2-ribbon-builds-hrow fn2-ribbon-builds-set-hrow update-fn2-ribbon-builds-hrow$ai
                          fn2-ribbon-builds-pending fn2-ribbon-builds-set-pending update-fn2-ribbon-builds-pending$ai
                          fn2-ribbon-builds-ps fn2-ribbon-builds-set-ps update-fn2-ribbon-builds-ps$ai
                          fn2-ribbon-builds-plo fn2-ribbon-builds-set-plo update-fn2-ribbon-builds-plo$ai
                          fn2-ribbon-builds-phi fn2-ribbon-builds-set-phi update-fn2-ribbon-builds-phi$ai)
                                    (nth update-nth fn2-ribbon-slots fn2-ribbon-band-rows))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-clear-readies-band
   (let* ((step (fn2-ribbon-clear-step 0 4096 fn2-ribbon-builds fn2-ribbon-band))
          (slots (fn2-ribbon-slots n)))
     (implies (and (posp n) (<= n 256) (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
                   (equal (fn2-ribbon-builds-i 0 fn2-ribbon-builds) 0)
                   (equal (fn2-ribbon-builds-pending 0 fn2-ribbon-builds) 0)
                   (equal (fn2-ribbon-builds-added 0 fn2-ribbon-builds) 0)
                   (<= slots (fn2-ribbon-band-rows fn2-ribbon-band)))
              (and (equal (mv-nth 0 step) :ready)
                   (fn2-ribbon-adding-p n slots (fn2-ribbon-seed 7) (mv-nth 1 step))
                   (fn2-ribbon-build-identity-p n (mv-nth 1 step))
                   (fn2-ribbon-band-ready-p slots (mv-nth 2 step)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-cleared-band-invariants (n (fn2-ribbon-slots n))
                                   (base 0) (slots (fn2-ribbon-slots n))))
            :in-theory (e/d (fn2-ribbon-clear-step fn2-ribbon-builds-rows
                             fn2-ribbon-builds-set-phase fn2-ribbon-builds-set-i
                             update-fn2-ribbon-builds-phase$ai update-fn2-ribbon-builds-i$ai)
                      (nth update-nth fn2-ribbon-slots fn2-ribbon-clear-rows fn2-ribbon-band-rows
                       fn2-ribbon-band-fits-p fn2-ribbon-pivots-p))))
   :rule-classes nil))

; The emitted band is the solution page, including after each padding write.
(local
 (defthm fn2-ribbon-emitted-solution-page
   (let ((wr (fn2-ribbon-emit-bytes slots 0 0 slot gen *fn2-ribbon-base* 9 0 1 fn2-ribbon-band fn2-pool)))
     (implies (and (natp slots) (natp m) (<= m slots) (natp (fn2-pool-base slot fn2-pool))
                   (equal (mv-nth 0 wr) :ok))
              (fn2-ribbon-solution-page-p m slot gen fn2-ribbon-band (mv-nth 1 wr))))
   :hints (("Goal" :induct (fn2-ribbon-row-induct m)
            :in-theory (disable fn2-pool-base fn2-pool-read fn2-ribbon-band-z fn2-ribbon-band-rows
                                unsigned-byte-p fn2-ribbon-emit-bytes))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-emit-validates-row (i 0) (base 0) (n slots) (off *fn2-ribbon-base*) (pk 9) (ps 0) (pg 1) (p (1- m)))
                             (:instance fn2-ribbon-emit-reads (i 0) (base 0) (n slots) (off *fn2-ribbon-base*) (pk 9) (ps 0) (pg 1) (p (1- m))))))
   :rule-classes nil))

(defthm fn2-ribbon-padding-keeps-solution
   (let ((wr (fn2-run-zero k slot gen pos 9 0 1 fn2-pool)))
     (implies (and (natp k) (natp pos) (natp m) (<= (+ *fn2-ribbon-base* m) pos)
                   (natp (fn2-pool-base slot fn2-pool))
                   (equal (mv-nth 0 wr) :ok)
                   (fn2-ribbon-solution-page-p m slot gen fn2-ribbon-band fn2-pool))
              (fn2-ribbon-solution-page-p m slot gen fn2-ribbon-band (mv-nth 1 wr))))
   :hints (("Goal" :induct (fn2-ribbon-row-induct m)
            :in-theory (disable fn2-run-zero fn2-pool-base fn2-pool-read unsigned-byte-p
                                fn2-ribbon-band-z fn2-ribbon-band-rows))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-read-through-padding
                                  (n k) (i (+ *fn2-ribbon-base* -1 m)) (pk 9) (ps 0) (pg 1)))))
   :rule-classes nil)

; The final digest step seals through the actual adapter and returns the same page.
(local
 (defthm fn2-ribbon-drive-clear-result
   (let ((step (fn2-ribbon-clear-step 0 4096 fn2-ribbon-builds fn2-ribbon-band)))
     (implies (and (posp fuel) (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
                   (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-clearing*)
                   (not (equal (mv-nth 0 step) :more)))
              (equal (fn2-rba-call fn2-rba-drive fuel)
                     (list (mv-nth 0 step) (mv-nth 1 step) (mv-nth 2 step) fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))))
   :hints (("Goal" :expand ((fn2-rba-call fn2-rba-drive fuel))
            :in-theory (e/d (fn2-ribbon-work) (fn2-rba-drive fn2-ribbon-builds-rows fn2-ribbon-builds-phase
                            fn2-ribbon-clear-step fn2-ribbon-seal))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-drive-seal-result
   (let ((step (fn2-ribbon-seal 0 4096 fn2-ribbon-builds fn2-run-writers fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
     (implies (and (posp fuel) (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
                   (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-sealing*)
                   (not (equal (mv-nth 0 step) :more)))
              (equal (fn2-rba-call fn2-rba-drive fuel)
                     (list (mv-nth 0 step) (mv-nth 1 step) fn2-ribbon-band (mv-nth 2 step) fn2-run-restarts (mv-nth 5 step) (mv-nth 6 step) (mv-nth 3 step) fn2-fc-context (mv-nth 4 step) (mv-nth 7 step)))))
   :hints (("Goal" :expand ((fn2-rba-call fn2-rba-drive fuel))
            :in-theory (e/d (fn2-ribbon-work) (fn2-rba-drive fn2-ribbon-builds-rows fn2-ribbon-builds-phase
                            fn2-ribbon-clear-step fn2-ribbon-seal))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-format-completes-seal
   (let ((run (fn2-format-run :page t 0 slot gen 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
     (implies (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                   (equal (fn2-fc-context-hash 0 fn2-fc-context) 136))
              (equal run (list :ok (fn2-fc-reset 0 fn2-fc) fn2-b3 fn2-fields fn2-pool
                          (fn2-digest-copy 136 (fn2-digest-slot 0 *fn2-fc-result*) fn2-digests)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-finish-sealer-digest (fuel 4096)))
            :in-theory (e/d (fn2-format-run fn2-fc-step)
                            (fn2-fc-phase fn2-fc-reset fn2-fc-context-hash fn2-fc-run-bytes fn2-digest-copy fn2-digest-equal))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-last-seal-step
   (implies (and (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
                   (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
                   (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-sealing*)
                   (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                   (equal (fn2-fc-context-hash 0 fn2-fc-context) 136)
                   (< 0 (fn2-fc-rows fn2-fc)) (< 0 (fn2-fc-context-rows fn2-fc-context))
                   (fn2-digest-rowp 136 fn2-digests)
                   (fn2-digest-rowp (fn2-fc-context-geometry 0 fn2-fc-context) fn2-digests)
                   (fn2-digest-rowp (fn2-fc-context-previous-seal 0 fn2-fc-context) fn2-digests)
                   (fn2-b3-ready 0 fn2-b3 fn2-digests) (< 301 (fn2-fields-rows fn2-fields)))
            (equal (fn2-ribbon-seal 0 4096 fn2-ribbon-builds fn2-run-writers fn2-fc fn2-fc-context
                                    fn2-b3 fn2-fields fn2-pool fn2-digests)
                   (list :sealed (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-sealed* fn2-ribbon-builds)
                         (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-sealed* fn2-run-writers)
                         (fn2-fc-reset 0 fn2-fc) fn2-b3 fn2-fields fn2-pool
                         (fn2-digest-copy 136 (fn2-digest-slot 0 *fn2-fc-result*) fn2-digests))))
   :hints (("Goal" :use fn2-ribbon-format-completes-seal
            :in-theory (e/d (fn2-ribbon-seal fn2-run-seal-step)
                       (fn2-format-run fn2-fc-phase fn2-fc-reset fn2-fc-context-hash fn2-digest-copy
                        fn2-fc-rows fn2-fc-context-rows fn2-digest-rowp fn2-fc-context-geometry
                        fn2-fc-context-previous-seal fn2-b3-ready fn2-fields-rows fn2-run-writers-phase
                        fn2-ribbon-builds-set-phase fn2-run-writers-set-phase fn2-run-writers-rows fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-page-kind fn2-run-writers-schema fn2-run-writers-run fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-restarts fn2-ribbon-builds-rows fn2-ribbon-builds-keys fn2-ribbon-builds-schema fn2-ribbon-builds-run fn2-ribbon-builds-seed fn2-ribbon-builds-slots fn2-ribbon-builds-base fn2-ribbon-builds-w fn2-ribbon-builds-crow fn2-ribbon-builds-hrow))))
   :rule-classes nil))

(defthm fn2-ribbon-drive-finishes-seal
   (let ((drive (fn2-rba-call fn2-rba-drive fuel)))
     (implies (and (posp fuel)
                   (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-sealing*)
                   (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
                   (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
                   (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-sealing*)
                   (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                   (equal (fn2-fc-context-hash 0 fn2-fc-context) 136)
                   (< 0 (fn2-fc-rows fn2-fc)) (< 0 (fn2-fc-context-rows fn2-fc-context))
                   (fn2-digest-rowp 136 fn2-digests)
                   (fn2-digest-rowp (fn2-fc-context-geometry 0 fn2-fc-context) fn2-digests)
                   (fn2-digest-rowp (fn2-fc-context-previous-seal 0 fn2-fc-context) fn2-digests)
                   (fn2-b3-ready 0 fn2-b3 fn2-digests) (< 301 (fn2-fields-rows fn2-fields)))
              (and (equal (mv-nth 0 drive) :sealed) (equal (mv-nth 6 drive) fn2-pool)
                   (equal (mv-nth 5 drive) fn2-fields) (equal (mv-nth 7 drive) (fn2-fc-reset 0 fn2-fc))
                   (equal (mv-nth 10 drive) (fn2-digest-copy 136 (fn2-digest-slot 0 *fn2-fc-result*) fn2-digests))
                   (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) 136 (mv-nth 10 drive)))))
   :hints (("Goal" :use (fn2-ribbon-drive-seal-result fn2-ribbon-last-seal-step
                         (:instance fn2-ribbon-seal-copies-computed-digest (dest 136)))
            :in-theory (union-theories '(fn2-ribbon-build-identity-p mv-nth-of-cons (:e mv-nth) (:e zp) (:e binary-+)
                              car-cons cdr-cons (:e equal) (:e not) (:e natp) (:e fn2-digest-slot))
                          (theory 'minimal-theory))))
   :rule-classes nil)

; The checker starts from the writer's context and decodes the full-page input range.
(defun fn2-ribbon-seal-context-p (fn2-fc-context)
   (declare (xargs :stobjs fn2-fc-context :verify-guards nil))
   (and (equal (fn2-fc-context-location 0 fn2-fc-context) 5)
        (equal (fn2-fc-context-allocation 0 fn2-fc-context) 3)
        (equal (fn2-fc-context-history 0 fn2-fc-context) 1)
        (equal (fn2-fc-context-incarnation 0 fn2-fc-context) 1)
        (equal (fn2-fc-context-writer-epoch 0 fn2-fc-context) 2)
        (equal (fn2-fc-context-page-kind 0 fn2-fc-context) *page-kind-partitioned-filter*)
        (equal (fn2-fc-context-encoded-length 0 fn2-fc-context) 65536)
        (equal (fn2-fc-context-hash 0 fn2-fc-context) 136)
        (equal (fn2-fc-context-geometry 0 fn2-fc-context) (fn2-digest-slot 0 *fn2-fc-geometry*))
        (equal (fn2-fc-context-previous-seal 0 fn2-fc-context) (fn2-digest-slot 0 *fn2-fc-previous-seal*))))

(defthm fn2-ribbon-prepares-seal-context
   (implies (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
            (fn2-ribbon-seal-context-p (fn2-run-seal-context 0 0 136 fn2-run-writers fn2-fc-context)))
   :hints (("Goal" :in-theory (e/d (fn2-run-seal-context
                               fn2-fc-context-location fn2-fc-context-set-location update-fn2-fc-context-location$ai
                               fn2-fc-context-allocation fn2-fc-context-set-allocation update-fn2-fc-context-allocation$ai
                               fn2-fc-context-history fn2-fc-context-set-history update-fn2-fc-context-history$ai
                               fn2-fc-context-incarnation fn2-fc-context-set-incarnation update-fn2-fc-context-incarnation$ai
                               fn2-fc-context-writer-epoch fn2-fc-context-set-writer-epoch update-fn2-fc-context-writer-epoch$ai
                               fn2-fc-context-page-kind fn2-fc-context-set-page-kind update-fn2-fc-context-page-kind$ai
                               fn2-fc-context-encoded-length fn2-fc-context-set-encoded-length update-fn2-fc-context-encoded-length$ai
                               fn2-fc-context-hash fn2-fc-context-set-hash update-fn2-fc-context-hash$ai
                               fn2-fc-context-geometry fn2-fc-context-set-geometry update-fn2-fc-context-geometry$ai
                               fn2-fc-context-previous-seal fn2-fc-context-set-previous-seal update-fn2-fc-context-previous-seal$ai)
                              (nth update-nth fn2-run-writers-rows fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-page-kind fn2-run-writers-schema fn2-run-writers-run fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-restarts fn2-ribbon-builds-rows fn2-ribbon-builds-keys fn2-ribbon-builds-schema fn2-ribbon-builds-run fn2-ribbon-builds-seed fn2-ribbon-builds-slots fn2-ribbon-builds-base fn2-ribbon-builds-w fn2-ribbon-builds-crow fn2-ribbon-builds-hrow))))
   :rule-classes nil)

(defthm fn2-ribbon-page-begins-check
   (let ((init (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) fn2-digests fn2-b3)))
     (implies (and (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)
                   (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-idle*))
              (equal (fn2-format-run :page sealp 0 slot gen 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
                     (list :more (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fn2-fc) (mv-nth 1 init)
                           (fn2-fc-start :page 0 fn2-fields) fn2-pool (mv-nth 0 init)))))
   :hints (("Goal" :in-theory (e/d (fn2-format-run fn2-fc-step)
                     (fn2-fc-start fn2-fc-set-phase fn2-b3-init fn2-ribbon-arena-p fn2-layout-range-code fn2-fc-phase))))
   :rule-classes nil)

; The adapter emits the solved bytes and hands that same page to the padding loop.
(defthm fn2-ribbon-emit-step-starts-padding
   (let* ((slots (fn2-ribbon-slots n)) (cursor (+ *fn2-ribbon-base* slots))
          (emit (fn2-ribbon-emit-bytes slots 0 0 slot gen *fn2-ribbon-base* 9 0 1 fn2-ribbon-band fn2-pool))
          (step (fn2-ribbon-emit-step 0 4096 fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool)))
     (implies (and (posp n) (<= n 256) (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
                   (equal (fn2-ribbon-builds-i 0 fn2-ribbon-builds) 0)
                   (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
                   (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-open*)
                   (equal (mv-nth 0 emit) :ok))
              (equal step
                (list :more (fn2-ribbon-builds-set-i 0 slots
                                    (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-closing* fn2-ribbon-builds))
                      (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-closing*
                           (fn2-run-writers-set-pos 0 0 (fn2-run-writers-set-cursor 0 cursor fn2-run-writers)))
                      (mv-nth 1 emit)))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-emit-step fn2-run-close fn2-run-writers-set-cursor
                                    fn2-run-writers-phase update-fn2-run-writers-cursor$ai)
                              (nth update-nth fn2-ribbon-emit-bytes fn2-ribbon-builds-i fn2-ribbon-builds-set-i
                               fn2-ribbon-builds-set-phase fn2-run-writers-set-pos fn2-run-writers-set-phase
                               fn2-ribbon-slots fn2-run-writers-rows fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-page-kind fn2-run-writers-schema fn2-run-writers-run fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-restarts fn2-ribbon-builds-rows fn2-ribbon-builds-keys fn2-ribbon-builds-schema fn2-ribbon-builds-run fn2-ribbon-builds-seed fn2-ribbon-builds-slots fn2-ribbon-builds-base fn2-ribbon-builds-w fn2-ribbon-builds-crow fn2-ribbon-builds-hrow))))
   :rule-classes nil)

(local
 (defthm fn2-ribbon-closed-writer-starts-at-zero
   (let ((writer (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-closing*
                           (fn2-run-writers-set-pos 0 0 (fn2-run-writers-set-cursor 0 cursor fn2-run-writers)))))
     (implies (and (fn2-ribbon-writer-identity-p slot gen fn2-run-writers) (natp cursor) (<= cursor 65536)
                   (fn2-ribbon-arena-p slot gen 9 0 1 cursor 65536 fn2-pool))
              (and (fn2-ribbon-padding-p cursor 0 slot gen writer fn2-pool)
                   (fn2-ribbon-writer-identity-p slot gen writer))))
   :hints (("Goal" :in-theory (e/d (fn2-run-writers-rows fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-page-kind fn2-run-writers-schema fn2-run-writers-run fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-restarts
                          fn2-run-writers-phase fn2-run-writers-set-phase update-fn2-run-writers-phase$ai
                          fn2-run-writers-cursor fn2-run-writers-set-cursor update-fn2-run-writers-cursor$ai
                          fn2-run-writers-pos fn2-run-writers-set-pos update-fn2-run-writers-pos$ai)
                         (nth update-nth fn2-ribbon-arena-p))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-adapter-emits-solved-band
   (let* ((slots (fn2-ribbon-slots n)) (cursor (+ *fn2-ribbon-base* slots))
          (step (fn2-ribbon-emit-step 0 4096 fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool))
          (writer (mv-nth 2 step)) (pool (mv-nth 3 step)))
     (implies (and (posp n) (<= n 256) (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
                   (equal (fn2-ribbon-builds-i 0 fn2-ribbon-builds) 0)
                   (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
                   (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-open*)
                   (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band)
                   (<= slots (fn2-ribbon-band-rows fn2-ribbon-band))
                   (fn2-ribbon-arena-p slot gen 9 0 1 *fn2-ribbon-base* 65536 fn2-pool))
              (and (equal (mv-nth 0 step) :more)
                   (fn2-ribbon-writer-identity-p slot gen writer)
                   (fn2-ribbon-padding-p cursor 0 slot gen writer pool)
                   (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band pool))))
   :hints (("Goal" :use (fn2-ribbon-emit-step-starts-padding
                         (:instance fn2-ribbon-emit-to-workspace (i 0) (base 0) (n (fn2-ribbon-slots n))
                                    (pk 9) (ps 0) (pg 1) (off *fn2-ribbon-base*) (cap 65536))
                         (:instance fn2-ribbon-emitted-solution-page (m (fn2-ribbon-slots n)) (slots (fn2-ribbon-slots n)))
                         (:instance fn2-ribbon-closed-writer-starts-at-zero (cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))
                                    (fn2-pool (mv-nth 1 (fn2-ribbon-emit-bytes (fn2-ribbon-slots n) 0 0 slot gen *fn2-ribbon-base* 9 0 1 fn2-ribbon-band fn2-pool)))))
             :in-theory (disable fn2-ribbon-build-identity-p fn2-ribbon-writer-identity-p fn2-ribbon-padding-p
                                 fn2-ribbon-solution-page-p fn2-ribbon-bandp fn2-ribbon-band-wfp fn2-ribbon-emit-bytes
                                 fn2-ribbon-slots fn2-ribbon-emit-step fn2-ribbon-builds-i fn2-run-writers-phase
                                 fn2-pool-base fn2-pool-cap fn2-pool-fill fn2-pool-workspace-code fn2-pool-data-length
                                 fn2-run-writers-set-phase fn2-run-writers-set-pos fn2-run-writers-set-cursor
                                 fn2-ribbon-builds-set-phase fn2-ribbon-builds-set-i fn2-ribbon-band-rows)))
   :rule-classes nil))

(defthm fn2-ribbon-padding-extends-zero-region
   (let ((wr (fn2-run-zero k slot gen pos 9 0 1 fn2-pool)))
     (implies (and (natp count) (natp start) (natp k) (natp pos)
                   (<= (+ start count) (+ pos k)) (natp (fn2-pool-base slot fn2-pool))
                   (fn2-ribbon-zero-region-p (nfix (- pos start)) start slot gen fn2-pool)
                   (equal (mv-nth 0 wr) :ok))
              (fn2-ribbon-zero-region-p count start slot gen (mv-nth 1 wr))))
   :hints (("Goal" :induct (fn2-ribbon-padding-induct count start)
            :in-theory (disable fn2-pool-read fn2-run-zero fn2-pool-base))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-read-through-padding (i start) (n k) (pk 9) (ps 0) (pg 1)))
            :expand ((:free (c) (fn2-ribbon-zero-region-p c start slot gen fn2-pool)))))
   :rule-classes nil)

(local
 (defthm fn2-ribbon-raw-zero-at-readable-zero
   (implies (and (equal (mv-nth 0 (fn2-pool-read slot gen i 9 0 1 fn2-pool)) :ok)
                 (equal (mv-nth 1 (fn2-pool-read slot gen i 9 0 1 fn2-pool)) 0))
            (equal (fn2-pool-datai (+ (fn2-pool-base slot fn2-pool) i) fn2-pool) 0))
   :hints (("Goal" :in-theory (e/d (fn2-pool-read)
                    (fn2-pool-readable-code fn2-pool-base fn2-pool-datai fn2-pool-data-length fn2-pool-fill))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-checker-reads-zero-span
   (implies (and (natp start) (natp count) (natp (fn2-pool-base slot fn2-pool))
                 (fn2-ribbon-zero-region-p count start slot gen fn2-pool))
            (equal (fn2-fc-zero-prefix (+ (fn2-pool-base slot fn2-pool) start) count fn2-pool) count))
   :hints (("Goal" :induct (fn2-ribbon-padding-induct count start)
            :in-theory (e/d (fn2-fc-zero-prefix) (fn2-pool-datai fn2-pool-base fn2-pool-read)))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-raw-zero-at-readable-zero (i start)))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-zero-region-suffix
   (implies (and (natp start) (natp count) (natp offset) (<= start offset) (<= offset (+ start count))
                 (fn2-ribbon-zero-region-p count start slot gen fn2-pool))
            (fn2-ribbon-zero-region-p (- (+ start count) offset) offset slot gen fn2-pool))
   :hints (("Goal" :induct (fn2-ribbon-padding-induct count start)
            :in-theory (disable fn2-pool-read)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-zero-region-prefix
   (implies (and (natp start) (natp count) (natp span) (<= span count)
                 (fn2-ribbon-zero-region-p count start slot gen fn2-pool))
            (fn2-ribbon-zero-region-p span start slot gen fn2-pool))
   :hints (("Goal" :induct (list (fn2-ribbon-padding-induct count start) (fn2-ribbon-padding-induct span start))
            :in-theory (disable fn2-pool-read)))
   :rule-classes nil))

(defthm fn2-ribbon-checker-accepts-padding-span
   (implies (and (natp pad) (natp pos) (natp span) (<= pad pos) (<= (+ pos span) 65536)
                 (natp (fn2-pool-base slot fn2-pool)) (fn2-ribbon-zero-region-p (- 65536 pad) pad slot gen fn2-pool))
            (equal (fn2-fc-zero-prefix (+ (fn2-pool-base slot fn2-pool) pos) span fn2-pool) span))
   :hints (("Goal" :use ((:instance fn2-ribbon-zero-region-suffix (start pad) (count (- 65536 pad)) (offset pos))
                        (:instance fn2-ribbon-zero-region-prefix (start pos) (count (- 65536 pos)))
                        (:instance fn2-ribbon-checker-reads-zero-span (count span) (start pos)))
            :in-theory (disable fn2-ribbon-zero-region-p fn2-fc-zero-prefix fn2-pool-base)))
   :rule-classes nil)

; Evaluate the fixed allocations once with local stobjs and expose their logical results.
(defmacro fn2-ribbon-first-reservation ()
   '(fn2-pool-reserve 0 9 0 1 (fn2-pool-init '((3 . 65536)) 1 100 (create-fn2-pool))))

(defmacro fn2-ribbon-opened-writer ()
   '(fn2-run-open 0 (mv-nth 1 (fn2-ribbon-first-reservation)) (mv-nth 2 (fn2-ribbon-first-reservation))
                  1 1 0 7 0 *page-kind-partitioned-filter* 5 2 3 1 1 9 0 1 0 65536
                  (fn2-run-writers-init 1 (create-fn2-run-writers)) (mv-nth 3 (fn2-ribbon-first-reservation))))

(defmacro fn2-ribbon-key-reservation ()
   '(fn2-pool-reserve 0 9 0 1 (mv-nth 2 (fn2-ribbon-opened-writer))))

(local
 (defun fn2-ribbon-initial-arenas-check (fn2-run-writers fn2-pool)
   (declare (xargs :stobjs (fn2-run-writers fn2-pool) :verify-guards nil))
   (b* ((fn2-run-writers (fn2-run-writers-init 1 fn2-run-writers))
        (fn2-pool (fn2-pool-init '((3 . 65536)) 1 100 fn2-pool))
        ((mv pcode p pg fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
        ((mv wcode fn2-run-writers fn2-pool)
         (fn2-run-open 0 p pg 1 1 0 7 0 *page-kind-partitioned-filter* 5 2 3 1 1 9 0 1 0 65536 fn2-run-writers fn2-pool))
        ((mv kcode k kg fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool)))
     (mv (and (equal pcode :ok) (equal wcode :ok) (equal kcode :ok)
              (equal p 0) (equal pg 1) (equal k 1) (equal kg 1)
              (fn2-ribbon-writer-identity-p p pg fn2-run-writers)
              (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-open*)
              (equal (fn2-run-writers-entries 0 fn2-run-writers) 0)
              (equal (fn2-run-writers-cursor 0 fn2-run-writers) *fn2-ribbon-base*)
              (fn2-ribbon-page-before-arena-p p k fn2-pool)
              (fn2-ribbon-arena-p k kg 9 0 1 0 65536 fn2-pool)
              (fn2-ribbon-arena-p p pg 9 0 1 *fn2-ribbon-base* 65536 fn2-pool))
         fn2-run-writers fn2-pool))))

(local
 (defun fn2-ribbon-fresh-arenas-check ()
   (declare (xargs :verify-guards nil))
   (fn2-run-with-local (fn2-run-writers fn2-pool) (fn2-ribbon-initial-arenas-check fn2-run-writers fn2-pool))))

(local
 (defthm fn2-ribbon-fresh-arenas-pass
   (fn2-ribbon-fresh-arenas-check)
   :hints (("Goal" :in-theory (union-theories '((:e fn2-ribbon-fresh-arenas-check)) (theory 'minimal-theory))))
   :rule-classes nil))

(defthm fn2-ribbon-initial-page-and-key-arenas
   (let* ((page (fn2-ribbon-first-reservation)) (writer (fn2-ribbon-opened-writer))
          (keys (fn2-ribbon-key-reservation)) (p (mv-nth 1 page)) (pg (mv-nth 2 page))
          (k (mv-nth 1 keys)) (kg (mv-nth 2 keys)) (pool (mv-nth 3 keys)) (w (mv-nth 1 writer)))
     (and (equal (mv-nth 0 page) :ok) (equal (mv-nth 0 writer) :ok) (equal (mv-nth 0 keys) :ok)
          (fn2-ribbon-writer-identity-p p pg w) (equal (fn2-run-writers-phase 0 w) *fn2-run-writer-phase-open*)
          (equal (fn2-run-writers-entries 0 w) 0) (equal (fn2-run-writers-cursor 0 w) *fn2-ribbon-base*)
          (equal p 0) (equal pg 1) (equal k 1) (equal kg 1)
          (fn2-ribbon-page-before-arena-p p k pool) (fn2-ribbon-arena-p k kg 9 0 1 0 65536 pool)
          (fn2-ribbon-arena-p p pg 9 0 1 *fn2-ribbon-base* 65536 pool)))
   :hints (("Goal" :use fn2-ribbon-fresh-arenas-pass
            :in-theory (union-theories '(fn2-ribbon-fresh-arenas-check fn2-ribbon-initial-arenas-check
                              mv-nth-of-cons car-cons cdr-cons (:e zp) (:e binary-+) (:e equal))
                            (theory 'minimal-theory))))
   :rule-classes nil)

; Compose the actual initial state, writer, clearing drive, reservations, and insertion loop.
(defun fn2-ribbon-state-arguments (i count snapshot replacements)
   (if (zp count) nil
     (let ((entry (assoc-equal i replacements)))
       (cons (if entry (cadr entry) (list 'mv-nth i snapshot))
             (fn2-ribbon-state-arguments (1+ i) (1- count) snapshot replacements)))))

(defmacro fn2-ribbon-call-with-state (op args snapshot &rest replacements)
   (cons op (append args (fn2-ribbon-state-arguments 1 10 snapshot replacements))))

(defun-nx fn2-ribbon-fresh-state (n)
   (fn2-rba-setup n (create-fn2-ribbon-builds)
                    (create-fn2-ribbon-band)
                    (create-fn2-run-writers)
                    (create-fn2-run-restarts)
                    (create-fn2-fields)
                    (create-fn2-pool)
                    (create-fn2-fc)
                    (create-fn2-fc-context)
                    (create-fn2-b3)
                    (create-fn2-digests)))

(defthm fn2-ribbon-fresh-state-shape
   (let ((st (fn2-ribbon-fresh-state n)))
     (and (equal (fn2-ribbon-builds-rows (mv-nth 1 st)) 1)
          (equal (fn2-ribbon-band-rows (mv-nth 2 st)) (fn2-ribbon-slots n))
          (equal (fn2-fields-rows (mv-nth 5 st)) 400)
          (fn2-fields-wfp (mv-nth 5 st))
          (equal (mv-nth 6 st) (fn2-pool-init '((3 . 65536)) 1 100 (create-fn2-pool)))
          (equal (mv-nth 3 st) (fn2-run-writers-init 1 (create-fn2-run-writers)))))
   :hints (("Goal" :in-theory (union-theories
                     '(fn2-ribbon-fresh-state fn2-rba-setup mv-nth-of-cons car-cons cdr-cons (:e zp) (:e binary-+)
                       (:e natp) (:e <) fn2-fields-init-wfp fn2-fields-init-rows fn2-ribbon-band-init-rows fn2-ribbon-builds-init-rows)
                     (theory 'minimal-theory))))
   :rule-classes nil)

(defun-nx fn2-ribbon-started-build (n)
   (let ((st (fn2-ribbon-fresh-state n)))
     (fn2-ribbon-start 0 0 0 136 0 n (mv-nth 1 st) (mv-nth 2 st) (mv-nth 1 (fn2-ribbon-opened-writer)))))

(defthm fn2-ribbon-fresh-build-clears
   (let* ((start (fn2-ribbon-started-build n)) (b (mv-nth 1 start)))
     (implies (and (posp n) (<= n 256))
              (and (equal (mv-nth 0 start) :ok) (fn2-ribbon-build-identity-p n b)
                   (equal (fn2-ribbon-builds-phase 0 b) *fn2-ribbon-phase-clearing*)
                   (equal (fn2-ribbon-builds-pending 0 b) 0) (equal (fn2-ribbon-builds-added 0 b) 0)
                   (equal (fn2-ribbon-builds-i 0 b) 0))))
   :hints (("Goal" :use (fn2-ribbon-fresh-state-shape fn2-ribbon-initial-page-and-key-arenas
                         (:instance fn2-ribbon-adapter-starts-clearing
                           (slot (mv-nth 1 (fn2-ribbon-first-reservation))) (gen (mv-nth 2 (fn2-ribbon-first-reservation)))
                           (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-fresh-state n)))
                           (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-fresh-state n)))
                           (fn2-run-writers (mv-nth 1 (fn2-ribbon-opened-writer)))))
            :in-theory (union-theories '(fn2-ribbon-started-build (:e <) (:e equal) (:e not))
                            (theory 'minimal-theory))))
   :rule-classes nil)

(defun-nx fn2-ribbon-ready-state (n)
   (fn2-ribbon-call-with-state fn2-rba-drive (100000) (fn2-ribbon-fresh-state n)
     (1 (mv-nth 1 (fn2-ribbon-started-build n))) (3 (mv-nth 1 (fn2-ribbon-opened-writer)))
     (6 (mv-nth 2 (fn2-ribbon-opened-writer)))))

(local
 (defthm fn2-ribbon-build-identity-has-row
   (implies (fn2-ribbon-build-identity-p n fn2-ribbon-builds) (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds)))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-build-identity-p) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-clear-drive-contract
   (let ((r (fn2-rba-call fn2-rba-drive fuel)) (slots (fn2-ribbon-slots n)))
     (implies (and (posp fuel) (posp n) (<= n 256) (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
                   (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-clearing*)
                   (equal (fn2-ribbon-builds-i 0 fn2-ribbon-builds) 0) (equal (fn2-ribbon-builds-pending 0 fn2-ribbon-builds) 0)
                   (equal (fn2-ribbon-builds-added 0 fn2-ribbon-builds) 0) (<= slots (fn2-ribbon-band-rows fn2-ribbon-band)))
              (and (equal (mv-nth 0 r) :ready)
                   (fn2-ribbon-adding-p n slots (fn2-ribbon-seed 7) (mv-nth 1 r))
                   (fn2-ribbon-band-ready-p slots (mv-nth 2 r)) (fn2-ribbon-build-identity-p n (mv-nth 1 r))
                   (equal (mv-nth 3 r) fn2-run-writers)
                   (equal (mv-nth 4 r) fn2-run-restarts)
                   (equal (mv-nth 5 r) fn2-fields)
                   (equal (mv-nth 6 r) fn2-pool)
                   (equal (mv-nth 7 r) fn2-fc)
                   (equal (mv-nth 8 r) fn2-fc-context)
                   (equal (mv-nth 9 r) fn2-b3)
                   (equal (mv-nth 10 r) fn2-digests))))
   :hints (("Goal" :use (fn2-ribbon-drive-clear-result fn2-ribbon-clear-readies-band fn2-ribbon-build-identity-has-row)
            :do-not '(preprocess) :in-theory (union-theories
                '(mv-nth-of-cons car-cons cdr-cons (:e zp) (:e binary-+) (:e equal) (:e not))
                 (theory 'minimal-theory))))
   :rule-classes nil))

(defthm fn2-ribbon-drive-clears-fresh-band
   (let ((ready (fn2-ribbon-ready-state n)) (st (fn2-ribbon-fresh-state n)) (w (fn2-ribbon-opened-writer)) (slots (fn2-ribbon-slots n)))
     (implies (and (posp n) (<= n 256))
              (and (equal (mv-nth 0 ready) :ready)
                   (fn2-ribbon-adding-p n slots (fn2-ribbon-seed 7) (mv-nth 1 ready))
                   (fn2-ribbon-band-ready-p slots (mv-nth 2 ready))
                   (fn2-ribbon-build-identity-p n (mv-nth 1 ready))
                   (equal (mv-nth 3 ready) (mv-nth 1 w)) (equal (mv-nth 6 ready) (mv-nth 2 w))
                   (equal (mv-nth 4 ready) (mv-nth 4 st))
                   (equal (mv-nth 5 ready) (mv-nth 5 st))
                   (equal (mv-nth 7 ready) (mv-nth 7 st))
                   (equal (mv-nth 8 ready) (mv-nth 8 st))
                   (equal (mv-nth 9 ready) (mv-nth 9 st))
                   (equal (mv-nth 10 ready) (mv-nth 10 st)))))
   :hints (("Goal" :use (fn2-ribbon-fresh-state-shape fn2-ribbon-fresh-build-clears
                 (:instance fn2-ribbon-clear-drive-contract (fuel 100000)
                   (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-started-build n)))
                   (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-fresh-state n)))
                   (fn2-run-writers (mv-nth 1 (fn2-ribbon-opened-writer)))
                   (fn2-run-restarts (mv-nth 4 (fn2-ribbon-fresh-state n)))
                   (fn2-fields (mv-nth 5 (fn2-ribbon-fresh-state n)))
                   (fn2-pool (mv-nth 2 (fn2-ribbon-opened-writer)))
                   (fn2-fc (mv-nth 7 (fn2-ribbon-fresh-state n)))
                   (fn2-fc-context (mv-nth 8 (fn2-ribbon-fresh-state n)))
                   (fn2-b3 (mv-nth 9 (fn2-ribbon-fresh-state n)))
                   (fn2-digests (mv-nth 10 (fn2-ribbon-fresh-state n)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-ready-state
                           mv-nth-of-cons car-cons cdr-cons (:e zp) (:e binary-+) (:e posp) (:e equal) (:e not))
                        (theory 'minimal-theory))))
   :rule-classes nil)

(defun-nx fn2-ribbon-added-state (keys)
   (let ((reserve (fn2-ribbon-key-reservation)))
     (fn2-ribbon-call-with-state fn2-rba-adds (keys (mv-nth 1 reserve) (mv-nth 2 reserve) 0)
           (fn2-ribbon-ready-state (len keys)) (6 (mv-nth 3 reserve)))))

(defthm fn2-ribbon-fresh-adds-solve-key-equations
   (let* ((a (fn2-ribbon-added-state keys)) (band (mv-nth 2 a))
          (n (len keys)) (slots (fn2-ribbon-slots n)) (seed (fn2-ribbon-seed 7))
          (solve (fn2-ribbon-solve-rows slots slots 0 slots seed band)))
     (implies (and (fn2-ribbon-keysp keys) (posp n) (<= n 256))
              (and (equal (mv-nth 0 a) :ok)
                   (fn2-ribbon-adding-p 0 slots seed (mv-nth 1 a))
                   (fn2-ribbon-band-ready-p slots band)
                   (fn2-ribbon-key-equations-p keys slots seed (fn2-ribbon-band-suffix 0 slots (mv-nth 1 solve))))))
   :hints (("Goal" :use ((:instance fn2-ribbon-drive-clears-fresh-band (n (len keys)))
                           (:instance fn2-ribbon-fresh-state-shape (n (len keys)))
                           fn2-ribbon-initial-page-and-key-arenas
                           (:instance fn2-ribbon-adds-and-solve-satisfy-all-keys (slot (mv-nth 1 (fn2-ribbon-key-reservation))) (gen (mv-nth 2 (fn2-ribbon-key-reservation)))
                   (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7)) (off 0)
                   (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-ready-state (len keys))))
                   (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-ready-state (len keys))))
                   (fn2-run-writers (mv-nth 3 (fn2-ribbon-ready-state (len keys))))
                   (fn2-run-restarts (mv-nth 4 (fn2-ribbon-ready-state (len keys))))
                   (fn2-fields (mv-nth 5 (fn2-ribbon-ready-state (len keys))))
                   (fn2-pool (mv-nth 3 (fn2-ribbon-key-reservation)))
                   (fn2-fc (mv-nth 7 (fn2-ribbon-ready-state (len keys))))
                   (fn2-fc-context (mv-nth 8 (fn2-ribbon-ready-state (len keys))))
                   (fn2-b3 (mv-nth 9 (fn2-ribbon-ready-state (len keys))))
                   (fn2-digests (mv-nth 10 (fn2-ribbon-ready-state (len keys)))))
                           (:instance fn2-ribbon-adds-key-equations (z nil) (slot (mv-nth 1 (fn2-ribbon-key-reservation))) (gen (mv-nth 2 (fn2-ribbon-key-reservation)))
                   (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7)) (off 0)
                   (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-ready-state (len keys))))
                   (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-ready-state (len keys))))
                   (fn2-run-writers (mv-nth 3 (fn2-ribbon-ready-state (len keys))))
                   (fn2-run-restarts (mv-nth 4 (fn2-ribbon-ready-state (len keys))))
                   (fn2-fields (mv-nth 5 (fn2-ribbon-ready-state (len keys))))
                   (fn2-pool (mv-nth 3 (fn2-ribbon-key-reservation)))
                   (fn2-fc (mv-nth 7 (fn2-ribbon-ready-state (len keys))))
                   (fn2-fc-context (mv-nth 8 (fn2-ribbon-ready-state (len keys))))
                   (fn2-b3 (mv-nth 9 (fn2-ribbon-ready-state (len keys))))
                   (fn2-digests (mv-nth 10 (fn2-ribbon-ready-state (len keys))))))
            :do-not '(preprocess)
            :in-theory (union-theories '(fn2-ribbon-added-state (:e equal) (:e natp) (:e <) (:e not))
                                       (theory 'minimal-theory))))
   :rule-classes nil)

; The public image executes the successful setup and insertion prefix and returns the drive, checker and probe results.
(defthm fn2-ribbon-fresh-finish-enters-emitter
   (let* ((a (fn2-ribbon-added-state keys)) (band (mv-nth 2 a))
          (finish (fn2-ribbon-finish 0 (mv-nth 1 a))) (b (mv-nth 1 finish))
          (step (fn2-ribbon-solve-step 0 4096 b band))
          (n (len keys)) (slots (fn2-ribbon-slots n)) (seed (fn2-ribbon-seed 7)))
     (implies (and (fn2-ribbon-keysp keys) (posp n) (<= n 256))
              (and (equal (mv-nth 0 finish) :ok)
                   (< 0 (fn2-ribbon-builds-rows b)) (equal (fn2-ribbon-builds-phase 0 b) *fn2-ribbon-phase-solving*)
                   (equal (mv-nth 0 step) :more)
                   (equal (fn2-ribbon-builds-phase 0 (mv-nth 1 step)) *fn2-ribbon-phase-emitting*)
                   (fn2-ribbon-key-equations-p keys slots seed (fn2-ribbon-band-suffix 0 slots (mv-nth 2 step))))))
   :hints (("Goal" :use (fn2-ribbon-fresh-adds-solve-key-equations
                  (:instance fn2-ribbon-finish-starts-solve (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7))
                    (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-added-state keys))))
                  (:instance fn2-ribbon-adapter-solve-step (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7))
                    (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-finish 0 (mv-nth 1 (fn2-ribbon-added-state keys)))))
                    (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-added-state keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-solving-p) (theory 'minimal-theory))))
   :rule-classes nil)

(defun-nx fn2-ribbon-final-drive (keys)
   (let* ((added (fn2-ribbon-added-state keys)) (finish (fn2-ribbon-finish 0 (mv-nth 1 added))))
     (fn2-ribbon-call-with-state fn2-rba-drive (100000) added (1 (mv-nth 1 finish)))))

(defun-nx fn2-ribbon-final-check (keys)
   (fn2-ribbon-call-with-state fn2-rba-check (0 1) (fn2-ribbon-final-drive keys)))

(defun-nx fn2-ribbon-final-answers (keys queries)
   (let* ((checked (fn2-ribbon-final-check keys))
          (q (fn2-pool-reserve 0 9 0 1 (mv-nth 6 checked))))
     (mv-nth 0 (fn2-ribbon-call-with-state fn2-rba-probes
                   (queries (mv-nth 1 q) (mv-nth 2 q) 0 0 1) checked (6 (mv-nth 3 q))))))

; Key insertion preserves the page workspace and the build tables needed by the real emitter.
(local
 (defthm fn2-ribbon-other-arena-after-key-write
   (implies (and (natp pslot) (natp slot) (not (equal pslot slot))
                 (fn2-ribbon-arena-p pslot pgen 9 0 1 prior cap fn2-pool))
            (fn2-ribbon-arena-p pslot pgen 9 0 1 prior cap
               (mv-nth 1 (fn2-pool-write slot gen off byte 9 0 1 fn2-pool))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-arena-p fn2-pool-write fn2-pool-workspace-code fn2-pool-handle-code
                                 fn2-pool-ownerp fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai)
                             (nth update-nth))))))


(local
 (defthm fn2-ribbon-other-arena-after-key-load
   (implies (and (natp pslot) (natp slot) (not (equal pslot slot))
                 (fn2-ribbon-arena-p pslot pgen 9 0 1 prior cap fn2-pool))
            (fn2-ribbon-arena-p pslot pgen 9 0 1 prior cap
                (mv-nth 1 (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-ribbon-arena-p fn2-pool-write))))))

(local
 (defthm fn2-ribbon-counting-key-preserves-build-identity
   (equal (fn2-ribbon-build-identity-p n (fn2-ribbon-builds-set-added 0 v fn2-ribbon-builds))
          (fn2-ribbon-build-identity-p n fn2-ribbon-builds))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-builds-set-added update-fn2-ribbon-builds-added$ai
                                  fn2-ribbon-builds-rows fn2-ribbon-builds-keys fn2-ribbon-builds-schema fn2-ribbon-builds-run fn2-ribbon-builds-seed fn2-ribbon-builds-slots fn2-ribbon-builds-base fn2-ribbon-builds-w fn2-ribbon-builds-crow fn2-ribbon-builds-hrow)
                                  (nth update-nth fn2-ribbon-slots))))))

(defun fn2-ribbon-insertion-environment-p (n pslot pgen fn2-ribbon-builds fn2-ribbon-band fn2-pool)
   (declare (xargs :stobjs (fn2-ribbon-builds fn2-ribbon-band fn2-pool) :verify-guards nil))
   (and (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
        (fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds)
        (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band)
        (fn2-ribbon-arena-p pslot pgen 9 0 1 *fn2-ribbon-base* 65536 fn2-pool)))

(local
 (defthm fn2-ribbon-loaded-key-preserves-environment
   (let* ((load (fn2-ribbon-key-load bytes 300 slot gen off)) (add (fn2-ribbon-adapter-add bytes slot gen off)))
     (implies (and (fn2-ribbon-insertion-environment-p n pslot pgen fn2-ribbon-builds fn2-ribbon-band fn2-pool)
                   (natp pslot) (natp slot) (not (equal pslot slot))
                   (fn2-ribbon-adding-p remaining slots seed fn2-ribbon-builds) (posp remaining)
                   (fn2-ribbon-band-ready-p slots fn2-ribbon-band) (< 300 (fn2-fields-rows fn2-fields))
                   (fn2-ribbon-bytesp bytes) (<= (len bytes) 250) (natp off) (<= off 32768)
                   (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
              (fn2-ribbon-insertion-environment-p n pslot pgen (mv-nth 1 add) (mv-nth 2 add) (mv-nth 3 load))))
   :hints (("Goal" :use (fn2-ribbon-add-loaded-key
                (:instance fn2-ribbon-key-reference (row 300)))
            :do-not '(preprocess) :in-theory (disable fn2-ribbon-add fn2-run-load-values fn2-run-load-bytes
                         fn2-ribbon-build-identity-p fn2-ribbon-builds-set-added fn2-ribbon-builds-added
                         fn2-ribbon-buildsp fn2-ribbon-builds-wfp fn2-ribbon-bandp fn2-ribbon-band-wfp fn2-ribbon-band-ready-p
                         fn2-ribbon-key-placement fn2-ribbon-adding-p fn2-ribbon-arena-p fn2-fields-rows fn2-ribbon-bytesp)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-one-load-and-add-progress
   (let* ((load (fn2-ribbon-key-load bytes 300 slot gen off)) (add (fn2-ribbon-adapter-add bytes slot gen off))
          (pos (mv-nth 1 load)) (next (if (< 32768 pos) 0 pos)))
     (implies (and (fn2-ribbon-insertion-environment-p n pslot pgen fn2-ribbon-builds fn2-ribbon-band fn2-pool)
                   (natp pslot) (natp slot) (not (equal pslot slot))
                   (fn2-ribbon-adding-p remaining slots seed fn2-ribbon-builds) (posp remaining)
                   (fn2-ribbon-band-ready-p slots fn2-ribbon-band) (< 300 (fn2-fields-rows fn2-fields))
                   (fn2-ribbon-bytesp bytes) (<= (len bytes) 250) (natp off) (<= off 32768)
                   (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
              (and (equal (mv-nth 0 load) :ok) (equal (mv-nth 0 add) :ok) (natp next) (<= next 32768)
                   (equal (fn2-fields-rows (mv-nth 2 load)) (fn2-fields-rows fn2-fields))
                   (fn2-ribbon-insertion-environment-p n pslot pgen (mv-nth 1 add) (mv-nth 2 add) (mv-nth 3 load))
                   (fn2-ribbon-adding-p (1- remaining) slots seed (mv-nth 1 add))
                   (fn2-ribbon-band-ready-p slots (mv-nth 2 add))
                   (fn2-ribbon-arena-p slot gen 9 0 1 next 65536 (mv-nth 3 load)))))
   :hints (("Goal" :use (fn2-ribbon-loaded-key-preserves-environment
                         (:instance fn2-ribbon-adapter-adds-one-equation (z nil))
                         (:instance fn2-ribbon-key-reference (row 300))
                         (:instance fn2-ribbon-key-load-in-arena (row 300)))
            :do-not '(preprocess) :in-theory (disable fn2-ribbon-insertion-environment-p fn2-ribbon-adding-p
                         fn2-ribbon-band-ready-p fn2-ribbon-arena-p fn2-ribbon-bytesp fn2-fields-rows fn2-ribbon-add
                         fn2-run-load-values fn2-run-load-bytes fn2-ribbon-key-reference fn2-ribbon-key-load-in-arena
                         fn2-ribbon-bytes-at-p fn2-ribbon-band-satisfied-p fn2-ribbon-key-equation)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-input-fields-keep-shape
   (implies (and (fn2-fields-wfp fn2-fields) (< 300 (fn2-fields-rows fn2-fields)))
            (fn2-fields-wfp (mv-nth 2 (fn2-ribbon-key-load bytes 300 slot gen off))))
   :hints (("Goal" :in-theory (e/d (fn2-run-load-values fn2-run-load-ref)
                       (fn2-fields-wfp fn2-fields-rows fn2-run-load-bytes fn2-fields-set-ref-slot
                        fn2-fields-set-ref-gen fn2-fields-set-ref-off fn2-fields-set-ref-len))))))

(local
 (defthm fn2-ribbon-adds-preserve-emitter-inputs
   (let ((a (fn2-rba-call fn2-rba-adds keys slot gen off)))
     (implies (and (fn2-ribbon-insertion-environment-p n pslot pgen fn2-ribbon-builds fn2-ribbon-band fn2-pool)
                   (natp pslot) (natp slot) (not (equal pslot slot))
                   (fn2-ribbon-keysp keys) (fn2-ribbon-adding-p (len keys) slots seed fn2-ribbon-builds)
                   (fn2-ribbon-band-ready-p slots fn2-ribbon-band) (< 300 (fn2-fields-rows fn2-fields))
                   (natp off) (<= off 32768) (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
              (and (fn2-ribbon-insertion-environment-p n pslot pgen (mv-nth 1 a) (mv-nth 2 a) (mv-nth 6 a))
                   (implies (fn2-fields-wfp fn2-fields) (fn2-fields-wfp (mv-nth 5 a)))
                   (implies (fn2-ribbon-query-slot-free-p fn2-pool) (fn2-ribbon-query-slot-free-p (mv-nth 6 a)))
                   (equal (fn2-fields-rows (mv-nth 5 a)) (fn2-fields-rows fn2-fields))
                   (equal (mv-nth 3 a) fn2-run-writers)
                   (equal (mv-nth 4 a) fn2-run-restarts)
                   (equal (mv-nth 7 a) fn2-fc)
                   (equal (mv-nth 8 a) fn2-fc-context)
                   (equal (mv-nth 9 a) fn2-b3)
                   (equal (mv-nth 10 a) fn2-digests))))
   :hints (("Goal" :induct (fn2-rba-call fn2-ribbon-adds-induct keys slot gen off)
            :do-not '(preprocess)
            :expand ((fn2-rba-call fn2-rba-adds keys slot gen off) (len keys) (fn2-ribbon-keysp keys))
            :in-theory (union-theories '(fn2-ribbon-key-load-leaves-query-slot-free fn2-ribbon-input-fields-keep-shape mv-nth-of-cons car-cons cdr-cons (:e zp) (:e binary-+) (:e equal)
                           |(+ c (+ d x))| |(+ 0 x)| (:t fn2-ribbon-add) (:t fn2-run-load-values) (:e member-equal) (:e not) len posp zp-open (:t len)
                           (:e posp) (:e natp) (:induction fn2-ribbon-adds-induct))
                           (theory 'minimal-theory)))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-one-load-and-add-progress
                                    (remaining (len keys)) (bytes (car keys))))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-clearing-preserves-table-shapes
   (let ((r (fn2-ribbon-clear-step 0 4096 fn2-ribbon-builds fn2-ribbon-band)))
     (implies (and (fn2-ribbon-buildsp fn2-ribbon-builds) (fn2-ribbon-builds-wfp fn2-ribbon-builds)
                   (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band)
                   (posp n) (<= n 256) (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
                   (equal (fn2-ribbon-builds-i 0 fn2-ribbon-builds) 0))
              (and (fn2-ribbon-buildsp (mv-nth 1 r))
                   (fn2-ribbon-builds-wfp (mv-nth 1 r))
                   (fn2-ribbon-bandp (mv-nth 2 r))
                   (fn2-ribbon-band-wfp (mv-nth 2 r)))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-clear-step fn2-ribbon-build-identity-p)
                         (fn2-ribbon-buildsp fn2-ribbon-builds-wfp fn2-ribbon-bandp fn2-ribbon-band-wfp
                          fn2-ribbon-builds-rows fn2-ribbon-builds-set-i fn2-ribbon-builds-set-phase fn2-ribbon-clear-rows
                          fn2-ribbon-builds-i fn2-ribbon-builds-seed fn2-ribbon-builds-slots fn2-ribbon-builds-base fn2-ribbon-slots))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-setup-build-tables
   (let ((st (fn2-ribbon-fresh-state n)))
     (and (equal (mv-nth 1 st) (fn2-ribbon-builds-init 1 (create-fn2-ribbon-builds)))
          (equal (mv-nth 2 st) (fn2-ribbon-band-init (fn2-ribbon-slots n) (create-fn2-ribbon-band)))))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-fresh-state fn2-rba-setup mv-nth-of-cons (:e zp) (:e binary-+) car-cons cdr-cons)
                                             (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-started-table-shapes
   (let ((b (mv-nth 1 (fn2-ribbon-started-build n))) (band (mv-nth 2 (fn2-ribbon-fresh-state n))))
     (implies (and (posp n) (<= n 256))
              (and (fn2-ribbon-buildsp b) (fn2-ribbon-builds-wfp b) (fn2-ribbon-bandp band) (fn2-ribbon-band-wfp band))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-started-build)
                    (fn2-ribbon-fresh-state fn2-ribbon-start fn2-ribbon-slots fn2-ribbon-band-init fn2-ribbon-builds-init
                     fn2-ribbon-buildsp fn2-ribbon-builds-wfp fn2-ribbon-bandp fn2-ribbon-band-wfp
                     fn2-run-open fn2-pool-reserve fn2-pool-init (:e fn2-run-open) (:e fn2-pool-reserve) (:e fn2-pool-init)
                     (:e create-fn2-pool) (:e create-fn2-run-writers)))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-fresh-cleared-shapes
   (let ((r (fn2-ribbon-ready-state n)))
     (implies (and (posp n) (<= n 256))
              (and (fn2-ribbon-buildsp (mv-nth 1 r)) (fn2-ribbon-builds-wfp (mv-nth 1 r))
                   (fn2-ribbon-bandp (mv-nth 2 r)) (fn2-ribbon-band-wfp (mv-nth 2 r)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-build-identity-has-row (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-started-build n)))) fn2-ribbon-fresh-build-clears fn2-ribbon-fresh-state-shape fn2-ribbon-started-table-shapes
            (:instance fn2-ribbon-clearing-preserves-table-shapes (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-started-build n)))
                       (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-fresh-state n))))
            (:instance fn2-ribbon-clear-readies-band (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-started-build n)))
                       (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-fresh-state n))))
            (:instance fn2-ribbon-drive-clear-result (fuel 100000)
                   (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-started-build n)))
                   (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-fresh-state n)))
                   (fn2-run-writers (mv-nth 1 (fn2-ribbon-opened-writer)))
                   (fn2-run-restarts (mv-nth 4 (fn2-ribbon-fresh-state n)))
                   (fn2-fields (mv-nth 5 (fn2-ribbon-fresh-state n)))
                   (fn2-pool (mv-nth 2 (fn2-ribbon-opened-writer)))
                   (fn2-fc (mv-nth 7 (fn2-ribbon-fresh-state n)))
                   (fn2-fc-context (mv-nth 8 (fn2-ribbon-fresh-state n)))
                   (fn2-b3 (mv-nth 9 (fn2-ribbon-fresh-state n)))
                   (fn2-digests (mv-nth 10 (fn2-ribbon-fresh-state n)))))
            :do-not '(preprocess)
            :in-theory (union-theories '(fn2-ribbon-ready-state mv-nth-of-cons
                            (:e posp) (:e zp) (:e equal) (:e binary-+) car-cons cdr-cons) (theory 'minimal-theory))))
   :rule-classes nil))

(defthm fn2-ribbon-fresh-added-environment
   (let ((a (fn2-ribbon-added-state keys)) (n (len keys)))
     (implies (and (fn2-ribbon-keysp keys) (posp n) (<= n 256))
              (and (fn2-ribbon-insertion-environment-p n 0 1 (mv-nth 1 a) (mv-nth 2 a) (mv-nth 6 a))
                   (equal (mv-nth 3 a) (mv-nth 1 (fn2-ribbon-opened-writer)))
                   (fn2-fields-wfp (mv-nth 5 a))
                   (implies (fn2-ribbon-query-slot-free-p (mv-nth 3 (fn2-ribbon-key-reservation)))
                            (fn2-ribbon-query-slot-free-p (mv-nth 6 a)))
                   (equal (mv-nth 4 a) (mv-nth 4 (fn2-ribbon-fresh-state n)))
                   (equal (mv-nth 7 a) (mv-nth 7 (fn2-ribbon-fresh-state n)))
                   (equal (mv-nth 8 a) (mv-nth 8 (fn2-ribbon-fresh-state n)))
                   (equal (mv-nth 9 a) (mv-nth 9 (fn2-ribbon-fresh-state n)))
                   (equal (mv-nth 10 a) (mv-nth 10 (fn2-ribbon-fresh-state n)))
                   (equal (fn2-fields-rows (mv-nth 5 a)) 400))))
   :hints (("Goal" :use ((:instance fn2-ribbon-fresh-cleared-shapes (n (len keys)))
                         (:instance fn2-ribbon-drive-clears-fresh-band (n (len keys)))
                         (:instance fn2-ribbon-fresh-state-shape (n (len keys))) fn2-ribbon-initial-page-and-key-arenas
                         (:instance fn2-ribbon-adds-preserve-emitter-inputs (n (len keys)) (pslot 0) (pgen 1) (slot (mv-nth 1 (fn2-ribbon-key-reservation))) (gen (mv-nth 2 (fn2-ribbon-key-reservation)))
                   (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7)) (off 0)
                   (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-ready-state (len keys))))
                   (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-ready-state (len keys))))
                   (fn2-run-writers (mv-nth 3 (fn2-ribbon-ready-state (len keys))))
                   (fn2-run-restarts (mv-nth 4 (fn2-ribbon-ready-state (len keys))))
                   (fn2-fields (mv-nth 5 (fn2-ribbon-ready-state (len keys))))
                   (fn2-pool (mv-nth 3 (fn2-ribbon-key-reservation)))
                   (fn2-fc (mv-nth 7 (fn2-ribbon-ready-state (len keys))))
                   (fn2-fc-context (mv-nth 8 (fn2-ribbon-ready-state (len keys))))
                   (fn2-b3 (mv-nth 9 (fn2-ribbon-ready-state (len keys))))
                   (fn2-digests (mv-nth 10 (fn2-ribbon-ready-state (len keys))))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-insertion-environment-p fn2-ribbon-added-state
                      (:e natp) (:e equal) (:e not) (:e <)) (theory 'minimal-theory))))
   :rule-classes nil)

(defthm fn2-ribbon-build-identity-across-phase-and-index
   (and (equal (fn2-ribbon-build-identity-p n (fn2-ribbon-builds-set-phase 0 v fn2-ribbon-builds))
               (fn2-ribbon-build-identity-p n fn2-ribbon-builds))
        (equal (fn2-ribbon-build-identity-p n (fn2-ribbon-builds-set-i 0 v fn2-ribbon-builds))
               (fn2-ribbon-build-identity-p n fn2-ribbon-builds))
        (equal (fn2-ribbon-builds-i 0 (fn2-ribbon-builds-set-i 0 v fn2-ribbon-builds)) v))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-builds-set-i update-fn2-ribbon-builds-i$ai
                       fn2-ribbon-builds-set-phase update-fn2-ribbon-builds-phase$ai fn2-ribbon-builds-i
                       fn2-ribbon-builds-rows fn2-ribbon-builds-keys fn2-ribbon-builds-schema fn2-ribbon-builds-run fn2-ribbon-builds-seed fn2-ribbon-builds-slots fn2-ribbon-builds-base fn2-ribbon-builds-w fn2-ribbon-builds-crow fn2-ribbon-builds-hrow)
                       (nth update-nth fn2-ribbon-slots)))))

(defthm fn2-ribbon-finish-maintains-identity
   (implies (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
            (fn2-ribbon-build-identity-p n (mv-nth 1 (fn2-ribbon-finish 0 fn2-ribbon-builds))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-finish)
                   (fn2-ribbon-build-identity-p fn2-ribbon-builds-set-i fn2-ribbon-builds-set-phase
                    fn2-ribbon-builds-rows fn2-ribbon-builds-phase fn2-ribbon-builds-pending fn2-ribbon-builds-slots)))))

(defthm fn2-ribbon-solve-maintains-emitter-inputs
   (let ((step (fn2-ribbon-solve-step 0 4096 fn2-ribbon-builds fn2-ribbon-band)))
     (implies (and (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
                   (fn2-ribbon-solving-p slots seed fn2-ribbon-builds)
                   (fn2-ribbon-band-ready-p slots fn2-ribbon-band)
                   (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band)
                   (equal (mv-nth 0 step) :more)
                   (equal (fn2-ribbon-builds-phase 0 (mv-nth 1 step)) *fn2-ribbon-phase-emitting*))
              (and (fn2-ribbon-build-identity-p n (mv-nth 1 step))
                   (equal (fn2-ribbon-builds-i 0 (mv-nth 1 step)) 0)
                   (fn2-ribbon-bandp (mv-nth 2 step)) (fn2-ribbon-band-wfp (mv-nth 2 step))
                   (<= slots (fn2-ribbon-band-rows (mv-nth 2 step))))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-solve-step fn2-ribbon-solving-p fn2-ribbon-band-ready-p)
                    (fn2-ribbon-build-identity-p fn2-ribbon-builds-i fn2-ribbon-builds-set-i fn2-ribbon-builds-set-phase
                     fn2-ribbon-builds-rows fn2-ribbon-builds-slots fn2-ribbon-builds-base fn2-ribbon-builds-seed
                     fn2-ribbon-band-rows fn2-ribbon-bandp fn2-ribbon-band-wfp fn2-ribbon-band-fits-p
                     fn2-ribbon-pivots-p fn2-ribbon-solve-rows))))
   :rule-classes nil)

(defun-nx fn2-ribbon-solved-step (keys)
   (let ((added (fn2-ribbon-added-state keys)))
     (fn2-ribbon-solve-step 0 4096 (mv-nth 1 (fn2-ribbon-finish 0 (mv-nth 1 added))) (mv-nth 2 added))))

(defun-nx fn2-ribbon-emitted-step (keys)
   (let ((added (fn2-ribbon-added-state keys)) (solved (fn2-ribbon-solved-step keys)))
     (fn2-ribbon-emit-step 0 4096 (mv-nth 1 solved) (mv-nth 2 solved) (mv-nth 3 added) (mv-nth 6 added))))

(defthm fn2-ribbon-fresh-keys-produce-solution-page
   (let* ((n (len keys)) (slots (fn2-ribbon-slots n)) (solved (fn2-ribbon-solved-step keys))
          (z (mv-nth 2 solved)) (emit (fn2-ribbon-emitted-step keys)))
     (implies (and (fn2-ribbon-keysp keys) (posp n) (<= n 256))
              (and (equal (mv-nth 0 emit) :more)
                   (fn2-ribbon-key-equations-p keys slots (fn2-ribbon-seed 7) (fn2-ribbon-band-suffix 0 slots z))
                   (fn2-ribbon-solution-page-p slots 0 1 z (mv-nth 3 emit))
                   (fn2-ribbon-writer-identity-p 0 1 (mv-nth 2 emit))
                   (fn2-ribbon-padding-p (+ *fn2-ribbon-base* slots) 0 0 1 (mv-nth 2 emit) (mv-nth 3 emit)))))
   :hints (("Goal" :use (fn2-ribbon-fresh-added-environment fn2-ribbon-fresh-finish-enters-emitter
                   fn2-ribbon-fresh-adds-solve-key-equations fn2-ribbon-initial-page-and-key-arenas
                   (:instance fn2-ribbon-finish-starts-solve (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7))
                             (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-added-state keys))))
                   (:instance fn2-ribbon-solve-maintains-emitter-inputs (n (len keys))
                             (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7))
                             (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-finish 0 (mv-nth 1 (fn2-ribbon-added-state keys))))) (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-added-state keys))))
                   (:instance fn2-ribbon-adapter-emits-solved-band (n (len keys)) (slot 0) (gen 1)
                             (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-solved-step keys)))
                             (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-solved-step keys)))
                             (fn2-run-writers (mv-nth 3 (fn2-ribbon-added-state keys))) (fn2-pool (mv-nth 6 (fn2-ribbon-added-state keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-insertion-environment-p
                      fn2-ribbon-finish-maintains-identity fn2-ribbon-solved-step fn2-ribbon-emitted-step)
                      (theory 'minimal-theory))))
   :rule-classes nil)

; Two actual work iterations reduce the public final drive to the closing phase.
(local
 (defthm fn2-ribbon-drive-after-solving
   (let ((step (fn2-ribbon-solve-step 0 4096 fn2-ribbon-builds fn2-ribbon-band)))
     (implies (and (posp fuel) (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
                   (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-solving*)
                   (equal (mv-nth 0 step) :more))
              (equal (fn2-rba-call fn2-rba-drive fuel)
                     (fn2-rba-drive (1- fuel) (mv-nth 1 step) (mv-nth 2 step) fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))))
   :hints (("Goal" :expand ((fn2-rba-call fn2-rba-drive fuel))
            :in-theory (e/d (fn2-ribbon-work) (fn2-ribbon-builds-rows fn2-ribbon-builds-phase
                                  fn2-ribbon-solve-step fn2-ribbon-emit-step fn2-rba-drive))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-drive-after-emitting
   (let ((step (fn2-ribbon-emit-step 0 4096 fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool)))
     (implies (and (posp fuel) (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
                   (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-emitting*)
                   (equal (mv-nth 0 step) :more))
              (equal (fn2-rba-call fn2-rba-drive fuel)
                     (fn2-rba-drive (1- fuel) (mv-nth 1 step) fn2-ribbon-band (mv-nth 2 step) fn2-run-restarts fn2-fields (mv-nth 3 step) fn2-fc fn2-fc-context fn2-b3 fn2-digests))))
   :hints (("Goal" :expand ((fn2-rba-call fn2-rba-drive fuel))
            :in-theory (e/d (fn2-ribbon-work) (fn2-ribbon-builds-rows fn2-ribbon-builds-phase
                                  fn2-ribbon-solve-step fn2-ribbon-emit-step fn2-rba-drive))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-solve-step-keeps-rows
   (equal (fn2-ribbon-builds-rows (mv-nth 1 (fn2-ribbon-solve-step 0 4096 fn2-ribbon-builds fn2-ribbon-band)))
          (fn2-ribbon-builds-rows fn2-ribbon-builds))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-solve-step fn2-ribbon-builds-rows fn2-ribbon-builds-set-i
                                   fn2-ribbon-builds-set-phase update-fn2-ribbon-builds-i$ai update-fn2-ribbon-builds-phase$ai)
                                  (nth update-nth fn2-ribbon-solve-rows fn2-ribbon-builds-i fn2-ribbon-builds-slots
                                   fn2-ribbon-builds-seed fn2-ribbon-builds-base unsigned-byte-p))))))

(defthm fn2-ribbon-final-drive-reaches-closing
   (let ((emit (fn2-ribbon-emitted-step keys)) (solved (fn2-ribbon-solved-step keys)) (a (fn2-ribbon-added-state keys)))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
              (equal (fn2-ribbon-final-drive keys)
                     (fn2-ribbon-call-with-state fn2-rba-drive (99998) a
                           (1 (mv-nth 1 emit)) (2 (mv-nth 2 solved)) (3 (mv-nth 2 emit)) (6 (mv-nth 3 emit))))))
   :hints (("Goal" :use (fn2-ribbon-fresh-finish-enters-emitter fn2-ribbon-fresh-keys-produce-solution-page
                         (:instance fn2-ribbon-drive-after-solving (fuel 100000)
                           (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-finish 0 (mv-nth 1 (fn2-ribbon-added-state keys)))))
                        (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-added-state keys)))
                        (fn2-run-writers (mv-nth 3 (fn2-ribbon-added-state keys)))
                        (fn2-run-restarts (mv-nth 4 (fn2-ribbon-added-state keys)))
                        (fn2-fields (mv-nth 5 (fn2-ribbon-added-state keys)))
                        (fn2-pool (mv-nth 6 (fn2-ribbon-added-state keys)))
                        (fn2-fc (mv-nth 7 (fn2-ribbon-added-state keys)))
                        (fn2-fc-context (mv-nth 8 (fn2-ribbon-added-state keys)))
                        (fn2-b3 (mv-nth 9 (fn2-ribbon-added-state keys)))
                        (fn2-digests (mv-nth 10 (fn2-ribbon-added-state keys))))
                         (:instance fn2-ribbon-drive-after-emitting (fuel 99999)
                           (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-solved-step keys)))
                        (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-solved-step keys)))
                        (fn2-run-writers (mv-nth 3 (fn2-ribbon-added-state keys)))
                        (fn2-run-restarts (mv-nth 4 (fn2-ribbon-added-state keys)))
                        (fn2-fields (mv-nth 5 (fn2-ribbon-added-state keys)))
                        (fn2-pool (mv-nth 6 (fn2-ribbon-added-state keys)))
                        (fn2-fc (mv-nth 7 (fn2-ribbon-added-state keys)))
                        (fn2-fc-context (mv-nth 8 (fn2-ribbon-added-state keys)))
                        (fn2-b3 (mv-nth 9 (fn2-ribbon-added-state keys)))
                        (fn2-digests (mv-nth 10 (fn2-ribbon-added-state keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-final-drive fn2-ribbon-solved-step
                         fn2-ribbon-emitted-step fn2-ribbon-solve-step-keeps-rows (:e posp) (:e binary-+)
                         (:e equal) (:e not)) (theory 'minimal-theory))))
   :rule-classes nil)
