; A parent index write stores its child's first key, physical address,
; digest and entry count in exactly the overview index layout.
(in-package "ACL2")
(include-book "runs-index-emit-prefix-proof")

(local
 (defthm fn2-run-index-byte-count
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn2-run-index-scalar-prefix-tag
   (let* ((load (fn2-run-load-bytes prefix slot gen off 9 0 1 pool))
          (tag (fn2-codec-emit-fixed 1 1 slot gen (+ off (len prefix)) 9 0 1 (mv-nth 1 load)))
          (header (fn2-run-load-bytes (append prefix '(1)) slot gen off 9 0 1 pool)))
     (implies (and (natp off) (equal (car header) :ok))
              (and (equal (car load) :ok) (equal (car tag) :ok)
                   (equal (mv-nth 1 tag) (+ 1 off (len prefix)))
                   (equal (mv-nth 2 tag) (mv-nth 1 header)))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-fixed-writes-layout-octets (n 1) (v 1)
                      (off (+ off (len prefix))) (pk 9) (ps 0) (pg 1)
                      (pool (mv-nth 1 (fn2-run-load-bytes prefix slot gen off 9 0 1 pool)))))
            :in-theory (e/d (fn2-run-load-byte-segments)
                         (fn2-run-load-bytes fn2-codec-emit-fixed len binary-append))))))

(local
 (defthmd fn2-run-parent-index-emitter
   (let* ((i (fn2-run-index-digest-field base)) (prefix (fn2-run-index-prefix-octets base f))
          (head (fn2-run-load-bytes (append prefix '(1)) slot gen off 9 0 1 pool))
          (next (+ 1 off (len prefix)))
          (copy (fn2-layout-copy (fn2-fields-ref-slot i f) (fn2-fields-ref-gen i f) (fn2-fields-ref-off i f)
                                 slot gen next 32 9 0 1 (mv-nth 1 head)))
          (count (fn2-run-index-count-octets base f))
          (tail (fn2-run-load-bytes count slot gen (+ next 32) 9 0 1 (mv-nth 1 copy))))
     (implies (and (natp off) (natp base) (fn2-run-index-prefix-values-p base f)
                   (natp (fn2-fields-value (+ base *fn2-overview-index-field-child-entries*) f))
                   (equal (fn2-fields-ref-len i f) 32)
                   (equal (car head) :ok) (equal (car copy) :ok) (equal (car tail) :ok))
              (equal (fn2-overview-index-emit-group base slot gen off off 9 0 1 f pool)
                     (list :ok (+ next 32 (len count)) (mv-nth 1 tail)))))
   :hints (("Goal" :do-not '(preprocess) :do-not-induct t
            :use ((:instance fn2-run-index-emits-reference-prefix (pk 9) (ps 0) (pg 1))
                  (:instance fn2-run-index-scalar-prefix-tag (prefix (fn2-run-index-prefix-octets base f))))
            :in-theory (e/d (fn2-overview-index-emit-child-expected-hash fn2-overview-index-emit-child-entries
                             fn2-run-index-count-octets fn2-run-varint-writes-layout-octets)
                      (fn2-run-index-prefix-octets fn2-fields-value fn2-fields-ref-len fn2-fields-ref-slot
                       fn2-fields-ref-gen fn2-fields-ref-off fn2-codec-emit-fixed fn2-codec-emit-varint
                       fn2-layout-varoctets fn2-run-load-bytes fn2-layout-copy
                       fn2-overview-index-emit-group binary-append len unsigned-byte-p))))))

(local
 (defthmd fn2-run-index-encoder-checks
   (let ((i (fn2-run-index-digest-field base)))
     (implies (and (natp base) (unsigned-byte-p 32 off) (fn2-run-index-prefix-values-p base f)
                   (equal (fn2-fields-value i f) 1) (equal (fn2-fields-ref-len i f) 32)
                   (not (equal slot (fn2-fields-ref-slot i f)))
                   (equal (fn2-layout-range-code (fn2-fields-ref-slot i f) (fn2-fields-ref-gen i f)
                         (fn2-fields-ref-off i f) (+ 32 (fn2-fields-ref-off i f)) nil 9 0 1 pool) :ok)
                   (equal (fn2-layout-range-code slot gen off (+ off (fn2-overview-index-size base f)) t 9 0 1 pool) :ok))
              (equal (fn2-overview-index-encode base slot gen off 9 0 1 f pool)
                     (fn2-overview-index-emit-group base slot gen off off 9 0 1 f pool))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                          (e/d (fn2-overview-index-encode fn2-overview-index-check-values)
                           (fn2-overview-index-emit-group fn2-overview-index-size fn2-fields-value
                            fn2-fields-ref-len fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-layout-range-code))
                          (fn2-run-header-encoder-definitions 'fn2-overview-index *fn2-overview-index*))))))

(local
 (defthm fn2-run-write-shorter-prefix
   (implies (and (unsigned-byte-p 32 off) (unsigned-byte-p 32 middle) (<= off middle) (<= middle end)
                 (equal (fn2-layout-range-code slot gen off end t pk ps pg pool) :ok))
            (equal (fn2-layout-range-code slot gen off middle t pk ps pg pool) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code)
                         (fn2-pool-workspace-code fn2-pool-slot-fill fn2-pool-slot-base
                          fn2-pool-slot-cap fn2-pool-capacity-bytes))))))

(local
 (defthm fn2-run-index-join-octets
   (implies (and (fn-b3-octet-listp a) (fn-b3-octet-listp b))
            (fn-b3-octet-listp (append a b)))))

(local (defthm fn2-run-index-fix-octets (implies (fn-b3-octet-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn2-run-index-load-final-segment
   (let* ((first (append header body)) (bytes (append first count))
          (written (fn2-run-load-bytes first dst dg off 9 0 1 pool))
          (tail (fn2-run-load-bytes count dst dg (+ off (len first)) 9 0 1 (mv-nth 1 written)))
          (full (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)))
     (implies (and (natp off) (natp (fn2-pool-base dst pool))
                   (fn-b3-octet-listp header) (fn-b3-octet-listp body) (fn-b3-octet-listp count)
                   (equal (fn2-layout-range-code dst dg off (+ off (len bytes)) t 9 0 1 pool) :ok))
              (and (equal (car full) :ok) (equal (car written) :ok) (equal (car tail) :ok)
                   (equal (mv-nth 1 tail) (mv-nth 1 full))
                   (equal (fn2-run-read-bytes (len bytes) dst dg off 9 0 1 (mv-nth 1 tail)) bytes))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-load-byte-segments (a (append header body)) (b count)
                       (slot dst) (gen dg) (pk 9) (ps 0) (pg 1))
                  (:instance fn2-run-load-bytes-roundtrip (bytes (append (append header body) count))
                       (slot dst) (gen dg) (pk 9) (ps 0) (pg 1)
                       (cap (+ off (len (append (append header body) count))))))
            :in-theory (disable fn-b3-octet-listp fn2-run-load-bytes fn2-layout-range-code fn2-run-read-bytes
                                fn2-pool-base true-list-fix binary-append len)))))

(local
 (defthm fn2-run-index-write-digest-and-count
   (let* ((body (fn2-run-read-bytes 32 src sg at 9 0 1 pool)) (bytes (append (append header body) count))
          (end (+ off (len bytes))) (next (+ off (len header))) (start (+ at (fn2-pool-base src pool)))
          (target (+ off (fn2-pool-base dst pool))) (head (fn2-run-load-bytes header dst dg off 9 0 1 pool))
          (copy (fn2-layout-copy src sg at dst dg next 32 9 0 1 (mv-nth 1 head)))
          (tail (fn2-run-load-bytes count dst dg (+ 32 next) 9 0 1 (mv-nth 1 copy))))
     (implies (and (natp src) (natp dst) (not (equal src dst))
                   (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                   (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (unsigned-byte-p 32 at)
                   (equal (len body) 32)
                   (or (<= (+ start 32) target) (<= (+ target (len bytes)) start))
                   (fn-b3-octet-listp header) (fn-b3-octet-listp body) (fn-b3-octet-listp count)
                   (equal (fn2-layout-range-code src sg at (+ at 32) nil 9 0 1 pool) :ok)
                   (equal (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok))
              (and (equal (car head) :ok) (equal (car copy) :ok) (equal (car tail) :ok)
                   (equal (mv-nth 1 tail) (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)))
                   (equal (fn2-run-read-bytes (len bytes) dst dg off 9 0 1 (mv-nth 1 tail)) bytes))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-index-load-final-segment (body (fn2-run-read-bytes 32 src sg at 9 0 1 pool)))
                  (:instance fn2-run-write-shorter-prefix (slot dst) (gen dg) (pk 9) (ps 0) (pg 1)
                             (middle (+ 32 off (len header))) (end (+ 32 off (len header) (len count))))
                  (:instance fn2-run-write-prefix-and-payload (n 32) (pk 9) (ps 0) (pg 1)))
            :in-theory (disable fn-b3-octet-listp fn2-run-load-bytes fn2-layout-range-code fn2-run-read-bytes
                                fn2-pool-base fn2-layout-copy binary-append len)))))

(defun-nx fn2-run-overview-index-write-room-p (base dst dg off f pool)
  (let* ((i (fn2-run-index-digest-field base)) (src (fn2-fields-ref-slot i f))
         (sg (fn2-fields-ref-gen i f)) (at (fn2-fields-ref-off i f))
         (size (fn2-overview-index-size base f)) (end (+ off size))
         (source (+ at (fn2-pool-base src pool))) (target (+ off (fn2-pool-base dst pool))))
    (and (natp base) (fn2-run-index-prefix-values-p base f)
         (natp (fn2-fields-value (+ base *fn2-overview-index-field-child-entries*) f))
         (equal (fn2-fields-value i f) 1) (equal (fn2-fields-ref-len i f) 32)
         (natp src) (natp dst) (not (equal src dst))
         (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
         (unsigned-byte-p 32 at) (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)
         (or (<= (+ source 32) target) (<= (+ target size) source))
         (fn-b3-octet-listp (fn2-run-index-digest-octets base f pool))
         (equal (fn2-layout-range-code src sg at (+ at 32) nil 9 0 1 pool) :ok)
         (equal (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok))))

(local (defthm fn2-run-index-wire-append
         (equal (append (append a b) c) (append a (append b c)))))

(defthmd fn2-run-overview-index-encode-writes-layout
  (let* ((size (fn2-overview-index-size base f))
         (bytes (fn2-layout-octets *fn2-overview-index* (fn2-run-unload-values *fn2-overview-index* base f pool)))
         (actual (fn2-run-layout-encode 3 level base dst dg off 9 0 1 f pool))
         (load (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)))
    (implies (and (posp level) (fn2-run-overview-index-write-room-p base dst dg off f pool))
             (and (equal (car actual) :ok) (equal (mv-nth 1 actual) (+ off size))
                  (equal (mv-nth 2 actual) (mv-nth 1 load))
                  (equal (fn2-run-read-bytes size dst dg off 9 0 1 (mv-nth 2 actual)) bytes))))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
           :use (fn2-run-index-wire-segments fn2-run-index-scalars-are-octets
                 (:instance fn2-run-index-write-digest-and-count
                   (src (fn2-fields-ref-slot (fn2-run-index-digest-field base) f))
                   (sg (fn2-fields-ref-gen (fn2-run-index-digest-field base) f))
                   (at (fn2-fields-ref-off (fn2-run-index-digest-field base) f))
                   (header (append (fn2-run-index-prefix-octets base f) '(1)))
                   (count (fn2-run-index-count-octets base f))))
           :in-theory (e/d (fn2-run-layout-encode fn2-run-index-encoder-checks fn2-run-parent-index-emitter
                           fn2-run-overview-index-write-room-p fn2-run-index-digest-octets)
                     (fn2-overview-index-size fn2-overview-index-encode fn2-overview-index-emit-group
                      fn2-run-index-count-octets fn2-run-index-prefix-octets fn2-layout-octets fn2-run-unload-values
                      fn-b3-octet-listp fn2-layout-range-code fn2-run-load-bytes fn2-run-read-bytes fn2-layout-copy
                      fn2-fields-value fn2-fields-ref-len fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off
                      len binary-append fn2-pool-base unsigned-byte-p)))))
