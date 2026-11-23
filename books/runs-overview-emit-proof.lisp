; The overview writer emits the layout's ID fields and line length in base 128.
(in-package "ACL2")
(include-book "runs-served")
(include-book "runs-page-copy-proof")

(defthmd fn2-run-varint-writes-layout-octets
  (let* ((bytes (fn2-layout-varoctets v))
         (load (fn2-run-load-bytes bytes slot gen off pk ps pg pool))
         (write (fn2-codec-emit-varint v slot gen off pk ps pg pool)))
    (implies (and (natp v) (natp off))
             (and (equal (car write) (car load))
                  (equal (mv-nth 2 write) (mv-nth 1 load))
                  (implies (eq (car load) :ok)
                           (equal (mv-nth 1 write) (+ off (len bytes)))))))
  :hints (("Goal" :induct (fn2-codec-emit-varint v slot gen off pk ps pg pool)
           :expand ((fn2-layout-varoctets v))
           :in-theory (e/d (fn2-codec-emit-varint fn2-run-load-bytes)
                           (fn2-pool-write fn2-layout-varoctets mod floor)))))

(local
 (defun-nx fn2-run-overview-prefix-octets (base f)
  (append (fn2-layout-varoctets (fn2-fields-value base f))
          (fn2-layout-varoctets (fn2-fields-value (+ base 1) f))
          (fn2-layout-varoctets (fn2-fields-value (+ base 2) f))
          (fn2-layout-varoctets (fn2-fields-value (+ base 3) f))
          (fn2-layout-varoctets (fn2-fields-ref-len (+ base 4) f)))))

(local
 (defthm fn2-run-bytes-append-length (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn2-run-overview-emit-prefix
  (let* ((h (fn2-run-overview-prefix-octets base f)) (next (+ off (len h)))
         (head (fn2-run-load-bytes h dst dg off pk ps pg pool))
         (i (+ base 4)) (n (fn2-fields-ref-len i f))
         (copy (fn2-layout-copy (fn2-fields-ref-slot i f) (fn2-fields-ref-gen i f)
                                (fn2-fields-ref-off i f) dst dg next n pk ps pg (mv-nth 1 head)))
         (actual (fn2-overview-entry-emit-group base dst dg off off pk ps pg f pool)))
    (implies (and (natp base) (natp off) (natp (fn2-fields-value base f))
                  (natp (fn2-fields-value (+ base 1) f)) (natp (fn2-fields-value (+ base 2) f))
                  (natp (fn2-fields-value (+ base 3) f)) (natp n)
                  (eq (car head) :ok) (eq (car copy) :ok))
             (and (equal (car actual) :ok) (equal (mv-nth 1 actual) (+ next n))
                  (equal (mv-nth 2 actual) (mv-nth 1 copy)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-run-overview-prefix-octets fn2-overview-entry-emit-group
                            fn2-overview-entry-emit-number fn2-overview-entry-emit-article
                            fn2-overview-entry-emit-position fn2-overview-entry-emit-line
                            fn2-run-varint-writes-layout-octets fn2-run-load-byte-segments)
                           (fn2-codec-emit-varint fn2-run-load-bytes fn2-layout-copy
                            fn2-fields-value fn2-fields-ref-len fn2-layout-varoctets
                            fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off binary-append))))))

(local
 (defthm fn2-run-read-bytes-length
  (equal (len (fn2-run-read-bytes n src sg at pk ps pg pool)) (nfix n))
  :hints (("Goal" :induct (fn2-run-read-bytes n src sg at pk ps pg pool)
           :in-theory (disable fn2-pool-read)))))

(local
 (defthm fn2-run-varoctets-size
  (equal (len (fn2-layout-varoctets v)) (fn2-layout-varsize v))
  :hints (("Goal" :induct (fn2-layout-varsize v)))))

(local
 (defthm fn2-run-varoctets-octets
  (implies (natp v) (fn-b3-octet-listp (fn2-layout-varoctets v)))
  :hints (("Goal" :induct (fn2-layout-varoctets v)))))

(local
 (defthm fn2-run-octets-concatenate
  (implies (and (fn-b3-octet-listp a) (fn-b3-octet-listp b))
           (fn-b3-octet-listp (append a b)))))

(local
 (defthm fn2-run-byte-segments-associate
  (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn2-run-append-nil-to-bytes
  (implies (true-listp xs) (equal (append xs nil) xs))))

(local
 (defthm fn2-run-overview-wire-and-size
  (let* ((h (fn2-run-overview-prefix-octets base f)) (i (+ base 4))
         (n (fn2-fields-ref-len i f)) (body (fn2-run-read-bytes n (fn2-fields-ref-slot i f)
                             (fn2-fields-ref-gen i f) (fn2-fields-ref-off i f) 9 0 1 pool)))
    (implies (and (natp base) (natp n)
                  (natp (fn2-fields-value base f)) (natp (fn2-fields-value (+ base 1) f))
                  (natp (fn2-fields-value (+ base 2) f)) (natp (fn2-fields-value (+ base 3) f)))
             (and (fn-b3-octet-listp h)
                  (equal (fn2-overview-entry-size base f) (+ (len h) n))
                  (equal (fn2-layout-octets *fn2-overview-entry*
                            (fn2-run-unload-values *fn2-overview-entry* base f pool))
                         (append h body)))))
  :hints (("Goal" :in-theory
           (e/d (fn2-run-overview-prefix-octets fn2-run-unload-values fn2-layout-octets
                 fn2-layout-field-octets fn2-overview-entry-size fn2-overview-entry-size-group
                 fn2-overview-entry-size-number fn2-overview-entry-size-article
                 fn2-overview-entry-size-position fn2-overview-entry-size-line)
                (fn2-layout-varoctets fn2-layout-varsize fn2-run-read-bytes
                 fn2-fields-value fn2-fields-ref-len fn2-fields-ref-slot fn2-fields-ref-gen
                 fn2-fields-ref-off binary-append fn-b3-octet-listp))))))

(local
 (defthm fn2-run-readable-first-octet
  (implies (and (natp at) (posp n) (natp (fn2-pool-base src pool))
                (eq (fn2-layout-range-code src sg at (+ at n) nil pk ps pg pool) :ok))
           (and (equal (car (fn2-pool-read src sg at pk ps pg pool)) :ok)
                (equal (fn2-layout-range-code src sg (+ 1 at) (+ at n) nil pk ps pg pool) :ok)))
  :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-read fn2-pool-slot-base
                                    fn2-pool-slot-fill fn2-pool-capacity-bytes)
                                  (fn2-pool-readable-code fn2-pool-base fn2-pool-fill fn2-pool-data-length))))))

(local
 (defthm fn2-run-read-returns-byte
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool))
           (unsigned-byte-p 8 (mv-nth 1 (fn2-pool-read src sg at pk ps pg pool))))
  :hints (("Goal" :in-theory (enable fn2-pool-read)))))

(local
 (defthm fn2-run-read-range-octets
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool)
                (natp n) (natp at) (natp (fn2-pool-base src pool))
                (eq (fn2-layout-range-code src sg at (+ at n) nil pk ps pg pool) :ok))
           (fn-b3-octet-listp (fn2-run-read-bytes n src sg at pk ps pg pool)))
  :hints (("Goal" :induct (fn2-run-read-bytes n src sg at pk ps pg pool)
           :in-theory (e/d (fn2-run-read-bytes)
                           (fn2-poolp fn2-pool-wfp fn2-layout-range-code
                            fn2-pool-base fn2-pool-read fn2-run-read-returns-byte)))
          ("Subgoal *1/2" :use (fn2-run-read-returns-byte fn2-run-readable-first-octet)))))

(local
 (defthm fn2-run-true-list-fix-octets
 (implies (fn-b3-octet-listp bytes) (equal (true-list-fix bytes) bytes))))

(local
 (defthm fn2-run-overview-encode-checked
 (let* ((i (+ base 4)) (n (fn2-fields-ref-len i f)) (at (fn2-fields-ref-off i f))
        (src (fn2-fields-ref-slot i f)) (sg (fn2-fields-ref-gen i f)))
  (implies (and (unsigned-byte-p 32 off) (<= n 1024) (not (equal src dst))
                (eq (fn2-layout-range-code src sg at (+ at n) nil 9 0 1 pool) :ok)
                (eq (fn2-layout-range-code dst dg off (+ off (fn2-overview-entry-size base f)) t 9 0 1 pool) :ok))
           (equal (fn2-run-layout-encode 3 0 base dst dg off 9 0 1 f pool)
                  (fn2-overview-entry-emit-group base dst dg off off 9 0 1 f pool))))
 :hints (("Goal" :in-theory (e/d (fn2-run-layout-encode fn2-overview-entry-encode fn2-overview-entry-check-values
                            fn2-overview-entry-check-group fn2-overview-entry-check-number
                            fn2-overview-entry-check-article fn2-overview-entry-check-position
                            fn2-overview-entry-check-line)
                           (fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                            fn2-layout-range-code fn2-overview-entry-emit-group fn2-overview-entry-size unsigned-byte-p))))))

(defthm fn2-run-overview-leaf-encode-writes-layout
  (let* ((i (+ base 4)) (src (fn2-fields-ref-slot i f)) (sg (fn2-fields-ref-gen i f))
         (at (fn2-fields-ref-off i f)) (n (fn2-fields-ref-len i f))
         (size (fn2-overview-entry-size base f)) (end (+ off size))
         (source (+ at (fn2-pool-base src pool))) (target (+ off (fn2-pool-base dst pool)))
         (bytes (fn2-layout-octets *fn2-overview-entry*
                  (fn2-run-unload-values *fn2-overview-entry* base f pool)))
         (actual (fn2-run-layout-encode 3 0 base dst dg off 9 0 1 f pool)))
    (implies (and (natp base) (natp (fn2-fields-value base f))
                  (natp (fn2-fields-value (+ base 1) f)) (natp (fn2-fields-value (+ base 2) f))
                  (natp (fn2-fields-value (+ base 3) f))
                  (fn2-poolp pool) (fn2-pool-wfp pool)
                  (natp src) (natp dst) (not (equal src dst))
                  (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)
                  (unsigned-byte-p 32 at) (natp n) (<= n 1024)
                  (or (<= (+ source n) target) (<= (+ target size) source))
                  (eq (fn2-layout-range-code src sg at (+ at n) nil 9 0 1 pool) :ok)
                  (eq (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok))
             (and (equal (car actual) :ok)
                  (equal (mv-nth 1 actual) end)
                  (equal (mv-nth 2 actual) (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)))
                  (equal (fn2-run-read-bytes size dst dg off 9 0 1 (mv-nth 2 actual)) bytes))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t :use
           ((:instance fn2-run-overview-emit-prefix (pk 9) (ps 0) (pg 1))
            (:instance fn2-run-write-prefix-and-payload
              (header (fn2-run-overview-prefix-octets base f)) (pk 9) (ps 0) (pg 1)
              (src (fn2-fields-ref-slot (+ base 4) f)) (sg (fn2-fields-ref-gen (+ base 4) f))
              (at (fn2-fields-ref-off (+ base 4) f)) (n (fn2-fields-ref-len (+ base 4) f)))
            (:instance fn2-run-load-bytes-roundtrip
              (bytes (append (fn2-run-overview-prefix-octets base f)
                       (fn2-run-read-bytes (fn2-fields-ref-len (+ base 4) f)
                         (fn2-fields-ref-slot (+ base 4) f) (fn2-fields-ref-gen (+ base 4) f)
                         (fn2-fields-ref-off (+ base 4) f) 9 0 1 pool)))
              (slot dst) (gen dg) (pk 9) (ps 0) (pg 1) (cap (+ off (fn2-overview-entry-size base f)))))
           :in-theory (disable fn2-run-layout-encode fn2-run-load-byte-segments fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off
                            fn2-fields-ref-len fn2-pool-base fn2-poolp fn2-pool-wfp fn2-layout-range-code
                            fn2-run-read-bytes fn2-run-load-bytes fn2-run-unload-values fn2-layout-octets
                            fn2-layout-copy fn2-run-overview-prefix-octets fn2-overview-entry-emit-group
                            fn2-overview-entry-size fn-b3-octet-listp binary-append true-list-fix))))
