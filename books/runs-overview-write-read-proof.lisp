; The actual row loader, leaf encoder, and page decoder agree on the written byte interval.
(in-package "ACL2")
(include-book "runs-overview-emit-proof")
(include-book "runs-overview-cursor-proof")
(include-book "runs-overview-source-proof")

(local
 (defthm fn2-run-true-list-fix-octets
 (implies (fn-b3-octet-listp bytes) (equal (true-list-fix bytes) bytes))))

(local
 (defthm fn2-run-admitted-wire-octets
 (implies (fn2-run-values-layoutp layout row)
          (and (fn-b3-octet-listp (fn2-layout-octets layout row))
               (equal (true-list-fix (fn2-layout-octets layout row)) (fn2-layout-octets layout row))))
 :hints (("Goal" :use ((:instance fn2-run-true-list-fix-octets
                               (bytes (fn2-layout-octets layout row))))
          :in-theory (e/d (fn2-run-values-layoutp)
                          (fn-b3-octet-listp fn2-layout-parse fn2-layout-octets true-list-fix))))))

(local
 (defthm fn2-run-loaded-overview-wire-decodes
 (let* ((bytes (fn2-layout-octets *fn2-overview-entry* row)) (end (+ off (len bytes)))
        (load (fn2-run-load-bytes bytes slot gen off 9 0 1 pool))
        (after (mv-nth 1 load))
        (read (fn2-run-layout-decode 3 0 rb slot gen off end 9 0 1 fields after)))
  (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row)
                (natp rb) (<= (+ rb (len *fn2-overview-entry*)) (fn2-fields-rows fields))
                (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)
                (eq (fn2-layout-range-code slot gen off end t 9 0 1 pool) :ok))
           (and (equal (car load) :ok)
                (equal (car read) :ok) (equal (mv-nth 1 read) end))))
 :rule-classes nil
 :hints (("Goal" :use
          ((:instance fn2-run-load-bytes-roundtrip
             (bytes (fn2-layout-octets *fn2-overview-entry* row))
             (cap (+ off (len (fn2-layout-octets *fn2-overview-entry* row)))) (pk 9) (ps 0) (pg 1))
           (:instance fn2-run-writable-end-readable-prefix
             (pool (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-overview-entry* row) slot gen off 9 0 1 pool)))
             (end (+ off (len (fn2-layout-octets *fn2-overview-entry* row))))
             (cap (+ off (len (fn2-layout-octets *fn2-overview-entry* row)))) (pk 9) (ps 0) (pg 1))
           (:instance fn2-run-overview-page-row-boundary (level 0) (base rb) (f fields)
             (end (+ off (len (fn2-layout-octets *fn2-overview-entry* row)))) (pk 9) (ps 0) (pg 1)
             (pool (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-overview-entry* row) slot gen off 9 0 1 pool)))))
          :in-theory (disable fn2-run-values-layoutp fn2-layout-octets fn2-run-load-bytes fn2-run-layout-decode
                              fn2-layout-range-code fn2-run-read-bytes fn2-pool-base fn2-poolp fn2-pool-wfp
                              fn2-fields-rows fn-b3-octet-listp true-list-fix)))))

(local
 (defthm fn2-run-overview-reader-consumes-writer-output
  (let* ((i (+ base 4)) (src (fn2-fields-ref-slot i f)) (sg (fn2-fields-ref-gen i f))
         (at (fn2-fields-ref-off i f)) (n (fn2-fields-ref-len i f))
         (size (fn2-overview-entry-size base f)) (end (+ off size))
         (source (+ at (fn2-pool-base src pool))) (target (+ off (fn2-pool-base dst pool)))
         (bytes (fn2-layout-octets *fn2-overview-entry*
                  (fn2-run-unload-values *fn2-overview-entry* base f pool)))
         (actual (fn2-run-layout-encode 3 0 base dst dg off 9 0 1 f pool))
         (read (fn2-run-layout-decode 3 0 rb dst dg off (mv-nth 1 actual) 9 0 1 rf (mv-nth 2 actual))))
    (implies (and (fn2-run-values-layoutp *fn2-overview-entry* (fn2-run-unload-values *fn2-overview-entry* base f pool))
                  (natp rb) (<= (+ rb (len *fn2-overview-entry*)) (fn2-fields-rows rf))
                  (natp base) (natp (fn2-fields-value base f))
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
             (and (equal (car actual) :ok) (equal (car read) :ok)
                  (equal (mv-nth 1 actual) (+ off (len bytes)))
                  (equal (mv-nth 1 read) (mv-nth 1 actual)))))
  :rule-classes nil
  :hints (("Goal" :use
            (fn2-run-overview-leaf-encode-writes-layout fn2-run-overview-wire-size
             (:instance fn2-run-loaded-overview-wire-decodes
               (slot dst) (gen dg) (fields rf)
               (row (fn2-run-unload-values *fn2-overview-entry* base f pool))))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(eq not commutativity-of-+ (:e equal)))))))

(local
 (defthm fn2-run-fifth-row-value
 (equal (nth 4 row) (car (cddddr row)))
 :hints (("Goal" :expand ((:free (x) (nth 4 x)) (:free (x) (nth 3 x))
                          (:free (x) (nth 2 x)) (:free (x) (nth 1 x)) (:free (x) (nth 0 x)))))))

(defthm fn2-run-adapter-source-wire-readback
 (let* ((line (nth 4 row)) (n (len line)) (bytes (fn2-layout-octets *fn2-overview-entry* row))
        (size (len bytes)) (end (+ off size)) (source (+ at (fn2-pool-base src pool)))
        (target (+ off (fn2-pool-base dst pool)))
        (load (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))
        (sf (mv-nth 2 load)) (sp (mv-nth 3 load))
        (write (fn2-run-layout-encode 3 0 base dst dg off 9 0 1 sf sp))
        (read (fn2-run-layout-decode 3 0 rb dst dg off (mv-nth 1 write) 9 0 1 rf (mv-nth 2 write))))
  (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row) (natp base) (natp rb)
                (<= (+ rb (len *fn2-overview-entry*)) (fn2-fields-rows rf))
                (fn2-poolp pool) (fn2-pool-wfp pool) (natp src) (natp dst) (not (equal src dst))
                (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                (unsigned-byte-p 32 off) (unsigned-byte-p 32 at) (unsigned-byte-p 32 end)
                (or (<= (+ source n) target) (<= (+ target size) source))
                (equal (fn2-layout-range-code src sg at (+ at n) t 9 0 1 pool) :ok)
                (equal (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok))
           (and (equal (car load) :ok) (equal (car write) :ok) (equal (car read) :ok)
                (equal (mv-nth 1 write) end) (equal (mv-nth 1 read) end)
                (equal (fn2-run-read-bytes size dst dg off 9 0 1 (mv-nth 2 write)) bytes))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :use
          (fn2-run-admitted-line-fits-source
           (:instance fn2-run-overview-source-fields (slot src) (gen sg) (off at))
           (:instance fn2-run-load-overview-roundtrip (slot src) (gen sg) (off at) (cap (+ at (len (nth 4 row)))))
           (:instance fn2-run-overview-wire-size
              (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool)))
              (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))))
           (:instance fn2-run-overview-leaf-encode-writes-layout
              (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool)))
              (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))))
           (:instance fn2-run-overview-reader-consumes-writer-output
              (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool)))
              (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))))
           (:instance fn2-run-writable-end-readable-prefix (slot src) (gen sg) (off at)
              (cap (+ at (len (nth 4 row)))) (end (+ at (len (nth 4 row)))) (pk 9) (ps 0) (pg 1)
              (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool)))))
          :in-theory (disable natp unsigned-byte-p fn2-layout-octets fn2-run-unload-values fn2-run-values-layoutp fn2-fields-rows
                              fn2-run-load-values fn2-run-layout-encode fn2-run-layout-decode fn2-run-load-bytes
                              fn2-run-read-bytes fn2-layout-range-code fn2-overview-entry-size
                              fn2-poolp fn2-pool-wfp fn2-pool-base fn2-fields-value
                              fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len nth))))
