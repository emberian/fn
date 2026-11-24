; Scanning the five fields of a stored overview installs the physical
; reference read by the range adapter to recover the complete line.
(in-package "ACL2")
(include-book "runs-overview-wire-parts-proof")
(include-book "runs-scan-prefix-proof")
(include-book "runs-scan-line-proof")

(defun-nx fn2-run-line-at (i f pool)
  (fn2-run-read-bytes (fn2-fields-ref-len i f) (fn2-fields-ref-slot i f)
                      (fn2-fields-ref-gen i f) (fn2-fields-ref-off i f) 9 0 1 pool))

(local
 (defthm fn2-run-line-at-store
   (implies (and (natp i) (< i (fn2-fields-rows f)) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                 (unsigned-byte-p 32 off) (unsigned-byte-p 32 size))
            (equal (fn2-run-line-at i (fn2-layout-store i 0 slot gen off size 0 f) pool)
                   (fn2-run-read-bytes size slot gen off 9 0 1 pool)))
   :hints (("Goal" :in-theory (e/d (fn2-run-line-at fn2-layout-store fn2-fields-ref-slot fn2-fields-ref-gen
                                    fn2-fields-ref-off fn2-fields-ref-len nth-update-nth)
                                   (fn2-run-read-bytes fn2-fields-rows nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-run-readable-line-subrange
   (implies (and (natp at) (natp bound) (<= off at) (<= at bound) (<= bound end)
                 (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok))
            (eq (fn2-layout-range-code slot gen at bound nil pk ps pg pool) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code)
                         (fn2-pool-readable-code fn2-pool-slot-base fn2-pool-slot-fill fn2-pool-capacity-bytes))))))

(local
 (defthm fn2-run-scan-attaches-stored-line
   (let* ((n (len line)) (header (fn2-layout-varoctets n)) (off (+ at (len header))) (bound (+ off n))
          (scan (fn2-layout-scan '((line (:octets 1024))) fuel i 0 0 0 0 0 0 at slot gen end 9 0 1 f pool)))
     (implies (and (natp i) (< i (fn2-fields-rows f)) (natp at) (natp fuel)
                   (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 end)
                   (<= n 1024) (<= (+ (len header) n) fuel) (<= bound end)
                   (natp (fn2-pool-base slot pool))
                   (eq (fn2-layout-range-code slot gen at bound nil 9 0 1 pool) :ok)
                   (equal (fn2-run-read-bytes (+ (len header) n) slot gen at 9 0 1 pool) (append header line)))
              (and (equal (car scan) :ok) (equal (mv-nth 8 scan) bound)
                   (equal (fn2-run-line-at i (mv-nth 9 scan) pool) line))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-scan-stored-line (pk 9) (ps 0) (pg 1)))
            :in-theory (disable fn2-run-line-at fn2-layout-store fn2-layout-varoctets fn2-run-read-bytes
                                fn2-layout-range-code fn2-pool-base fn2-fields-rows binary-append)))))

(local
 (defthm fn2-run-read-two-checked-segments
   (implies (and (natp off) (natp n) (natp m) (<= (+ off n m) end)
                 (equal (fn2-layout-range-code slot gen off end nil 9 0 1 pool) :ok))
            (and (equal (fn2-layout-range-code slot gen off (+ off n) nil 9 0 1 pool) :ok)
                 (equal (fn2-layout-range-code slot gen (+ off n) (+ off n m) nil 9 0 1 pool) :ok)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-readable-line-subrange (at off) (bound (+ off n)) (pk 9) (ps 0) (pg 1))
                         (:instance fn2-run-readable-line-subrange (at (+ off n)) (bound (+ off n m)) (pk 9) (ps 0) (pg 1)))
            :in-theory (disable fn2-run-readable-line-subrange fn2-layout-range-code)))))

(local
 (defthm fn2-run-scan-ids-and-line
   (let* ((layout (fn2-run-overview-id-layout)) (prefix (fn2-layout-octets layout ids))
          (header (fn2-layout-varoctets (len line))) (at (+ off (len prefix))) (m (+ (len header) (len line)))
          (bound (+ at m))
          (scan (fn2-layout-scan *fn2-overview-entry* fuel base 0 0 0 0 0 0 off slot gen end 9 0 1 f pool)))
     (implies (and (fn2-run-values-layoutp layout ids) (<= (len line) 1024)
                   (natp base) (<= (+ 5 base) (fn2-fields-rows f)) (natp fuel) (<= (+ (len prefix) m) fuel)
                   (natp off) (unsigned-byte-p 32 end) (<= bound end) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                   (equal (fn2-layout-range-code slot gen off at nil 9 0 1 pool) :ok)
                   (equal (fn2-layout-range-code slot gen at bound nil 9 0 1 pool) :ok)
                   (equal (fn2-run-read-bytes (len prefix) slot gen off 9 0 1 pool) prefix)
                   (equal (fn2-run-read-bytes m slot gen at 9 0 1 pool) (append header line)))
              (and (equal (car scan) :ok) (equal (mv-nth 8 scan) bound)
                   (equal (fn2-run-line-at (+ base 4) (mv-nth 9 scan) pool) line))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-page-scan-consumes-admitted-row (layout (fn2-run-overview-id-layout)) (row ids) (pk 9) (ps 0) (pg 1))
                  (:instance fn2-run-scan-attaches-stored-line (i (+ 4 base))
                   (at (+ off (len (fn2-layout-octets (fn2-run-overview-id-layout) ids))))
                   (fuel (- fuel (len (fn2-layout-octets (fn2-run-overview-id-layout) ids))))
                   (f (mv-nth 9 (fn2-layout-scan (fn2-run-overview-id-layout) fuel base 0 0 0 0 0 0 off slot gen end 9 0 1 f pool))))
                  (:instance fn2-run-scan-through-field-prefix (prefix (fn2-run-overview-id-layout))
                   (suffix '((line (:octets 1024)))) (pk 9) (ps 0) (pg 1) (i base)
                   (pos 0) (v 0) (hi 0) (size 0) (ref 0) (phase 0) (next off)))
            :in-theory (disable fn2-run-readable-line-subrange fn2-run-line-at fn2-run-values-layoutp fn2-layout-octets
                                fn2-run-read-bytes fn2-layout-varoctets fn2-fields-rows fn2-layout-range-code
                                fn2-pool-base fn2-poolp fn2-pool-wfp binary-append unsigned-byte-p)))))

(defthm fn2-run-overview-scan-recovers-line
  (let* ((wire (fn2-layout-octets *fn2-overview-entry* row)) (bound (+ off (len wire)))
         (scan (fn2-layout-scan *fn2-overview-entry* fuel base 0 0 0 0 0 0 off slot gen end 9 0 1 f pool)))
    (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row)
                  (natp base) (<= (+ 5 base) (fn2-fields-rows f)) (natp fuel) (<= (len wire) fuel)
                  (natp off) (unsigned-byte-p 32 end) (<= bound end) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen off end nil 9 0 1 pool) :ok)
                  (equal (fn2-run-read-bytes (len wire) slot gen off 9 0 1 pool) wire))
             (and (equal (car scan) :ok) (equal (mv-nth 8 scan) bound)
                  (equal (fn2-run-line-at (+ base 4) (mv-nth 9 scan) pool) (nth 4 row)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-overview-stored-parts (pk 9) (ps 0) (pg 1))
                 (:instance fn2-run-read-two-checked-segments (n (len (fn2-layout-octets (fn2-run-overview-id-layout) (take 4 row))))
                    (m (+ (len (fn2-layout-varoctets (len (nth 4 row)))) (len (nth 4 row)))))
                 (:instance fn2-run-scan-ids-and-line (ids (take 4 row)) (line (nth 4 row))))
           :in-theory (disable fn2-run-line-at fn2-run-read-bytes fn2-layout-octets fn2-layout-varoctets
                               fn2-run-values-layoutp fn2-fields-rows fn2-pool-base fn2-pool-wfp fn2-poolp
                               fn2-layout-range-code binary-append nth take))))
