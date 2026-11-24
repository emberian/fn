; An overlay loaded in ascending order stores the concatenated row bytes
; starting at zero. Each index offset is the size of the preceding rows.
(in-package "ACL2")
(include-book "range-stored-entry-bytes-proof")
(include-book "range-stored-page-rows-proof")
(include-book "range-overlay-row-proof")

(defun-nx fn2-ov-prefix-offsets-p (n rows b ix)
  (if (zp n) t
    (let ((j (1- n)))
      (and (equal (fn2-overlay-index-off (+ b j) ix)
                  (fn2-run-row-offset j *fn2-overview-entry* rows 0))
           (fn2-ov-prefix-offsets-p j rows b ix)))))

(defun-nx fn2-ov-contiguous-arena-p (rows o ov ix pool)
  (let* ((slot (fn2-overlays-slot o ov)) (gen (fn2-overlays-gen o ov)) (end (fn2-overlays-fill o ov))
         (bytes (fn2-run-entries-octets *fn2-overview-entry* rows)))
    (and (equal (fn2-overlays-count o ov) (len rows)) (equal end (len bytes))
         (unsigned-byte-p 32 end) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
         (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
         (equal (fn2-overlays-okind o ov) 9) (equal (fn2-overlays-oslot o ov) 0) (equal (fn2-overlays-ogen o ov) 1)
         (equal (fn2-layout-range-code slot gen 0 end nil 9 0 1 pool) :ok)
         (equal (fn2-run-read-bytes end slot gen 0 9 0 1 pool) bytes)
         (fn2-ov-prefix-offsets-p (len rows) rows (fn2-overlays-ibase o ov) ix))))

(local
 (defthm fn2-ov-addresses-contiguous-rows
   (let* ((slot (fn2-overlays-slot o ov)) (gen (fn2-overlays-gen o ov)) (end (fn2-overlays-fill o ov))
          (pk (fn2-overlays-okind o ov)) (ps (fn2-overlays-oslot o ov)) (pg (fn2-overlays-ogen o ov)))
     (implies (and (natp n) (<= n (len rows)) (fn2-ov-prefix-offsets-p n rows (fn2-overlays-ibase o ov) ix)
                   (fn2-run-overview-page-rowsp 0 rows eb slot gen 0 end pk ps pg f pool))
              (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)))
   :hints (("Goal" :induct (fn2-ov-indexed-rows-p n rows o eb ov ix f pool) :do-not '(preprocess)
            :in-theory (e/d (fn2-ov-indexed-row-p) (fn2-run-overview-row-atp fn2-run-overview-page-rowsp fn2-run-row-offset
                        fn2-overlays-slot fn2-overlays-gen fn2-overlays-fill fn2-overlays-ibase fn2-overlay-index-off
                        fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen len nth)))
           (and (equal (access clause-id id :pool-lst) '(1))
                (equal (len (access clause-id id :case-lst)) 1) (equal (access clause-id id :primes) 0)
                '(:use ((:instance fn2-run-overview-page-suffix (i (1- n)) (level 0) (base eb) (off 0)
                        (slot (fn2-overlays-slot o ov)) (gen (fn2-overlays-gen o ov)) (end (fn2-overlays-fill o ov))
                        (pk (fn2-overlays-okind o ov)) (ps (fn2-overlays-oslot o ov)) (pg (fn2-overlays-ogen o ov)))))))))

(defthm fn2-ov-contiguous-arena-supplies-reader
  (implies (and (fn2-ov-contiguous-arena-p rows o ov ix pool) (fn2-run-entries-layoutp *fn2-overview-entry* rows)
                (natp eb) (<= (+ eb 5) (fn2-fields-rows f)))
           (fn2-ov-indexed-rows-p (len rows) rows o eb ov ix f pool))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-addresses-contiguous-rows (n (len rows)))
                 (:instance fn2-run-entry-bytes-supply-stored-rows (level 0) (base eb) (off 0)
                    (slot (fn2-overlays-slot o ov)) (gen (fn2-overlays-gen o ov)) (end (fn2-overlays-fill o ov))
                    (pk 9) (ps 0) (pg 1)))
           :in-theory (e/d (fn2-ov-contiguous-arena-p)
                     (fn2-ov-addresses-contiguous-rows fn2-ov-indexed-rows-p fn2-run-overview-page-rowsp fn2-ov-prefix-offsets-p
                      fn2-run-entries-octets fn2-run-entries-layoutp fn2-run-read-bytes fn2-layout-range-code fn2-pool-base
                      fn2-poolp fn2-pool-wfp fn2-fields-rows fn2-overlays-slot fn2-overlays-gen fn2-overlays-fill fn2-overlays-ibase
                      fn2-overlays-count fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen len unsigned-byte-p)))))
