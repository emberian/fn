; The parent writer records a fitting index entry and its restart. Its
; previous-key decoder rereads the bytes just emitted for the child.
(in-package "ACL2")
(include-book "runs-index-encode-proof")
(include-book "runs-overview-builder-proof")

(local
 (defthm fn2-run-index-span-length
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn2-run-sized-index-write
   (let ((row (fn2-run-unload-values *fn2-overview-index* base f pool)))
     (implies (fn2-run-overview-index-write-room-p base dst dg off f pool)
              (equal (len (fn2-layout-octets *fn2-overview-index* row)) (fn2-overview-index-size base f))))
   :hints (("Goal" :use fn2-run-index-wire-segments
            :in-theory (e/d (fn2-run-overview-index-write-room-p)
                  (fn2-overview-index-size fn2-run-unload-values fn2-layout-octets fn2-run-index-prefix-octets
                   fn2-run-index-count-octets fn2-run-index-digest-octets fn2-layout-range-code fn2-pool-base
                   fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-off fn2-fields-ref-gen fn2-fields-ref-len
                   fn-b3-octet-listp unsigned-byte-p binary-append len))))))

(local
 (defthm fn2-run-index-admitted-bytes
   (implies (fn2-run-values-layoutp layout row)
            (fn-b3-octet-listp (fn2-layout-octets layout row)))
   :hints (("Goal" :in-theory (e/d (fn2-run-values-layoutp) (fn2-layout-parse fn2-layout-octets fn-b3-octet-listp))))))

(local (defthm fn2-run-proper-index-octets (implies (fn-b3-octet-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn2-run-written-index-is-readable
   (let* ((bytes (fn2-layout-octets *fn2-overview-index* row)) (end (+ off (len bytes)))
          (load (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)) (after (mv-nth 1 load))
          (read (fn2-run-layout-decode 3 level prev dst dg off end 9 0 1 f after)))
     (implies (and (posp level) (fn2-run-values-layoutp *fn2-overview-index* row)
                   (natp prev) (<= (+ prev (len *fn2-overview-index*)) (fn2-fields-rows f))
                   (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base dst pool))
                   (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)
                   (equal (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok))
              (and (equal (car read) :ok) (equal (mv-nth 1 read) end))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-load-bytes-roundtrip (bytes (fn2-layout-octets *fn2-overview-index* row))
                     (slot dst) (gen dg) (pk 9) (ps 0) (pg 1) (cap (+ off (len (fn2-layout-octets *fn2-overview-index* row)))))
                  (:instance fn2-run-writable-end-readable-prefix (slot dst) (gen dg) (pk 9) (ps 0) (pg 1)
                    (end (+ off (len (fn2-layout-octets *fn2-overview-index* row))))
                    (cap (+ off (len (fn2-layout-octets *fn2-overview-index* row))))
                    (pool (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-overview-index* row) dst dg off 9 0 1 pool))))
                  (:instance fn2-run-overview-page-row-boundary (base prev) (slot dst) (gen dg) (pk 9) (ps 0) (pg 1)
                    (end (+ off (len (fn2-layout-octets *fn2-overview-index* row))))
                    (pool (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-overview-index* row) dst dg off 9 0 1 pool)))))
            :in-theory (disable fn2-run-values-layoutp fn2-layout-octets fn2-run-load-bytes fn2-run-layout-decode
                                fn2-layout-range-code fn2-run-read-bytes fn2-pool-base fn2-poolp fn2-pool-wfp
                                fn2-fields-rows fn-b3-octet-listp true-list-fix)))))

(local
 (defthm fn2-run-index-output-window
   (let ((size (fn2-overview-index-size base f)))
     (implies (fn2-run-overview-index-write-room-p base dst dg off f pool)
              (and (natp (fn2-pool-base dst pool)) (unsigned-byte-p 32 off) (unsigned-byte-p 32 (+ off size))
                   (equal (fn2-layout-range-code dst dg off (+ off size) t 9 0 1 pool) :ok))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                '(fn2-run-overview-index-write-room-p))))))

(local
 (defthm fn2-run-index-previous-row-space
   (let ((prev (+ (nfix (fn2-run-writers-fields w writers)) *fn2-run-prev-fields*)))
     (implies (equal (fn2-run-add-ready w 3 base writers restarts f pool) :ok)
              (and (natp prev) (<= (+ prev (len *fn2-overview-index*)) (fn2-fields-rows f)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-add-ready)
                             (fn2-run-add-check fn2-run-layout-size fn2-run-roomp fn2-run-layout-compare
                              fn2-run-writers-level fn2-run-writers-fields fn2-run-writers-prev fn2-fields-rows
                              fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen nfix))))))

(local
 (defthm fn2-run-parent-decoder-reads-encoded-index
   (let* ((row (fn2-run-unload-values *fn2-overview-index* base f pool))
          (enc (fn2-run-layout-encode 3 level base dst dg off 9 0 1 f pool))
          (end (mv-nth 1 enc))
          (read (fn2-run-layout-decode 3 level prev dst dg off end 9 0 1 f (mv-nth 2 enc))))
     (implies (and (posp level) (fn2-run-overview-index-write-room-p base dst dg off f pool)
                   (fn2-run-values-layoutp *fn2-overview-index* row) (fn2-poolp pool) (fn2-pool-wfp pool)
                   (natp prev) (<= (+ prev (len *fn2-overview-index*)) (fn2-fields-rows f)))
              (and (equal (car enc) :ok) (unsigned-byte-p 32 end)
                   (equal (car read) :ok) (equal (mv-nth 1 read) end))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-index-output-window fn2-run-sized-index-write fn2-run-overview-index-encode-writes-layout
                  (:instance fn2-run-written-index-is-readable (row (fn2-run-unload-values *fn2-overview-index* base f pool))))
            :in-theory (union-theories (theory 'minimal-theory) '((:e len) (:e equal)))))))

(defthmd fn2-run-parent-appends-index-row
  (let* ((level (fn2-run-writers-level w writers)) (dst (fn2-run-writers-slot w writers))
         (dg (fn2-run-writers-gen w writers)) (off (fn2-run-writers-cursor w writers))
         (row (fn2-run-unload-values *fn2-overview-index* base f pool))
         (bytes (fn2-layout-octets *fn2-overview-index* row)) (end (+ off (len bytes)))
         (idx (fn2-run-writers-entries w writers)) (nr (fn2-run-writers-restarts w writers))
         (restartp (equal (mod idx *fn2-run-restart-interval*) 0))
         (add (fn2-run-add w 3 base writers restarts f pool)) (after (mv-nth 1 add)))
    (implies (and (posp level) (fn2-run-overview-index-write-room-p base dst dg off f pool)
                  (fn2-run-values-layoutp *fn2-overview-index* row) (fn2-poolp pool) (fn2-pool-wfp pool)
                  (equal (fn2-run-writers-okind w writers) 9) (equal (fn2-run-writers-oslot w writers) 0)
                  (equal (fn2-run-writers-ogen w writers) 1) (natp nr) (< nr *fn2-run-restart-capacity*)
                  (unsigned-byte-p 32 (1+ idx)) (equal (fn2-run-add-ready w 3 base writers restarts f pool) :ok))
             (and (equal (car add) :ok) (equal (fn2-run-writers-cursor w after) end)
                  (equal (fn2-run-writers-entries w after) (1+ idx))
                  (equal (fn2-run-writers-restarts w after) (if restartp (1+ nr) nr))
                  (implies restartp (equal (fn2-run-restarts-offset (+ (* w *fn2-run-restart-capacity*) nr) (mv-nth 2 add)) off))
                  (equal (mv-nth 4 add) (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)))
                  (equal (fn2-run-read-bytes (len bytes) dst dg off 9 0 1 (mv-nth 4 add)) bytes))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-index-previous-row-space (:instance fn2-run-append-stores-encoded-row (sid 3))
                 (:instance fn2-run-parent-decoder-reads-encoded-index (level (fn2-run-writers-level w writers))
                   (dst (fn2-run-writers-slot w writers)) (dg (fn2-run-writers-gen w writers))
                   (off (fn2-run-writers-cursor w writers)) (prev (+ (nfix (fn2-run-writers-fields w writers)) *fn2-run-prev-fields*)))
                 (:instance fn2-run-overview-index-encode-writes-layout (level (fn2-run-writers-level w writers))
                   (dst (fn2-run-writers-slot w writers)) (dg (fn2-run-writers-gen w writers)) (off (fn2-run-writers-cursor w writers)))
                 (:instance fn2-run-sized-index-write (dst (fn2-run-writers-slot w writers))
                   (dg (fn2-run-writers-gen w writers)) (off (fn2-run-writers-cursor w writers))))
           :in-theory (union-theories (theory 'minimal-theory) '(eq not (:e len) (:e equal) commutativity-of-+)))))
