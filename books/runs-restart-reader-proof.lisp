; The run reader recovers a restart word from the same four bytes the writer emits.
(in-package "ACL2")
(include-book "runs-page-window-proof")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defun-nx fn2-run-four-octet-value (bytes)
  (+ (nth 0 bytes) (* 256 (nth 1 bytes)) (* 65536 (nth 2 bytes))
     (* 16777216 (nth 3 bytes))))

(defthm fn2-run-four-octet-value-of-word
  (implies (unsigned-byte-p 32 v)
           (equal (fn2-run-four-octet-value (fn2-layout-le 4 v)) v))
  :hints (("Goal" :expand ((:free (x) (fn2-layout-le 4 x)) (:free (x) (fn2-layout-le 3 x))
                    (:free (x) (fn2-layout-le 2 x)) (:free (x) (fn2-layout-le 1 x))
                    (:free (x) (fn2-layout-le 0 x))) :in-theory (enable mod))
          ("Goal''" :in-theory (enable floor))))

(local
 (defthm fn2-run-restart-value-after-store
   (implies (and (natp base) (< base (fn2-fields-rows f)) (unsigned-byte-p 60 v)
                 (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))
            (equal (fn2-fields-value base (fn2-layout-store base v slot gen 0 0 0 f)) v))
   :hints (("Goal" :in-theory (e/d (fn2-layout-store fn2-fields-value fn2-fields-set-value
                       update-fn2-fields-value$ai nth-update-nth)
                      (fn2-fields-rows unsigned-byte-p nth update-nth))))))

(local
 (defthm fn2-run-restart-value-after-save
   (equal (fn2-fields-value i (fn2-codec-save base ph pos v hi size ref payload next f))
          (fn2-fields-value i f))
   :hints (("Goal" :in-theory (e/d (fn2-codec-save fn2-fields-value) (nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-run-restart-read-byte
   (let ((read (fn2-pool-read slot gen (+ off j) pk ps pg pool)))
     (implies (and (natp off) (natp j) (< j 4) (natp (fn2-pool-base slot pool))
                   (equal (fn2-layout-range-code slot gen off (+ 4 off) nil pk ps pg pool) :ok))
              (equal (car read) :ok)))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-read fn2-pool-slot-base
                                     fn2-pool-slot-fill fn2-pool-capacity-bytes)
                                   (fn2-pool-readable-code fn2-pool-base fn2-pool-fill fn2-pool-data-length))))))

(local
 (defthm fn2-run-restart-scan-word
   (let* ((scan (fn2-run-restart-scan 4096 base 0 0 0 0 0 0 0 off slot gen (+ off 4) pk ps pg f pool))
          (word (fn2-run-four-octet-value (fn2-run-read-bytes 4 slot gen off pk ps pg pool))))
     (implies (and (natp base) (< base (fn2-fields-rows f)) (natp off)
                   (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                   (equal (fn2-layout-range-code slot gen off (+ 4 off) nil pk ps pg pool) :ok))
              (and (equal (car scan) :ok) (equal (mv-nth 1 scan) (+ off 4))
                   (equal (fn2-fields-value base (mv-nth 2 scan)) word))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :expand ((:free (v at f) (fn2-run-restart-scan 4096 base 0 0 v 0 0 0 0 at slot gen (+ 4 off) pk ps pg f pool))
                     (:free (v at f) (fn2-run-restart-scan 4095 base 0 1 v 0 0 0 0 at slot gen (+ 4 off) pk ps pg f pool))
                     (:free (v at f) (fn2-run-restart-scan 4094 base 0 2 v 0 0 0 0 at slot gen (+ 4 off) pk ps pg f pool))
                     (:free (v at f) (fn2-run-restart-scan 4093 base 0 3 v 0 0 0 0 at slot gen (+ 4 off) pk ps pg f pool))
                     (:free (v at f) (fn2-run-restart-scan 4092 base 1 0 v 0 0 0 0 at slot gen (+ 4 off) pk ps pg f pool))
                     (:free (at) (fn2-run-read-bytes 0 slot gen at pk ps pg pool))
                     (:free (at) (fn2-run-read-bytes 1 slot gen at pk ps pg pool))
                     (:free (at) (fn2-run-read-bytes 2 slot gen at pk ps pg pool))
                     (:free (at) (fn2-run-read-bytes 3 slot gen at pk ps pg pool))
                     (:free (at) (fn2-run-read-bytes 4 slot gen at pk ps pg pool)))
            :use ((:instance fn2-run-reader-octet (next (+ off 0)))
                  (:instance fn2-run-reader-octet (next (+ off 1)))
                  (:instance fn2-run-reader-octet (next (+ off 2)))
                  (:instance fn2-run-reader-octet (next (+ off 3)))
                  (:instance fn2-run-restart-read-byte (j 0)) (:instance fn2-run-restart-read-byte (j 1))
                  (:instance fn2-run-restart-read-byte (j 2)) (:instance fn2-run-restart-read-byte (j 3)))
            :in-theory (e/d (fn2-run-restart-scan fn2-run-restart-byte fn2-run-reader-octet
                               fn2-run-reader-nfix fn2-run-read-bytes ash)
                       (fn2-layout-range-code fn2-pool-read fn2-layout-store fn2-fields-value fn2-fields-rows
                        fn2-codec-save fn2-poolp fn2-pool-wfp fn2-pool-base mod))))))

(defthm fn2-run-restart-decode-reads-offset
  (let* ((read (fn2-run-restart-decode base slot gen off (+ 4 off) pk ps pg f pool)))
    (implies (and (natp base) (< base (fn2-fields-rows f)) (natp off) (unsigned-byte-p 32 (+ 4 off))
                  (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 v)
                  (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen off (+ 4 off) nil pk ps pg pool) :ok)
                  (equal (fn2-run-read-bytes 4 slot gen off pk ps pg pool) (fn2-layout-le 4 v)))
             (and (equal (car read) :ok) (equal (mv-nth 1 read) (+ off 4))
                  (equal (fn2-fields-value base (mv-nth 2 read)) v))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-run-restart-scan-word (f (fn2-run-restart-start base f))))
           :in-theory (e/d (fn2-run-restart-start fn2-run-restart-decode fn2-run-restart-decode-step fn2-run-reader-start-coordinates)
                       (fn2-layout-scan fn2-codec-save fn2-layout-le fn2-run-four-octet-value
                        fn2-run-restart-scan fn2-layout-range-code fn2-run-read-bytes fn2-fields-value
                        fn2-fields-decode-phase fn2-fields-decode-pos fn2-fields-decode-acc fn2-fields-decode-high
                        fn2-fields-decode-size fn2-fields-decode-ref fn2-fields-decode-payload fn2-fields-decode-next
                        fn2-fields-rows fn2-poolp fn2-pool-wfp fn2-pool-base)))))

(defthm fn2-run-restart-offset-reads-directory-word
  (let* ((dir (fn2-run-directory base fn2-fields)) (at (+ dir (* 4 j)))
         (read (fn2-run-restart-offset j slot gen base pk ps pg fn2-fields pool)))
    (implies (and (natp j) (< j (fn2-run-hdr base restarts))
                  (natp base) (< (+ base *fn2-run-reader-restart*) (fn2-fields-rows fn2-fields))
                  (natp dir) (unsigned-byte-p 32 (+ 4 at))
                  (unsigned-byte-p 32 v) (<= *fn2-run-entries-base* v) (< v dir)
                  (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen at (+ 4 at) nil pk ps pg pool) :ok)
                  (equal (fn2-run-read-bytes 4 slot gen at pk ps pg pool) (fn2-layout-le 4 v)))
             (and (equal (car read) :ok) (equal (mv-nth 1 read) v))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-run-restart-decode-reads-offset
                         (f fn2-fields) (off (+ (fn2-run-directory base fn2-fields) (* 4 j)))
                         (base (+ base *fn2-run-reader-restart*))))
           :in-theory (e/d (fn2-run-restart-offset)
                       (fn2-run-restart-decode fn2-run-directory fn2-run-header-value fn2-layout-range-code
                        fn2-run-read-bytes fn2-layout-le fn2-fields-value fn2-fields-rows
                        fn2-poolp fn2-pool-wfp fn2-pool-base)))))
