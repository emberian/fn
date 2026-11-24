; One binary-search comparison reads a saved offset, then decodes and compares
; the overview row at that byte address.
(in-package "ACL2")
(include-book "runs-restart-fields-proof")
(include-book "range-page-lower-bound-proof")

(defun-nx fn2-run-page-restart-word-p (j at rb slot gen pk ps pg f pool)
  (let* ((dir (fn2-run-directory rb f)) (word (+ dir (* 4 j)))
         (count (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-restarts*) f)))
    (and (natp j) (< j count) (natp rb) (< (+ rb *fn2-run-reader-restart*) (fn2-fields-rows f))
         (natp dir) (unsigned-byte-p 32 (+ 4 word))
         (unsigned-byte-p 32 at) (<= *fn2-run-entries-base* at) (< at dir)
         (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
         (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
         (equal (fn2-layout-range-code slot gen word (+ word 4) nil pk ps pg pool) :ok)
         (equal (fn2-run-read-bytes 4 slot gen word pk ps pg pool) (fn2-layout-le 4 at)))))

(defthm fn2-run-page-restart-recovers-row
   (let ((read (fn2-run-restart-offset j slot gen rb pk ps pg f pool)))
     (implies (fn2-run-page-restart-word-p j at rb slot gen pk ps pg f pool)
              (and (equal (car read) :ok) (equal (mv-nth 1 read) at))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-restart-offset-reads-directory-word
                                     (base rb) (v at) (fn2-fields f)))
            :in-theory (disable fn2-run-restart-offset fn2-run-directory fn2-run-header-value fn2-fields-rows
                       fn2-layout-range-code fn2-layout-le fn2-run-read-bytes fn2-poolp fn2-pool-wfp fn2-pool-base))))

(local
 (defthm fn2-run-restart-preserves-row-view
   (let* ((end (fn2-run-directory rb f)) (base (+ rb *fn2-run-reader-entry*))
          (rf (mv-nth 2 (fn2-run-restart-offset j slot gen rb pk ps pg f pool))))
     (implies (and (fn2-fieldsp f) (fn2-run-readerp rb f)
                   (fn2-run-overview-row-atp level row base slot gen at end pk ps pg f pool))
              (fn2-run-overview-row-atp level row base slot gen at end pk ps pg rf pool)))
   :hints (("Goal" :in-theory (e/d (fn2-run-overview-row-atp)
                         (fn2-run-readerp fn2-fieldsp fn2-run-restart-offset fn2-fields-rows
                          fn2-run-directory fn2-layout-octets fn2-run-read-bytes fn2-run-values-layoutp
                          fn2-layout-range-code fn2-pool-base fn2-poolp fn2-pool-wfp unsigned-byte-p))))))

(defthmd fn2-run-overview-restart-comparison
  (let* ((dir (fn2-run-directory rb f)) (base (+ rb *fn2-run-reader-entry*))
         (restart (fn2-run-restart-offset j slot gen rb pk ps pg f pool)) (rf (mv-nth 2 restart))
         (read (fn2-run-layout-decode 3 level base slot gen (mv-nth 1 restart) dir pk ps pg rf pool))
         (after (mv-nth 2 read)) (query (fn2-overview-range-key-at qbase f)))
    (implies (and (fn2-fieldsp f) (fn2-run-readerp rb f) (natp rb) (natp qbase)
                  (< (+ qbase 1) (+ rb *fn2-run-reader-restart*))
                  (fn2-run-page-restart-word-p j at rb slot gen pk ps pg f pool)
                  (fn2-run-overview-row-atp level row base slot gen at dir pk ps pg f pool))
             (and (equal (car restart) :ok) (equal (mv-nth 1 restart) at)
                  (equal (car read) :ok)
                  (equal (fn2-run-layout-compare 3 base qbase pk ps pg qk qs qg after pool)
                         (list :ok (fn2-run-key-order-spec *fn2-overview-range-key* row query))))))
  :hints (("Goal" :use (fn2-run-page-restart-recovers-row fn2-run-restart-preserves-row-view fn2-run-restart-keeps-header-and-query
                        (:instance fn2-run-overview-page-key-order (base (+ rb *fn2-run-reader-entry*))
                                   (off at) (end (fn2-run-directory rb f))
                                   (f (mv-nth 2 (fn2-run-restart-offset j slot gen rb pk ps pg f pool)))))
           :in-theory (e/d (fn2-overview-range-key-at)
                        (fn2-run-page-restart-word-p fn2-run-overview-row-atp fn2-run-restart-offset
                         fn2-fields-value fn2-run-directory fn2-run-header-value fn2-run-readerp fn2-fieldsp
                         fn2-run-layout-compare fn2-run-layout-decode fn2-run-key-order-spec fn2-layout-octets)))))

(defthm fn2-run-seek-narrows-at-checked-restart
  (let* ((j (floor (+ lo hi) 2)) (dir (fn2-run-directory rb f)) (base (+ rb *fn2-run-reader-entry*))
         (rf (mv-nth 2 (fn2-run-restart-offset j slot gen rb pk ps pg f pool)))
         (after (mv-nth 2 (fn2-run-layout-decode 3 level base slot gen at dir pk ps pg rf pool)))
         (less (eq (fn2-run-key-order-spec *fn2-overview-range-key* row (fn2-overview-range-key-at qbase f)) :lt)))
    (implies (and (posp fuel) (natp lo) (natp hi) (< lo hi) (posp (fn2-run-page-entry-count rb f))
                  (fn2-fieldsp f) (fn2-run-readerp rb f) (natp rb) (natp qbase)
                  (< (+ qbase 1) (+ rb *fn2-run-reader-restart*))
                  (fn2-run-page-restart-word-p j at rb slot gen pk ps pg f pool)
                  (fn2-run-overview-row-atp level row base slot gen at dir pk ps pg f pool))
             (equal (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
                    (fn2-run-seek 3 level (1- fuel) (if less (1+ j) lo) (if less hi j)
                                  idx off qbase rb slot gen pk ps pg qk qs qg after pool))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-run-overview-restart-comparison (j (floor (+ lo hi) 2))))
           :expand ((fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))
           :in-theory (disable fn2-run-page-restart-word-p fn2-run-overview-row-atp fn2-run-restart-offset
                              fn2-overview-range-key-at fn2-run-directory fn2-run-header-value
                              fn2-run-readerp fn2-fieldsp fn2-run-layout-compare fn2-run-layout-decode
                              fn2-run-key-order-spec fn2-run-seek floor))))
