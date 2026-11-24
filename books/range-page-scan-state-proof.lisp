; The query, page metadata, and readable suffix survive a row decode.
(in-package "ACL2")
(include-book "range-page-search-proof")

(defun-nx fn2-run-overview-next-offset (level row off)
 (+ off (len (fn2-layout-octets (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*) row))))

(defun-nx fn2-run-overview-page-rowsp (level rows base slot gen off end pk ps pg f pool)
 (if (atom rows) (equal off end)
   (and (fn2-run-overview-row-atp level (car rows) base slot gen off end pk ps pg f pool)
        (fn2-run-overview-page-rowsp level (cdr rows) base slot gen
          (fn2-run-overview-next-offset level (car rows) off) end pk ps pg f pool))))

(defthm fn2-run-page-rows-use-field-count
 (implies (equal (fn2-fields-rows f2) (fn2-fields-rows f))
          (equal (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f2 pool)
                 (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool)
          :in-theory (e/d (fn2-run-overview-row-atp)
            (fn2-run-overview-next-offset fn2-run-values-layoutp unsigned-byte-p fn2-layout-octets
             fn2-run-read-bytes fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code fn2-fields-rows)))))

(defmacro fn2-run-page-entry-count (rb f)
 `(fn2-run-header-value ,rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-entries*) ,f))

(local
 (defthm fn2-run-page-row-keeps-earlier-value
 (implies (and (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f pool)
               (natp target) (< target base))
          (equal (fn2-fields-value target (mv-nth 2 (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)))
                 (fn2-fields-value target f)))
 :rule-classes nil
 :hints (("Goal" :use (fn2-run-overview-page-row-keeps-query)
          :in-theory (e/d (fn2-run-overview-row-atp)
              (fn2-run-layout-decode fn2-run-values-layoutp nth fn2-layout-octets fn2-fields-value fn2-run-read-bytes
               fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code fn2-fields-rows unsigned-byte-p))))))

(local
 (defthm fn2-run-decoding-keeps-search-state
 (let* ((base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))
        (read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)) (rf (mv-nth 2 read)))
  (implies (and (natp rb) (natp qbase) (< (1+ qbase) base)
                (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f pool))
           (and (equal (fn2-run-page-entry-count rb rf) (fn2-run-page-entry-count rb f))
                (equal (fn2-run-directory rb rf) end)
                (equal (fn2-overview-range-key-at qbase rf) (fn2-overview-range-key-at qbase f)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-page-row-keeps-earlier-value (target qbase) (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)))
                 (:instance fn2-run-page-row-keeps-earlier-value (target (1+ qbase)) (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)))
                 (:instance fn2-run-page-row-keeps-earlier-value (target (+ rb *fn2-format-page-header-field-payload-length*)) (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)))
                 (:instance fn2-run-page-row-keeps-earlier-value (target (+ rb *fn2-run-c-header-fields* *fn2-run-page-header-field-restarts*)) (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)))
                 (:instance fn2-run-page-row-keeps-earlier-value (target (+ rb *fn2-run-c-header-fields* *fn2-run-page-header-field-entries*)) (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))))
          :in-theory (e/d (fn2-overview-range-key-at fn2-run-header-value fn2-run-directory)
                      (fn2-run-overview-row-atp fn2-run-values-layoutp nth fn2-layout-octets fn2-run-read-bytes fn2-poolp fn2-pool-wfp
                       fn2-fields-value fn2-run-layout-decode unsigned-byte-p fn2-pool-base fn2-layout-range-code
                       fn2-fields-rows nfix))))))

(defthm fn2-run-overview-page-scan-tail
 (let* ((base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))
        (next (fn2-run-overview-next-offset level (car rows) off))
        (read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)) (rf (mv-nth 2 read)))
  (implies (and (natp rb) (natp qbase) (< (1+ qbase) base) (consp rows)
                (fn2-fieldsp f) (fn2-fields-wfp f)
                (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool))
           (and (natp next) (< off next) (<= next end)
                (fn2-run-overview-row-atp level (car rows) base slot gen off end pk ps pg f pool)
                (fn2-run-overview-page-rowsp level (cdr rows) base slot gen next (fn2-run-directory rb rf) pk ps pg rf pool)
                (equal (fn2-run-page-entry-count rb rf) (fn2-run-page-entry-count rb f))
                (equal (fn2-run-directory rb rf) end)
                (equal (fn2-overview-range-key-at qbase rf) (fn2-overview-range-key-at qbase f)))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (off end base) (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool)))
          :use ((:instance fn2-run-overview-next-row-offset (row (car rows)) (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)))
                (:instance fn2-run-decoding-keeps-search-state (row (car rows)))
                (:instance fn2-run-page-rows-use-field-count (rows (cdr rows))
                  (off (fn2-run-overview-next-offset level (car rows) off)) (base (+ rb *fn2-run-reader-entry*))
                  (end (fn2-run-directory rb f))
                  (f2 (mv-nth 2 (fn2-run-layout-decode 3 level (+ rb *fn2-run-reader-entry*) slot gen off (fn2-run-directory rb f) pk ps pg f pool)))))
          :in-theory (e/d (fn2-run-overview-next-offset)
                  (fn2-run-overview-row-atp fn2-run-overview-page-rowsp fn2-layout-octets fn2-fields-rows fn2-fieldsp
                   fn2-fields-wfp fn2-run-header-value fn2-run-directory fn2-run-layout-decode fn2-overview-range-key-at)))))
