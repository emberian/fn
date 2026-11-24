; Decoding a restart and its entry preserves the header and query needed by
; the next binary comparison.
(in-package "ACL2")
(include-book "range-restart-probe-proof")

(defmacro fn2-run-page-restart-count (rb f)
  `(fn2-run-header-value ,rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-restarts*) ,f))

(defun-nx fn2-run-overview-restart-fields (level j at rb slot gen pk ps pg f pool)
  (let ((rf (mv-nth 2 (fn2-run-restart-offset j slot gen rb pk ps pg f pool))))
    (mv-nth 2 (fn2-run-layout-decode 3 level (+ rb *fn2-run-reader-entry*) slot gen at
                                     (fn2-run-directory rb f) pk ps pg rf pool))))

(local
 (defthm fn2-run-restart-entry-keeps-value
   (let* ((eb (+ rb *fn2-run-reader-entry*)) (dir (fn2-run-directory rb f))
          (rf (mv-nth 2 (fn2-run-restart-offset j slot gen rb pk ps pg f pool)))
          (out (fn2-run-overview-restart-fields level j at rb slot gen pk ps pg f pool)))
     (implies (and (natp rb) (natp target) (< target (+ rb *fn2-run-reader-restart*))
                   (fn2-fieldsp f) (fn2-run-readerp rb f)
                   (fn2-run-overview-row-atp level row eb slot gen at dir pk ps pg f pool))
              (and (equal (fn2-fields-value target rf) (fn2-fields-value target f))
                   (equal (fn2-fields-value target out) (fn2-fields-value target f)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-overview-page-row-keeps-query
                                    (base (+ rb *fn2-run-reader-entry*)) (off at) (end (fn2-run-directory rb f))
                                    (f (mv-nth 2 (fn2-run-restart-offset j slot gen rb pk ps pg f pool)))))
            :in-theory (e/d (fn2-run-overview-restart-fields fn2-run-overview-row-atp)
                      (fn2-run-restart-offset fn2-run-layout-decode fn2-run-directory fn2-fields-value
                       fn2-fields-rows fn2-run-values-layoutp fn2-layout-octets fn2-poolp fn2-pool-wfp
                       fn2-pool-base fn2-layout-range-code fn2-run-read-bytes unsigned-byte-p fn2-run-readerp fn2-fieldsp))))))

(defthmd fn2-run-restart-comparison-keeps-search-state
  (let* ((eb (+ rb *fn2-run-reader-entry*)) (dir (fn2-run-directory rb f))
         (out (fn2-run-overview-restart-fields level j at rb slot gen pk ps pg f pool)))
    (implies (and (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-overview-row-atp level row eb slot gen at dir pk ps pg f pool))
             (and (equal (fn2-run-directory rb out) dir)
                  (equal (fn2-run-page-entry-count rb out) (fn2-run-page-entry-count rb f))
                  (equal (fn2-run-page-restart-count rb out) (fn2-run-page-restart-count rb f))
                  (equal (fn2-overview-range-key-at qbase out) (fn2-overview-range-key-at qbase f))
                  (equal (fn2-fields-rows out) (fn2-fields-rows f))
                  (fn2-fieldsp out) (fn2-run-readerp rb out))))
  :hints (("Goal" :use ((:instance fn2-run-restart-entry-keeps-value (target (+ rb *fn2-format-page-header-field-payload-length*)))
                        (:instance fn2-run-restart-entry-keeps-value (target (+ rb *fn2-run-c-header-fields* *fn2-run-page-header-field-entries*)))
                        (:instance fn2-run-restart-entry-keeps-value (target (+ rb *fn2-run-c-header-fields* *fn2-run-page-header-field-restarts*)))
                        (:instance fn2-run-restart-entry-keeps-value (target qbase))
                        (:instance fn2-run-restart-entry-keeps-value (target (1+ qbase))))
           :in-theory (e/d (fn2-run-directory fn2-run-header-value fn2-overview-range-key-at
                            fn2-run-readerp fn2-run-overview-restart-fields)
                         (fn2-run-restart-offset fn2-run-layout-decode fn2-fields-value
                          fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-run-overview-row-atp nfix)))))
