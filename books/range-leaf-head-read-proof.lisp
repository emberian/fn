; The selected address on a stored leaf supplies the actual row that the
; range merge unloads, including the line associated with that key.
(in-package "ACL2")
(include-book "range-stored-row-proof")
(include-book "range-stored-leaf-row-proof")

(local
 (defthm fn2-run-unload-at-delivery
   (let* ((path (fn2-run-path-row c 0)) (base (+ rb *fn2-run-reader-entry*))
          (step (fn2-run-step-deliver c 3 i at slot gen unit counter rb 9 0 1 curs paths f pool)))
     (implies (and (< path (fn2-run-paths-rows paths)) (< i (fn2-run-paths-entries path paths)) (posp at)
                   (fn2-run-overview-row-atp 0 row base slot gen at (fn2-run-directory rb f) 9 0 1 f pool))
              (equal (fn2-run-unload-values *fn2-overview-entry* base (mv-nth 2 step) pool) row)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-range-unloads-stored-overview-row (base (+ rb *fn2-run-reader-entry*))
                          (off at) (end (fn2-run-directory rb f))))
            :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-run-step-deliver posp eq not mv-nth car-cons cdr-cons
                          (:e equal) (:e mv-nth) (:e zp) (:e consp) (:e unary--) (:e binary-+)))))))

(defthm fn2-range-leaf-reads-lower-bound
  (let* ((n (fn2-run-page-restart-count rb f)) (query (fn2-overview-range-key-at qbase f))
         (i (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0)))
         (seek (fn2-run-seek 3 0 fuel 0 n 0 0 qbase rb slot gen 9 0 1 qk qs qg f pool))
         (path (fn2-run-path-row c 0))
         (step (fn2-run-step-deliver c 3 (mv-nth 3 seek) (mv-nth 4 seek) slot gen unit counter rb 9 0 1
                                     curs paths (mv-nth 5 seek) pool)))
    (implies (and (natp fuel) (< (+ (integer-length n) *fn2-run-restart-interval* 1) fuel)
                  (consp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (unsigned-byte-p 32 (len rows)) (< i (len rows))
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (natp c) (< c (fn2-run-cursors-rows curs)) (< path (fn2-run-paths-rows paths))
                  (equal (fn2-run-paths-entries path paths) (len rows))
                  (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows 0 rb slot gen 9 0 1 f pool))
             (and (equal (car step) :entry)
                  (equal (fn2-run-unload-values *fn2-overview-entry* (+ rb *fn2-run-reader-entry*) (mv-nth 2 step) pool)
                         (nth i rows)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-stored-leaf-locates-head (pk 9) (ps 0) (pg 1))
                 (:instance fn2-run-stored-leaf-supplies-source-head (pk 9) (ps 0) (pg 1) (j 0))
                 (:instance fn2-run-unload-at-delivery
                    (row (nth (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows (fn2-overview-range-key-at qbase f) 0)) rows))
                    (i (mv-nth 3 (fn2-run-seek 3 0 fuel 0 (fn2-run-page-restart-count rb f) 0 0 qbase rb slot gen 9 0 1 qk qs qg f pool)))
                    (at (mv-nth 4 (fn2-run-seek 3 0 fuel 0 (fn2-run-page-restart-count rb f) 0 0 qbase rb slot gen 9 0 1 qk qs qg f pool)))
                    (f (mv-nth 5 (fn2-run-seek 3 0 fuel 0 (fn2-run-page-restart-count rb f) 0 0 qbase rb slot gen 9 0 1 qk qs qg f pool)))))
           :in-theory (union-theories (theory 'minimal-theory) '((:e <) (:e equal) (:e natp) (:e not))))))
