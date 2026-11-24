; Enter the search with the counts and directory decoded from this page.
(in-package "ACL2")
(include-book "runs-stored-headers-proof")
(include-book "runs-seek-budget-proof")

(local
 (defthm fn2-run-header-records-path-length
   (let* ((note (fn2-run-path-note c level slot gen unit counter count paths)) (r (fn2-run-path-row c level)))
     (implies (and (natp c) (natp level) (< level *fn2-run-max-levels*) (< r (fn2-run-paths-rows paths))
                   (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 60 unit)
                   (unsigned-byte-p 60 counter) (unsigned-byte-p 32 count))
              (and (equal (car note) :ok) (equal (fn2-run-paths-entries r (mv-nth 1 note)) count)
                   (equal (fn2-run-paths-idx r (mv-nth 1 note)) 0))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-path-note fn2-run-paths-entries fn2-run-paths-idx
                   fn2-run-paths-set-slot fn2-run-paths-set-gen fn2-run-paths-set-unit fn2-run-paths-set-counter
                   fn2-run-paths-set-idx fn2-run-paths-set-entries update-fn2-run-paths-entries$ai
                   update-fn2-run-paths-idx$ai nth-update-nth)
                   (fn2-run-path-row fn2-run-paths-rows unsigned-byte-p nth update-nth))))))

(defthmd fn2-run-stored-header-starts-page-search
  (let* ((step (fn2-run-step-header c level slot gen lo hi idx off unit counter rb pk ps pg curs paths f pool))
         (after (mv-nth 1 step)) (path (fn2-run-path-row c level)) (rf (mv-nth 3 step)))
    (implies (and (fn2-run-page-headers-p bvals cvals dir count nr slot gen pk ps pg pool)
                  (equal (nth *fn2-format-page-header-field-page-kind* bvals)
                         (fn2-run-layout-page-kind (fn2-run-cursors-schema c curs) level))
                  (natp rb) (<= (+ rb *fn2-run-reader-restart*) (fn2-fields-rows f))
                  (natp c) (< c (fn2-run-cursors-rows curs)) (unsigned-byte-p 8 level) (< level *fn2-run-max-levels*)
                  (< path (fn2-run-paths-rows paths)) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                  (unsigned-byte-p 32 nr) (unsigned-byte-p 32 count))
             (and (equal (car step) :more) (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-seek*)
                  (equal (fn2-run-cursors-lo c after) 0) (equal (fn2-run-cursors-hi c after) nr)
                  (equal (fn2-run-cursors-idx c after) 0) (equal (fn2-run-cursors-off c after) 0)
                  (equal (fn2-run-paths-entries path (mv-nth 2 step)) count)
                  (equal (fn2-run-paths-idx path (mv-nth 2 step)) 0)
                  (equal (fn2-run-directory rb rf) dir)
                  (equal rf (mv-nth 1 (fn2-run-read-header slot gen rb pk ps pg f pool))))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-reads-stored-page-headers (watch (+ rb *fn2-format-page-header-field-page-kind*)))
                 fn2-run-header-records-path-length
                 (:instance fn2-run-saved-cursor-position (phase *fn2-run-cursor-phase-seek*) (hi nr) (lo 0) (idx 0) (off 0)))
           :in-theory (e/d (fn2-run-step-header)
                     (fn2-run-page-headers-p fn2-run-read-header fn2-run-directory fn2-run-header-value
                      fn2-run-cursor-save fn2-run-path-note fn2-run-cursors-rows fn2-run-cursors-schema fn2-run-layout-page-kind
                      fn2-run-cursors-phase fn2-run-cursors-lo fn2-run-cursors-hi fn2-run-cursors-idx fn2-run-cursors-off
                      fn2-run-path-row fn2-run-paths-rows fn2-run-paths-idx fn2-run-paths-entries fn2-fields-rows
                      fn2-fields-value unsigned-byte-p nth)))))
