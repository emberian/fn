; Follow the child reference read from the selected physical index row.
(in-package "ACL2")
(include-book "range-stored-nth-proof")
(include-book "runs-built-cache-proof")

(defthmd fn2-run-cursor-follows-stored-index-row
  (let* ((row (nth idx rows))
         (step (fn2-run-step-child c 3 t level 2 slot gen lo hi idx off parent alloc rb
                                   ok os og curs paths (fn2-run-run-cache-all pages cache) f pool))
         (after (mv-nth 1 step)))
    (implies (and (fn2-run-stored-overview-page-p rows level rb slot gen ok os og f pool)
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (posp level) (< level *fn2-run-max-levels*)
                  (unsigned-byte-p 32 idx) (< idx (len rows))
                  (equal (nth (+ 2 *fn2-format-ref-field-physical-unit*) row) (nth 1 page))
                  (equal (nth (+ 2 *fn2-format-ref-field-allocation*) row) (nth 2 page))
                  (fn2-run-page-addressp page) (member-equal page pages)
                  (posp (fn2-run-cache-rows cache))
                  (fn2-run-cache-compatible-pages-p page pages (fn2-run-cache-rows cache))
                  (natp c) (< c (fn2-run-cursors-rows curs))
                  (< (fn2-run-path-row c level) (fn2-run-paths-rows paths)))
             (and (equal (car step) :more)
                  (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-header*)
                  (equal (fn2-run-cursors-level c after) (1- level))
                  (equal (fn2-run-cursors-slot c after) (nth 3 page))
                  (equal (fn2-run-cursors-gen c after) (nth 4 page))
                  (equal (fn2-run-cursors-unit c after) (nth 1 page))
                  (equal (fn2-run-cursors-counter c after) (nth 2 page)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-cursor-descends-to-built-page (sid 3) (nkeys 2))
                 (:instance fn2-run-nth-reads-stored-scalar (j (+ 2 *fn2-format-ref-field-physical-unit*))
                            (k idx) (pk ok) (ps os) (pg og))
                 (:instance fn2-run-nth-reads-stored-scalar (j (+ 2 *fn2-format-ref-field-allocation*))
                            (k idx) (pk ok) (ps os) (pg og)))
           :in-theory (e/d (fn2-run-readerp)
                     (fn2-run-stored-overview-page-p fn2-run-page-addressp fn2-run-cache-compatible-pages-p
                      fn2-run-step-child fn2-run-run-cache-all fn2-run-nth fn2-run-path-row fn2-run-cursors-rows
                      fn2-run-paths-rows fn2-run-cache-rows fn2-run-cursors-phase fn2-run-cursors-level
                      fn2-run-cursors-slot fn2-run-cursors-gen fn2-run-cursors-unit fn2-run-cursors-counter
                      fn2-fields-value fn2-fieldsp fn2-fields-wfp fn2-fields-rows member-equal nth len)))))
