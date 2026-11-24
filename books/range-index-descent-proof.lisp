; Follow the child chosen by page search, using the fields and cursor
; returned by that search. Retain the right siblings on a lower-bound miss.
(in-package "ACL2")
(include-book "range-index-partition-proof")
(include-book "range-index-address-proof")
(include-book "range-page-search-state-proof")
(include-book "range-stored-child-proof")

(local
 (defthm fn2-range-selected-row-fits-cursor
   (implies (and (natp i) (< i n) (unsigned-byte-p 32 n)) (unsigned-byte-p 32 i))))

(local
 (defthm fn2-range-index-level-fits-cursor
   (implies (and (posp level) (< level *fn2-run-max-levels*)) (unsigned-byte-p 8 level))
   :rule-classes nil))

(local
 (defthm fn2-range-follow-indexed-address
   (let* ((page (nth k child-pages))
          (step (fn2-run-step-child c 3 t level 2 slot gen lo hi k off unit counter rb pk ps pg
                                    curs paths (fn2-run-run-cache-all pages cache) f pool))
          (after (mv-nth 1 step)))
     (implies (and (fn2-range-index-addresses-p rows child-pages)
                   (natp k) (< k (len rows)) (unsigned-byte-p 32 (len rows))
                   (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool)
                   (fn2-fieldsp f) (fn2-run-readerp rb f) (posp level) (< level *fn2-run-max-levels*)
                   (fn2-run-page-addressp page) (member-equal page pages) (posp (fn2-run-cache-rows cache))
                   (fn2-run-cache-compatible-pages-p page pages (fn2-run-cache-rows cache))
                   (natp c) (< c (fn2-run-cursors-rows curs)) (< (fn2-run-path-row c level) (fn2-run-paths-rows paths)))
              (and (equal (car step) :more)
                   (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-header*)
                   (equal (fn2-run-cursors-level c after) (1- level))
                   (equal (fn2-run-cursors-slot c after) (nth 3 page)) (equal (fn2-run-cursors-gen c after) (nth 4 page))
                   (equal (fn2-run-cursors-unit c after) (nth 1 page)) (equal (fn2-run-cursors-counter c after) (nth 2 page)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-selected-row-fits-cursor (i k) (n (len rows)))
                  (:instance fn2-range-index-address-at (index rows) (pages child-pages) (i k))
                  (:instance fn2-run-cursor-follows-stored-index-row (idx k) (parent unit) (alloc counter)
                             (ok pk) (os ps) (og pg) (page (nth k child-pages))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defmacro fn2-range-index-search-step ()
   '(fn2-run-step-seek c 3 nil level fuel 0 (fn2-run-page-restart-count rb f) 0 0 qbase slot gen unit counter
                       rb pk ps pg qk qs qg curs f pool)))

(defthm fn2-range-index-search-descends-to-selected-child
  (let* ((query (fn2-overview-range-key-at qbase f))
         (page (nth (fn2-range-index-child-at rows query) child-pages))
         (search (fn2-run-step-seek c 3 nil level fuel 0 (fn2-run-page-restart-count rb f) 0 0 qbase slot gen unit counter
                                   rb pk ps pg qk qs qg curs f pool)) (positioned (mv-nth 1 search))
         (k (fn2-run-cursors-idx c positioned)) (remaining (nthcdr k children))
         (step (fn2-run-step-child c 3 t level 2 slot gen (fn2-run-cursors-lo c positioned)
                      (fn2-run-cursors-hi c positioned) k (fn2-run-cursors-off c positioned)
                      unit counter rb pk ps pg positioned paths (fn2-run-run-cache-all pages cache) (mv-nth 2 search) pool))
         (after (mv-nth 1 step)))
    (implies (and (consp rows) (unsigned-byte-p 32 (len rows))
                  (fn2-range-index-addresses-p rows child-pages) (fn2-range-indexes-children-p rows children)
                  (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (fn2-run-sorted-spec *fn2-overview-range-key* (append-lst children))
                  (natp c) (< c (fn2-run-cursors-rows curs)) (posp level) (< level *fn2-run-max-levels*)
                  (< (fn2-run-path-row c level) (fn2-run-paths-rows paths))
                  (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                  (fn2-run-page-addressp page) (member-equal page pages)
                  (posp (fn2-run-cache-rows cache))
                  (fn2-run-cache-compatible-pages-p page pages (fn2-run-cache-rows cache))
                  (natp fuel) (< (+ (integer-length (fn2-run-page-restart-count rb f)) *fn2-run-restart-interval* 1) fuel)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
             (and (equal (car search) :more)
                  (equal (fn2-run-cursors-phase c positioned) *fn2-run-cursor-phase-child*)
                  (equal (car step) :more)
                  (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-header*)
                  (equal (fn2-run-cursors-level c after) (1- level))
                  (equal (fn2-run-cursors-slot c after) (nth 3 page))
                  (equal (fn2-run-cursors-gen c after) (nth 4 page))
                  (equal (fn2-run-cursors-unit c after) (nth 1 page))
                  (equal (fn2-run-cursors-counter c after) (nth 2 page))
                  (equal (fn2-run-from-spec *fn2-overview-range-key* (append-lst children) query)
                         (append (fn2-run-from-spec *fn2-overview-range-key* (car remaining) query)
                                 (append-lst (cdr remaining)))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-stored-index-selects-lower-bound-child fn2-range-stored-index-preserves-run-suffix
                 (:instance fn2-range-cursor-search-keeps-stored-page
                   (left nil) (lo 0) (hi (fn2-run-page-restart-count rb f)) (idx 0) (off 0))
                 fn2-range-index-level-fits-cursor
                 (:instance fn2-range-follow-indexed-address
                   (curs (mv-nth 1 (fn2-range-index-search-step))) (f (mv-nth 2 (fn2-range-index-search-step)))
                   (lo (fn2-run-cursors-lo c (mv-nth 1 (fn2-range-index-search-step))))
                   (hi (fn2-run-cursors-hi c (mv-nth 1 (fn2-range-index-search-step))))
                   (k (fn2-run-cursors-idx c (mv-nth 1 (fn2-range-index-search-step))))
                   (off (fn2-run-cursors-off c (mv-nth 1 (fn2-range-index-search-step))))))
           :in-theory (theory 'minimal-theory))))
