; The next cursor phase can read the same stored page after any search slice.
(in-package "ACL2")
(include-book "range-stored-restarts-proof")
(include-book "range-page-search-fields-proof")

(local
 (defthm fn2-range-search-keeps-page-metadata
   (let ((after (mv-nth 5 (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))))
     (implies (and (fn2-fieldsp f) (fn2-run-readerp rb f))
              (and (equal (fn2-run-directory rb after) (fn2-run-directory rb f))
                   (equal (fn2-run-page-entry-count rb after) (fn2-run-page-entry-count rb f))
                   (equal (fn2-run-page-restart-count rb after) (fn2-run-page-restart-count rb f))
                   (fn2-fieldsp after) (fn2-run-readerp rb after)
                   (equal (fn2-fields-rows after) (fn2-fields-rows f)))))
   :hints (("Goal" :use ((:instance fn2-run-seek-shape (sid 3) (lv level) (steps fuel)
                            (fn2-fields f) (fn2-pool pool)))
            :in-theory (e/d (fn2-range-page-search-keeps-earlier-scalar fn2-run-header-value
                             fn2-run-directory fn2-run-readerp)
                       (fn2-fields-rows fn2-fieldsp fn2-fields-wfp fn2-run-seek fn2-fields-value nfix))))))

(local
 (defthm fn2-range-search-keeps-stored-page
   (let ((after (mv-nth 5 (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))))
     (implies (and (fn2-fieldsp f) (fn2-run-readerp rb f)
                   (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
              (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg after pool)))
   :hints (("Goal" :use ((:instance fn2-run-page-rows-use-field-count (base (+ rb *fn2-run-reader-entry*))
                        (off *fn2-run-entries-base*) (end (fn2-run-directory rb f))
                        (f2 (mv-nth 5 (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))))
            :in-theory (e/d (fn2-run-stored-overview-page-p)
               (fn2-run-directory fn2-run-header-value fn2-run-overview-page-rowsp fn2-run-restart-offsets-spec
                fn2-run-read-bytes fn2-run-directory-octets fn2-poolp fn2-pool-wfp fn2-layout-range-code
                fn2-pool-base fn2-fields-rows fn2-run-seek fn2-fieldsp fn2-run-readerp len))))))

(defthmd fn2-range-cursor-search-keeps-stored-page
  (let* ((step (fn2-run-step-seek c 3 left level fuel lo hi idx off qbase slot gen unit counter
                                  rb pk ps pg qk qs qg curs f pool))
         (after (mv-nth 2 step)))
    (implies (and (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
             (and (fn2-fieldsp after) (fn2-run-readerp rb after)
                  (equal (fn2-run-cursors-rows (mv-nth 1 step)) (fn2-run-cursors-rows curs))
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg after pool))))
  :hints (("Goal" :cases (left)
           :in-theory (e/d (fn2-run-step-seek)
               (fn2-run-seek fn2-run-cursor-save fn2-run-cursors-rows fn2-run-stored-overview-page-p
                fn2-run-readerp fn2-fieldsp nfix)))))
