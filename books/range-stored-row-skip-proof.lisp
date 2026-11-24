; An indexed row access skips whole encodings from a restart, preserving
; the directory and landing at the requested row even for variable widths.
(in-package "ACL2")
(include-book "range-page-scan-state-proof")

(local
 (defun-nx fn2-run-overview-skip-walk (m rows level off rb slot gen pk ps pg f pool)
   (if (or (zp m) (atom rows)) (list off f)
     (let ((read (fn2-run-layout-decode 3 level (+ rb *fn2-run-reader-entry*) slot gen off
                                        (fn2-run-directory rb f) pk ps pg f pool)))
       (fn2-run-overview-skip-walk (1- m) (cdr rows) level (fn2-run-overview-next-offset level (car rows) off)
                                   rb slot gen pk ps pg (mv-nth 2 read) pool)))))

(defthmd fn2-run-skip-to-stored-overview-row
  (let* ((base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))
         (skip (fn2-run-skip 3 level m off slot gen rb pk ps pg f pool))
         (at (mv-nth 1 skip)) (after (mv-nth 2 skip)))
    (implies (and (natp m) (< m (len rows)) (natp rb) (fn2-fieldsp f) (fn2-fields-wfp f)
                  (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool))
             (and (equal (car skip) :ok)
                  (equal (fn2-run-directory rb after) end)
                  (fn2-run-overview-row-atp level (nth m rows) base slot gen at end pk ps pg after pool))))
  :hints (("Goal" :induct (fn2-run-overview-skip-walk m rows level off rb slot gen pk ps pg f pool)
           :do-not '(preprocess generalize fertilize eliminate-destructors)
           :expand ((len rows) (nth m rows)
                    (:free (n) (fn2-run-skip 3 level n off slot gen rb pk ps pg f pool)))
           :in-theory (e/d (fn2-run-overview-next-offset)
                     (fn2-run-skip fn2-run-layout-decode fn2-run-directory fn2-fields-wfp
                      fn2-run-header-value fn2-fields-value fn2-fieldsp fn2-fields-rows fn2-run-overview-page-rowsp fn2-layout-octets
                      fn2-run-overview-row-atp fn2-run-layout-compare fn2-run-key-order-spec fn2-overview-range-key-at)))
          ("Subgoal *1/1" :expand ((fn2-run-skip 3 level 0 off slot gen rb pk ps pg f pool) (:free (base end) (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool))))
          ("Subgoal *1/2" :use ((:instance fn2-run-overview-page-scan-tail (qbase 0))
                                (:instance fn2-run-overview-page-key-order (qbase 0) (row (car rows))
                                           (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)))))))
