; Every suffix of a stored overview page starts after the serialized prefix.
(in-package "ACL2")
(include-book "range-page-scan-state-proof")
(include-book "runs-restart-row-offset-proof")

(local
 (defun-nx fn2-run-overview-suffix-induct (i level rows off)
   (if (or (zp i) (atom rows)) off
     (fn2-run-overview-suffix-induct (1- i) level (cdr rows)
                                    (fn2-run-overview-next-offset level (car rows) off)))))

(defthmd fn2-run-overview-page-suffix
  (let* ((layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
         (at (fn2-run-row-offset i layout rows off)))
    (implies (and (natp i) (<= i (len rows)) (natp off)
                  (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool))
             (and (natp at) (<= off at)
                  (fn2-run-overview-page-rowsp level (nthcdr i rows) base slot gen at end pk ps pg f pool)
                  (implies (< i (len rows))
                           (and (< at end)
                                (fn2-run-overview-row-atp level (nth i rows) base slot gen at end pk ps pg f pool))))))
  :hints (("Goal" :induct (fn2-run-overview-suffix-induct i level rows off)
           :expand ((len rows) (nthcdr i rows) (nth i rows)
                    (:free (layout) (fn2-run-row-offset i layout rows off))
                    (:free (start) (fn2-run-overview-page-rowsp level rows base slot gen start end pk ps pg f pool)))
           :in-theory (e/d (fn2-run-overview-next-offset)
                        (fn2-run-overview-row-atp fn2-run-overview-page-rowsp fn2-layout-octets fn2-run-row-offset)))
          ("Subgoal *1/1" :use ((:instance fn2-run-overview-next-row-offset (row (car rows)))))
          ("Subgoal *1/2" :use ((:instance fn2-run-overview-next-row-offset (row (car rows)))))))
