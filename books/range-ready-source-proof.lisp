; A stable set of positioned heads is ready for delivery at any budget.
(in-package "ACL2")
(include-book "range-head-pick-proof")

(defun-nx fn2-overview-sources-readyp (n base sources ov)
  (if (zp n) t
    (let* ((s (+ base (1- n))) (state (fn2-range-sources-state s sources))
           (o (fn2-range-sources-src s sources)))
      (and (< s (fn2-range-sources-rows sources))
           (or (equal state *fn2-range-state-head*) (equal state *fn2-range-state-end*))
           (implies (and (equal (fn2-range-sources-kind s sources) *fn2-range-kind-overlay*)
                         (< o (fn2-overlays-rows ov)))
                    (equal (fn2-overlays-count o ov) (fn2-range-sources-count s sources)))
           (fn2-overview-sources-readyp (1- n) base sources ov)))))

(defthmd fn2-overview-recheck-positioned-sources
  (implies (and (natp g) (< g (fn2-ranges-rows r))
                (fn2-overview-sources-readyp n (fn2-ranges-sbase g r) sources ov))
           (equal (fn2-range-recheck n g r sources ov) (list :ok sources)))
  :hints (("Goal" :induct (fn2-overview-sources-readyp n (fn2-ranges-sbase g r) sources ov)
           :expand ((fn2-range-recheck n g r sources ov))
           :in-theory (e/d (fn2-overview-sources-readyp)
                           (fn2-range-recheck fn2-range-sources-rows fn2-ranges-rows
                            fn2-ranges-sbase fn2-range-sources-kind fn2-range-sources-state
                            fn2-range-sources-src fn2-range-sources-count fn2-overlays-rows
                            fn2-overlays-count fn2-range-sources-set-state)))))

(defthmd fn2-overview-advance-positioned-sources
  (implies (and (natp g) (< g (fn2-ranges-rows r))
                (fn2-overview-sources-readyp n (fn2-ranges-sbase g r) sources ov))
           (equal (fn2-range-advance-all n g budget r sources ov ix runs curs paths cache f pool)
                  (list :ok sources curs paths f)))
  :hints (("Goal" :induct (fn2-overview-sources-readyp n (fn2-ranges-sbase g r) sources ov)
           :expand ((fn2-range-advance-all n g budget r sources ov ix runs curs paths cache f pool))
           :in-theory (e/d (fn2-overview-sources-readyp)
                           (fn2-range-advance-run fn2-range-advance-overlay fn2-range-advance-all
                            fn2-range-sources-rows fn2-ranges-rows fn2-ranges-sbase fn2-range-sources-state)))))

(defthmd fn2-overview-step-delivers-positioned-heads
  (let ((deliver (fn2-range-deliver g r sources f pool)))
    (implies (and (natp g) (< g (fn2-ranges-rows r))
                  (equal (fn2-ranges-schema g r) 3)
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-idle*))
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-done*))
                  (equal (fn2-run-version 3 (fn2-run-installed-rows runs) runs) (fn2-ranges-vrun g r))
                  (natp (fn2-ranges-scount g r))
                  (fn2-overview-sources-readyp (fn2-ranges-scount g r) (fn2-ranges-sbase g r) sources ov))
             (equal (fn2-range-step g budget r sources ov ix runs curs paths cache f pool)
                    (list (car deliver) (mv-nth 1 deliver) (mv-nth 2 deliver) curs paths (mv-nth 3 deliver)))))
  :hints (("Goal" :in-theory (e/d (fn2-range-step fn2-overview-recheck-positioned-sources
                                   fn2-overview-advance-positioned-sources)
                                  (fn2-range-advance-all fn2-range-recheck fn2-range-deliver
                                   fn2-overview-sources-readyp fn2-range-enumerate fn2-ranges-sbase
                                   fn2-ranges-scount fn2-ranges-phase fn2-ranges-schema fn2-ranges-rows
                                   fn2-run-version fn2-run-installed-rows fn2-ranges-vrun)))))
