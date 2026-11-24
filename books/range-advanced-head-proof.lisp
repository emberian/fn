; A range can deliver on the same call that positions its final source.
(in-package "ACL2")
(include-book "range-head-delivery-proof")
(include-book "range-delivered-row-proof")

(local
 (defthm fn2-overview-step-after-advance
   (let* ((n (fn2-ranges-scount g r))
          (check (fn2-range-recheck n g r sources ov))
          (advance (fn2-range-advance-all n g budget r (mv-nth 1 check) ov ix runs curs paths cache f pool))
          (deliver (fn2-range-deliver g r (mv-nth 1 advance) (mv-nth 4 advance) pool)))
     (implies (and (natp g) (< g (fn2-ranges-rows r)) (natp n)
                   (not (equal (fn2-ranges-phase g r) *fn2-range-phase-idle*))
                   (not (equal (fn2-ranges-phase g r) *fn2-range-phase-done*))
                   (equal (fn2-ranges-schema g r) 3)
                   (equal (fn2-run-version 3 (fn2-run-installed-rows runs) runs) (fn2-ranges-vrun g r))
                   (equal (car check) :ok))
              (equal (fn2-range-step g budget r sources ov ix runs curs paths cache f pool)
                     (if (equal (car advance) :ok)
                         (list (car deliver) (mv-nth 1 deliver) (mv-nth 2 deliver)
                               (mv-nth 2 advance) (mv-nth 3 advance) (mv-nth 3 deliver))
                       (list (car advance) r (mv-nth 1 advance)
                             (mv-nth 2 advance) (mv-nth 3 advance) (mv-nth 4 advance))))))
   :hints (("Goal" :in-theory (e/d (fn2-range-step)
                                   (fn2-range-advance-all fn2-range-recheck fn2-range-deliver
                                    fn2-range-enumerate fn2-ranges-scount fn2-ranges-phase
                                    fn2-ranges-schema fn2-ranges-rows fn2-run-version
                                    fn2-run-installed-rows fn2-ranges-vrun))))))

(defthm fn2-overview-step-reads-advanced-head
  (let* ((n (fn2-ranges-scount g r)) (check (fn2-range-recheck n g r sources ov))
         (advance (fn2-range-advance-all n g budget r (mv-nth 1 check) ov ix runs curs paths cache f pool))
         (heads (mv-nth 1 advance)) (fields (mv-nth 4 advance))
         (best (fn2-overview-winner g r heads fields)) (eb (fn2-overview-head-base best heads))
         (entry (and best (consp (fn2-overview-head-window g eb r fields pool))))
         (step (fn2-range-step g budget r sources ov ix runs curs paths cache f pool)))
    (implies (and (natp g) (< g (fn2-ranges-rows r)) (natp n)
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-idle*))
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-done*))
                  (equal (fn2-ranges-schema g r) 3)
                  (equal (fn2-run-version 3 (fn2-run-installed-rows runs) runs) (fn2-ranges-vrun g r))
                  (equal (car check) :ok) (equal (car advance) :ok)
                  (fn2-overview-delivery-fitp g r heads fields)
                  (implies entry (and (natp eb) (natp (fn2-ranges-qbase g r))
                                      (<= (+ 2 (fn2-ranges-qbase g r)) eb))))
             (and (equal (car step) (if entry :entry :end))
                  (implies entry
                    (and (equal (fn2-ranges-out g (mv-nth 1 step)) eb)
                         (equal (fn2-run-unload-values *fn2-overview-entry* eb (mv-nth 5 step) pool)
                                (fn2-run-unload-values *fn2-overview-entry* eb fields pool)))))))
  :rule-classes nil
  :hints (("Goal" :use fn2-overview-step-after-advance
           :in-theory (union-theories (theory 'minimal-theory)
             '(fn2-overview-delivery-returns-winning-head fn2-overview-successor-preserves-delivered-row
               mv-nth car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal))))))
