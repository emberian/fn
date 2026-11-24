; Once each source supplies its own lower bound, the concrete step returns
; the first full row of the specified window, or end for an empty window.
(in-package "ACL2")
(include-book "range-advanced-head-proof")
(include-book "range-source-selection-proof")

(local
 (defthm fn2-overview-one-row-window
   (let ((row (fn2-run-unload-values *fn2-overview-entry* eb f pool)))
     (equal (consp (fn2-overview-head-window g eb r f pool))
            (and (not (eq (fn2-run-key-order-spec *fn2-overview-range-key* row
                             (fn2-overview-range-key-at (fn2-ranges-hbase g r) f)) :gt))
                 (let ((pf (fn2-ranges-pfield g r)))
                   (not (and (not (equal pf *fn2-range-no-position*)) (natp pf)
                             (< (nfix (fn2-ranges-plimit g r)) (nfix (nth pf row)))))))))
   :hints (("Goal" :in-theory (disable nfix nth fn2-ranges-pfield fn2-ranges-plimit fn2-ranges-hbase
                              fn2-overview-head-base fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen
                              fn2-fields-ref-off fn2-fields-ref-len fn2-run-read-bytes)))))

(local
 (defthm fn2-overview-winning-head-active
   (implies (and (natp n) (natp base) (fn2-overview-best-head n base nil sources f))
            (fn2-overview-active-headp (fn2-overview-best-head n base nil sources f) sources))
   :hints (("Goal" :use ((:instance fn2-overview-best-head-is-supplied (best nil)))
            :in-theory (theory 'minimal-theory)))))

(local (defthm fn2-overview-absent-slot-inactive (not (fn2-overview-active-headp nil sources))))

(defthmd fn2-overview-winner-matches-window
  (let* ((n (fn2-ranges-scount g r)) (base (fn2-ranges-sbase g r))
         (best (fn2-overview-winner g r sources f)) (eb (fn2-overview-head-base best sources))
         (pf (fn2-ranges-pfield g r)) (hi (fn2-overview-range-key-at (fn2-ranges-hbase g r) f))
         (window (fn2-range-spec *fn2-overview-range-key* streams lo hi
                                 (if (equal pf *fn2-range-no-position*) nil pf) (fn2-ranges-plimit g r))))
    (implies (and (natp n) (natp base) (fn2-range-listsp layout *fn2-overview-range-key* streams)
                  (fn2-overview-supplied-source-heads-p streams lo n base sources f pool))
             (and (iff (and best (consp (fn2-overview-head-window g eb r f pool))) (consp window))
                  (implies (consp window)
                           (equal (fn2-run-unload-values *fn2-overview-entry* eb f pool) (car window))))))
  :hints (("Goal"
           :use ((:instance fn2-overview-winning-row-from-sources
                   (n (fn2-ranges-scount g r)) (base (fn2-ranges-sbase g r)))
                 (:instance fn2-overview-window-head-from-sources
                   (sources streams) (hi (fn2-overview-range-key-at (fn2-ranges-hbase g r) f))
                   (pidx (if (equal (fn2-ranges-pfield g r) *fn2-range-no-position*) nil (fn2-ranges-pfield g r)))
                   (plimit (fn2-ranges-plimit g r))))
           :cases ((fn2-overview-winner g r sources f) (equal (fn2-ranges-pfield g r) *fn2-range-no-position*))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-overview-winner fn2-overview-winning-head-active fn2-overview-resident-head
                         fn2-overview-absent-slot-inactive fn2-overview-one-row-window iff eq atom car-cons (:e natp) (:e consp)
                         (:e equal) (:e car) cons-equal)))))

(defthm fn2-overview-step-returns-first-supplied-window-row
  (let* ((n (fn2-ranges-scount g r)) (base (fn2-ranges-sbase g r))
         (check (fn2-range-recheck n g r sources ov))
         (advance (fn2-range-advance-all n g budget r (mv-nth 1 check) ov ix runs curs paths cache f pool))
         (heads (mv-nth 1 advance)) (fields (mv-nth 4 advance))
         (best (fn2-overview-winner g r heads fields)) (eb (fn2-overview-head-base best heads))
         (pf (fn2-ranges-pfield g r))
         (window (fn2-range-spec *fn2-overview-range-key* streams lo
                   (fn2-overview-range-key-at (fn2-ranges-hbase g r) fields)
                   (if (equal pf *fn2-range-no-position*) nil pf) (fn2-ranges-plimit g r)))
         (step (fn2-range-step g budget r sources ov ix runs curs paths cache f pool)))
    (implies (and (natp g) (< g (fn2-ranges-rows r)) (natp n) (natp base)
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-idle*))
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-done*))
                  (equal (fn2-ranges-schema g r) 3)
                  (equal (fn2-run-version 3 (fn2-run-installed-rows runs) runs) (fn2-ranges-vrun g r))
                  (equal (car check) :ok) (equal (car advance) :ok)
                  (fn2-overview-delivery-fitp g r heads fields)
                  (implies best (and (natp eb) (natp (fn2-ranges-qbase g r)) (<= (+ 2 (fn2-ranges-qbase g r)) eb)))
                  (fn2-range-listsp *fn2-overview-entry* *fn2-overview-range-key* streams)
                  (fn2-overview-supplied-source-heads-p streams lo n base heads fields pool))
             (and (equal (car step) (if (consp window) :entry :end))
                  (implies (consp window)
                           (equal (fn2-run-unload-values *fn2-overview-entry*
                                    (fn2-ranges-out g (mv-nth 1 step)) (mv-nth 5 step) pool)
                                  (car window))))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-overview-step-reads-advanced-head
                        (:instance fn2-overview-winner-matches-window (layout *fn2-overview-entry*)
                          (sources (mv-nth 1 (fn2-range-advance-all (fn2-ranges-scount g r) g budget r
                                     (mv-nth 1 (fn2-range-recheck (fn2-ranges-scount g r) g r sources ov))
                                     ov ix runs curs paths cache f pool)))
                          (f (mv-nth 4 (fn2-range-advance-all (fn2-ranges-scount g r) g budget r
                                     (mv-nth 1 (fn2-range-recheck (fn2-ranges-scount g r) g r sources ov))
                                     ov ix runs curs paths cache f pool)))))
           :in-theory (union-theories (theory 'minimal-theory) '(iff)))))
