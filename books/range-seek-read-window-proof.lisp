; The read part of a seek passes the specified window row to the narrowing step.
(in-package "ACL2")
(include-book "range-supplied-window-proof")

(local
 (defthm fn2-overview-seek-reads-range
   (let* ((g (fn2-seeks-g k s)) (read (fn2-range-step g budget r sources ov ix runs curs paths cache f pool))
          (code (car read)))
     (implies (and (natp k) (< k (fn2-seeks-rows s)) (equal (fn2-seeks-phase k s) *fn2-seek-phase-read*))
              (equal (fn2-seek-step k budget s r sources ov ix runs curs paths cache f pool)
                     (list (if (member-eq code '(:entry :end)) :more code)
                           (case code (:entry (fn2-seeks-set-phase k *fn2-seek-phase-entry* s))
                                      (:end (fn2-seeks-set-phase k *fn2-seek-phase-end* s)) (otherwise s))
                           (mv-nth 1 read) (mv-nth 2 read) (mv-nth 3 read) (mv-nth 4 read) (mv-nth 5 read)))))
   :hints (("Goal" :in-theory (e/d (fn2-seek-step)
                                   (fn2-range-step fn2-seek-narrow fn2-seek-probe fn2-seeks-phase fn2-seeks-g
                                    fn2-seeks-set-phase fn2-seeks-rows))))))

(local
 (defthm fn2-overview-seek-read-phase-update
   (implies (natp k) (equal (fn2-seeks-phase k (fn2-seeks-set-phase k phase s)) phase))
   :hints (("Goal" :in-theory (e/d (fn2-seeks-phase fn2-seeks-set-phase update-fn2-seeks-phase$ai nth-update-nth)
                                   (nth update-nth))))))

(local
 (defthm fn2-range-no-position-window
   (implies (syntaxp (not (equal limit ''0)))
            (equal (fn2-range-window-spec key rows lo hi nil limit) (fn2-range-window-spec key rows lo hi nil 0)))
   :hints (("Goal" :induct (fn2-range-window-spec key rows lo hi nil limit)
            :in-theory (disable fn2-run-key-order-spec)))))

(local
 (defthm fn2-range-no-position-spec
   (implies (syntaxp (not (equal limit ''0)))
            (equal (fn2-range-spec key streams lo hi nil limit) (fn2-range-spec key streams lo hi nil 0)))
   :hints (("Goal" :in-theory (e/d (fn2-range-spec) (fn2-range-union-spec fn2-range-window-spec))))))

(local
 (defthm fn2-overview-unloaded-probe-coordinates
   (implies (equal (fn2-run-unload-values *fn2-overview-entry* base f pool) row)
            (and (equal (fn2-fields-value (+ 1 base) f) (nth 1 row))
                 (equal (fn2-fields-value (+ 3 base) f) (nth 3 row))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn2-fields-value fn2-fields-ref-off fn2-fields-ref-len
                             fn2-fields-ref-gen fn2-fields-ref-slot fn2-run-read-bytes)))))

(defthm fn2-overview-seek-reads-supplied-probe-window
  (let* ((g (fn2-seeks-g k s)) (n (fn2-ranges-scount g r)) (base (fn2-ranges-sbase g r))
         (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s)) (lo (list group mid))
         (check (fn2-range-recheck n g r sources ov))
         (advance (fn2-range-advance-all n g budget r (mv-nth 1 check) ov ix runs curs paths cache f pool))
         (heads (mv-nth 1 advance)) (fields (mv-nth 4 advance))
         (best (fn2-overview-winner g r heads fields)) (eb (fn2-overview-head-base best heads))
         (window (fn2-range-spec *fn2-overview-range-key* streams lo (list group (1- hi)) nil 0))
         (step (fn2-seek-step k budget s r sources ov ix runs curs paths cache f pool))
         (out (fn2-ranges-out g (mv-nth 2 step))) (returned (mv-nth 6 step)))
    (implies (and (natp k) (< k (fn2-seeks-rows s)) (equal (fn2-seeks-phase k s) *fn2-seek-phase-read*)
                  (natp g) (< g (fn2-ranges-rows r)) (natp n) (natp base)
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-idle*))
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-done*))
                  (equal (fn2-ranges-schema g r) 3)
                  (equal (fn2-run-version 3 (fn2-run-installed-rows runs) runs) (fn2-ranges-vrun g r))
                  (equal (car check) :ok) (equal (car advance) :ok)
                  (fn2-overview-delivery-fitp g r heads fields)
                  (implies best (and (natp eb) (natp (fn2-ranges-qbase g r)) (<= (+ 2 (fn2-ranges-qbase g r)) eb)))
                  (equal (fn2-overview-range-key-at (fn2-ranges-hbase g r) fields) (list group (1- hi)))
                  (equal (fn2-ranges-pfield g r) *fn2-range-no-position*)
                  (fn2-range-listsp *fn2-overview-entry* *fn2-overview-range-key* streams)
                  (fn2-overview-supplied-source-heads-p streams lo n base heads fields pool))
             (and (equal (car step) :more)
                  (equal (fn2-seeks-phase k (mv-nth 1 step))
                         (if (consp window) *fn2-seek-phase-entry* *fn2-seek-phase-end*))
                  (equal (mv-nth 1 step) (fn2-seeks-set-phase k
                           (if (consp window) *fn2-seek-phase-entry* *fn2-seek-phase-end*) s))
                  (implies (consp window)
                           (and (equal (fn2-run-unload-values *fn2-overview-entry* out returned pool) (car window))
                                (equal (fn2-fields-value (+ 1 out) returned) (nth 1 (car window)))
                                (equal (fn2-fields-value (+ 3 out) returned) (nth 3 (car window))))))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-overview-seek-reads-range
                        (:instance fn2-overview-unloaded-probe-coordinates
                          (base (fn2-ranges-out (fn2-seeks-g k s) (mv-nth 2 (fn2-seek-step k budget s r sources ov
                                           ix runs curs paths cache f pool))))
                          (f (mv-nth 6 (fn2-seek-step k budget s r sources ov ix runs curs paths cache f pool)))
                          (row (car (fn2-range-spec *fn2-overview-range-key* streams (list group (fn2-seeks-mid k s))
                                                    (list group (1- (fn2-seeks-hi k s))) nil 0))))
                        (:instance fn2-overview-step-returns-first-supplied-window-row
                          (g (fn2-seeks-g k s)) (lo (list group (fn2-seeks-mid k s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-range-no-position-spec fn2-overview-seek-read-phase-update member-equal eq eql mv-nth car-cons cdr-cons
                          (:e equal) (:e mv-nth) (:e binary-+) (:e zp))))))
