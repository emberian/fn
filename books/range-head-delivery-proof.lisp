; The ready overview read returns the winning head unless it crosses the cutoff.
(in-package "ACL2")
(include-book "range-ready-source-proof")
(include-book "range-head-consume-proof")
(include-book "range-resume-order-proof")

(defun-nx fn2-overview-winner (g r sources f)
  (fn2-overview-best-head (fn2-ranges-scount g r) (fn2-ranges-sbase g r) nil sources f))

(defun-nx fn2-overview-head-window (g eb r f pool)
  (let ((pf (fn2-ranges-pfield g r)))
    (fn2-range-window-spec *fn2-overview-range-key*
      (list (fn2-run-unload-values *fn2-overview-entry* eb f pool))
      (fn2-overview-range-key-at eb f) (fn2-overview-range-key-at (fn2-ranges-hbase g r) f)
      (if (equal pf *fn2-range-no-position*) nil pf) (fn2-ranges-plimit g r))))

(defun-nx fn2-overview-delivery-fitp (g r sources f)
  (let* ((n (fn2-ranges-scount g r)) (base (fn2-ranges-sbase g r))
         (best (fn2-overview-winner g r sources f)) (eb (fn2-overview-head-base best sources))
         (hb (fn2-ranges-hbase g r)) (qb (fn2-ranges-qbase g r)) (pf (fn2-ranges-pfield g r)))
    (and (natp g) (< g (fn2-ranges-rows r)) (equal (fn2-ranges-schema g r) 3)
         (natp n) (natp base) (fn2-overview-heads-fitp n base sources f)
         (fn2-fieldsp f) (fn2-fields-wfp f)
         (natp hb) (<= (+ hb *fn2-run-entry-rows*) (fn2-fields-rows f))
         (natp qb) (<= (+ qb *fn2-run-entry-rows*) (fn2-fields-rows f))
         (natp (fn2-ranges-plimit g r))
         (or (equal pf *fn2-range-no-position*) (and (natp pf) (< pf 5)))
         (unsigned-byte-p 60 (+ 1 (fn2-ranges-delivered g r)))
         (implies best
           (and (unsigned-byte-p 32 eb)
                (or (< (+ eb 1) qb) (< (+ qb 1) eb))
                (implies (equal pf 4) (equal (fn2-fields-value (+ eb 4) f) 0)))))))

(local (in-theory (disable fn2-fields-rows fn2-fields-value fn2-fieldsp fn2-fields-wfp
            fn2-ranges-qbase fn2-ranges-hbase fn2-ranges-sbase fn2-ranges-scount fn2-ranges-schema
            fn2-ranges-rows fn2-ranges-pfield fn2-ranges-plimit fn2-ranges-delivered
            fn2-range-sources-rows fn2-range-sources-rb fn2-range-sources-state
            fn2-overview-best-head fn2-overview-heads-fitp fn2-overview-head-order
            fn2-range-pick fn2-range-consume fn2-range-past fn2-range-successor
            fn2-run-unload-values fn2-range-window-spec fn2-overview-range-key-at)))

(local
 (defthm fn2-overview-fitting-candidate
   (implies (and (natp n) (natp base) (natp j) (<= base j) (< j (+ base n))
                 (fn2-overview-active-headp j sources) (fn2-overview-heads-fitp n base sources f))
            (fn2-overview-head-fitp j sources f))
   :hints (("Goal" :induct (fn2-overview-heads-fitp n base sources f)
            :expand ((fn2-overview-heads-fitp n base sources f))
            :in-theory (enable (:induction fn2-overview-heads-fitp)))
           ("Subgoal *1/2" :cases ((equal j (+ base (1- n))))))))

(local
 (defthm fn2-overview-winner-fits
   (let ((best (fn2-overview-best-head n base nil sources f)))
     (implies (and best (natp n) (natp base) (fn2-overview-heads-fitp n base sources f))
              (fn2-overview-head-fitp best sources f)))
   :hints (("Goal" :use ((:instance fn2-overview-best-head-is-supplied (best nil)))
            :in-theory (disable fn2-overview-head-fitp)))))

(local
 (defthm fn2-overview-delivered-output-row
   (implies (natp g)
            (equal (fn2-ranges-out g
                     (let ((fn2-ranges r))
                       (fn2-ranges-put g (phase ph) (out eb) (ok ok) (os os) (og og) (delivered count))))
                   eb))
   :hints (("Goal" :in-theory (enable fn2-ranges-out fn2-ranges-set-out update-fn2-ranges-out$ai
              fn2-ranges-set-phase fn2-ranges-set-ok fn2-ranges-set-os fn2-ranges-set-og
              fn2-ranges-set-delivered update-fn2-ranges-phase$ai update-fn2-ranges-ok$ai
              update-fn2-ranges-os$ai update-fn2-ranges-og$ai update-fn2-ranges-delivered$ai)))))

(local
 (defthm fn2-overview-consume-code
   (implies (and (natp n) (natp base) (fn2-overview-head-fitp best sources f)
                 (fn2-overview-heads-fitp n base sources f))
            (equal (car (fn2-range-consume n base 3 best sources f pool)) :ok))
   :hints (("Goal" :use ((:instance fn2-overview-consume-matching-heads (j 0)))
            :in-theory (union-theories (theory 'minimal-theory) '((:e natp)))))))

(local
 (defthm fn2-overview-successor-code
   (implies (and (fn2-fieldsp f) (fn2-fields-wfp f) (natp eb) (natp qb)
                 (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
                 (<= (+ qb *fn2-run-entry-rows*) (fn2-fields-rows f))
                 (or (< (+ eb 1) qb) (< (+ qb 1) eb)))
            (member-eq (car (fn2-range-successor 3 eb qb f)) '(:ok :end)))
   :hints (("Goal" :use fn2-overview-range-successor
            :in-theory (enable mv-nth)))))

(local
 (defthm fn2-overview-empty-pick
   (implies (and (natp n) (natp base) (fn2-overview-heads-fitp n base sources f))
            (equal (fn2-range-pick n base 3 nil sources f pool)
                   (list :ok (fn2-overview-best-head n base nil sources f))))
   :hints (("Goal" :use ((:instance fn2-overview-pick-selects-best-head (best nil)))
            :in-theory (disable fn2-overview-head-fitp fn2-overview-active-headp)))))

(local
 (defthm fn2-overview-past-window
   (let ((hb (fn2-ranges-hbase g r)) (pf (fn2-ranges-pfield g r)))
     (implies (and (natp g) (< g (fn2-ranges-rows r)) (equal (fn2-ranges-schema g r) 3)
                   (natp eb) (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
                   (natp hb) (<= (+ hb *fn2-run-entry-rows*) (fn2-fields-rows f))
                   (or (equal pf *fn2-range-no-position*) (and (natp pf) (< pf 5)))
                   (natp (fn2-ranges-plimit g r))
                   (implies (equal pf 4) (equal (fn2-fields-value (+ eb 4) f) 0)))
              (equal (fn2-range-past g eb ok os og r f pool)
                     (list :ok (not (consp (fn2-overview-head-window g eb r f pool)))))))
   :hints (("Goal" :use fn2-overview-range-window-cutoff))))

(defthmd fn2-overview-delivery-returns-winning-head
  (let* ((best (fn2-overview-winner g r sources f)) (eb (fn2-overview-head-base best sources))
         (entryp (and best (consp (fn2-overview-head-window g eb r f pool))))
         (result (fn2-range-deliver g r sources f pool)))
    (implies (fn2-overview-delivery-fitp g r sources f)
             (and (equal (car result) (if entryp :entry :end))
                  (implies entryp (equal (fn2-ranges-out g (mv-nth 1 result)) eb)))))
  :hints (("Goal" :do-not '(preprocess)
           :cases ((fn2-overview-winner g r sources f))
           :use ((:instance fn2-overview-winner-fits (n (fn2-ranges-scount g r)) (base (fn2-ranges-sbase g r))))
           :in-theory (e/d (fn2-range-deliver)
             (fn2-overview-head-window fn2-overview-winner-fits fn2-range-sources-okind
              fn2-range-sources-ogen fn2-range-sources-oslot fn2-ranges-out
              fn2-ranges-set-phase fn2-ranges-set-out fn2-ranges-set-ok fn2-ranges-set-os
              fn2-ranges-set-og fn2-ranges-set-delivered fn2-overview-active-headp
              unsigned-byte-p member-equal)))))

(defthm fn2-overview-step-returns-winning-head
  (let* ((best (fn2-overview-winner g r sources f)) (eb (fn2-overview-head-base best sources))
         (entryp (and best (consp (fn2-overview-head-window g eb r f pool))))
         (step (fn2-range-step g budget r sources ov ix runs curs paths cache f pool)))
    (implies (and (fn2-overview-delivery-fitp g r sources f)
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-idle*))
                  (not (equal (fn2-ranges-phase g r) *fn2-range-phase-done*))
                  (equal (fn2-run-version 3 (fn2-run-installed-rows runs) runs) (fn2-ranges-vrun g r))
                  (fn2-overview-sources-readyp (fn2-ranges-scount g r) (fn2-ranges-sbase g r) sources ov))
             (and (equal (car step) (if entryp :entry :end))
                  (implies entryp (equal (fn2-ranges-out g (mv-nth 1 step)) eb)))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-overview-step-delivers-positioned-heads
                        fn2-overview-delivery-returns-winning-head)
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-overview-delivery-fitp mv-nth car-cons cdr-cons
                         (:e mv-nth) (:e zp) (:e binary-+) (:e consp) (:e equal))))))
