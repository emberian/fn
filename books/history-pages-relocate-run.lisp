; Finite composition/reference for the private relocation continuation.
; RUN includes explicit flat-array growth and is NOT a bounded scheduling tick.
; Native consumers schedule STEP and prepaid GROW-IMAGE separately. Fuel comes
; from the ACL2 rank: rank+1 suffices and is not an operator data ceiling.
(in-package "ACL2")
(include-book "history-pages-relocate-step")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-hpr-grow-keeps-cursor
 (implies (fn-hpr-cursorp cursor)
  (fn-hpr-cursorp (mv-nth 1 (fn-hpr-grow-image cursor pgs-mem))))
 :hints (("Goal" :in-theory (disable pgs-x-grow-image))))
(defun fn-hpr-tick (cursor pgs-mem)
 (declare (xargs :stobjs pgs-mem :guard (fn-hpr-cursorp cursor)))
 (if (eq (nth 0 cursor) :grow-image)
     (fn-hpr-grow-image cursor pgs-mem)
   (fn-hpr-step cursor pgs-mem)))
(defthm fn-hpr-tick-keeps-cursor
 (implies (fn-hpr-cursorp cursor)
  (fn-hpr-cursorp (mv-nth 1 (fn-hpr-tick cursor pgs-mem))))
 :hints (("Goal" :in-theory (disable fn-hpr-step fn-hpr-grow-image fn-hpr-cursorp))))
(defthm fn-hpr-tick-progresses
 (implies (and (fn-hpr-cursorp cursor)
               (equal (mv-nth 0 (fn-hpr-tick cursor pgs-mem)) :yield))
  (< (fn-hpr-rank (mv-nth 1 (fn-hpr-tick cursor pgs-mem))) (fn-hpr-rank cursor)))
 :hints (("Goal" :in-theory (disable fn-hpr-step fn-hpr-grow-image fn-hpr-cursorp fn-hpr-rank))))
(defun fn-hpr-run (fuel cursor pgs-mem)
 (declare (xargs :stobjs pgs-mem :guard (and (natp fuel) (fn-hpr-cursorp cursor))
                 :verify-guards nil))
 (if (zp fuel) (mv (list :refused :continuation-fuel) cursor pgs-mem)
  (mv-let (v next pgs-mem) (fn-hpr-tick cursor pgs-mem)
   (if (eq v :yield) (fn-hpr-run (1- fuel) next pgs-mem)
     (mv v next pgs-mem)))))
(verify-guards fn-hpr-run
 :hints (("Goal" :in-theory (disable fn-hpr-tick fn-hpr-cursorp))))
(defun-nx fn-hpr-target (cursor pgs-mem)
 (if (member-eq (nth 0 cursor) '(:header-ready :ready :grow-image))
  (fn-hpr-remaining (fn-hpr-phase :copy 0 cursor)
                    (pgs-x-grow-image (+ (nfix (nth 6 cursor)) (nfix (nth 2 cursor))) pgs-mem))
  (fn-hpr-remaining cursor pgs-mem)))
(defthm fn-hpr-tick-preserves-target
 (implies (fn-hpr-cursorp cursor)
  (equal (fn-hpr-target (mv-nth 1 (fn-hpr-tick cursor pgs-mem))
                         (mv-nth 2 (fn-hpr-tick cursor pgs-mem)))
         (fn-hpr-target cursor pgs-mem)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hpr-step-preserves-completion))
          :in-theory (e/d (fn-hpr-tick fn-hpr-target fn-hpr-grow-image fn-hpr-step
                                     fn-hpr-phase fn-hpr-cursor fn-hpr-cursorp)
                          (fn-hpr-remaining fn-hpr-step-preserves-completion
                           nth adt-nth-0 adt-nth-1+ adt-cap adt-placement-ok
                           fn-hp-hdr-m fn-hp-u64-listp fn-hp-x-copy fn-hp-x-zero
                           fn-hp-x-put fn-hp-x-mark fn-hp-x-ready pgs-x-grow-image)))))
(defthm fn-hpr-run-preserves-target
 (implies (fn-hpr-cursorp cursor)
  (equal (fn-hpr-target (mv-nth 1 (fn-hpr-run fuel cursor pgs-mem))
                         (mv-nth 2 (fn-hpr-run fuel cursor pgs-mem)))
         (fn-hpr-target cursor pgs-mem)))
 :hints (("Goal" :induct (fn-hpr-run fuel cursor pgs-mem)
          :in-theory (e/d (fn-hpr-run)
                          (fn-hpr-tick fn-hpr-target fn-hpr-cursorp)))))
(local (defthm fn-hpr-ready-not-done
 (not (equal (fn-hp-x-ready p pgs-mem) :done))
 :hints (("Goal" :in-theory (enable fn-hp-x-ready)))))
(defthm fn-hpr-tick-done-phase
 (implies (and (fn-hpr-cursorp cursor)
               (equal (mv-nth 0 (fn-hpr-tick cursor pgs-mem)) :done))
          (equal (car (mv-nth 1 (fn-hpr-tick cursor pgs-mem))) :done))
 :hints (("Goal" :in-theory (disable fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-ready pgs-x-grow-image))))
(defthm fn-hpr-run-done-phase
 (implies (and (fn-hpr-cursorp cursor)
               (equal (mv-nth 0 (fn-hpr-run fuel cursor pgs-mem)) :done))
          (equal (car (mv-nth 1 (fn-hpr-run fuel cursor pgs-mem))) :done))
 :hints (("Goal" :induct (fn-hpr-run fuel cursor pgs-mem)
          :in-theory (e/d (fn-hpr-run) (fn-hpr-tick fn-hpr-cursorp)))))
(defthm fn-hpr-target-done
 (implies (equal (car cursor) :done)
          (equal (fn-hpr-target cursor pgs-mem) pgs-mem))
 :hints (("Goal" :in-theory (enable fn-hpr-target fn-hpr-remaining))))
(defthm fn-hpr-run-done-is-target
 (implies (and (fn-hpr-cursorp cursor)
               (equal (car (fn-hpr-run fuel cursor pgs-mem)) :done))
          (equal (mv-nth 2 (fn-hpr-run fuel cursor pgs-mem))
                 (fn-hpr-target cursor pgs-mem)))
 :hints (("Goal" :use ((:instance fn-hpr-run-preserves-target)
                       (:instance fn-hpr-run-done-phase)
                       (:instance fn-hpr-target-done
                                  (cursor (mv-nth 1 (fn-hpr-run fuel cursor pgs-mem)))
                                  (pgs-mem (mv-nth 2 (fn-hpr-run fuel cursor pgs-mem)))))
          :in-theory (disable fn-hpr-target fn-hpr-run fn-hpr-cursorp
                              fn-hpr-run-preserves-target fn-hpr-run-done-phase fn-hpr-target-done))))
(defthm fn-hpr-tick-progresses-linear
 (implies (and (fn-hpr-cursorp cursor)
               (equal (car (fn-hpr-tick cursor pgs-mem)) :yield))
  (< (fn-hpr-rank (mv-nth 1 (fn-hpr-tick cursor pgs-mem))) (fn-hpr-rank cursor)))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-hpr-tick-progresses))
          :in-theory (disable fn-hpr-tick fn-hpr-cursorp fn-hpr-rank))))
(defthm fn-hpr-ready-not-fuel
 (not (equal (fn-hp-x-ready p pgs-mem) '(:refused :continuation-fuel)))
 :hints (("Goal" :in-theory (enable fn-hp-x-ready))))
(defthm fn-hpr-tick-not-fuel
 (not (equal (mv-nth 0 (fn-hpr-tick cursor pgs-mem)) '(:refused :continuation-fuel)))
 :hints (("Goal" :in-theory (disable fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-ready pgs-x-grow-image))))
(defthm fn-hpr-rank-natural (natp (fn-hpr-rank cursor))
 :rule-classes :type-prescription)
(local (defthm fn-hpr-tick-car-not-fuel
 (not (equal (car (fn-hpr-tick cursor pgs-mem)) '(:refused :continuation-fuel)))
 :hints (("Goal" :use ((:instance fn-hpr-tick-not-fuel))
          :in-theory (e/d (mv-nth) (fn-hpr-tick fn-hpr-tick-not-fuel))))))
(defthm fn-hpr-run-rank-suffices
 (implies (and (fn-hpr-cursorp cursor) (natp fuel) (< (fn-hpr-rank cursor) fuel))
  (not (equal (mv-nth 0 (fn-hpr-run fuel cursor pgs-mem)) '(:refused :continuation-fuel))))
 :hints (("Goal" :induct (fn-hpr-run fuel cursor pgs-mem)
          :in-theory (e/d (fn-hpr-run) (fn-hpr-tick fn-hpr-cursorp fn-hpr-rank)))))
(defun fn-hpr-final-placement (cursor)
 (declare (xargs :guard (fn-hpr-cursorp cursor)))
 (list (update-nth (nth 1 cursor) (nth 6 cursor) (nth 5 cursor))
       (+ (nth 6 cursor) (nth 2 cursor))))
(defthm fn-hpr-tick-keeps-placement
 (implies (fn-hpr-cursorp cursor)
  (equal (fn-hpr-final-placement (mv-nth 1 (fn-hpr-tick cursor pgs-mem)))
         (fn-hpr-final-placement cursor)))
 :hints (("Goal" :in-theory (disable fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-ready pgs-x-grow-image))))
(defthm fn-hpr-run-keeps-placement
 (implies (fn-hpr-cursorp cursor)
  (equal (fn-hpr-final-placement (mv-nth 1 (fn-hpr-run fuel cursor pgs-mem)))
         (fn-hpr-final-placement cursor)))
 :hints (("Goal" :induct (fn-hpr-run fuel cursor pgs-mem)
          :in-theory (e/d (fn-hpr-run) (fn-hpr-tick fn-hpr-cursorp fn-hpr-final-placement)))))
(defthm fn-hpr-run-done-placement
 (implies (and (fn-hpr-cursorp cursor)
               (equal (mv-nth 0 (fn-hpr-run fuel cursor pgs-mem)) :done))
  (equal (fn-hpr-placement (mv-nth 1 (fn-hpr-run fuel cursor pgs-mem)))
         (fn-hpr-final-placement cursor)))
 :hints (("Goal" :use ((:instance fn-hpr-run-keeps-placement)
                       (:instance fn-hpr-run-done-phase))
          :in-theory (e/d (fn-hpr-placement fn-hpr-final-placement)
                          (fn-hpr-run fn-hpr-cursorp fn-hpr-run-keeps-placement fn-hpr-run-done-phase)))))
(defthm fn-hpr-run-is-old-relocation
 (implies
  (and (natp r) (< r 5) (natp c) (natp n) (natp np)
       (nat-listp lens) (equal (len lens) 5)
       (nat-listp starts) (equal (len starts) 5)
       (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok)
       (equal (mv-nth 0 (fn-hpr-run fuel (fn-hpr-cursor :header-ready r c n lens starts np 0) pgs-mem)) :done))
  (and
   (equal (mv-nth 2 (fn-hpr-run fuel (fn-hpr-cursor :header-ready r c n lens starts np 0) pgs-mem))
          (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem)))
   (equal (fn-hpr-placement (mv-nth 1 (fn-hpr-run fuel (fn-hpr-cursor :header-ready r c n lens starts np 0) pgs-mem)))
          (list (mv-nth 1 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                (mv-nth 2 (fn-hp-x-relocate r c n lens starts np pgs-mem))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hpr-run-done-is-target (cursor (fn-hpr-cursor :header-ready r c n lens starts np 0)))
                (:instance fn-hpr-run-done-placement (cursor (fn-hpr-cursor :header-ready r c n lens starts np 0)))
                (:instance fn-hpr-grow-starts-old-relocation)
                (:instance fn-hp-x-relocate-ok-unfolds))
          :in-theory (e/d (fn-hpr-target fn-hpr-phase fn-hpr-cursor fn-hpr-cursorp fn-hpr-final-placement)
                          (fn-hpr-run fn-hpr-remaining fn-hp-x-relocate fn-hp-x-copy fn-hp-x-zero fn-hp-x-put
                           fn-hp-x-mark fn-hp-hdr-m adt-cap pgs-x-grow-image fn-hp-x-relocate-ok-unfolds)))))
