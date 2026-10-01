; Actual yielded basic-loop turns compose through generated action fuel.
; Logical source observer only; not a native work/allocation tariff.
(in-package "ACL2")
(include-book "decoded-window-output-trajectory")

(local
 (defthm fn-pwy-atomic-output-loop-split-budget
  (implies (and (natp b1) (natp b2)
                (equal (car (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out))
                       :yield))
           (equal (fn-pwz-atomic-output-loop (+ b1 b2) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))
                    (fn-pwz-atomic-output-loop b2 (mv-nth 2 r) end lim (mv-nth 3 r) fn-octets
                                 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
  :hints (("Goal" :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need)) :induct (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                       fn-zin-out)))))

(local
 (defthm fn-pwy-loop-semantic-fuel-natural
  (natp (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-actual-loop-semantic-fuel) (fn-zin-act fn-zin-step fn-zin-pull fn-pwz-step-action-count))))))

(defthm fn-pwy-actual-two-yielded-loops-complete-effects
 (let* ((r1 (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-zin-loop b2 (mv-nth 2 r1) end lim (mv-nth 3 r1) fn-octets
                         (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (f1 (fn-pwz-actual-loop-semantic-fuel b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (f2 (fn-pwz-actual-loop-semantic-fuel b2 (mv-nth 2 r1) end lim (mv-nth 3 r1) fn-octets
                                            (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))))
  (implies (equal (car r1) :yield)
   (equal r2 (fn-pwz-atomic-output-loop (+ f1 f2) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b1))
        (:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b2)
          (ip (mv-nth 2 (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (fn-zin-st (mv-nth 3 (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (fn-zin-win (mv-nth 4 (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (fn-zin-tab (mv-nth 5 (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (fn-zin-out (mv-nth 6 (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
  :in-theory (disable fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel fn-zin-act fn-zin-step fn-zin-pull fn-zin-need))))

; Proof-only transcript of real loop calls. Stop on the actual first nonyield
; status; finite scheduler quanta are not primitive runtime allocation credit.
(defun-nx fn-pwy-actual-loop-turns
 (quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :measure (len quanta) :verify-guards nil))
 (let* ((b (if (consp quanta) (car quanta) 0))
        (r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (fuel (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (if (and (consp quanta) (consp (cdr quanta)) (equal (car r) :yield))
   (mv-let (next rest)
    (fn-pwy-actual-loop-turns (cdr quanta) (mv-nth 2 r) end lim (mv-nth 3 r) fn-octets
                             (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))
    (mv next (+ fuel rest)))
   (mv r fuel))))

(local
 (defthm fn-pwy-actual-turns-fuel-natural
  (natp (mv-nth 1 (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwy-actual-loop-turns) (fn-zin-loop fn-pwz-actual-loop-semantic-fuel))))))

(local
 (defthm fn-pwy-actual-loop-normalization-rewrite
  (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   (fn-pwz-atomic-output-loop
    (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
    ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :hints (("Goal" :use fn-pwz-actual-basic-loop-is-atomic-unconditionally
   :in-theory (disable fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel)))))

(defthm fn-pwy-actual-finite-yield-turns-complete-effects
 (let ((r (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (equal (mv-nth 0 r)
   (fn-pwz-atomic-output-loop (mv-nth 1 r) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
 :rule-classes nil
 :hints (("Goal"
  :induct (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  :in-theory (e/d (fn-pwy-actual-loop-turns)
   (fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel)))))

(local
 (defthm fn-pwy-atomic-completed-budget-padding
 (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (natp b) (natp extra) (not (equal (car r) :yield)))
   (equal (fn-pwz-atomic-output-loop (+ b extra) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          (mv (car r) (+ extra (mv-nth 1 r)) (mv-nth 2 r) (mv-nth 3 r)
              (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-pwz-atomic-output-loop)
                          (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts
                           fn-pwy-atomic-output-loop-split-budget))))))

(defthm fn-pwy-actual-completed-finite-yields-match-basic-loop
 (let* ((r (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (whole (fn-zin-loop b0 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (not (equal (car (mv-nth 0 r)) :yield)) (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation (mv-nth 0 r)) (fn-pwz-semantic-observation whole))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-pwy-actual-finite-yield-turns-complete-effects)
        (:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b0))
        (:instance fn-pwy-atomic-completed-budget-padding
          (b (mv-nth 1 (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (extra (fn-pwz-actual-loop-semantic-fuel b0 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
        (:instance fn-pwy-atomic-completed-budget-padding
          (b (fn-pwz-actual-loop-semantic-fuel b0 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
          (extra (mv-nth 1 (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
  :in-theory (e/d (fn-pwz-semantic-observation)
    (fn-zin-loop fn-pwy-actual-loop-turns fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))
