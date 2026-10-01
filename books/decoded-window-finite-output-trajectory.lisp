; General finite output-frontier continuation of the actual basic decoder.
; Proof-only source observer; no native work/allocation tariff.
(in-package "ACL2")
(include-book "decoded-window-clear-trajectory")

(local
 (defthm fn-pwf-cancel-prefix-fuel
  (equal (+ x (- x) y) (fix y))
  :hints (("Goal" :use (:instance associativity-of-+ (x x) (y (- x)) (z y))
   :in-theory (disable associativity-of-+)))))

(local
 (defthm fn-pwf-atomic-fuel-left-natural
  (implies (natp b) (natp (mv-nth 1 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need))))))
(local
 (defthm fn-pwf-atomic-fuel-left-bound
  (implies (natp b) (<= (mv-nth 1 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) b))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need))))))

(local
 (defthm fn-pwf-atomic-full-frontier-resume-complete-effects
  (let ((r (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (natp b1) (natp b2) (<= (nfix m) (nfix lim))
                 (equal (car r) :full))
    (equal (fn-pwz-atomic-output-loop (+ (- b1 (mv-nth 1 r)) b2) ip end lim
               fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           (fn-pwz-atomic-output-loop b2 (mv-nth 2 r) end lim (mv-nth 3 r)
               fn-octets (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
  :rule-classes :rewrite
  :hints (("Goal" :do-not '(generalize fertilize)
   :induct (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-atomic-output-loop)
    (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts fn-zin-loop-counts))))))

(local
 (defthm fn-pwf-loop-semantic-fuel-natural
  (natp (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-actual-loop-semantic-fuel) (fn-zin-act fn-zin-step fn-zin-pull fn-pwz-step-action-count))))))

(local
 (defthm fn-pwf-yield-turns-fuel-natural
  (natp (mv-nth 1 (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwy-actual-loop-turns) (fn-zin-loop fn-pwz-actual-loop-semantic-fuel))))))

(local
 (defthm fn-pwf-yield-turns-atomic-rewrite
  (equal (mv-nth 0 (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
   (fn-pwz-atomic-output-loop
    (mv-nth 1 (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
    ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :hints (("Goal" :use fn-pwy-actual-finite-yield-turns-complete-effects
   :in-theory (disable fn-pwy-actual-loop-turns fn-pwz-atomic-output-loop)))))

; Each row holds one actual output frontier and finite actual scheduler quanta.
; Stop when the actual decoder returns any non-FULL status, or the rows end.
(defun-nx fn-pwf-actual-output-turns
 (turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :measure (len turns) :verify-guards nil))
 (let* ((frontier (nfix (caar turns)))
        (q (cdar turns))
        (s (fn-pwy-actual-loop-turns q ip end frontier fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r (mv-nth 0 s)) (fuel (mv-nth 1 s)))
  (if (and (consp turns) (consp (cdr turns)) (equal (car r) :full))
   (mv-let (next rest final valid)
    (fn-pwf-actual-output-turns (cdr turns) (mv-nth 2 r) end (mv-nth 3 r) fn-octets
                              (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))
    (mv next (+ (- fuel (mv-nth 1 r)) rest) final (and valid (<= frontier final))))
   (mv r fuel frontier t))))

(local
 (defthm fn-pwf-output-turns-frontier-natural
  (natp (mv-nth 2 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwf-actual-output-turns)
    (fn-pwy-actual-loop-turns fn-pwz-atomic-output-loop))))))

(local
 (defthm fn-pwf-output-turns-fuel-natural
  (natp (mv-nth 1 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwf-actual-output-turns)
    (fn-pwy-actual-loop-turns fn-pwz-atomic-output-loop))))))

(defthm fn-pwf-actual-finite-output-yields-complete-effects
 (let ((s (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (mv-nth 3 s)
   (equal (mv-nth 0 s)
    (fn-pwz-atomic-output-loop (mv-nth 1 s) ip end (mv-nth 2 s)
                 fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  :in-theory (e/d (fn-pwf-actual-output-turns)
   (fn-pwy-actual-loop-turns fn-pwz-atomic-output-loop)))
  ("Subgoal *1/1" :use (:instance fn-pwf-atomic-full-frontier-resume-complete-effects
    (b1 (mv-nth 1 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (b2 (mv-nth 1 (fn-pwf-actual-output-turns (cdr turns) (mv-nth 2 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) end (mv-nth 3 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) fn-octets (mv-nth 4 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (mv-nth 5 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (mv-nth 6 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))))
    (m (nfix (caar turns)))
    (lim (mv-nth 2 (fn-pwf-actual-output-turns (cdr turns) (mv-nth 2 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) end (mv-nth 3 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) fn-octets (mv-nth 4 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (mv-nth 5 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (mv-nth 6 (mv-nth 0 (fn-pwy-actual-loop-turns (cdar turns) ip end (nfix (caar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))))))))

(local
 (defthm fn-pwf-atomic-completed-budget-padding
 (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (natp b) (natp extra) (not (equal (car r) :yield)))
   (equal (fn-pwz-atomic-output-loop (+ b extra) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          (mv (car r) (+ extra (mv-nth 1 r)) (mv-nth 2 r) (mv-nth 3 r)
              (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-pwz-atomic-output-loop)
                          (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts
                           fn-pwf-atomic-full-frontier-resume-complete-effects))))))

(defthm fn-pwf-actual-completed-finite-output-yields-match-basic-loop
 (let* ((r (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (whole (fn-zin-loop b0 ip end (mv-nth 2 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (mv-nth 3 r) (not (equal (car (mv-nth 0 r)) :yield)) (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation (mv-nth 0 r)) (fn-pwz-semantic-observation whole))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-pwf-actual-finite-output-yields-complete-effects)
        (:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b0) (lim (mv-nth 2 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
        (:instance fn-pwf-atomic-completed-budget-padding
          (lim (mv-nth 2 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (b (mv-nth 1 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (extra (fn-pwz-actual-loop-semantic-fuel b0 ip end (mv-nth 2 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
        (:instance fn-pwf-atomic-completed-budget-padding
          (lim (mv-nth 2 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          (b (fn-pwz-actual-loop-semantic-fuel b0 ip end (mv-nth 2 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
          (extra (mv-nth 1 (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
  :in-theory (e/d (fn-pwz-semantic-observation)
    (fn-zin-loop fn-pwy-actual-loop-turns fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop)))))

