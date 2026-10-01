; Actual basic-loop turns may advance output room after either FULL or YIELD.
; Proof-only source composition, no native allocation tariff or activation.
(in-package "ACL2")
(include-book "decoded-window-canonical-trajectory")

(local
 (defthm fn-pwif-atomic-nonfull-allows-larger-frontier
  (let ((r (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (<= (nfix m) (nfix lim)) (not (equal (car r) :full)))
    (equal r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-atomic-output-loop)
    (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts fn-zin-loop-counts))))))

(local
 (defthm fn-pwif-atomic-output-loop-split-budget
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
 (defthm fn-pwif-cancel-prefix-fuel
  (equal (+ x (- x) y) (fix y))
  :hints (("Goal" :use (:instance associativity-of-+ (x x) (y (- x)) (z y))
   :in-theory (disable associativity-of-+)))))
(local
 (defthm fn-pwif-atomic-fuel-left-natural
  (implies (natp b) (natp (mv-nth 1 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need))))))
(local
 (defthm fn-pwif-atomic-fuel-left-bound
  (implies (natp b) (<= (mv-nth 1 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) b))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need))))))

(local
 (defthm fn-pwif-atomic-full-frontier-resume-complete-effects
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
 (defthm fn-pwif-yield-left-zero
  (implies (equal (car (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) :yield)
   (equal (mv-nth 1 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) 0))
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need))))))

(local
 (defthm fn-pwif-atomic-full-or-yield-frontier-resume
  (let ((r (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (natp b1) (natp b2) (<= (nfix m) (nfix lim))
                 (member-equal (car r) '(:full :yield)))
    (equal (fn-pwz-atomic-output-loop (+ (- b1 (mv-nth 1 r)) b2) ip end lim
               fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           (fn-pwz-atomic-output-loop b2 (mv-nth 2 r) end lim (mv-nth 3 r)
               fn-octets (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
  :rule-classes nil
  :hints (("Goal" :cases ((equal (car (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) :full))
   :use ((:instance fn-pwif-atomic-nonfull-allows-larger-frontier (b b1))
         (:instance fn-pwif-atomic-full-frontier-resume-complete-effects)
         (:instance fn-pwif-atomic-output-loop-split-budget)
         (:instance fn-pwif-yield-left-zero (b b1) (lim m)))
   :in-theory (disable fn-pwz-atomic-output-loop)))))

(local
 (defthm fn-pwif-loop-semantic-fuel-natural
  (natp (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-actual-loop-semantic-fuel) (fn-zin-act fn-zin-step fn-zin-pull fn-pwz-step-action-count))))))
(local
 (defthm fn-pwif-actual-loop-normalization-rewrite
  (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   (fn-pwz-atomic-output-loop
    (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
    ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :hints (("Goal" :use fn-pwz-actual-basic-loop-is-atomic-unconditionally
   :in-theory (disable fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel)))))

; Each row is (actual requested quantum, actual output frontier).
; The actual basic loop returns every status, remaining quantum and child.
; Only FULL/YIELD permit another source turn; all other outcomes stop.
(defun-nx fn-pwif-actual-frontier-turns
 (turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :measure (len turns) :verify-guards nil))
 (let* ((b (nfix (caar turns))) (frontier (nfix (cadar turns)))
        (r (fn-zin-loop b ip end frontier fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (fuel (fn-pwz-actual-loop-semantic-fuel b ip end frontier fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (if (and (consp turns) (consp (cdr turns)) (member-equal (car r) '(:full :yield)))
   (mv-let (next rest final valid)
    (fn-pwif-actual-frontier-turns (cdr turns) (mv-nth 2 r) end (mv-nth 3 r) fn-octets
                                 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))
    (mv next (+ (- fuel (mv-nth 1 r)) rest) final (and valid (<= frontier final))))
   (mv r fuel frontier t))))

(local
 (defthm fn-pwif-output-turns-frontier-natural
  (natp (mv-nth 2 (fn-pwif-actual-frontier-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwif-actual-frontier-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwif-actual-frontier-turns)
    (fn-zin-loop fn-pwz-atomic-output-loop))))))

(local
 (defthm fn-pwif-output-turns-fuel-natural
  (natp (mv-nth 1 (fn-pwif-actual-frontier-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwif-actual-frontier-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwif-actual-frontier-turns)
    (fn-zin-loop fn-pwz-atomic-output-loop))))))

(defthm fn-pwif-actual-full-or-yield-frontier-turns-complete-effects
 (let ((s (fn-pwif-actual-frontier-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (mv-nth 3 s)
   (equal (mv-nth 0 s)
    (fn-pwz-atomic-output-loop (mv-nth 1 s) ip end (mv-nth 2 s)
                 fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwif-actual-frontier-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  :in-theory (e/d (fn-pwif-actual-frontier-turns)
   (fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel)))
  ("Subgoal *1/1" :use (:instance fn-pwif-atomic-full-or-yield-frontier-resume
   (b1 (fn-pwz-actual-loop-semantic-fuel (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (b2 (mv-nth 1 (fn-pwif-actual-frontier-turns (cdr turns) (mv-nth 2 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) end (mv-nth 3 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 4 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 5 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 6 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))) (m (nfix (cadar turns))) (lim (mv-nth 2 (fn-pwif-actual-frontier-turns (cdr turns) (mv-nth 2 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) end (mv-nth 3 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 4 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 5 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 6 (fn-zin-loop (nfix (caar turns)) ip end (nfix (cadar turns)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))))))
