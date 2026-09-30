; Actual stored decoder input refill and canonical answer. PRF1131 component.
; Two actual STORED-CHUNK calls, second with a separate tail buffer atIP0,
; preserve the complete decoded answer of actual FN-PZD-DECODE. Exact global
; budget-left and credit/recredit effects are composed in the proof.
; Three premises: first :more, second not :yield, second not :full. Final output
; frontier and whole-call completion are derived, not assumed. No logical
; dictionary/input type or supplied-buffer shape hypothesis. Runtime unchanged.
; Actual host prototype calls FN-PWZ-CODEC-TICK ->FN-EWZ-CODEC-TICK, whose
; existing exact window/output/effects boundary names STORED-CHUNK. Fixed1024
; and input64+6 are reachable source-call coordinates in tests; native source
; authority/private holder/compiler funding and arbitrary schedules remain open.
; This source component does not authorize native compressed activation.
(in-package "ACL2")

(include-book "decoded-window-stored-trajectory")

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defun-nx fn-pwie-semantic-observation (r)
  (list (car r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))))

(local
 (defun-nx fn-pwie-actual-loop-budget-pair-induction
  (b1 b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :measure (nfix b1)))
  (cond ((or (zp b1) (zp b2) (<= (nfix lim) (len fn-zin-out))) nil)
        ((< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
         (if (and (natp ip) (< ip (min (nfix end) (fn-octets-len fn-octets))))
          (fn-pwie-actual-loop-budget-pair-induction (1- b1) (1- b2) (1+ ip) end lim
            (fn-zin-pull ip fn-zin-st fn-octets) fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          nil))
        (t (let ((r (fn-zin-step (- (nfix lim) (len fn-zin-out)) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             (if (car r) nil
              (fn-pwie-actual-loop-budget-pair-induction (1- b1) (1- b2) ip end lim
                (mv-nth 1 r) fn-octets (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))))))

(local
 (defthm fn-pwie-actual-completed-loop-budget-independent
  (let ((r1 (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-zin-loop b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (not (equal (car r1) :yield)) (not (equal (car r2) :yield)))
    (equal (fn-pwie-semantic-observation r1) (fn-pwie-semantic-observation r2))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pwie-actual-loop-budget-pair-induction b1 b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwie-actual-loop-budget-pair-induction fn-pwie-semantic-observation fn-zin-loop)
                           (fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-loop-counts fn-zin-loop-keeps))))))

(local
 (defthm fn-pwzd-atomic-output-proper-and-monotone
  (implies (true-listp fn-zin-out)
   (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (true-listp (mv-nth 6 r)) (<= (len fn-zin-out) (len (mv-nth 6 r))))))
  :rule-classes (:rewrite (:linear :corollary
   (implies (true-listp fn-zin-out)
    (<= (len fn-zin-out) (len (mv-nth 6 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))))
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-atomic-output-loop)
                           (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts))))))

(local
 (defthm fn-pwz-atomic-output-loop-split-budget
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
 (defun-nx fn-pwz-atomic-fuel-pair-induction
 (b1 b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :measure (nfix b1)))
 (cond ((or (zp b1) (zp b2) (<= (nfix lim) (len fn-zin-out))) nil)
       ((< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
        (if (and (natp ip) (< ip (min (nfix end) (fn-octets-len fn-octets))))
         (fn-pwz-atomic-fuel-pair-induction (1- b1) (1- b2) (1+ ip) end lim
           (fn-zin-pull ip fn-zin-st fn-octets) fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         nil))
       (t (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
            (if (car r) nil
             (fn-pwz-atomic-fuel-pair-induction (1- b1) (1- b2) ip end lim
               (mv-nth 1 r) fn-octets (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))))))

(local
 (defthm fn-pwz-atomic-terminal-observation-fuel-independent
 (let ((r1 (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
       (r2 (fn-pwz-atomic-output-loop b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (not (equal (car r1) :yield)) (not (equal (car r2) :yield)))
   (equal (list (car r1) (mv-nth 2 r1) (mv-nth 3 r1) (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))
          (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2) (mv-nth 6 r2)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwz-atomic-fuel-pair-induction b1 b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-pwz-atomic-output-loop fn-pwz-atomic-fuel-pair-induction)
                          (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts
                           fn-pwz-atomic-output-loop-split-budget))))))

(local
 (defthm fn-pwzd-atomic-nonfull-prefix-can-change-frontier
  (let ((r (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (true-listp fn-zin-out) (not (equal (car r) :full))
                 (< (len (mv-nth 6 r)) (nfix lim)))
    (equal (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out) r)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-atomic-output-loop)
                           (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts))))))

(local
 (defthm fn-pwzd-actual-basic-loop-terminal-frontier-independent
 (let ((r1 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
       (r2 (fn-zin-loop b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (true-listp fn-zin-out) (not (equal (car r1) :full))
                (not (equal (car r1) :yield)) (not (equal (car r2) :yield))
                (< (len (mv-nth 6 r1)) (nfix lim)))
   (equal (fn-pwz-semantic-observation r1) (fn-pwz-semantic-observation r2))))
 :rule-classes nil
 :hints (("Goal"
           :use ((:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b1) (lim m))
                 (:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b2))
                 (:instance fn-pwzd-atomic-nonfull-prefix-can-change-frontier (b (fn-pwz-actual-loop-semantic-fuel b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (:instance fn-pwz-atomic-terminal-observation-fuel-independent (b1 (fn-pwz-actual-loop-semantic-fuel b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (b2 (fn-pwz-actual-loop-semantic-fuel b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
           :in-theory (e/d (fn-pwz-semantic-observation)
                           (fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel
                            fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-loop-counts
                            fn-zin-step-out-free nfix min))))))

(local
 (defthm fn-pwie-actual-loop-output-proper
  (implies (true-listp fn-zin-out)
   (true-listp (mv-nth 6 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :use fn-pwz-actual-basic-loop-is-atomic-unconditionally
           :in-theory (disable fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel
                               fn-zin-step fn-zin-act fn-zin-pull fn-zin-need)))))

(local
 (defthm fn-pwie-actual-loop-nonmore-input-extension-full-tuple
  (let ((r (fn-zin-loop b ip cut lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (<= (nfix cut) (nfix end)) (not (equal (car r) :more)))
    (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out) r)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-zin-loop b ip cut lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
                           (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts fn-zin-loop-keeps
                            fn-zin-loop-split-input fn-zin-loop-out-free))))))

(local
 (defthm fn-pwie-actual-whole-completion-implies-prefix-completion
  (implies (and (<= (nfix cut) (nfix end))
                (not (equal (car (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) :yield)))
   (not (equal (car (fn-zin-loop b ip cut lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) :yield)))
  :rule-classes nil
  :hints (("Goal" :use fn-pwie-actual-loop-nonmore-input-extension-full-tuple
           :in-theory (disable fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need)))))

(local
 (defthm fn-pwie-observation-of-seven-tuple
  (implies (equal r (list a b c d e f g))
   (equal (fn-pwie-semantic-observation r) (list a c d e f g)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwie-semantic-observation)))))

(local
 (defthm fn-pwie-actual-more-cut-cleared-output-confluence
  (let* ((r1 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (r2 (fn-zin-loop b2 (mv-nth 2 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) end lim (mv-nth 3 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) nil)) (whole (fn-zin-loop b0 ip end (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)))
   (implies (and (<= (nfix cut) (nfix end)) (equal (car r1) :more)
                 (posp (nfix lim)) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)))
    (equal (fn-pwie-semantic-observation whole)
     (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
           (append (mv-nth 6 r1) (mv-nth 6 r2))))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pwie-observation-of-seven-tuple (r (fn-zin-loop b0 ip end (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (a (car (fn-zin-loop b2 (mv-nth 2 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) end lim (mv-nth 3 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) nil))) (b (mv-nth 1 (fn-zin-loop (mv-nth 1 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 2 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) end lim (mv-nth 3 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) fn-octets (mv-nth 4 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) nil))) (c (mv-nth 2 (fn-zin-loop b2 (mv-nth 2 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) end lim (mv-nth 3 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) nil))) (d (mv-nth 3 (fn-zin-loop b2 (mv-nth 2 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) end lim (mv-nth 3 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) nil))) (e (mv-nth 4 (fn-zin-loop b2 (mv-nth 2 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) end lim (mv-nth 3 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) nil))) (f (mv-nth 5 (fn-zin-loop b2 (mv-nth 2 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) end lim (mv-nth 3 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) nil))) (g (append (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 6 (fn-zin-loop b2 (mv-nth 2 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) end lim (mv-nth 3 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)) nil)))))
         (:instance fn-pwie-actual-whole-completion-implies-prefix-completion (b b0) (lim (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim))) (fn-zin-out nil))
         (:instance fn-pwzd-actual-basic-loop-terminal-frontier-independent (b2 b0) (end cut) (lim (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim))) (fn-zin-out nil))
         (:instance fn-zin-loop-split-input (b b0) (m cut) (lim (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim))) (fn-zin-out nil))
         (:instance fn-pwie-actual-loop-output-proper (b b0) (end cut) (lim (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim))) (fn-zin-out nil))
         (:instance fn-zin-loop-out-free (b (mv-nth 1 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (ip (mv-nth 2 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)))
          (fn-zin-st (mv-nth 3 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (fn-zin-win (mv-nth 4 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)))
          (fn-zin-tab (mv-nth 5 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (fn-zin-out (mv-nth 6 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))))
         (:instance fn-pwie-actual-completed-loop-budget-independent
          (b1 (mv-nth 1 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (ip (mv-nth 2 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)))
          (fn-zin-st (mv-nth 3 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (fn-zin-win (mv-nth 4 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)))
          (fn-zin-tab (mv-nth 5 (fn-zin-loop b0 ip cut (+ (len (mv-nth 6 (fn-zin-loop b1 ip cut m fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab nil))) (fn-zin-out nil)))
   :in-theory (e/d (fn-pwie-semantic-observation fn-pwz-semantic-observation)
                   (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need
                    fn-zin-loop-split-input fn-zin-loop-out-free fn-zin-loop-counts fn-zin-loop-keeps
                    fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel min))))))

(local
 (defthm fn-pwie-actual-loop-ip-bound
  (implies (and (natp ip) (natp end) (<= ip end))
   (<= (mv-nth 2 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) end))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop) (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts fn-zin-loop-keeps))))))

(local
 (defthm fn-pwie-actual-more-consumes-exact-input-cut
  (implies (and (natp ip) (natp cut) (<= ip cut) (<= cut (len fn-octets))
                (equal (car (fn-zin-loop b ip cut lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) :more))
   (equal (mv-nth 2 (fn-zin-loop b ip cut lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) cut))
  :rule-classes nil
  :hints (("Goal" :use (:instance fn-zin-loop-stops (end cut))
           :in-theory (e/d (min nfix) (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-stops))))))

(local (defthm fn-pwie-nthcdr-append-prefix
 (equal (nthcdr (len a) (append a c)) c)))

(local (defthm fn-pwie-length-append
 (equal (len (append a c)) (+ (len a) (len c)))))

(local
 (defthm fn-pwie-actual-two-refilled-stored-chunks-full-tuple
  (let* ((r1 (fn-pzw-stored-chunk requested1 remaining1 0 (len a) compressed expected fn-zin-st a fn-zin-win fn-zin-tab nil)) (r2 (fn-pzw-stored-chunk requested2 remaining2 0 (len c) compressed expected (mv-nth 3 r1) c (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
         (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
         (a1 (fn-zin-feed (fn-pzw-quantum requested1 remaining1) credited 0 (len a)
               (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout credited)) a fn-zin-win fn-zin-tab nil))
         (a2 (fn-zin-feed (fn-pzw-quantum requested2 remaining2) (mv-nth 3 a1) 0 (len c)
               (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout (mv-nth 3 a1))) c (mv-nth 4 a1) (mv-nth 5 a1) nil)))
   (equal (list (car r2) (mv-nth 1 r2) (mv-nth 2 r2)
                (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
                (mv-nth 4 r2) (mv-nth 5 r2) (mv-nth 6 r2)) a2))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple
          (requested requested1) (remaining remaining1) (start 0) (end (len a)) (fn-octets a) (fn-zin-out nil))
         (:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple
          (requested requested2) (remaining remaining2) (start 0) (end (len c)) (fn-octets c)
          (fn-zin-st (mv-nth 3 (fn-pzw-stored-chunk requested1 remaining1 0 (len a) compressed expected fn-zin-st a fn-zin-win fn-zin-tab nil))) (fn-zin-win (mv-nth 4 (fn-pzw-stored-chunk requested1 remaining1 0 (len a) compressed expected fn-zin-st a fn-zin-win fn-zin-tab nil)))
          (fn-zin-tab (mv-nth 5 (fn-pzw-stored-chunk requested1 remaining1 0 (len a) compressed expected fn-zin-st a fn-zin-win fn-zin-tab nil))) (fn-zin-out (mv-nth 6 (fn-pzw-stored-chunk requested1 remaining1 0 (len a) compressed expected fn-zin-st a fn-zin-win fn-zin-tab nil)))))
   :in-theory (disable fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-zin-loop
                       fn-pzw-room fn-pzw-quantum fn-pzw-stored-allowance nfix min
)))))

(local (defthm fn-pwie-take-append-physical-prefix
 (equal (take (len a) (append a c)) (take (len a) a))))

(local
 (defthm fn-pwie-actual-prefix-buffer-refill-without-logical-type
  (equal (fn-zin-loop b 0 (len a) lim fn-zin-st (append a c) fn-zin-win fn-zin-tab fn-zin-out)
         (fn-zin-loop b 0 (len a) lim fn-zin-st a fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-zin-loop-is-run (ip 0) (end (len a)) (x (append a c)))
                       (:instance fn-zin-loop-is-run (ip 0) (end (len a)) (x a))
                       (:instance fn-zin-loop-counts (ip 0) (end (len a)) (fn-octets a)))
           :in-theory (e/d (fn-zin-run) (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts))))))

(local
 (defthm fn-pwie-actual-tail-buffer-refill-without-logical-type
  (equal (fn-zin-loop b (len a) (len (append a c)) lim fn-zin-st (append a c) fn-zin-win fn-zin-tab nil)
    (let ((r (fn-zin-loop b 0 (len c) lim fn-zin-st c fn-zin-win fn-zin-tab nil)))
     (list (car r) (mv-nth 1 r) (+ (len a) (mv-nth 2 r)) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-zin-loop-is-run (ip (len a)) (end (len (append a c))) (x (append a c)) (fn-zin-out nil))
                       (:instance fn-zin-loop-is-run (ip 0) (end (len c)) (x c) (fn-zin-out nil))
                       (:instance fn-zin-loop-counts (ip 0) (end (len c)) (fn-octets c) (fn-zin-out nil)))
           :in-theory (e/d (fn-zin-run) (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts))))))

(local
 (defthm fn-pwie-actual-refilled-more-windows-without-logical-types
  (let* ((r1 (fn-zin-loop b1 0 (len a) m fn-zin-st a fn-zin-win fn-zin-tab nil)) (r2 (fn-zin-loop b2 0 (len c) lim (mv-nth 3 (fn-zin-loop b1 0 (len a) m fn-zin-st a fn-zin-win fn-zin-tab nil)) c (mv-nth 4 (fn-zin-loop b1 0 (len a) m fn-zin-st a fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-loop b1 0 (len a) m fn-zin-st a fn-zin-win fn-zin-tab nil)) nil)) (whole (fn-zin-loop b0 0 (len (append a c)) (+ (len (mv-nth 6 (fn-zin-loop b1 0 (len a) m fn-zin-st a fn-zin-win fn-zin-tab nil))) (nfix lim)) fn-zin-st (append a c) fn-zin-win fn-zin-tab nil)))
   (implies (and (equal (car r1) :more)
                 (posp (nfix lim)) (not (equal (car r2) :yield)) (not (equal (car whole) :yield)))
    (equal (fn-pwie-semantic-observation whole)
     (list (car r2) (+ (len a) (mv-nth 2 r2)) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
           (append (mv-nth 6 r1) (mv-nth 6 r2))))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pwie-actual-more-cut-cleared-output-confluence
          (ip 0) (cut (len a)) (end (len (append a c))) (fn-octets (append a c)))
         (:instance fn-pwie-actual-prefix-buffer-refill-without-logical-type (b b1) (lim m) (fn-zin-out nil))
         (:instance fn-pwie-actual-more-consumes-exact-input-cut (b b1) (ip 0) (cut (len a)) (lim m) (fn-octets a) (fn-zin-out nil))
         (:instance fn-pwie-actual-tail-buffer-refill-without-logical-type (b b2)
          (fn-zin-st (mv-nth 3 (fn-zin-loop b1 0 (len a) m fn-zin-st a fn-zin-win fn-zin-tab nil))) (fn-zin-win (mv-nth 4 (fn-zin-loop b1 0 (len a) m fn-zin-st a fn-zin-win fn-zin-tab nil))) (fn-zin-tab (mv-nth 5 (fn-zin-loop b1 0 (len a) m fn-zin-st a fn-zin-win fn-zin-tab nil)))))
   :in-theory (e/d (fn-pwie-semantic-observation)
                   (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need
                    fn-zin-loop-counts fn-zin-loop-keeps fn-zin-loop-stops
                    fn-zin-loop-split-input fn-zin-loop-out-free fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel))))))

(local
 (defthm fn-pwzc-canonical-initialize-tout-zero
  (equal (fn-zin-tout (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0)
  :hints (("Goal" :in-theory (enable fn-pzw-initialize fn-zin-reset fn-zin-reset-loop)))))

(local
 (defthm fn-pwzc-canonical-initialize-tin-zero
  (equal (fn-zin-tin (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0)
  :hints (("Goal" :in-theory (enable fn-pzw-initialize fn-zin-reset fn-zin-reset-loop)))))

(local
 (defthm fn-pwzc-actual-payload-buffers-initializer-by-definition
  (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
         (c (nfix (- end start)))
         (credited (fn-zin-set 7 c (car init)))
         (r (fn-zin-feed b credited start end (fn-zin-stored-limit c lim)
                         fn-octets (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init))))
   (equal (fn-zin-payload-bufs b dict start end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          (list (fn-zin-stored-status (car r) c (mv-nth 3 r)) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-payload-bufs fn-pzw-initialize fn-zin-feed fn-zin-stored-status)
                           (fn-zin-loop fn-zin-payload-ready fn-zin-reset fn-zin-stored-terminalp fn-zin-stored-allowance nfix))))))

(local
 (defthm fn-pwzc-stored-status-unaffected-by-tin-credit
  (equal (fn-zin-stored-status status c (fn-zin-set 7 credit fn-zin-st))
         (fn-zin-stored-status status c fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-zin-stored-status fn-zin-stored-terminalp)))))

(local
 (defthm fn-pwzc-canonical-initialize-progress-controls
  (let ((s (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
   (and (fn-pwz-progress-statep s) (equal (fn-pwz-progress-phase s) -2)
        (equal (fn-zin-nbits s) 0) (equal (fn-zin-tout s) 0)))
  :hints (("Goal" :in-theory (enable fn-pzw-initialize fn-zin-reset fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwzc-actual-loop-input-position-upper-bound
  (implies (and (natp ip) (<= ip (nfix end)))
   (<= (mv-nth 2 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (nfix end)))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
                           (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts fn-zin-step-out-free))))))

(local
 (defthm fn-pwzc-progress-controls-unaffected-by-credit
  (and (equal (fn-pwz-progress-statep (fn-zin-set 7 credit fn-zin-st)) (fn-pwz-progress-statep fn-zin-st))
       (equal (fn-pwz-progress-phase (fn-zin-set 7 credit fn-zin-st)) (fn-pwz-progress-phase fn-zin-st)))
  :hints (("Goal" :in-theory (enable fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwzc-canonical-output-frontier-bounds
  (let ((lim (fn-zin-stored-limit c (+ 1 (nfix n)))))
   (and (natp lim) (< 0 lim) (<= lim (+ 1 (nfix n)))))
  :rule-classes (:rewrite (:linear :corollary (<= (fn-zin-stored-limit c (+ 1 (nfix n))) (+ 1 (nfix n)))))
  :hints (("Goal" :in-theory (enable fn-zin-stored-limit fn-zin-stored-allowance nfix min)))))

(local
 (defthm fn-pwzc-canonical-nfix-natural
  (implies (natp x) (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix)))))

(local
 (defthm fn-pwzc-actual-canonical-feed-budget-margin
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets)) (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed (fn-pzd-budget c n) credited 0 c (fn-zin-stored-limit c (+ 1 (nfix n)))
                        fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (<= (+ 3837 (* 7 c)) (mv-nth 1 r)))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-actual-loop-charge-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-zin-loop-counts
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-pwzc-actual-loop-input-position-upper-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-zin-feed-out-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (start 0) (end (len fn-octets))
                 (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil)))
          :in-theory (e/d (fn-zin-feed fn-pzd-budget)
                          (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need
                           fn-pzw-initialize fn-zin-reset create-fn-zin-st fn-zin-bomb-okp fn-zin-stored-limit fn-zin-stored-allowance
                           fn-pwz-progress-statep fn-pwz-progress-phase
                           fn-zin-loop-counts fn-zin-feed-out-bound nfix min))))))

(local
 (defthm fn-pwzc-actual-feed-yield-exhausts-charge
  (let ((r (fn-zin-feed b fn-zin-st start end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (equal (car r) :yield) (equal (mv-nth 1 r) 0)))
  :hints (("Goal" :in-theory (e/d (fn-zin-feed) (fn-zin-loop))))))

(local
 (defthm fn-pwzc-actual-canonical-feed-never-yields
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets)) (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed (fn-pzd-budget c n) credited 0 c (fn-zin-stored-limit c (+ 1 (nfix n)))
                        fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (not (equal (car r) :yield)))
 :rule-classes nil
 :hints (("Goal" :use fn-pwzc-actual-canonical-feed-budget-margin
          :in-theory (disable fn-pzw-initialize create-fn-zin-st fn-zin-feed fn-zin-loop
                              fn-pzd-budget fn-zin-stored-limit fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwzd-actual-feed-terminal-frontier-independent
 (let ((r1 (fn-zin-feed b1 fn-zin-st ip end m fn-octets fn-zin-win fn-zin-tab nil))
       (r2 (fn-zin-feed b2 fn-zin-st ip end lim fn-octets fn-zin-win fn-zin-tab nil)))
  (implies (and (not (equal (car r1) :full))
                (not (equal (car r1) :yield)) (not (equal (car r2) :yield))
                (< (len (mv-nth 6 r1)) (nfix lim)))
   (equal (fn-pwz-semantic-observation r1) (fn-pwz-semantic-observation r2))))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn-pwzd-actual-basic-loop-terminal-frontier-independent (fn-zin-out nil))
           :in-theory (e/d (fn-zin-feed fn-zin-window-ready-p fn-zin-tab-okp fn-pwz-semantic-observation)
                           (fn-zin-loop fn-zin-feed-unfolds nfix min))))))

(local
 (defthm fn-pwzd-actual-initialize-output-empty
  (equal (mv-nth 3 (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)) nil)
  :hints (("Goal" :in-theory (e/d (fn-pzw-initialize) (fn-zin-reset fn-zin-payload-ready))))))

(local
 (defthm fn-pwzd-actual-bounded-frontier-feed-budget-margin
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets)) (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed (fn-pzd-budget c n) credited 0 c m
                        fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (implies (<= (nfix m) (+ 1 (nfix n)))
   (<= (+ 3837 (* 7 c)) (mv-nth 1 r))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-actual-loop-charge-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim m)
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-zin-loop-counts
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim m)
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-pwzc-actual-loop-input-position-upper-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim m)
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-zin-feed-out-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (start 0) (end (len fn-octets))
                 (lim m)
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil)))
          :in-theory (e/d (fn-zin-feed fn-pzd-budget)
                          (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need
                           fn-pzw-initialize fn-zin-reset create-fn-zin-st fn-zin-bomb-okp fn-zin-stored-limit fn-zin-stored-allowance
                           fn-pwz-progress-statep fn-pwz-progress-phase
                           fn-zin-loop-counts fn-zin-feed-out-bound nfix min))))))

(local
 (defthm fn-pwzd-actual-bounded-frontier-feed-never-yields
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets)) (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed (fn-pzd-budget c n) credited 0 c m
                        fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (implies (<= (nfix m) (+ 1 (nfix n)))
   (not (equal (car r) :yield))))
 :rule-classes nil
 :hints (("Goal" :use fn-pwzd-actual-bounded-frontier-feed-budget-margin
          :in-theory (disable fn-pzw-initialize create-fn-zin-st fn-zin-feed fn-zin-loop
                              fn-pzd-budget fn-zin-stored-limit fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwzd-stored-global-frontier-bound
  (implies (and (natp produced) (<= produced (nfix expected)))
   (<= (+ produced (fn-pzw-room (min (nfix expected) allowance) produced)) (+ 1 (nfix expected))))
  :hints (("Goal" :in-theory (enable fn-pzw-room min nfix)))))

(local
 (defthm fn-pwzd-actual-initialize-ignores-buffers
  (implies (syntaxp (not (and (equal fn-zin-win ''nil) (equal fn-zin-tab ''nil) (equal fn-zin-out ''nil))))
   (equal (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
          (fn-pzw-initialize dict fn-zin-st nil nil nil)))
  :hints (("Goal" :in-theory (e/d (fn-pzw-initialize) (fn-zin-reset fn-zin-payload-ready))))))

(local
 (defthm fn-pwzd-actual-canonical-decode-feed-unrestricted-input
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets))
        (r (fn-zin-feed (fn-pzd-budget c n) (fn-zin-set 7 c (car init)) 0 c
                       (fn-zin-stored-limit c (+ 1 (nfix n)))
                       fn-octets (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init))))
  (equal (fn-pzd-decode dict fn-octets n)
          (if (and (zp n) (atom fn-octets)) (list :ok nil)
            (fn-pzd-answer (fn-zin-stored-status (car r) c (mv-nth 3 r)) (mv-nth 6 r) n))))
 :rule-classes nil
 :hints (("Goal"
           :in-theory (e/d (fn-pzd-decode fn-zin-payload-with fn-octets-from-list fn-zin-out-list)
                           (fn-zin-payload-bufs fn-pzw-initialize create-fn-zin-st
                            fn-zin-feed fn-zin-stored-limit fn-zin-stored-status fn-pzd-answer
                            fn-pzd-budget fn-zin-payload-bufs-is-payload-with nfix min))))))

(local
 (defthm fn-pwzd-actual-canonical-decode-terminal-unrestricted-input
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets))
        (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed b credited 0 c m fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (implies (and (not (equal (car r) :full)) (not (equal (car r) :yield))
                (< (len (mv-nth 6 r)) (fn-zin-stored-limit c (+ 1 (nfix n)))))
   (equal (fn-pzd-decode dict fn-octets n)
          (if (and (zp n) (atom fn-octets)) (list :ok nil)
            (fn-pzd-answer (fn-zin-stored-status (car r) c (mv-nth 3 r)) (mv-nth 6 r) n)))))
 :rule-classes nil
 :hints (("Goal"
           :use ((:instance fn-pwzd-actual-canonical-decode-feed-unrestricted-input)
                 (:instance fn-pwzc-actual-canonical-feed-never-yields)
                 (:instance fn-pwzd-actual-feed-terminal-frontier-independent
                  (b1 b) (b2 (fn-pzd-budget (len fn-octets) n))
                  (ip 0) (end (len fn-octets)) (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                  (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))))
           :in-theory (e/d (fn-pwz-semantic-observation)
                           (fn-pzd-decode fn-pzd-answer fn-pzd-budget fn-zin-feed fn-zin-loop
                            fn-zin-stored-status fn-zin-stored-limit fn-pzw-initialize create-fn-zin-st
                            nfix min))))))

(local
 (defthm fn-pwzd-logical-snoc-length
  (equal (len (fn-oct-snoc xs o)) (+ 1 (len xs)))
  :hints (("Goal" :induct (fn-oct-snoc xs o) :in-theory (enable fn-oct-snoc)))))

(local
 (defthm fn-pwzd-logical-back-copy-length
   (implies (and (posp off) (<= off (len xs)))
            (equal (len (fn-oct-back-copy off n xs)) (+ (len xs) (nfix n))))
   :hints (("Goal" :induct (fn-oct-back-copy off n xs)))))

(local
 (defthm fn-pwzd-logical-nthcdr-length
  (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))
  :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr nfix len)))))

(local
 (defthm fn-pwzd-actual-payload-ready-buffer-lengths-unconditional
  (let ((r (fn-zin-payload-ready dict fn-zin-win fn-zin-tab)))
   (and (equal (len (mv-nth 1 r)) 65536) (equal (len (mv-nth 2 r)) 3494)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-payload-ready)
                           (fn-oct-back-copy (:e fn-oct-back-copy)
                            (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back)
                            (:e fn-octets$a-append-back)))))))

(local
 (defthm fn-pwzd-actual-initialize-buffer-lengths-unconditional
  (let ((r (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (and (equal (len (mv-nth 1 r)) 65536) (equal (len (mv-nth 2 r)) 3494)))
  :hints (("Goal" :in-theory (e/d (fn-pzw-initialize) (fn-zin-reset fn-zin-payload-ready))))))

(local
 (defthm fn-pwzd-actual-initialized-stored-output-count-unconditional
  (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
         (r (fn-pzw-stored-chunk requested remaining 0 end compressed expected (car init)
                                 fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
   (equal (fn-zin-tout (mv-nth 3 r)) (len (mv-nth 6 r))))
  :hints (("Goal" :use (:instance fn-pzw-stored-chunk-counts-real-input (start 0)
                        (fn-zin-st (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                        (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
           :in-theory (disable fn-pzw-stored-chunk fn-pzw-initialize create-fn-zin-st
                               fn-pzw-stored-chunk-counts-real-input fn-zin-loop-counts)))))

(local
 (defthm fn-pwzc-update-octet-retains-length
  (implies (and (natp i) (< i (len x)))
   (equal (len (fn-oct-update i o x)) (len x)))
  :hints (("Goal" :induct (fn-oct-update i o x) :in-theory (enable fn-oct-update)))))

(local
 (defthm fn-pwzc-table-length-word-write
  (implies (and (natp e) (< e *fn-zin-tab-entries*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (equal (len (fn-zin-tput e v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-tput) (fn-oct-update))))))

(local
 (defthm fn-pwzc-code-length-bounds-unconditional
  (and (natp (fn-zin-len-of e fn-zin-tab)) (<= (fn-zin-len-of e fn-zin-tab) 15))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (fn-zin-len-of e fn-zin-tab))) (:linear :corollary (<= (fn-zin-len-of e fn-zin-tab) 15)))
  :hints (("Goal" :in-theory (enable fn-zin-len-of)))))

(local
 (defthm fn-pwzc-zero-counts-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-counts k cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-counts k cb fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-counts) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-count-lens-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-count-lens s n lb cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-count-lens s n lb cb fn-zin-tab)
           :in-theory (e/d (fn-zin-count-lens) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-offsets-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-offsets len off cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-offsets len off cb fn-zin-tab)
           :in-theory (e/d (fn-zin-offsets) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-place-syms-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-place-syms s n lb sb smax fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-place-syms s n lb sb smax fn-zin-tab)
           :in-theory (e/d (fn-zin-place-syms) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-zero-range-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-range e k fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-range e k fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-range) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-next-codes-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-next-codes len code cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-next-codes len code cb fn-zin-tab)
           :in-theory (e/d (fn-zin-next-codes) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-replicate-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-replicate e step k v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-replicate e step k v fn-zin-tab)
           :in-theory (e/d (fn-zin-replicate) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-fill-lookup-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fill-lookup s n lb base fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-fill-lookup s n lb base fn-zin-tab)
           :in-theory (e/d (fn-zin-fill-lookup) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-fill-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fill e k v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-fill e k v fn-zin-tab)
           :in-theory (e/d (fn-zin-fill) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-zero-cl-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-cl i fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-cl i fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-cl) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-construct-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (mv-nth 1 (fn-zin-construct tb lb n fn-zin-tab))) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-construct)
                           (fn-zin-tput fn-zin-zero-range fn-zin-zero-counts fn-zin-count-lens
                            fn-zin-offsets fn-zin-place-syms fn-zin-next-codes fn-zin-fill-lookup))))))

(local
 (defthm fn-pwzc-fixed-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fixed-tables fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-fixed-tables) (fn-zin-fill fn-zin-construct))))))

(local
 (defthm fn-pwzc-dynamic-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (mv-nth 1 (fn-zin-dynamic-tables hlit hdist fn-zin-tab))) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-dynamic-tables) (fn-zin-construct))))))

(local
 (defthm fn-pwzc-emit-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit) (fn-oct-update fn-zin-emit-out))))))

(local
 (defthm fn-pwzc-actual-action-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-zin-act)
           (fn-zin-emit fn-zin-emit-out fn-zin-construct fn-zin-fixed-tables fn-zin-dynamic-tables fn-zin-fill fn-zin-zero-cl fn-zin-tput))))))

(local
 (defthm fn-pwzc-copy-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 1 (fn-zin-copy k w d tout h fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :induct (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)
           :in-theory (e/d (fn-zin-copy) (fn-oct-update))))))

(local
 (defthm fn-pwzc-match-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-match) (fn-zin-copy))))))

(local
 (defthm fn-pwzc-literal-loop-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 4 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
           :in-theory (e/d (fn-zin-lit-loop) (fn-oct-update))))))

(local
 (defthm fn-pwzc-literals-retain-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-lits) (fn-zin-lit-loop))))))

(local
 (defthm fn-pwzc-actual-step-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :in-theory (e/d (fn-zin-step)
           (fn-zin-act fn-zin-match fn-zin-lits fn-zin-step-out-free))))))

(local
 (defthm fn-pwzc-actual-loop-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 4 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 5 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
           (fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-step-out-free fn-zin-loop-counts))))))

(local
 (defthm fn-pwie-actual-feed-refilled-more-windows
  (let* ((r1 (fn-zin-feed b1 fn-zin-st 0 (len a) m a fn-zin-win fn-zin-tab nil)) (r2 (fn-zin-feed b2 (mv-nth 3 (fn-zin-feed b1 fn-zin-st 0 (len a) m a fn-zin-win fn-zin-tab nil)) 0 (len c) lim c (mv-nth 4 (fn-zin-feed b1 fn-zin-st 0 (len a) m a fn-zin-win fn-zin-tab nil)) (mv-nth 5 (fn-zin-feed b1 fn-zin-st 0 (len a) m a fn-zin-win fn-zin-tab nil)) nil)) (whole (fn-zin-feed b0 fn-zin-st 0 (len (append a c)) (+ (len (mv-nth 6 (fn-zin-feed b1 fn-zin-st 0 (len a) m a fn-zin-win fn-zin-tab nil))) (nfix lim)) (append a c) fn-zin-win fn-zin-tab nil)))
   (implies (and (equal (len fn-zin-win) 65536) (equal (len fn-zin-tab) 3494)
                 (equal (car r1) :more) (posp (nfix lim))
                 (not (equal (car r2) :yield)) (not (equal (car whole) :yield)))
    (equal (fn-pwie-semantic-observation whole)
     (list (car r2) (+ (len a) (mv-nth 2 r2)) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
           (append (mv-nth 6 r1) (mv-nth 6 r2))))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pwie-actual-refilled-more-windows-without-logical-types)
         (:instance fn-pwzc-actual-loop-keeps-buffer-lengths (b b1) (ip 0) (end (len a)) (lim m) (fn-octets a) (fn-zin-out nil)))
   :in-theory (e/d (fn-zin-feed fn-zin-window-ready-p fn-zin-tab-okp fn-pwie-semantic-observation)
                   (fn-zin-loop fn-zin-feed-unfolds fn-zin-step fn-zin-act fn-zin-pull fn-zin-need
                    fn-zin-loop-counts fn-zin-loop-keeps fn-zin-loop-stops
                    fn-zin-loop-split-input fn-zin-loop-out-free fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel))))))

(local
 (defthm fn-pwzd-actual-stored-room-positive
  (posp (nfix (fn-pzw-room bound tout)))
  :hints (("Goal" :in-theory (enable fn-pzw-room)))))

(local
 (defthm fn-pwie-actual-initialized-refilled-stored-window-trajectory
  (let* ((r1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (r2 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (whole (fn-zin-feed b0 (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0 (len (append a c)) (+ (len (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))) (append a c) (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))
   (implies (and (equal (car r1) :more) (not (equal (car r2) :yield))
                 (not (equal (car whole) :yield)))
    (equal (fn-pwie-semantic-observation whole)
     (list (car r2) (+ (len a) (mv-nth 2 r2))
       (fn-zin-set 7 (+ (len (append a c)) (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
       (mv-nth 4 r2) (mv-nth 5 r2) (append (mv-nth 6 r1) (mv-nth 6 r2))))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple
          (requested requested1) (remaining (fn-pzd-budget (len (append a c)) n)) (start 0) (end (len a))
          (compressed (len (append a c))) (expected n) (fn-zin-st (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
          (fn-octets a) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
         (:instance fn-pwie-actual-two-refilled-stored-chunks-full-tuple
          (remaining1 (fn-pzd-budget (len (append a c)) n)) (remaining2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (compressed (len (append a c))) (expected n)
          (fn-zin-st (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
         (:instance fn-pwie-actual-feed-refilled-more-windows
          (b1 (fn-pzw-quantum requested1 (fn-pzd-budget (len (append a c)) n))) (b2 (fn-pzw-quantum requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))) (m (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))))) (lim (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))
          (fn-zin-st (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
         (:instance fn-pwie-observation-of-seven-tuple
          (r (fn-zin-feed (fn-pzw-quantum requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (mv-nth 3 (fn-zin-feed (fn-pzw-quantum requested1 (fn-pzd-budget (len (append a c)) n)) (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0 (len a) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) 0 (len c) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (mv-nth 3 (fn-zin-feed (fn-pzw-quantum requested1 (fn-pzd-budget (len (append a c)) n)) (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0 (len a) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) c (mv-nth 4 (fn-zin-feed (fn-pzw-quantum requested1 (fn-pzd-budget (len (append a c)) n)) (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0 (len a) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-zin-feed (fn-pzw-quantum requested1 (fn-pzd-budget (len (append a c)) n)) (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0 (len a) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) nil)) (a (car (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))) (b (mv-nth 1 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))) (c (mv-nth 2 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))
          (d (fn-zin-set 7 (+ (len (append a c)) (fn-zin-tin (mv-nth 3 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))) (mv-nth 3 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))) (e (mv-nth 4 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))) (f (mv-nth 5 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))) (g (mv-nth 6 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))))
   :in-theory (e/d (fn-pwie-semantic-observation)
                   (fn-zin-feed fn-zin-feed-unfolds fn-zin-loop fn-pzw-stored-chunk fn-pzw-stored-chunk-is-resumable-run fn-pzw-initialize create-fn-zin-st
                    fn-pzd-budget fn-pzw-budget-left fn-pzw-room fn-pzw-quantum fn-pzw-stored-allowance
                    fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-loop-counts nfix min))))))

(local
 (defthm fn-pwie-actual-refilled-stored-final-bound-funds-whole-trajectory
  (let* ((r1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (r2 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (whole (fn-zin-feed (fn-pzd-budget (len (append a c)) n) (fn-zin-set 7 (len (append a c)) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0 (len (append a c)) (+ (len (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))) (append a c) (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))
   (implies (< (len (append (mv-nth 6 r1) (mv-nth 6 r2))) (fn-zin-stored-limit (len (append a c)) (+ 1 (nfix n))))
    (not (equal (car whole) :yield))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pwzd-actual-bounded-frontier-feed-never-yields (fn-octets (append a c)) (m (+ (len (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))))
         (:instance fn-pwzc-canonical-output-frontier-bounds (c (len (append a c))))
         (:instance fn-pwzd-stored-global-frontier-bound (produced (len (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (expected n) (allowance (fn-pzw-stored-allowance (len (append a c))))))
   :in-theory (disable fn-zin-feed fn-zin-feed-unfolds fn-zin-loop fn-pzw-stored-chunk fn-pzw-stored-chunk-is-resumable-run
                       fn-pzw-initialize create-fn-zin-st fn-pzd-budget fn-pzw-budget-left
                       fn-pzw-room fn-pzw-quantum fn-pzw-stored-allowance fn-zin-stored-limit
                       fn-pwzd-stored-global-frontier-bound fn-pwzc-canonical-output-frontier-bounds
                       fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-loop-counts nfix min)))))

(local
 (defthm fn-pwie-actual-refused-act-retains-output
  (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (car r) (equal (mv-nth 4 r) fn-zin-out)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-act fn-zin-emit)
                           (fn-zin-act-counts fn-zin-emit-out))))))

(local
 (defthm fn-pwie-actual-refused-step-retains-output
  (let ((r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (car r) (equal (mv-nth 4 r) fn-zin-out)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-step fn-zin-match)
                           (fn-zin-act fn-zin-emit fn-zin-lits fn-zin-copy fn-zin-step-counts fn-zin-match-counts))))))

(local
 (defthm fn-pwie-actual-nonfull-nonyield-loop-output-strict
  (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (< (len fn-zin-out) (nfix lim))
                 (not (equal (car r) :full)) (not (equal (car r) :yield)))
    (< (len (mv-nth 6 r)) (nfix lim))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
                           (fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-loop-counts fn-zin-loop-keeps fn-zin-loop-stops nfix min))))))

(local
 (defthm fn-pwie-actual-stored-nonfull-nonyield-output-strict
  (let ((r (fn-pzw-stored-chunk requested remaining start end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (not (equal (car r) :full)) (not (equal (car r) :yield)))
    (< (len (mv-nth 6 r))
       (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout fn-zin-st)))))
  :rule-classes nil
  :hints (("Goal"
   :use (:instance fn-pwie-actual-nonfull-nonyield-loop-output-strict
          (b (fn-pzw-quantum requested remaining)) (ip start)
          (lim (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout fn-zin-st)))
          (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
          (fn-zin-out nil))
   :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-pzw-room nfix min)
                   (fn-pwie-actual-nonfull-nonyield-loop-output-strict fn-zin-loop fn-zin-feed-unfolds fn-pzw-stored-chunk-is-resumable-run
                    fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-pzw-quantum fn-zin-loop-counts))))))

(local
 (defthm fn-pwie-stored-initial-room-bound
  (<= (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance compressed)) 0)
      (+ 1 (min (nfix n) (fn-pzw-stored-allowance compressed))))
  :hints (("Goal" :in-theory (enable fn-pzw-room min nfix)))))

(local
 (defthm fn-pwie-stored-two-room-global-frontier
  (implies (and (natp produced) (natp count)
                (<= produced (min (nfix n) (fn-pzw-stored-allowance compressed)))
                (< count (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance compressed)) produced)))
   (< (+ produced count) (fn-zin-stored-limit compressed (+ 1 (nfix n)))))
  :hints (("Goal" :in-theory (enable fn-pzw-room fn-pzw-stored-allowance fn-zin-stored-allowance fn-zin-stored-limit min nfix)))))

(local
 (defthm fn-pwie-actual-more-refill-establishes-final-frontier
  (let* ((r1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (r2 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))
   (implies (and (equal (car r1) :more) (not (equal (car r2) :yield)) (not (equal (car r2) :full)))
    (< (len (append (mv-nth 6 r1) (mv-nth 6 r2))) (fn-zin-stored-limit (len (append a c)) (+ 1 (nfix n))))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pwie-actual-stored-nonfull-nonyield-output-strict
          (requested requested1) (remaining (fn-pzd-budget (len (append a c)) n)) (start 0) (end (len a)) (compressed (len (append a c))) (expected n)
          (fn-zin-st (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-octets a) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
         (:instance fn-pwie-actual-stored-nonfull-nonyield-output-strict
          (requested requested2) (remaining (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (start 0) (end (len c)) (compressed (len (append a c))) (expected n)
          (fn-zin-st (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-octets c) (fn-zin-win (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-zin-tab (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-zin-out (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))
         (:instance fn-pwie-stored-two-room-global-frontier
          (produced (len (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (count (len (mv-nth 6 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))) (compressed (len (append a c))))
         (:instance fn-pwie-stored-initial-room-bound (compressed (len (append a c)))))
   :in-theory (disable fn-zin-feed fn-zin-feed-unfolds fn-zin-loop fn-pzw-stored-chunk fn-pzw-stored-chunk-is-resumable-run
                       fn-pzw-initialize create-fn-zin-st fn-pzd-budget fn-pzw-budget-left fn-pzw-room fn-pzw-quantum
                       fn-pzw-stored-allowance fn-zin-stored-limit fn-pwie-stored-two-room-global-frontier fn-pwie-stored-initial-room-bound
                       fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-loop-counts nfix min)))))

(defthm fn-pwzi-actual-refilled-stored-windows-canonical-answer
  (let* ((r1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (r2 (fn-pzw-stored-chunk requested2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len (append a c)) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) 0 (len c) (len (append a c)) n (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) c (mv-nth 4 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 5 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)) (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (out (append (mv-nth 6 r1) (mv-nth 6 r2))))
   (implies (and (equal (car r1) :more) (not (equal (car r2) :yield)) (not (equal (car r2) :full))
                 )
    (equal (fn-pzd-decode dict (append a c) n)
     (if (and (zp n) (atom (append a c))) (list :ok nil)
       (fn-pzd-answer (fn-zin-stored-status (car r2) (len (append a c)) (mv-nth 3 r2)) out n)))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pwie-actual-more-refill-establishes-final-frontier)
         (:instance fn-pwie-actual-initialized-refilled-stored-window-trajectory (b0 (fn-pzd-budget (len (append a c)) n)))
         (:instance fn-pwie-actual-refilled-stored-final-bound-funds-whole-trajectory)
         (:instance fn-pwzd-actual-canonical-decode-terminal-unrestricted-input
          (fn-octets (append a c)) (b (fn-pzd-budget (len (append a c)) n)) (m (+ (len (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len (append a c)))) (fn-zin-tout (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len (append a c)) n) 0 (len a) (len (append a c)) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) a (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))))))
   :in-theory (e/d (fn-pwie-semantic-observation)
                   (fn-zin-feed fn-zin-feed-unfolds fn-zin-loop fn-pzw-stored-chunk fn-pzw-stored-chunk-is-resumable-run
                    fn-pzw-initialize create-fn-zin-st fn-pzd-decode fn-pzd-answer fn-zin-stored-status fn-zin-stored-limit
                    fn-pzd-budget fn-pzw-budget-left fn-pzw-room fn-pzw-quantum fn-pzw-stored-allowance
                    fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-loop-counts nfix min)))))
