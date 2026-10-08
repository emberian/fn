; Monotonic transfer from idle DEFAULT pool authority to larger Store state.
; Called under the actual owner->extent mutex envelope; no pool reset/refund.
(in-package "ACL2")
(include-book "page-read-ledger")
(defun fn-prl-resident-budget (resident budget)
 (declare (xargs :guard t))
 (list resident (fn-prl-nth 1 budget) (fn-prl-nth 2 budget)
                (fn-prl-nth 3 budget) (fn-prl-nth 4 budget)))
(defun fn-prl-resident-shrink (amount ledger)
 (declare (xargs :guard t))
 (let* ((budget (fn-prl-nth 0 ledger)) (charged (fn-prl-nth 1 ledger))
        (baseline (fn-prl-baseline ledger))
        (resident (fn-prl-nth 0 budget)))
  (if (not (and (natp amount) (natp resident) (<= amount resident)
                 (fn-prs-fundedp budget baseline '(0 0 0 0 0) charged)))
      (mv :read-resources-unavailable ledger)
    (let ((next (fn-prl-resident-budget (- resident amount) budget)))
     (if (not (fn-prs-fundedp next baseline '(0 0 0 0 0) charged))
         (mv :read-resources-unavailable ledger)
       (mv :protected-growth-admitted
           (fn-prl-build next charged (fn-prl-nth 2 ledger)
                         (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger))))))))
(defthm fn-prl-resident-shrink-preserves-custody
 (let ((next (mv-nth 1 (fn-prl-resident-shrink amount ledger))))
  (and (equal (fn-prl-nth 1 next) (fn-prl-nth 1 ledger))
       (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
       (equal (fn-prl-nth 3 next) (fn-prl-nth 3 ledger))
       (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger))))
 :hints (("Goal" :in-theory (e/d (fn-prl-resident-shrink fn-prl-build fn-prl-nth)
   (fn-prl-resident-budget fn-prs-fundedp fn-prl-baseline)))))
(defthm fn-prl-resident-shrink-keeps-funding
 (implies (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
                         (fn-prl-nth 1 ledger))
          (let ((next (mv-nth 1 (fn-prl-resident-shrink amount ledger))))
           (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next) '(0 0 0 0 0)
                          (fn-prl-nth 1 next))))
 :hints (("Goal" :in-theory (e/d (fn-prl-resident-shrink fn-prl-build fn-prl-nth fn-prl-baseline)
   (fn-prl-resident-budget fn-prs-fundedp)))))

; Growth RESERVATION across the phased reconfiguration's I/O windows (ruling 19).
; The reserve is a charged :cached row (demand (AMOUNT 0 0 0 0)) bound to the token
; (:growth-reserve NEXT); fn-prs-fundedp counts CHARGED, so every draw respects it.
; CONVERT evicts the row and shrinks the resident budget by AMOUNT in one entry (the
; transfer stays one-way); RELEASE is plain fn-prl-evict on the token.
; The row is IN MEMORY, not durable: a crash inside a window loses it, and open
; rebuilds the ledger.
(defun fn-prl-growth-token (next)
  (declare (xargs :guard t))
  (list :growth-reserve next))

(defun fn-prl-reserve-growth (ledger amount)
  (declare (xargs :guard t))
  (let* ((budget (fn-prl-nth 0 ledger)) (charged (fn-prl-nth 1 ledger))
         (next (fn-prl-nth 2 ledger)) (demand (list amount 0 0 0 0)))
    (mv-let (verdict next1 charged1)
      (if (natp amount)
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0) charged
                        next (fn-prl-nth 4 budget) demand)
        (mv :invalid-read-demand next charged))
      (if (not (equal verdict :admitted))
          (mv verdict nil ledger)
        (let ((token (fn-prl-growth-token next)))
          (mv :admitted token
              (fn-prl-build budget charged1 next1
                            (cons (cons token (list demand :cached nil)) (fn-prl-nth 3 ledger))
                            (fn-prl-nth 4 ledger))))))))

(defun fn-prl-convert-growth (ledger token amount)
  (declare (xargs :guard t))
  (mv-let (word released)
    (fn-prl-evict ledger token)
    (if (not (equal word :evicted))
        (mv word ledger)
      (mv-let (word2 grown)
        (fn-prl-resident-shrink amount released)
        (if (equal word2 :protected-growth-admitted)
            (mv word2 grown)
          (mv word2 ledger))))))

; G1
(defthm fn-prl-reserve-growth-preserves-pool-funding
  (implies (equal (mv-nth 0 (fn-prl-reserve-growth ledger amount)) :admitted)
           (fn-prs-fundedp
            (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
            (fn-prl-nth 1 (mv-nth 2 (fn-prl-reserve-growth ledger amount)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prl-reserve-growth fn-prl-build fn-prl-nth)
           :use ((:instance fn-prs-issue-preserves-static-rescue
                  (budget (fn-prl-nth 0 ledger))
                  (used (fn-prl-baseline ledger)) (rescue '(0 0 0 0 0))
                  (charged (fn-prl-nth 1 ledger))
                  (next (fn-prl-nth 2 ledger))
                  (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger)))
                  (demand (list amount 0 0 0 0)))))))

; --- local arithmetic and shape facts for G2/G4 ---
(local
 (defthm fn-prs-nats-p-of-list5
   (equal (fn-prs-nats-p (list a b c d e))
          (and (natp a) (natp b) (natp c) (natp d) (natp e)))
   :hints (("Goal" :in-theory (enable fn-prs-nats-p)))))

(local
 (defthm fn-prs-nats-p-true-listp-aux
   (implies (fn-prs-nats-p xs) (true-listp xs))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-prs-nats-p)))))

(local
 (defthm fn-prl-nth-is-nth
   (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-prl-nth)))))

(local
 (defthm fn-prs-fundedp-vectors
   (implies (fn-prs-fundedp b u r c)
            (and (fn-prs-vectorp b) (fn-prs-vectorp u) (fn-prs-vectorp r) (fn-prs-vectorp c)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-prs-fundedp)))))

(local
 (defthm fn-prs-vectorp-true-listp
   (implies (fn-prs-vectorp x) (true-listp x))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-prs-vectorp)
            :use ((:instance fn-prs-nats-p-true-listp-aux (xs x)))))))

(local
 (defthm fn-prl-evict-of-cached-row
   (implies (and (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                        (cons token (list demand :cached nil)))
                 (true-listp (fn-prl-nth 1 ledger)) (true-listp demand))
            (equal (fn-prl-evict ledger token)
                   (list :evicted
                         (fn-prl-build (fn-prl-nth 0 ledger)
                                       (fn-prs-release-reusable (fn-prl-nth 1 ledger) demand)
                                       (fn-prl-nth 2 ledger)
                                       (fn-prl-remove token (fn-prl-nth 3 ledger))
                                       (fn-prl-nth 4 ledger)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-prl-evict fn-prl-nth)))))

(local
 (defthm fn-prs-vectorp-natp-0
   (implies (fn-prs-vectorp x) (natp (nth 0 x)))
   :hints (("Goal" :in-theory (enable fn-prs-vectorp fn-prs-nats-p)))))

(local
 (defthm fn-prl-evict-of-cached-row-rewrite
   (implies (and (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                        (cons token (list (list amount 0 0 0 0) :cached nil)))
                 (true-listp (fn-prl-nth 1 ledger)))
            (and (equal (mv-nth 0 (fn-prl-evict ledger token)) :evicted)
                 (equal (mv-nth 1 (fn-prl-evict ledger token))
                        (fn-prl-build (fn-prl-nth 0 ledger)
                                      (fn-prs-release-reusable (fn-prl-nth 1 ledger)
                                                               (list amount 0 0 0 0))
                                      (fn-prl-nth 2 ledger)
                                      (fn-prl-remove token (fn-prl-nth 3 ledger))
                                      (fn-prl-nth 4 ledger)))))
   :hints (("Goal" :use ((:instance fn-prl-evict-of-cached-row (demand (list amount 0 0 0 0)))))))) 

(local
 (defthm fn-prl-nth-of-build
   (and (equal (fn-prl-nth 0 (fn-prl-build b c n r u)) b)
        (equal (fn-prl-nth 1 (fn-prl-build b c n r u)) c)
        (equal (fn-prl-nth 2 (fn-prl-build b c n r u)) n)
        (equal (fn-prl-nth 3 (fn-prl-build b c n r u)) r))
   :hints (("Goal" :in-theory (enable fn-prl-build fn-prl-nth)))))

(local
 (defthm fn-prl-nth-4-of-build
   (equal (fn-prl-nth 4 (fn-prl-build b c n r u)) u)
   :hints (("Goal" :in-theory (enable fn-prl-build fn-prl-nth)))))

(local
 (defthm fn-prl-baseline-of-build
   (equal (fn-prl-baseline (fn-prl-build b c n r u)) (or u '(0 0 0 0 0)))
   :hints (("Goal" :in-theory (enable fn-prl-baseline)))))

(local
 (defthm fn-prs-vectorp-destructure
   (implies (fn-prs-vectorp x)
            (equal x (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-prs-vectorp)
            :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x)) (len (cddddr x))
                     (fn-prs-nats-p x) (fn-prs-nats-p (cdr x)) (fn-prs-nats-p (cddr x))
                     (fn-prs-nats-p (cdddr x)) (fn-prs-nats-p (cddddr x)) (fn-prs-nats-p (cdr (cddddr x))) (len (cdr (cddddr x))))))))

(local
 (defthm fn-prl-shrink-core
   (implies (and (equal b (list b0 b1 b2 b3 b4)) (equal u (list u0 u1 u2 u3 u4))
                 (equal c (list c0 c1 c2 c3 c4))
                 (natp b0) (natp b1) (natp b2) (natp b3) (natp b4)
                 (natp u0) (natp u1) (natp u2) (natp u3) (natp u4)
                 (natp c0) (natp c1) (natp c2) (natp c3) (natp c4)
                 (natp a) (<= a c0)
                 (fn-prs-fundedp b u '(0 0 0 0 0) c))
            (and (<= a b0)
                 (fn-prs-fundedp b u '(0 0 0 0 0) (fn-prs-release-reusable c (list a 0 0 0 0)))
                 (fn-prs-fundedp (list (- b0 a) b1 b2 b3 b4) u '(0 0 0 0 0)
                                 (fn-prs-release-reusable c (list a 0 0 0 0)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-prs-fundedp fn-prs-vectorp fn-prs-plus fn-prs-below fn-prs-release-reusable fn-prs-nats-p)))))

(local
 (defthm fn-prs-vectorp-nths-natp
   (implies (fn-prs-vectorp x)
            (and (natp (nth 0 x)) (natp (nth 1 x)) (natp (nth 2 x)) (natp (nth 3 x)) (natp (nth 4 x))))
   :hints (("Goal" :in-theory (enable fn-prs-vectorp)
            :use fn-prs-vectorp-destructure))))

(local
 (defthm fn-prl-shrink-after-release-funded
   (implies (and (fn-prs-vectorp b) (fn-prs-vectorp u) (fn-prs-vectorp c)
                 (natp a) (<= a (nth 0 c))
                 (fn-prs-fundedp b u '(0 0 0 0 0) c))
            (and (<= a (nth 0 b))
                 (fn-prs-fundedp b u '(0 0 0 0 0) (fn-prs-release-reusable c (list a 0 0 0 0)))
                 (fn-prs-fundedp (fn-prl-resident-budget (- (nth 0 b) a) b) u '(0 0 0 0 0)
                                 (fn-prs-release-reusable c (list a 0 0 0 0)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-prl-resident-budget fn-prl-nth) (fn-prs-fundedp fn-prs-release-reusable fn-prs-vectorp))
            :use ((:instance fn-prl-shrink-core (b0 (nth 0 b)) (b1 (nth 1 b)) (b2 (nth 2 b)) (b3 (nth 3 b)) (b4 (nth 4 b))
                   (u0 (nth 0 u)) (u1 (nth 1 u)) (u2 (nth 2 u)) (u3 (nth 3 u)) (u4 (nth 4 u))
                   (c0 (nth 0 c)) (c1 (nth 1 c)) (c2 (nth 2 c)) (c3 (nth 3 c)) (c4 (nth 4 c)))
                  (:instance fn-prs-vectorp-destructure (x b)) (:instance fn-prs-vectorp-nths-natp (x b)) (:instance fn-prs-vectorp-nths-natp (x u)) (:instance fn-prs-vectorp-nths-natp (x c))
                  (:instance fn-prs-vectorp-destructure (x u))
                  (:instance fn-prs-vectorp-destructure (x c)))))))

(local
 (defthm fn-prl-evict-word-cases
   (or (equal (mv-nth 0 (fn-prl-evict ledger token)) :evicted)
       (equal (mv-nth 0 (fn-prl-evict ledger token)) :stale))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-prl-evict)))))

; G2: conversion is admitted and funded whenever CHARGED still covers the reserve
; row.  Across draws that hypothesis rests on repair item PRL-ROW-SUM-INVARIANT
; (charged >= the sum of the bound rows' demands), not yet a theorem.
(defthm fn-prl-convert-growth-when-charged-covers-the-reserve
  (implies (and (natp amount)
                (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                       (cons token (list (list amount 0 0 0 0) :cached nil)))
                (<= amount (fn-prl-nth 0 (fn-prl-nth 1 ledger)))
                (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                                '(0 0 0 0 0) (fn-prl-nth 1 ledger)))
           (and (equal (mv-nth 0 (fn-prl-convert-growth ledger token amount))
                       :protected-growth-admitted)
                (let ((next (mv-nth 1 (fn-prl-convert-growth ledger token amount))))
                  (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next)
                                  '(0 0 0 0 0) (fn-prl-nth 1 next)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-convert-growth fn-prl-resident-shrink fn-prl-baseline)
                                  (fn-prs-fundedp fn-prs-vectorp fn-prl-resident-budget
                                   fn-prs-release-reusable))
           :use ((:instance fn-prl-evict-of-cached-row (demand (list amount 0 0 0 0)))
                 (:instance fn-prl-shrink-after-release-funded
                  (b (fn-prl-nth 0 ledger)) (u (fn-prl-baseline ledger))
                  (c (fn-prl-nth 1 ledger)) (a amount))
                 (:instance fn-prs-fundedp-vectors (b (fn-prl-nth 0 ledger)) (u (fn-prl-baseline ledger))
                  (r '(0 0 0 0 0)) (c (fn-prl-nth 1 ledger)))
                 (:instance fn-prs-vectorp-true-listp (x (fn-prl-nth 1 ledger)))
                 (:instance fn-prs-vectorp-natp-0 (x (fn-prl-nth 0 ledger)))
                 (:instance fn-prl-nth-is-nth (n 0) (x (fn-prl-nth 0 ledger)))
                 (:instance fn-prl-nth-is-nth (n 0) (x (fn-prl-nth 1 ledger)))
                 (:instance fn-prl-nth-is-nth (n 0) (x (fn-prl-nth 0 ledger)))))))

; G3 (unfolds the definition; not cited as an event)
(defthm fn-prl-convert-growth-is-shrink-of-evict-by-definition
  (implies (equal (mv-nth 0 (fn-prl-convert-growth ledger token amount))
                  :protected-growth-admitted)
           (let ((conv (mv-nth 1 (fn-prl-convert-growth ledger token amount)))
                 (shr (mv-nth 1 (fn-prl-resident-shrink
                                 amount (mv-nth 1 (fn-prl-evict ledger token))))))
             (and (equal (fn-prl-nth 0 conv) (fn-prl-nth 0 shr))
                  (equal (fn-prl-nth 1 conv) (fn-prl-nth 1 shr))
                  (equal (fn-prl-nth 3 conv) (fn-prl-nth 3 shr)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prl-convert-growth)
           :use fn-prl-evict-word-cases)))


; G4: release releases exactly the reserve row's charge and its binding.
(defthm fn-prl-release-growth-frees-exactly-the-reserve
  (implies (and (natp amount)
                (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                       (cons token (list (list amount 0 0 0 0) :cached nil)))
                (true-listp (fn-prl-nth 1 ledger)))
           (and (equal (mv-nth 0 (fn-prl-evict ledger token)) :evicted)
                (equal (fn-prl-nth 1 (mv-nth 1 (fn-prl-evict ledger token)))
                       (list (nfix (- (nfix (nth 0 (fn-prl-nth 1 ledger))) amount))
                             (nfix (nth 1 (fn-prl-nth 1 ledger)))
                             (nfix (nth 2 (fn-prl-nth 1 ledger)))
                             (nfix (nth 3 (fn-prl-nth 1 ledger)))
                             (nfix (nth 4 (fn-prl-nth 1 ledger)))))
                (equal (fn-prl-nth 3 (mv-nth 1 (fn-prl-evict ledger token)))
                       (fn-prl-remove token (fn-prl-nth 3 ledger)))
                (equal (fn-prl-nth 0 (mv-nth 1 (fn-prl-evict ledger token)))
                       (fn-prl-nth 0 ledger))
                (equal (fn-prl-nth 2 (mv-nth 1 (fn-prl-evict ledger token)))
                       (fn-prl-nth 2 ledger))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prs-release-reusable))))

(local
 (defun fn-prl-rev2 (rev a b)
   (declare (xargs :guard t))
   (if (consp rev)
       (fn-prl-rev2 (cdr rev) (cons (car rev) a) (cons (car rev) b))
     (list a b))))

(local
 (defthm fn-prl-binding-of-revappend-congruence
   (implies (equal (fn-prl-binding token a) (fn-prl-binding token b))
            (equal (fn-prl-binding token (revappend rev a))
                   (fn-prl-binding token (revappend rev b))))
   :hints (("Goal" :in-theory (enable fn-prl-binding)
            :induct (fn-prl-rev2 rev a b)))))

(local
 (defthm fn-prl-binding-of-revappend-skip
   (implies (or (not (consp x)) (not (equal token (car x))))
            (equal (fn-prl-binding token (revappend rev (cons x r)))
                   (fn-prl-binding token (revappend rev r))))
   :hints (("Goal" :in-theory (enable fn-prl-binding)
            :use ((:instance fn-prl-binding-of-revappend-congruence
                   (a (cons x r)) (b r)))))))

(local
 (defthm fn-prl-binding-of-revappend-aux
   (implies (not (equal token other))
            (equal (fn-prl-binding token (fn-prl-remove-aux other rows rev))
                   (fn-prl-binding token (revappend rev rows))))
   :hints (("Goal" :in-theory (enable fn-prl-binding fn-prl-remove-aux)
            :induct (fn-prl-remove-aux other rows rev)))))

(local
 (defthm fn-prl-binding-of-remove-other
   (implies (not (equal token other))
            (equal (fn-prl-binding token (fn-prl-remove other rows))
                   (fn-prl-binding token rows)))
   :hints (("Goal" :in-theory (enable fn-prl-remove)))))

(local
 (defthm fn-prl-binding-of-cons-other
   (implies (not (equal token key))
            (equal (fn-prl-binding token (cons (cons key row) rows))
                   (fn-prl-binding token rows)))
   :hints (("Goal" :in-theory (enable fn-prl-binding)))))

; G5(b): binding survival.  Every ledger transition keeps the binding of a token
; it does not name.  The reserve row survives any draw by another token.
(defthm fn-prl-evict-keeps-other-bindings
  (implies (not (equal token other))
           (equal (fn-prl-binding token (fn-prl-nth 3 (mv-nth 1 (fn-prl-evict ledger other))))
                  (fn-prl-binding token (fn-prl-nth 3 ledger))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prl-evict))))

(defthm fn-prl-settle-keeps-other-bindings
  (implies (not (equal token other))
           (equal (fn-prl-binding token (fn-prl-nth 3 (mv-nth 1 (fn-prl-settle ledger other cachedp))))
                  (fn-prl-binding token (fn-prl-nth 3 ledger))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prl-settle))))

(defthm fn-prl-admit-keeps-reserve-binding
  (equal (fn-prl-binding (fn-prl-growth-token n)
                         (fn-prl-nth 3 (mv-nth 2 (fn-prl-admit ledger cid file eoff elen trailer
                                                                 demand native-demand))))
         (fn-prl-binding (fn-prl-growth-token n) (fn-prl-nth 3 ledger)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prl-admit fn-prl-token fn-prl-growth-token))))

(defthm fn-prl-register-keeps-reserve-binding
  (equal (fn-prl-binding (fn-prl-growth-token n)
                         (fn-prl-nth 3 (mv-nth 1 (fn-prl-register ledger file demand))))
         (fn-prl-binding (fn-prl-growth-token n) (fn-prl-nth 3 ledger)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prl-register fn-prl-growth-token))))

(defthm fn-prl-close-keeps-reserve-binding
  (equal (fn-prl-binding (fn-prl-growth-token n)
                         (fn-prl-nth 3 (mv-nth 1 (fn-prl-close ledger file))))
         (fn-prl-binding (fn-prl-growth-token n) (fn-prl-nth 3 ledger)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prl-close fn-prl-growth-token))))
