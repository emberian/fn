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

; G2: no draw between the quanta can unfund the conversion.  The charge
; coverage hypothesis is the row-sum fact a bound row's demand is part of CHARGED.
(defthm fn-prl-convert-growth-after-any-draw
  (implies (and (natp amount)
                (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                       (cons token (list (list amount 0 0 0 0) :cached nil)))
                (<= amount (fn-prl-nth 0 (fn-prl-nth 1 ledger)))
                (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                                '(0 0 0 0 0) (fn-prl-nth 1 ledger)))
           (let ((res (mv-list 2 (fn-prl-convert-growth ledger token amount))))
             (and (equal (car res) :protected-growth-admitted)
                  (fn-prs-fundedp (fn-prl-nth 0 (cadr res)) (fn-prl-baseline (cadr res))
                                  '(0 0 0 0 0) (fn-prl-nth 1 (cadr res))))))
  :rule-classes nil)

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
  :rule-classes nil)

; G4: release releases exactly the reserve row's charge and its binding.
(defthm fn-prl-release-growth-frees-exactly-the-reserve
  (implies (and (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                       (cons token (list (list amount 0 0 0 0) :cached nil)))
                (true-listp (fn-prl-nth 1 ledger)))
           (let ((res (mv-list 2 (fn-prl-evict ledger token))))
             (and (equal (car res) :evicted)
                  (equal (fn-prl-nth 1 (cadr res))
                         (list (nfix (- (nfix (nth 0 (fn-prl-nth 1 ledger))) amount))
                               (nfix (nth 1 (fn-prl-nth 1 ledger)))
                               (nfix (nth 2 (fn-prl-nth 1 ledger)))
                               (nfix (nth 3 (fn-prl-nth 1 ledger)))
                               (nfix (nth 4 (fn-prl-nth 1 ledger)))))
                  (equal (fn-prl-nth 3 (cadr res)) (fn-prl-remove token (fn-prl-nth 3 ledger)))
                  (equal (fn-prl-nth 0 (cadr res)) (fn-prl-nth 0 ledger))
                  (equal (fn-prl-nth 2 (cadr res)) (fn-prl-nth 2 ledger)))))
  :rule-classes nil)

; G5(b): binding survival.  Every ledger transition keeps the binding of a token
; it does not name.  The reserve row survives any draw by another token.
(defthm fn-prl-evict-keeps-other-bindings
  (implies (not (equal token other))
           (equal (fn-prl-binding token (fn-prl-nth 3 (mv-nth 1 (fn-prl-evict ledger other))))
                  (fn-prl-binding token (fn-prl-nth 3 ledger))))
  :rule-classes nil)

(defthm fn-prl-settle-keeps-other-bindings
  (implies (not (equal token other))
           (equal (fn-prl-binding token (fn-prl-nth 3 (mv-nth 1 (fn-prl-settle ledger other cachedp))))
                  (fn-prl-binding token (fn-prl-nth 3 ledger))))
  :rule-classes nil)

(defthm fn-prl-admit-keeps-reserve-binding
  (equal (fn-prl-binding (fn-prl-growth-token n)
                         (fn-prl-nth 3 (mv-nth 2 (fn-prl-admit ledger cid file eoff elen trailer
                                                                 demand native-demand))))
         (fn-prl-binding (fn-prl-growth-token n) (fn-prl-nth 3 ledger)))
  :rule-classes nil)

(defthm fn-prl-register-keeps-reserve-binding
  (equal (fn-prl-binding (fn-prl-growth-token n)
                         (fn-prl-nth 3 (mv-nth 1 (fn-prl-register ledger file demand))))
         (fn-prl-binding (fn-prl-growth-token n) (fn-prl-nth 3 ledger)))
  :rule-classes nil)

(defthm fn-prl-close-keeps-reserve-binding
  (equal (fn-prl-binding (fn-prl-growth-token n)
                         (fn-prl-nth 3 (mv-nth 1 (fn-prl-close ledger file))))
         (fn-prl-binding (fn-prl-growth-token n) (fn-prl-nth 3 ledger)))
  :rule-classes nil)
