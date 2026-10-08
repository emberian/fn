; Custody: every bound row is covered in all five resource coordinates.
; This predicate is proof state, never a served-path whole-ledger scan.
(in-package "ACL2")
(include-book "page-read-ledger")
(include-book "page-read-budget-growth")

(defun fn-prl-row-wfp (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       (fn-prs-vectorp (fn-prl-nth 0 (cdr entry)))
       (implies (equal (fn-prl-nth 1 (cdr entry)) :issued)
                (and (fn-prs-vectorp (fn-prl-nth 2 (cdr entry)))
                     (fn-prs-below (fn-prl-nth 2 (cdr entry))
                                   (fn-prl-nth 0 (cdr entry)))))))

(defun fn-prl-rows-wfp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-prl-row-wfp (car rows)) (fn-prl-rows-wfp (cdr rows)))
    (equal rows nil)))

(defun fn-prl-row-sum (n rows)
  (declare (xargs :guard (natp n)))
  (if (consp rows)
      (+ (nfix (fn-prl-nth n (fn-prl-nth 0
                        (if (consp (car rows)) (cdar rows) nil))))
         (fn-prl-row-sum n (cdr rows)))
    0))

(defun fn-prl-row-sum-invp (ledger)
  (declare (xargs :guard t))
  (let ((rows (fn-prl-nth 3 ledger)) (charged (fn-prl-nth 1 ledger)))
    (and (fn-prs-vectorp charged)
         (fn-prl-rows-wfp rows)
         (<= (fn-prl-row-sum 0 rows) (fn-prl-nth 0 charged))
         (<= (fn-prl-row-sum 1 rows) (fn-prl-nth 1 charged))
         (<= (fn-prl-row-sum 2 rows) (fn-prl-nth 2 charged))
         (<= (fn-prl-row-sum 3 rows) (fn-prl-nth 3 charged))
         (<= (fn-prl-row-sum 4 rows) (fn-prl-nth 4 charged)))))

; Statements committed before proof development. No budget premise is
; necessary: make establishes custody for every budget, and refusals retain it.
(defthm fn-prl-make-row-sum-invp
  (fn-prl-row-sum-invp (fn-prl-make budget))
  :rule-classes nil)

(defthm fn-prl-register-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-register ledger file demand))))
  :rule-classes nil)

(defthm fn-prl-admit-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 2 (fn-prl-admit ledger cid file eoff elen trailer demand native-demand))))
  :rule-classes nil)

(defthm fn-prl-settle-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-settle ledger token cachedp))))
  :rule-classes nil)

(defthm fn-prl-evict-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-evict ledger token))))
  :rule-classes nil)

(defthm fn-prl-close-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-close ledger file))))
  :rule-classes nil)

(defthm fn-prl-reserve-growth-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 2 (fn-prl-reserve-growth ledger amount))))
  :rule-classes nil)

(defthm fn-prl-convert-growth-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-convert-growth ledger token amount))))
  :rule-classes nil)

; Discharge G2's charged-covers premise from custody and the exact binding.
; NATP AMOUNT is unnecessary here: row well-formedness supplies it.
(defthm fn-prl-row-sum-covers-bound-reserve
  (implies (and (fn-prl-row-sum-invp ledger)
                (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                       (cons token (list (list amount 0 0 0 0) :cached nil))))
           (<= amount (fn-prl-nth 0 (fn-prl-nth 1 ledger))))
  :rule-classes nil)

; G2 with the charged-covers hypothesis discharged (and NATP derived).
(defthm fn-prl-convert-growth-under-row-sum-invp
  (implies (and (fn-prl-row-sum-invp ledger)
                (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                       (cons token (list (list amount 0 0 0 0) :cached nil)))
                (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                                '(0 0 0 0 0) (fn-prl-nth 1 ledger)))
           (and (equal (mv-nth 0 (fn-prl-convert-growth ledger token amount))
                       :protected-growth-admitted)
                (let ((next (mv-nth 1 (fn-prl-convert-growth ledger token amount))))
                  (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next)
                                  '(0 0 0 0 0) (fn-prl-nth 1 next)))))
  :rule-classes nil)
