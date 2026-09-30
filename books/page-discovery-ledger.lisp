; A synchronous unverified extent discovery owns a distinct typed lease.
; No fabricated trailer or verified-read token. Release is an observation
; after the caller no longer retains its vector/list/scratch; return alone
; is insufficient if that caller still borrows any charged representation.
(in-package "ACL2")
(include-book "page-read-ledger")

(defun fn-prd-admit (ledger file eoff elen demand)
  (declare (xargs :guard t))
  (let* ((budget (fn-prl-nth 0 ledger))
         (charged (fn-prl-nth 1 ledger))
         (next (fn-prl-nth 2 ledger)))
    (mv-let (word next1 charged1)
      (if (and (posp file) (natp eoff) (natp elen)
               (equal (fn-prl-nth 1
                       (cdr (fn-prl-binding (list :incarnation file)
                                            (fn-prl-nth 3 ledger)))) :incarnation)
               (fn-prs-vectorp demand)
               (equal (fn-prl-nth 3 demand) 1)
               (equal (fn-prl-nth 4 demand) 1))
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                        charged next (fn-prl-nth 4 budget) demand)
        (mv :invalid-read-demand next charged))
      (if (not (equal word :admitted)) (mv word nil ledger)
        (let ((token (list :discovery next file eoff elen)))
          (mv :admitted token
              (fn-prl-build budget charged1 next1
                            (cons (cons token (list demand :discovery nil))
                                  (fn-prl-nth 3 ledger))
                            (fn-prl-nth 4 ledger))))))))

(defun fn-prd-release (ledger token)
  (declare (xargs :guard t))
  (let* ((binding (fn-prl-binding token (fn-prl-nth 3 ledger)))
         (row (if (consp binding) (cdr binding) nil))
         (charged (fn-prl-nth 1 ledger))
         (demand (fn-prl-nth 0 row)))
    (if (not (and (equal (fn-prl-nth 0 token) :discovery)
                  (equal (fn-prl-nth 1 row) :discovery)
                  (true-listp charged) (true-listp demand)))
        (mv :stale ledger)
      (mv :released
          (fn-prl-build (fn-prl-nth 0 ledger)
                        (fn-prs-release-reusable charged demand)
                        (fn-prl-nth 2 ledger)
                        (fn-prl-remove token (fn-prl-nth 3 ledger))
                        (fn-prl-nth 4 ledger))))))

(defthm fn-prd-admit-preserves-pool-funding
  (implies (equal (mv-nth 0 (fn-prd-admit ledger file eoff elen demand)) :admitted)
           (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                           '(0 0 0 0 0)
                           (fn-prl-nth 1 (mv-nth 2 (fn-prd-admit ledger file eoff elen demand)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prd-admit fn-prl-nth fn-prl-build)
           :use ((:instance fn-prs-issue-preserves-static-rescue
                            (budget (fn-prl-nth 0 ledger))
                            (used (fn-prl-baseline ledger))
                            (rescue '(0 0 0 0 0))
                            (charged (fn-prl-nth 1 ledger))
                            (next (fn-prl-nth 2 ledger))
                            (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger))))))))

(defthm fn-prd-refusal-keeps-ledger-by-definition
  (implies (not (equal (mv-nth 0 (fn-prd-admit ledger file eoff elen demand)) :admitted))
           (equal (mv-nth 2 (fn-prd-admit ledger file eoff elen demand)) ledger)))

(in-theory (disable fn-prd-admit fn-prd-release))
