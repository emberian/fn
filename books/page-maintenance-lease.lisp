; Operational safe-attempt lease. This funds admitted allocations/cleanup;
; it is not the accepted-obligation W(P,capture) rescue guarantee.
(in-package "ACL2")
(include-book "page-read-ledger")

; An INITIAL row additionally retains its operation/source custody receipt.
; Growth replaces only the backing receipt, never that custody.  Ordinary
; maintenance rows retain their historical three-field representation.
(defun fn-pmn-row (demand backing initial)
  (declare (xargs :guard t))
  (if initial (list demand :maintenance backing initial)
    (list demand :maintenance backing)))

(defun fn-pmn-admit (ledger epoch suffix-count demand)
  (declare (xargs :guard t))
  (let ((budget (fn-prl-nth 0 ledger)) (charged (fn-prl-nth 1 ledger))
        (next (fn-prl-nth 2 ledger)))
    (mv-let (word next1 charged1)
      (if (and (natp epoch) (natp suffix-count) (fn-prs-vectorp demand)
               (equal (fn-prl-nth 3 demand) 1)
               (equal (fn-prl-nth 4 demand) 1))
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                        charged next (fn-prl-nth 4 budget) demand)
        (mv :invalid-maintenance-demand next charged))
      (if (not (equal word :admitted)) (mv word nil ledger)
        (let ((token (list :maintenance next epoch suffix-count)))
          (mv :admitted token
              (fn-prl-build budget charged1 next1
                            (cons (cons token (fn-pmn-row demand nil nil))
                                  (fn-prl-nth 3 ledger))
                            (fn-prl-nth 4 ledger))))))))

; DELTA is additional resident/disk/descriptor ownership, reserved before
; allocation or write. The operation retains one worker and its original ID.
; Shrink/refund is deliberately unavailable before definite final cleanup.
(defun fn-pmn-grow (ledger token delta)
  (declare (xargs :guard t))
  (let* ((bindings (fn-prl-nth 3 ledger))
         (entry (fn-prl-binding token bindings))
         (row (if (consp entry) (cdr entry) nil))
         (demand (fn-prl-nth 0 row))
         (charged1 (fn-prs-plus (fn-prl-nth 1 ledger) delta)))
    (cond ((not (and (equal (fn-prl-nth 0 token) :maintenance)
                     (equal (fn-prl-nth 1 row) :maintenance)))
           (mv :stale ledger))
          ((not (and (fn-prs-vectorp demand) (fn-prs-vectorp delta)
                     (equal (fn-prl-nth 3 delta) 0)
                     (equal (fn-prl-nth 4 delta) 0)))
           (mv :invalid-maintenance-growth ledger))
          ((not (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                                '(0 0 0 0 0) charged1))
           (mv :maintenance-resources-unavailable ledger))
          (t (mv :grown
                 (fn-prl-build
                  (fn-prl-nth 0 ledger) charged1 (fn-prl-nth 2 ledger)
                  (cons (cons token (fn-pmn-row (fn-prs-plus demand delta) nil
                                               (fn-prl-nth 3 row)))
                        (fn-prl-remove token bindings))
                  (fn-prl-nth 4 ledger)))))))

; Host calls only after joined/returned work, no surviving buffer aliases,
; and definite staging cleanup/publication. Ambiguous cleanup retains credit.
(defun fn-pmn-release (ledger token)
  (declare (xargs :guard t))
  (let* ((entry (fn-prl-binding token (fn-prl-nth 3 ledger)))
         (row (if (consp entry) (cdr entry) nil))
         (charged (fn-prl-nth 1 ledger)) (demand (fn-prl-nth 0 row)))
    (cond ((fn-prl-nth 3 row)
           ; The INITIAL producer's joined settlement is a distinct boundary.
           ; A naked maintenance token cannot release retained source/turn debt.
           (mv :initial-custody-retained ledger))
          ((not (and (equal (fn-prl-nth 0 token) :maintenance)
                  (equal (fn-prl-nth 1 row) :maintenance)
                  (true-listp charged) (true-listp demand)))
           (mv :stale ledger))
          (t (mv :released
          (fn-prl-build (fn-prl-nth 0 ledger)
                        (fn-prs-release-reusable charged demand)
                        (fn-prl-nth 2 ledger)
                        (fn-prl-remove token (fn-prl-nth 3 ledger))
                        (fn-prl-nth 4 ledger)))))))

(defthm fn-pmn-admit-preserves-pool-funding
  (implies (equal (mv-nth 0 (fn-pmn-admit ledger epoch suffix-count demand)) :admitted)
           (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                           '(0 0 0 0 0)
                           (fn-prl-nth 1 (mv-nth 2 (fn-pmn-admit ledger epoch suffix-count demand)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pmn-admit fn-prl-nth fn-prl-build)
           :use ((:instance fn-prs-issue-preserves-static-rescue
                            (budget (fn-prl-nth 0 ledger))
                            (used (fn-prl-baseline ledger))
                            (rescue '(0 0 0 0 0))
                            (charged (fn-prl-nth 1 ledger))
                            (next (fn-prl-nth 2 ledger))
                            (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger))))))))

(defthm fn-pmn-grown-pool-funded-by-definition
  (implies (equal (mv-nth 0 (fn-pmn-grow ledger token delta)) :grown)
           (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                           '(0 0 0 0 0)
                           (fn-prl-nth 1 (mv-nth 1 (fn-pmn-grow ledger token delta)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pmn-grow fn-prl-nth fn-prl-build))))

(defthm fn-pmn-growth-preserves-initial-custody
  (equal
            (fn-prl-nth 3
             (cdr (fn-prl-binding
                   token (fn-prl-nth 3
                          (mv-nth 1 (fn-pmn-grow ledger token delta))))))
            (fn-prl-nth 3
             (cdr (fn-prl-binding token (fn-prl-nth 3 ledger)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable fn-pmn-grow fn-pmn-row fn-prl-nth fn-prl-build
                   fn-prl-binding))))

(defthm fn-pmn-naked-release-retains-initial-custody
  (implies (fn-prl-nth 3
            (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))
           (equal (fn-pmn-release ledger token)
                  (mv :initial-custody-retained ledger)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pmn-release))))

(in-theory (disable fn-pmn-row fn-pmn-admit fn-pmn-grow fn-pmn-release))
