; Exact private window lifetime. Supplied demand is a separate allocator
; contract: this book neither derives it from ELEN nor proves it sufficient.
(in-package "ACL2")
(include-book "page-read-ledger")

(defun fn-prw-descriptorp (d)
  (declare (xargs :guard t))
  (and (true-listp d) (equal (len d) 7)
       (posp (nth 0 d)) (natp (nth 1 d)) (natp (nth 2 d))
       (natp (nth 3 d)) (natp (nth 4 d)) (natp (nth 5 d)) (natp (nth 6 d))
       (<= (nth 1 d) (nth 3 d))
       (<= (+ (nth 3 d) (nth 4 d)) (+ (nth 1 d) (nth 2 d)))
       (<= (nth 5 d) (nth 4 d))))

; Descriptor=(file eoff elen poff plen offset trailer). Every requested
; window gets a fresh ticket even when its physical descriptor is identical.
(defun fn-prw-admit (ledger descriptor demand)
  (declare (xargs :guard t))
  (let* ((budget (fn-prl-nth 0 ledger)) (charged (fn-prl-nth 1 ledger))
         (next (fn-prl-nth 2 ledger)) (file (fn-prl-nth 0 descriptor)))
    (mv-let (word next1 charged1)
      (if (and (fn-prw-descriptorp descriptor)
               (equal (fn-prl-nth 1 (cdr (fn-prl-binding (list :incarnation file)
                                                        (fn-prl-nth 3 ledger)))) :incarnation)
               (fn-prs-vectorp demand) (equal (fn-prl-nth 3 demand) 1)
               (equal (fn-prl-nth 4 demand) 1))
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                        charged next (fn-prl-nth 4 budget) demand)
        (mv :invalid-window-demand next charged))
      (if (not (equal word :admitted)) (mv word nil ledger)
        (let ((token (cons :window (cons next descriptor))))
          (mv :admitted token
              (fn-prl-build budget charged1 next1
                (cons (cons token (list demand :window :running)) (fn-prl-nth 3 ledger))
                (fn-prl-nth 4 ledger))))))))

(defun fn-prw-phase (ledger token)
  (declare (xargs :guard t))
  (let ((row (cdr (fn-prl-binding token (fn-prl-nth 3 ledger)))))
    (and (member-eq (fn-prl-nth 0 token) '(:window :decoded-window))
         (equal (fn-prl-nth 1 row) :window) (fn-prl-nth 2 row))))

; Physical observation: the private worker activation has actually returned
; (or a dead worker has actually joined). Authentication is not asserted.
; No credit is released: the output may still be borrowed by its consumer.
(defun fn-prw-return (ledger token)
  (declare (xargs :guard t))
  (if (not (equal (fn-prw-phase ledger token) :running)) (mv :stale ledger)
    (let* ((rows (fn-prl-nth 3 ledger)) (row (cdr (fn-prl-binding token rows))))
      (mv :returned
          (fn-prl-build (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
            (cons (cons token (list (fn-prl-nth 0 row) :window :returned))
                  (fn-prl-remove token rows))
            (fn-prl-nth 4 ledger))))))

; Caller has relinquished every private/output alias. Holding the worker
; credit through the borrow conservatively bounds outstanding buffers by W.
; A cancellation or deadline alone cannot satisfy the returned phase.
(defun fn-prw-release (ledger token)
  (declare (xargs :guard t))
  (let* ((row (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))
         (charged (fn-prl-nth 1 ledger)) (demand (fn-prl-nth 0 row)))
    (if (not (and (equal (fn-prw-phase ledger token) :returned)
                  (true-listp charged) (true-listp demand))) (mv :stale ledger)
      (mv :released
          (fn-prl-build (fn-prl-nth 0 ledger) (fn-prs-release-reusable charged demand)
                        (fn-prl-nth 2 ledger) (fn-prl-remove token (fn-prl-nth 3 ledger))
                        (fn-prl-nth 4 ledger))))))

(defthm fn-prw-admit-preserves-pool-funding
  (implies (equal (mv-nth 0 (fn-prw-admit ledger descriptor demand)) :admitted)
           (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
             (fn-prl-nth 1 (mv-nth 2 (fn-prw-admit ledger descriptor demand)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prw-admit fn-prl-nth fn-prl-build)
           :use ((:instance fn-prs-issue-preserves-static-rescue
                    (budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
                    (rescue '(0 0 0 0 0)) (charged (fn-prl-nth 1 ledger))
                    (next (fn-prl-nth 2 ledger))
                    (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger))))))))

(defthm fn-prw-admitted-window-holds-file
  (implies (equal (mv-nth 0 (fn-prw-admit ledger descriptor demand)) :admitted)
           (equal (fn-prl-close-preview (mv-nth 2 (fn-prw-admit ledger descriptor demand))
                                        (fn-prl-nth 0 descriptor)) :read-file-held))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prw-admit fn-prl-nth fn-prl-build
                                    fn-prl-close-preview fn-prl-file-heldp))))

(defthm fn-prw-unreturned-window-cannot-release
  (implies (not (equal (fn-prw-phase ledger token) :returned))
           (and (equal (mv-nth 0 (fn-prw-release ledger token)) :stale)
                (equal (mv-nth 1 (fn-prw-release ledger token)) ledger)))
  :rule-classes nil)

(defthm fn-prw-return-keeps-all-charges
  (equal (fn-prl-nth 1 (mv-nth 1 (fn-prw-return ledger token))) (fn-prl-nth 1 ledger))
  :hints (("Goal" :in-theory (enable fn-prw-return fn-prl-nth fn-prl-build))))

(in-theory (disable fn-prw-descriptorp fn-prw-admit fn-prw-phase fn-prw-return fn-prw-release))
