; Charged full-identity decoded job admission. DEMAND must be derived by
; the selected-runtime producer; a supplied vector alone is not adequacy.
(in-package "ACL2")
(include-book "decoded-window-descriptor")
(include-book "page-read-ledger")

(defun fn-pwz-admit (ledger descriptor demand)
  (declare (xargs :guard t))
  (let* ((budget (fn-prl-nth 0 ledger)) (charged (fn-prl-nth 1 ledger))
         (next (fn-prl-nth 2 ledger)) (file (fn-pwz-nth 0 descriptor)))
    (mv-let (word next1 charged1)
      (if (and (fn-pwz-descriptorp descriptor)
               (equal (fn-prl-nth 1 (cdr (fn-prl-binding (list :incarnation file)
                                                        (fn-prl-nth 3 ledger)))) :incarnation)
               (fn-prs-vectorp demand) (equal (fn-prl-nth 3 demand) 1)
               (equal (fn-prl-nth 4 demand) 1))
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                        charged next (fn-prl-nth 4 budget) demand)
        (mv :invalid-decoded-window-demand next charged))
      (if (not (equal word :admitted)) (mv word nil ledger)
        (let ((token (cons :decoded-window (cons next descriptor))))
          (mv :admitted token
              (fn-prl-build budget charged1 next1
                (cons (cons token (list demand :window :running)) (fn-prl-nth 3 ledger))
                (fn-prl-nth 4 ledger))))))))

(defthm fn-pwz-admit-preserves-pool-funding
  (implies (equal (mv-nth 0 (fn-pwz-admit ledger descriptor demand)) :admitted)
           (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
             (fn-prl-nth 1 (mv-nth 2 (fn-pwz-admit ledger descriptor demand)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-admit fn-prl-nth fn-prl-build)
           :use ((:instance fn-prs-issue-preserves-static-rescue
                    (budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
                    (rescue '(0 0 0 0 0)) (charged (fn-prl-nth 1 ledger))
                    (next (fn-prl-nth 2 ledger))
                    (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger))))))))

(defthm fn-pwz-admitted-window-holds-file
  (implies (equal (mv-nth 0 (fn-pwz-admit ledger descriptor demand)) :admitted)
           (equal (fn-prl-close-preview (mv-nth 2 (fn-pwz-admit ledger descriptor demand))
                                        (fn-pwz-nth 0 descriptor)) :read-file-held))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-admit fn-prl-nth fn-prl-build
                                    fn-prl-close-preview fn-prl-file-heldp fn-pwz-nth))))

(in-theory (disable fn-pwz-admit))
