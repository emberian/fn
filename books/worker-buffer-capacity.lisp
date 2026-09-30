; Internal shared-pool capacity authority. Actual constructor demand and
; installed-object refinement are separate supported-runtime obligations.
(in-package "ACL2")
(include-book "index-query-resources")
(defun fn-wbc-slot-heldp (slot rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (and (member-equal (fn-prl-nth 1 (if (consp (car rows)) (cdr (car rows)) nil))
                             '(:capacity-reserved :capacity-installed))
               (equal (fn-prl-nth 2 (if (consp (car rows)) (cdr (car rows)) nil)) slot))
          (fn-wbc-slot-heldp slot (cdr rows))) nil))
(defun fn-wbc-tokenp (token)
  (declare (xargs :guard t))
  (and (true-listp token) (equal (len token) 3)
       (eq (fn-prl-nth 0 token) :worker-capacity)
       (natp (fn-prl-nth 1 token)) (natp (fn-prl-nth 2 token))))
(defun fn-wbc-admit (slot demand ledger)
  (declare (xargs :guard t))
  (let ((next (fn-prl-nth 2 ledger)))
    (if (not (and (natp slot) (fn-prs-vectorp demand)
                  (equal (fn-prl-nth 1 demand) 0)
                  (equal (fn-prl-nth 2 demand) 0)
                  (equal (fn-prl-nth 3 demand) 0)
                  (equal (fn-prl-nth 4 demand) 1)
                  (not (fn-wbc-slot-heldp slot (fn-prl-nth 3 ledger)))))
        (mv :invalid-capacity-request nil ledger)
      (mv-let (word next1 charged1)
        (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                     '(0 0 0 0 0) (fn-prl-nth 1 ledger)
                     next (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
        (if (not (eq word :admitted)) (mv word nil ledger)
          (let ((token (list :worker-capacity next slot)))
            (mv :admitted token
                (fn-prl-build (fn-prl-nth 0 ledger) charged1 next1
                  (cons (cons token (list demand :capacity-reserved slot))
                        (fn-prl-nth 3 ledger)) (fn-prl-nth 4 ledger)))))))))
(defun fn-wbc-promote-installed (token ledger)
  (declare (xargs :guard t))
  (let* ((entry (fn-prl-binding token (fn-prl-nth 3 ledger)))
         (row (if (consp entry) (cdr entry) nil)) (demand (fn-prl-nth 0 row))
         (retained (list (fn-prl-nth 0 demand) 0 0 0 0)))
    (if (not (and (fn-wbc-tokenp token)
                  (eq (fn-prl-nth 1 row) :capacity-reserved)
                  (equal (fn-prl-nth 2 row) (fn-prl-nth 2 token))
                  (fn-prs-vectorp retained)
                  (true-listp (fn-prl-nth 1 ledger))
                  (fn-prs-below retained (fn-prl-nth 1 ledger))))
        (mv :stale-capacity ledger)
      (let ((ledger1 (fn-iqr-promoted-ledger ledger retained)))
        (mv :installed
            (fn-prl-build (fn-prl-nth 0 ledger1) (fn-prl-nth 1 ledger1)
              (fn-prl-nth 2 ledger1)
              (cons (cons token (list demand :capacity-installed (fn-prl-nth 2 row)))
                    (fn-prl-remove token (fn-prl-nth 3 ledger1)))
              (fn-prl-nth 4 ledger1)))))))
(local
 (defthm fn-wbc-rebuild-promoted-total
   (equal (fn-iqr-resident-total
            (fn-prl-build (fn-prl-nth 0 (fn-iqr-promoted-ledger ledger retained))
                          (fn-prl-nth 1 (fn-iqr-promoted-ledger ledger retained))
                          (fn-prl-nth 2 (fn-iqr-promoted-ledger ledger retained)) rows
                          (fn-prl-nth 4 (fn-iqr-promoted-ledger ledger retained))))
          (fn-iqr-resident-total (fn-iqr-promoted-ledger ledger retained)))
   :hints (("Goal" :in-theory (enable fn-iqr-promoted-ledger fn-iqr-resident-total
                                     fn-prl-build fn-prl-baseline fn-prl-nth)))))
(defthm fn-wbc-install-preserves-resident-total-unfolds
  (implies
   (and (equal (mv-nth 0 (fn-wbc-promote-installed token ledger)) :installed)
        (fn-iqr-resident-promotion-domainp
          ledger (list (fn-prl-nth 0 (fn-prl-nth 0
                         (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))) 0 0 0 0)))
   (equal (fn-iqr-resident-total (mv-nth 1 (fn-wbc-promote-installed token ledger)))
          (fn-iqr-resident-total ledger)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-iqr-promoted-ledger-preserves-resident-total
                    (retained (list (fn-prl-nth 0 (fn-prl-nth 0
                       (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))) 0 0 0 0))))
           :in-theory (e/d (fn-wbc-promote-installed)
                           (fn-prl-binding fn-prl-remove fn-prl-build fn-prl-baseline
                            fn-prl-nth fn-prs-plus fn-prs-release-reusable
                            fn-iqr-resident-promotion-domainp fn-prs-below fn-wbc-tokenp
                            fn-iqr-resident-total fn-iqr-promoted-ledger)))))
(verify-guards fn-wbc-slot-heldp)
(verify-guards fn-wbc-tokenp)
(verify-guards fn-wbc-admit)
(verify-guards fn-wbc-promote-installed)
