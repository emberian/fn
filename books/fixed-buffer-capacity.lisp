; Internal shared-pool capacity authority. Actual constructor demand and
; installed-object refinement are separate supported-runtime obligations.
(in-package "ACL2")
(include-book "index-query-resources")
(defun fn-bca-slot-heldp (tag slot rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (and (equal (fn-prl-nth 0 (fn-prl-nth 0 (car rows))) tag)
               (member-equal (fn-prl-nth 1 (if (consp (car rows)) (cdr (car rows)) nil))
                             '(:capacity-reserved :capacity-installed))
               (equal (fn-prl-nth 2 (if (consp (car rows)) (cdr (car rows)) nil)) slot))
          (fn-bca-slot-heldp tag slot (cdr rows))) nil))
(defun fn-bca-fieldsp (tag fields)
  (declare (xargs :guard t))
  (cond ((eq tag :worker-capacity)
         (and (consp fields) (natp (car fields)) (null (cdr fields))))
        ((eq tag :rx-capacity)
         (and (consp fields) (natp (car fields)) (consp (cdr fields))
              (equal (cadr fields) 4096) (null (cddr fields))))
        (t nil)))
(defun fn-bca-tokenp (token)
  (declare (xargs :guard t))
  (and (consp token) (consp (cdr token)) (natp (cadr token))
       (fn-bca-fieldsp (car token) (cddr token))))
(defun fn-bca-admit (tag fields demand ledger)
  (declare (xargs :guard t))
  (let ((next (fn-prl-nth 2 ledger)))
    (if (not (and (fn-bca-fieldsp tag fields) (fn-prs-vectorp demand)
                  (equal (fn-prl-nth 1 demand) 0)
                  (equal (fn-prl-nth 2 demand) 0)
                  (equal (fn-prl-nth 3 demand) 0)
                  (equal (fn-prl-nth 4 demand) 1)
                  (not (fn-bca-slot-heldp tag (fn-prl-nth 0 fields) (fn-prl-nth 3 ledger)))))
        (mv :invalid-capacity-request nil ledger)
      (mv-let (word next1 charged1)
        (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                     '(0 0 0 0 0) (fn-prl-nth 1 ledger)
                     next (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
        (if (not (eq word :admitted)) (mv word nil ledger)
          (let ((token (cons tag (cons next fields))))
            (mv :admitted token
                (fn-prl-build (fn-prl-nth 0 ledger) charged1 next1
                  (cons (cons token (cons demand (cons :capacity-reserved fields)))
                        (fn-prl-nth 3 ledger)) (fn-prl-nth 4 ledger)))))))))
(defun fn-bca-promote-installed (token ledger)
  (declare (xargs :guard t))
  (let* ((entry (fn-prl-binding token (fn-prl-nth 3 ledger)))
         (row (if (consp entry) (cdr entry) nil)) (demand (fn-prl-nth 0 row))
         (retained (list (fn-prl-nth 0 demand) 0 0 0 0)))
    (if (not (and (fn-bca-tokenp token)
                  (eq (fn-prl-nth 1 row) :capacity-reserved)
                  (equal (fn-prl-nth 2 row) (fn-prl-nth 2 token))
                  (equal (fn-prl-nth 3 row) (fn-prl-nth 3 token))
                  (fn-prs-vectorp retained)
                  (true-listp (fn-prl-nth 1 ledger))
                  (fn-prs-below retained (fn-prl-nth 1 ledger))))
        (mv :stale-capacity ledger)
      (let ((ledger1 (fn-iqr-promoted-ledger ledger retained)))
        (mv :installed
            (fn-prl-build (fn-prl-nth 0 ledger1) (fn-prl-nth 1 ledger1)
              (fn-prl-nth 2 ledger1)
              (cons (cons token (if (eq (fn-prl-nth 0 token) :rx-capacity)
                              (list demand :capacity-installed (fn-prl-nth 2 row) 4096)
                            (list demand :capacity-installed (fn-prl-nth 2 row))))
                    (fn-prl-remove token (fn-prl-nth 3 ledger1)))
              (fn-prl-nth 4 ledger1)))))))
(local
 (defthm fn-bca-rebuild-promoted-total
   (equal (fn-iqr-resident-total
            (fn-prl-build (fn-prl-nth 0 (fn-iqr-promoted-ledger ledger retained))
                          (fn-prl-nth 1 (fn-iqr-promoted-ledger ledger retained))
                          (fn-prl-nth 2 (fn-iqr-promoted-ledger ledger retained)) rows
                          (fn-prl-nth 4 (fn-iqr-promoted-ledger ledger retained))))
          (fn-iqr-resident-total (fn-iqr-promoted-ledger ledger retained)))
   :hints (("Goal" :in-theory (enable fn-iqr-promoted-ledger fn-iqr-resident-total
                                     fn-prl-build fn-prl-baseline fn-prl-nth)))))
(defthm fn-bca-install-preserves-resident-total-unfolds
  (implies
   (and (equal (mv-nth 0 (fn-bca-promote-installed token ledger)) :installed)
        (fn-iqr-resident-promotion-domainp
          ledger (list (fn-prl-nth 0 (fn-prl-nth 0
                         (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))) 0 0 0 0)))
   (equal (fn-iqr-resident-total (mv-nth 1 (fn-bca-promote-installed token ledger)))
          (fn-iqr-resident-total ledger)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-iqr-promoted-ledger-preserves-resident-total
                    (retained (list (fn-prl-nth 0 (fn-prl-nth 0
                       (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))) 0 0 0 0))))
           :in-theory (e/d (fn-bca-promote-installed)
                           (fn-prl-binding fn-prl-remove fn-prl-build fn-prl-baseline
                            fn-prl-nth fn-prs-plus fn-prs-release-reusable
                            fn-iqr-resident-promotion-domainp fn-prs-below fn-bca-tokenp
                            fn-iqr-resident-total fn-iqr-promoted-ledger)))))

(verify-guards fn-bca-slot-heldp)
(verify-guards fn-bca-fieldsp)
(verify-guards fn-bca-tokenp)
(verify-guards fn-bca-admit)
(verify-guards fn-bca-promote-installed)

; Establish this installed carry at the serialized installation boundary.
; Its ledger lookup is not a constant-cost served receive operation.
(defun fn-bca-installedp (token ledger)
  (declare (xargs :guard t))
  (let* ((entry (fn-prl-binding token (fn-prl-nth 3 ledger)))
         (row (if (consp entry) (cdr entry) nil)))
    (and (fn-bca-tokenp token)
         (eq (fn-prl-nth 1 row) :capacity-installed)
         (equal (fn-prl-nth 2 row) (fn-prl-nth 2 token))
         (equal (fn-prl-nth 3 row) (fn-prl-nth 3 token)))))
(defun fn-rxc-installed-readout (token ledger)
  (declare (xargs :guard t))
  (if (and (eq (fn-prl-nth 0 token) :rx-capacity)
           (fn-bca-installedp token ledger))
      (mv :installed (fn-prl-nth 2 token) 4096)
    (mv :stale-capacity nil 0)))
(verify-guards fn-bca-installedp)
(verify-guards fn-rxc-installed-readout)
