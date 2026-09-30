; Internal bounded query charge algebra over the SAME physical pool ledger.
; ROW must be fetched and persisted atomically by the indexed provider.
; These functions do not themselves establish current-row authority: replaying
; a caller-supplied old row is outside the provider refinement.
; No independent budget and no scan/copy of the pool's legacy binding list.
; DEMAND is operation-derived by the actual capture installer; supplied values
; alone do not establish selected-runtime allocation adequacy.
(in-package "ACL2")
(include-book "page-read-ledger")
(defun fn-iqr-naturals (count x)
  (declare (xargs :guard (natp count)))
  (if (zp count) (null x)
    (and (consp x) (natp (car x)) (fn-iqr-naturals (1- count) (cdr x)))))
(defun fn-iqr-tokenp (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :query-grant) (fn-iqr-naturals 11 (cdr x))))
; (:query-grant nonce segment local-slot generation table-root-ID row-root-ID
;               count frontier key-generation-ID arena-incarnation prefix)
; These are registered scalar identities, NOT the retained cons roots or key
; material. The provider carries their exact immutable object association.
(defun fn-iqr-livep (token row)
  (declare (xargs :guard t))
  (and (fn-iqr-tokenp token) (equal token (fn-prl-nth 0 row))
       (member-eq (fn-prl-nth 2 row) '(:active :cancelled)) t))
(defun fn-iqr-admit (ledger token row demand)
  (declare (xargs :guard t))
  (let* ((budget (fn-prl-nth 0 ledger))
         (charged (fn-prl-nth 1 ledger))
         (next-charge (fn-prs-plus charged demand))
         (spent (fn-prl-nth 3 row)))
    (if (not (and (fn-iqr-tokenp token)
                  (not (member-eq (fn-prl-nth 2 row) '(:active :cancelled)))
                  (or (not (natp spent)) (< spent (nfix (fn-prl-nth 1 token))))
                  (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 0)
                  (fn-prs-fundedp budget (fn-prl-baseline ledger) '(0 0 0 0 0) charged)
                  (fn-prs-fundedp budget (fn-prl-baseline ledger) '(0 0 0 0 0) next-charge)))
        (mv :refused nil row ledger)
      (mv :admitted token (list token demand :active (fn-prl-nth 1 token))
          (fn-prl-build budget next-charge (fn-prl-nth 2 ledger)
                        (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))))))
(defun fn-iqr-cancel (token row ledger)
  (declare (xargs :guard t))
  (if (not (fn-iqr-livep token row)) (mv :stale row ledger)
    (mv :retained (list token (fn-prl-nth 1 row) :cancelled (fn-prl-nth 3 row)) ledger)))
(defun fn-iqr-release (token row settlement ledger)
  (declare (xargs :guard t))
  (cond ((not (fn-iqr-livep token row)) (mv :stale row ledger))
        ((or (not (eq settlement :joined))
             (not (true-listp (fn-prl-nth 1 ledger)))
             (not (true-listp (fn-prl-nth 1 row)))) (mv :retained row ledger))
        (t (mv :released (list nil nil :released (fn-prl-nth 3 row))
               (fn-prl-build (fn-prl-nth 0 ledger)
                             (fn-prs-release-reusable (fn-prl-nth 1 ledger) (fn-prl-nth 1 row))
                             (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger)
                             (fn-prl-baseline ledger))))))
(defthm fn-iqr-cancellation-retains-exact-shared-pool
  (equal (mv-nth 2 (fn-iqr-cancel token row ledger)) ledger))
(defthm fn-iqr-other-query-cannot-settle-the-claim
  (implies (not (equal token (fn-prl-nth 0 row)))
           (and (equal (mv-nth 0 (fn-iqr-release token row settlement ledger)) :stale)
                (equal (mv-nth 1 (fn-iqr-release token row settlement ledger)) row)
                (equal (mv-nth 2 (fn-iqr-release token row settlement ledger)) ledger))))
(defthm fn-iqr-unjoined-query-retains-exact-shared-pool
  (implies (not (eq settlement :joined))
           (and (equal (mv-nth 1 (fn-iqr-release token row settlement ledger)) row)
                (equal (mv-nth 2 (fn-iqr-release token row settlement ledger)) ledger))))
; Move already reserved, definitely installed reusable capacity from this
; exact job's C claim to permanent U. No allocation happens in this transition.
; Failure/partial construction must leave C retained rather than call this.
(defun fn-iqr-promotablep (token row retained ledger)
  (declare (xargs :guard t))
  (let ((demand (fn-prl-nth 1 row)) (charged (fn-prl-nth 1 ledger)))
    (and (fn-iqr-livep token row) (fn-prs-vectorp demand)
         (fn-prs-vectorp retained) (true-listp demand) (true-listp retained)
         (true-listp charged) (equal (fn-prl-nth 4 retained) 0)
         (fn-prs-below retained demand) (fn-prs-below retained charged))))
(defun fn-iqr-promoted-ledger (ledger retained)
  (declare (xargs :guard (and (true-listp (fn-prl-nth 1 ledger)) (true-listp retained))))
  (fn-prl-build (fn-prl-nth 0 ledger)
                (fn-prs-release-reusable (fn-prl-nth 1 ledger) retained)
                (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger)
                (fn-prs-plus (fn-prl-baseline ledger) retained)))
(defun fn-iqr-promote-installed-capacity (token row retained ledger)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-iqr-promotablep)))))
  (if (not (fn-iqr-promotablep token row retained ledger))
      (mv :refused row ledger)
    (mv :promoted
        (list token (fn-prs-release-reusable (fn-prl-nth 1 row) retained)
              (fn-prl-nth 2 row) (fn-prl-nth 3 row))
        (fn-iqr-promoted-ledger ledger retained))))
(in-theory (disable fn-iqr-promotablep))
(local (include-book "arithmetic-5/top" :dir :system))
(defun fn-iqr-resident-total (ledger)
  (declare (xargs :guard t))
  (+ (nfix (fn-prl-nth 0 (fn-prl-baseline ledger)))
     (nfix (fn-prl-nth 0 (fn-prl-nth 1 ledger)))))
(in-theory (disable fn-iqr-resident-total))
(defun fn-iqr-resident-promotion-domainp (ledger retained)
  (declare (xargs :guard t))
  (and (natp (fn-prl-nth 0 (fn-prl-baseline ledger)))
       (natp (fn-prl-nth 0 (fn-prl-nth 1 ledger)))
       (natp (fn-prl-nth 0 retained))
       (consp (fn-prl-baseline ledger)) (consp (fn-prl-nth 1 ledger)) (consp retained)
       (<= (fn-prl-nth 0 retained) (fn-prl-nth 0 (fn-prl-nth 1 ledger)))))
(in-theory (disable fn-iqr-resident-promotion-domainp))
(local (defthm fn-iqr-plus-first
  (implies (and (consp a) (consp b))
    (equal (fn-prl-nth 0 (fn-prs-plus a b))
           (+ (nfix (fn-prl-nth 0 a)) (nfix (fn-prl-nth 0 b)))))
  :hints (("Goal" :in-theory (enable fn-prs-plus fn-prl-nth)))))
(local (defthm fn-iqr-plus-consp
  (equal (consp (fn-prs-plus a b)) (consp a))
  :hints (("Goal" :in-theory (enable fn-prs-plus)))))
(local (defthm fn-iqr-plus-non-nil
  (implies (consp a) (fn-prs-plus a b))
  :hints (("Goal" :in-theory (enable fn-prs-plus)))))
(local (defthm fn-iqr-release-first
  (equal (fn-prl-nth 0 (fn-prs-release-reusable a b))
         (nfix (- (nfix (fn-prl-nth 0 a)) (nfix (fn-prl-nth 0 b)))))
  :hints (("Goal" :in-theory (enable fn-prs-release-reusable fn-prl-nth)))))
(local (defthm fn-iqr-build-charge-first
  (equal (fn-prl-nth 0 (fn-prl-nth 1 (fn-prl-build b c n rows u)))
         (fn-prl-nth 0 c))
  :hints (("Goal" :in-theory (enable fn-prl-build fn-prl-nth)))))
(local (defthm fn-iqr-build-baseline-first
  (equal (fn-prl-nth 0 (fn-prl-baseline (fn-prl-build b c n rows u)))
         (if u (fn-prl-nth 0 u) 0))
  :hints (("Goal" :in-theory (enable fn-prl-build fn-prl-baseline fn-prl-nth)))))
(defthm fn-iqr-promoted-ledger-preserves-resident-total
  (implies (fn-iqr-resident-promotion-domainp ledger retained)
           (equal (fn-iqr-resident-total (fn-iqr-promoted-ledger ledger retained))
                  (fn-iqr-resident-total ledger)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-iqr-resident-promotion-domainp fn-iqr-resident-total
                                  fn-iqr-promoted-ledger)
                                 (fn-prl-build fn-prl-baseline fn-prl-nth fn-prs-plus fn-prs-release-reusable
                                  fn-iqr-promotablep fn-iqr-livep fn-iqr-tokenp fn-iqr-naturals
                                  fn-prs-vectorp fn-prs-nats-p fn-prs-below)))))
(defthm fn-iqr-promotion-preserves-resident-pool-total
  (implies (and (equal (mv-nth 0 (fn-iqr-promote-installed-capacity token row retained ledger)) :promoted)
                (fn-iqr-resident-promotion-domainp ledger retained))
           (equal (fn-iqr-resident-total (mv-nth 2 (fn-iqr-promote-installed-capacity token row retained ledger)))
                  (fn-iqr-resident-total ledger)))
  :rule-classes nil
  :hints (("Goal" :use fn-iqr-promoted-ledger-preserves-resident-total
            :in-theory (e/d (fn-iqr-promote-installed-capacity)
                           (fn-iqr-promotablep fn-iqr-promoted-ledger fn-iqr-resident-total
                            fn-iqr-resident-promotion-domainp)))))
