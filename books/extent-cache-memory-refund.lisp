; Ledger retirement follows backing retirement; a refund cannot uncharge
; any remaining row when the retired token is absent from the table.
(in-package "ACL2")
(include-book "extent-cache-memory-install")
(include-book "page-read-budget-growth")

(defthm fn-xce-refund-preserves-another-charge
  (implies (not (equal token other))
           (equal (fn-xce-cached-charge (mv-nth 1 (fn-prl-evict ledger other)) token)
                  (fn-xce-cached-charge ledger token)))
  :hints (("Goal" :in-theory (e/d (fn-xce-cached-charge) (fn-prl-evict fn-prl-binding))
           :use fn-prl-evict-keeps-other-bindings)))
(defthm fn-xce-nil-charge
  (equal (fn-xce-cached-charge ledger nil) 0)
  :hints (("Goal" :in-theory (enable fn-xce-cached-charge))))

(defthm fn-xce-refund-preserves-row-funding
  (implies (and (natp i) (fn-xce-row-fundedp i ledger slots entries)
                (not (fn-xc-find-token-except token nil 0 slots)))
           (fn-xce-row-fundedp i (mv-nth 1 (fn-prl-evict ledger token)) slots entries))
  :hints (("Goal" :cases ((equal token (fn-xc-slot-token i slots))) :in-theory (e/d (fn-xce-row-fundedp)
                                (fn-prl-evict fn-xce-cached-charge fn-xc-slot-token fn-xc-find-token-except))
           :use (:instance fn-xc-token-absent-except-at (target nil) (j i) (fn-xcs slots)))))
(defthm fn-xce-refund-preserves-funded-through
  (implies (and (fn-xce-funded-through n ledger slots entries)
                (not (fn-xc-find-token-except token nil 0 slots)))
           (fn-xce-funded-through n (mv-nth 1 (fn-prl-evict ledger token)) slots entries))
  :hints (("Goal" :induct (fn-xce-funded-through n ledger slots entries)
           :in-theory (disable fn-xce-row-fundedp fn-prl-evict fn-xc-find-token-except))))
(defthm fn-xce-refund-preserves-funding
  (implies (and (fn-xce-fundedp ledger slots entries)
                (not (fn-xc-find-token-except token nil 0 slots)))
           (fn-xce-fundedp (mv-nth 1 (fn-prl-evict ledger token)) slots entries))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xce-fundedp) (fn-xce-funded-through fn-prl-evict fn-xc-find-token-except)))))
