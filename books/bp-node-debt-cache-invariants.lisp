; Correspondence between one-row live journal-debt deltas and the cold fold.
; The host-called fn-bpnp-step cache invariant is stated below after the
; serving wrapper has slots 12/13; these lemmas connect its local updates to
; the actual kind-7 application rule.
(in-package "ACL2")
(include-book "bp-node-debt")
(include-book "bp-node-progress")

(local
 (defthm fn-bpnd-nth-is-nth
   (implies (natp n)
            (equal (fn-bpn-nth n xs) (nth n xs)))
   :hints (("Goal" :induct (fn-bpn-nth n xs)
            :in-theory (enable fn-bpn-nth nth fn-cbor-ag-car)))))

(defthm fn-bpnd-held-list-debt-cons
  (equal (fn-bpnd-held-list-debt (cons row rows) node)
         (+ (fn-bpnd-held-debt row node)
            (fn-bpnd-held-list-debt rows node)))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-bpnd-held-list-debt (cons row rows) node))
           :in-theory (disable fn-bpnd-held-list-debt
                               fn-bpnd-held-debt)))
  :rule-classes nil)

(defthm fn-bpnd-handoffs-debt-cons
  (equal (fn-bpnd-handoffs-debt (cons handoff rest))
         (+ (fn-bpnd-handoff-debt handoff)
            (fn-bpnd-handoffs-debt rest)))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-bpnd-handoffs-debt (cons handoff rest)))
           :in-theory (disable fn-bpnd-handoffs-debt
                               fn-bpnd-handoff-debt)))
  :rule-classes nil)

(defthm fn-bpnd-stored-held-debt-delta
  (equal
   (fn-bpnd-debt
    (update-nth 2 (cons row (fn-bpnf-held-list st)) st) node)
   (+ (fn-bpnd-debt st node)
      (fn-bpnd-held-debt row node)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnd-held-list-debt-cons
                            (rows (fn-bpnf-held-list st))))
           :in-theory (disable fn-bpnd-held-debt
                               fn-bpnd-held-list-debt
                               fn-bpnd-handoffs-debt)))
  :rule-classes nil)

(defthm fn-bpnd-delivery-replacement-debt-delta
  (implies
   (mv-nth 0 (fn-bpah-apply-delivery record held))
   (equal
    (fn-bpnd-held-list-debt
     (mv-nth 1 (fn-bpah-apply-delivery record held)) node)
    (+ (fn-bpnd-held-list-debt held node)
       (fn-bpnd-held-delta
        (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held)
        (fn-bpah-delivered-held
         (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held)
         record)
        node))))
  :hints (("Goal" :induct (fn-bpah-apply-delivery record held)
           :in-theory (e/d (fn-bpah-apply-delivery
                            fn-bpnf-find-arrival
                            fn-bpnd-held-list-debt
                            fn-bpnd-held-delta)
                           (fn-bpnd-held-debt
                            fn-bpah-delivery-matches-heldp
                            fn-bpah-delivered-held))))
  :rule-classes nil)

(defthm fn-bpnd-delivery-handoff-debt-delta
  (implies
   (mv-nth 0 (fn-bpah-apply-delivery record held))
   (equal
    (+ (fn-bpnd-held-list-debt
        (mv-nth 1 (fn-bpah-apply-delivery record held)) node)
       (fn-bpnd-handoff-debt
        (mv-nth 2 (fn-bpah-apply-delivery record held))))
    (+ (fn-bpnd-held-list-debt held node)
       (fn-bpnd-held-handoff-delta
        (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held)
        (fn-bpah-delivered-held
         (fn-bpnf-find-arrival (fn-bpn-nth 3 record) held)
         record)
        (mv-nth 2 (fn-bpah-apply-delivery record held))
        node))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnd-delivery-replacement-debt-delta))
           :in-theory
           (e/d (fn-bpnd-held-handoff-delta fn-bpnd-held-delta)
                (fn-bpnd-held-debt fn-bpnd-held-list-debt
                 fn-bpnd-handoff-debt fn-bpah-apply-delivery
                 fn-bpnf-find-arrival fn-bpah-delivered-held))))
  :rule-classes nil)
