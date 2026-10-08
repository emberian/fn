; Resident bytes retain a live cached charge across each backing transition.
(in-package "ACL2")
(include-book "extent-cache-memory")
(include-book "extent-cache-disjoint")
(include-book "extent-cache-storage-install")

(defthm fn-xce-funded-through-row
  (implies (and (natp n) (natp i) (< i n) (fn-xce-funded-through n ledger slots entries))
           (fn-xce-row-fundedp i ledger slots entries))
  :hints (("Goal" :induct (fn-xce-funded-through n ledger slots entries)
           :in-theory (disable fn-xce-row-fundedp))))

(defthm fn-xce-every-resident-row-is-charged
  (implies (and (fn-xce-fundedp ledger slots entries) (and (natp i)
                (< i (fn-xce-keys-length entries))))
           (let ((n (len (nth i (nth 1 entries)))))
             (and (<= n (fn-xce-cached-charge ledger (fn-xc-slot-token i slots)))
                  (implies (posp n)
                           (and (< i (fn-xcs-count slots))
                                (equal (fn-xcs-get-kind i slots) 1)
                                (fn-xc-slot-token i slots)
                                (equal (fn-prl-nth 1 (cdr (fn-prl-binding (fn-xc-slot-token i slots) (fn-prl-nth 3 ledger)))) :cached))))))
  :rule-classes nil
  :hints (("Goal" :use (:instance fn-xce-funded-through-row (n (fn-xce-keys-length entries)))
           :in-theory (e/d (fn-xce-fundedp fn-xce-row-fundedp fn-xce-cached-charge)
                           (fn-xce-funded-through fn-xce-funded-through-row fn-xc-slot-token)))))

(defthm fn-xce-created-row-is-empty
  (equal (nth i (nth 1 (create-fn-xce))) nil)
  :hints (("Goal" :in-theory (enable nth))))
(defthm fn-xce-empty-through-is-funded
  (fn-xce-funded-through n ledger slots (create-fn-xce))
  :hints (("Goal" :induct (fn-xce-funded-through n ledger slots (create-fn-xce))
           :in-theory (e/d (fn-xce-funded-through fn-xce-row-fundedp) (create-fn-xce)))))
(defthm fn-xc-init-all-empty-backing-is-funded
  (fn-xce-fundedp ledger (mv-nth 1 (fn-xc-init-all ne nw slots cells)) (create-fn-xce))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xce-fundedp) (fn-xce-funded-through fn-xc-init-all create-fn-xce)))))

(defthm fn-xce-drop-row-is-nil
  (implies (and (natp slot) (< slot (fn-xce-keys-length entries)))
           (equal (nth slot (nth 1 (fn-xce-drop slot entries))) nil))
  :hints (("Goal" :use fn-xce-drop-releases-the-row)))
(defthm fn-xce-drop-other-row
  (implies (and (natp slot) (natp i) (not (equal slot i)))
           (equal (nth i (nth 1 (fn-xce-drop slot entries))) (nth i (nth 1 entries))))
  :hints (("Goal" :use (:instance fn-xce-drop-leaves-other-rows (other i)))))
(defthm fn-xc-free-kind-at-other-row
  (implies (and (fn-xcsp slots) (natp slot) (natp i) (not (equal slot i)))
           (equal (fn-xcs-get-kind i (mv-nth 2 (fn-xc-free slot slots))) (fn-xcs-get-kind i slots)))
  :hints (("Goal" :in-theory (enable fn-xc-free))))

(defthm fn-xc-free-bytes-preserves-row-funding
  (let ((r (fn-xc-free-bytes slot slots entries)))
    (implies (and (fn-xcsp slots) (natp slot) (natp i) (< i (fn-xce-keys-length entries))
                  (fn-xce-row-fundedp i ledger slots entries))
             (fn-xce-row-fundedp i ledger (mv-nth 2 r) (mv-nth 3 r))))
  :rule-classes :rewrite
  :hints (("Goal" :cases ((equal slot i))
           :in-theory (e/d (fn-xc-free-bytes fn-xce-row-fundedp)
                           (fn-xce-drop fn-xc-free fn-xc-slot-token fn-xce-cached-charge)))))

(defthm fn-xc-free-bytes-preserves-funded-through
  (let ((r (fn-xc-free-bytes slot slots entries)))
    (implies (and (fn-xcsp slots) (natp slot) (natp n) (<= n (fn-xce-keys-length entries))
                  (fn-xce-funded-through n ledger slots entries))
             (fn-xce-funded-through n ledger (mv-nth 2 r) (mv-nth 3 r))))
  :hints (("Goal" :induct (fn-xce-funded-through n ledger slots entries)
           :in-theory (disable fn-xc-free-bytes fn-xce-row-fundedp))))
(defthm fn-xc-free-bytes-preserves-funding
  (let ((r (fn-xc-free-bytes slot slots entries)))
    (implies (and (fn-xcsp slots) (natp slot) (fn-xce-fundedp ledger slots entries))
             (fn-xce-fundedp ledger (mv-nth 2 r) (mv-nth 3 r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xce-fundedp) (fn-xc-free-bytes fn-xce-funded-through)))))

(defthm fn-xc-free-bytes-releases-freed-row
  (let ((r (fn-xc-free-bytes slot slots entries)))
    (implies (and (and (natp slot) (< slot (fn-xce-keys-length entries)) (equal (mv-nth 0 r) :freed)))
             (equal (nth slot (nth 1 (mv-nth 3 r))) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-free-bytes) (fn-xce-drop fn-xc-free)))))
(defthm fn-xc-yield-bytes-releases-yielded-row
  (let* ((r (fn-xc-yield-bytes slots cells entries)) (slot (mv-nth 1 r)))
    (implies (and (and (natp slot) (< slot (fn-xce-keys-length entries)) (equal (mv-nth 0 r) :yielded)))
             (equal (nth slot (nth 1 (mv-nth 4 r))) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-yield-bytes) (fn-xce-drop fn-xc-yield)))))

(defthm fn-xce-drop-after-free-preserves-row-funding
  (implies (and (fn-xcsp slots) (natp slot) (natp i) (< i (fn-xce-keys-length entries))
                (fn-xce-row-fundedp i ledger slots entries))
           (fn-xce-row-fundedp i ledger (mv-nth 2 (fn-xc-free slot slots)) (fn-xce-drop slot entries)))
  :hints (("Goal" :cases ((equal i slot))
           :in-theory (e/d (fn-xce-row-fundedp) (fn-xce-drop fn-xc-free fn-xc-slot-token fn-xce-cached-charge)))))
(defthm fn-xc-yield-bytes-preserves-row-funding
  (let ((r (fn-xc-yield-bytes slots cells entries)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (natp i) (< i (fn-xce-keys-length entries))
                  (fn-xce-row-fundedp i ledger slots entries))
             (fn-xce-row-fundedp i ledger (mv-nth 3 r) (mv-nth 4 r))))
  :hints (("Goal" :in-theory (e/d (fn-xc-yield-bytes fn-xc-yield)
                                (fn-xce-drop fn-xc-free fn-xc-slot-token fn-xce-cached-charge fn-xce-row-fundedp)))))
(defthm fn-xc-yield-bytes-preserves-funded-through
  (let ((r (fn-xc-yield-bytes slots cells entries)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (natp n) (<= n (fn-xce-keys-length entries))
                  (fn-xce-funded-through n ledger slots entries))
             (fn-xce-funded-through n ledger (mv-nth 3 r) (mv-nth 4 r))))
  :hints (("Goal" :induct (fn-xce-funded-through n ledger slots entries)
           :in-theory (disable fn-xc-yield-bytes fn-xce-row-fundedp))))
(defthm fn-xc-yield-bytes-preserves-funding
  (let ((r (fn-xc-yield-bytes slots cells entries)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xce-fundedp ledger slots entries))
             (fn-xce-fundedp ledger (mv-nth 3 r) (mv-nth 4 r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xce-fundedp) (fn-xc-yield-bytes fn-xce-funded-through)))))
