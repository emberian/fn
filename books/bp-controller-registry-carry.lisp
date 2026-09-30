; Proof-side maintained carry, never a served graph validator.
(in-package "ACL2")
(include-book "bp-controller-registry")
(include-book "bp-node-progress-premises")
(local (include-book "arithmetic-5/top" :dir :system))
(defun fn-bpc-row-carryp (row)
  (declare (xargs :guard t :verify-guards nil))
  (or (null row)
      (and (true-listp row) (equal (len row) 5)
           (natp (fn-bpn-nth 0 row))
           (member-eq (fn-bpn-nth 1 row) '(:live :fenced :retiring))
           (true-listp (fn-bpn-nth 2 row))
           (fn-bpnp-step-guard-premisesp (fn-bpn-nth 2 row)))))
(defun fn-bpc-segment-carry-loop (slot fn-bpc-segment)
  (declare (xargs :stobjs fn-bpc-segment :measure (nfix (- 64 (nfix slot)))
                  :guard (and (natp slot) (<= slot 64)) :verify-guards nil))
  (if (or (not (natp slot)) (<= 64 slot)) t
    (and (fn-bpc-row-carryp (fn-bpcs-rowsi slot fn-bpc-segment))
         (fn-bpc-segment-carry-loop (+ 1 slot) fn-bpc-segment))))
(defun fn-bpc-node-carryp (depth fn-bpc-node)
  (declare (xargs :stobjs fn-bpc-node :measure (nfix depth)
                  :guard (natp depth) :verify-guards nil))
  (if (zp depth)
      (if (not (fn-bpcn-children-boundp 'fn-bpc-segment fn-bpc-node)) t
        (stobj-let ((fn-bpc-segment (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node (create-fn-bpc-segment))))
          (okay) (fn-bpc-segment-carry-loop 0 fn-bpc-segment) okay))
    (and
      (if (not (fn-bpcn-children-boundp 'fn-bpc-left fn-bpc-node)) t
        (stobj-let ((fn-bpc-left (fn-bpcn-children-get 'fn-bpc-left fn-bpc-node (create-fn-bpc-left))))
          (okay) (fn-bpc-node-carryp (- depth 1) fn-bpc-left) okay))
      (if (not (fn-bpcn-children-boundp 'fn-bpc-right fn-bpc-node)) t
        (stobj-let ((fn-bpc-right (fn-bpcn-children-get 'fn-bpc-right fn-bpc-node (create-fn-bpc-right))))
          (okay) (fn-bpc-node-carryp (- depth 1) fn-bpc-right) okay)))))
(defun fn-bpc-registry-carryp (fn-bp-controller-registry)
  (declare (xargs :stobjs fn-bp-controller-registry :guard t :verify-guards nil))
  (and (fn-bp-controller-registryp fn-bp-controller-registry)
       (let ((depth (fn-bpcr-depth fn-bp-controller-registry)))
         (stobj-let ((fn-bpc-node (fn-bpcr-root fn-bp-controller-registry)))
           (okay) (fn-bpc-node-carryp depth fn-bpc-node) okay))))

(defthm fn-bpc-segment-carry-loop-covers-read
  (implies (and (natp start) (natp slot) (<= start slot) (< slot 64)
                (fn-bpc-segment-carry-loop start fn-bpc-segment))
           (fn-bpc-row-carryp (fn-bpcs-rowsi slot fn-bpc-segment)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bpc-segment-carry-loop start fn-bpc-segment)
           :in-theory (e/d (fn-bpc-segment-carry-loop)
                            (fn-bpc-row-carryp fn-bpcs-rowsi fn-bpnp-step-guard-premisesp)))))

(defthm fn-bpc-segment-carry-covers-slot
  (implies (and (natp slot) (< slot 64)
                (fn-bpc-segment-carry-loop 0 fn-bpc-segment))
           (fn-bpc-row-carryp (fn-bpcs-rowsi slot fn-bpc-segment)))
  :hints (("Goal" :use ((:instance fn-bpc-segment-carry-loop-covers-read (start 0)))
           :in-theory (disable fn-bpc-row-carryp fn-bpcs-rowsi fn-bpc-segment-carry-loop))))

(defthm fn-bpc-segment-live-row-carries-current
  (implies (and (natp slot) (< slot 64)
                (fn-bpc-segment-carry-loop 0 fn-bpc-segment)
                (fn-bpc-row-livep nonce (fn-bpcs-rowsi slot fn-bpc-segment)))
           (and (true-listp (fn-bpn-nth 2 (fn-bpcs-rowsi slot fn-bpc-segment)))
                (fn-bpnp-step-guard-premisesp (fn-bpn-nth 2 (fn-bpcs-rowsi slot fn-bpc-segment)))))
  :hints (("Goal" :use ((:instance fn-bpc-segment-carry-covers-slot))
           :in-theory (e/d (fn-bpc-row-carryp fn-bpc-row-livep)
                            (fn-bpcs-rowsi fn-bpc-segment-carry-loop fn-bpnp-step-guard-premisesp fn-bpc-segment-carry-covers-slot)))))

(defthm fn-bpc-node-current-carries-actual-current
  (implies (and (natp local-slot) (< local-slot 64)
                (fn-bpc-node-carryp depth fn-bpc-node)
                (equal (mv-nth 0 (fn-bpc-node-current nonce local-slot physical-segment depth fuel fn-bpc-node)) :current))
           (and (true-listp (mv-nth 1 (fn-bpc-node-current nonce local-slot physical-segment depth fuel fn-bpc-node)))
                (fn-bpnp-step-guard-premisesp
                  (mv-nth 1 (fn-bpc-node-current nonce local-slot physical-segment depth fuel fn-bpc-node)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bpc-node-current nonce local-slot physical-segment depth fuel fn-bpc-node)
           :in-theory (e/d (fn-bpc-node-current fn-bpc-node-carryp fn-bpc-row-carryp)
                          (fn-bpnp-step-guard-premisesp fn-bpc-segment-carry-loop fn-bpcs-rowsi fn-bpc-row-carryp fn-bpc-row-livep)))))

(defthm fn-bpc-current-carries-registered-current
  (implies (and (fn-bpc-registry-carryp fn-bp-controller-registry)
                (equal (mv-nth 0 (fn-bpc-current token fuel fn-bp-controller-registry)) :current))
           (and (true-listp (mv-nth 1 (fn-bpc-current token fuel fn-bp-controller-registry)))
                (fn-bpnp-step-guard-premisesp
                  (mv-nth 1 (fn-bpc-current token fuel fn-bp-controller-registry)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bpc-node-current-carries-actual-current
                   (nonce (cadr token)) (local-slot (mod (caddr token) 64))
                   (physical-segment (floor (caddr token) 64))
                   (depth (fn-bpcr-depth fn-bp-controller-registry))
                   (fn-bpc-node (fn-bpcr-root fn-bp-controller-registry))))
           :in-theory (e/d (fn-bpc-current fn-bpc-registry-carryp fn-bpc-tokenp)
                            (fn-bpc-node-current fn-bpc-node-carryp fn-bpnp-step-guard-premisesp)))))

(defthm fn-bpc-segment-carry-loop-update
  (implies (and (natp start) (<= start 64) (natp slot) (< slot 64)
                (fn-bpc-row-carryp row)
                (fn-bpc-segment-carry-loop start fn-bpc-segment))
           (fn-bpc-segment-carry-loop start
             (update-fn-bpcs-rowsi slot row fn-bpc-segment)))
  :hints (("Goal" :induct (fn-bpc-segment-carry-loop start fn-bpc-segment)
           :in-theory (e/d (fn-bpc-segment-carry-loop fn-bpcs-rowsi update-fn-bpcs-rowsi)
                            (fn-bpc-row-carryp fn-bpnp-step-guard-premisesp)))))

(defthm fn-bpc-child-get-after-put
  (equal (fn-bpcn-children-get key (fn-bpcn-children-put installed value fn-bpc-node) default)
         (if (equal key installed) value
           (fn-bpcn-children-get key fn-bpc-node default)))
  :hints (("Goal" :in-theory (enable fn-bpcn-children-get fn-bpcn-children-put hons-assoc-equal))))
(defthm fn-bpc-child-bound-after-put
  (equal (fn-bpcn-children-boundp key (fn-bpcn-children-put installed value fn-bpc-node))
         (or (equal key installed) (fn-bpcn-children-boundp key fn-bpc-node)))
  :hints (("Goal" :in-theory (enable fn-bpcn-children-boundp fn-bpcn-children-put hons-assoc-equal))))
(defthm fn-bpc-node-carry-put-left
  (implies (and (not (zp depth)) (fn-bpc-node-carryp depth fn-bpc-node)
                (fn-bpc-node-carryp (- depth 1) child))
           (fn-bpc-node-carryp depth (fn-bpcn-children-put 'fn-bpc-left child fn-bpc-node)))
  :hints (("Goal" :expand ((fn-bpc-node-carryp depth fn-bpc-node)
                           (fn-bpc-node-carryp depth (fn-bpcn-children-put 'fn-bpc-left child fn-bpc-node)))
           :in-theory (disable fn-bpc-node-carryp fn-bpcn-children-get fn-bpcn-children-put fn-bpcn-children-boundp))))
(defthm fn-bpc-node-carry-put-right
  (implies (and (not (zp depth)) (fn-bpc-node-carryp depth fn-bpc-node)
                (fn-bpc-node-carryp (- depth 1) child))
           (fn-bpc-node-carryp depth (fn-bpcn-children-put 'fn-bpc-right child fn-bpc-node)))
  :hints (("Goal" :expand ((fn-bpc-node-carryp depth fn-bpc-node)
                           (fn-bpc-node-carryp depth (fn-bpcn-children-put 'fn-bpc-right child fn-bpc-node)))
           :in-theory (disable fn-bpc-node-carryp fn-bpcn-children-get fn-bpcn-children-put fn-bpcn-children-boundp))))
(defthm fn-bpc-node-carry-put-segment
  (implies (and (zp depth) (fn-bpc-segment-carry-loop 0 child))
           (fn-bpc-node-carryp depth (fn-bpcn-children-put 'fn-bpc-segment child fn-bpc-node)))
  :hints (("Goal" :expand ((fn-bpc-node-carryp depth (fn-bpcn-children-put 'fn-bpc-segment child fn-bpc-node)))
           :in-theory (disable fn-bpc-node-carryp fn-bpcn-children-get fn-bpcn-children-put fn-bpcn-children-boundp))))
(defthm fn-bpc-segment-live-row-has-natural-nonce
  (implies (and (natp slot) (< slot 64)
                (fn-bpc-segment-carry-loop 0 fn-bpc-segment)
                (fn-bpc-row-livep nonce (fn-bpcs-rowsi slot fn-bpc-segment)))
           (natp nonce))
  :hints (("Goal" :use ((:instance fn-bpc-segment-carry-covers-slot))
           :in-theory (e/d (fn-bpc-row-carryp fn-bpc-row-livep)
                            (fn-bpcs-rowsi fn-bpc-segment-carry-loop fn-bpnp-step-guard-premisesp fn-bpc-segment-carry-covers-slot)))))

(defthm fn-bpc-node-carry-left-by-definition
  (implies (and (not (zp depth)) (fn-bpc-node-carryp depth fn-bpc-node)
                (fn-bpcn-children-boundp 'fn-bpc-left fn-bpc-node))
           (fn-bpc-node-carryp (- depth 1)
             (fn-bpcn-children-get 'fn-bpc-left fn-bpc-node (create-fn-bpc-left))))
  :hints (("Goal" :expand ((fn-bpc-node-carryp depth fn-bpc-node))
           :in-theory (disable fn-bpc-node-carryp fn-bpcn-children-get fn-bpcn-children-boundp))))
(defthm fn-bpc-node-carry-right-by-definition
  (implies (and (not (zp depth)) (fn-bpc-node-carryp depth fn-bpc-node)
                (fn-bpcn-children-boundp 'fn-bpc-right fn-bpc-node))
           (fn-bpc-node-carryp (- depth 1)
             (fn-bpcn-children-get 'fn-bpc-right fn-bpc-node (create-fn-bpc-right))))
  :hints (("Goal" :expand ((fn-bpc-node-carryp depth fn-bpc-node))
           :in-theory (disable fn-bpc-node-carryp fn-bpcn-children-get fn-bpcn-children-boundp))))
(defthm fn-bpc-node-carry-segment-by-definition
  (implies (and (zp depth) (fn-bpc-node-carryp depth fn-bpc-node)
                (fn-bpcn-children-boundp 'fn-bpc-segment fn-bpc-node))
           (fn-bpc-segment-carry-loop 0
             (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node (create-fn-bpc-segment))))
  :hints (("Goal" :expand ((fn-bpc-node-carryp depth fn-bpc-node))
           :in-theory (disable fn-bpc-node-carryp fn-bpcn-children-get fn-bpcn-children-boundp fn-bpc-segment-carry-loop))))
(defthm fn-bpc-replaced-row-carries-current
  (implies (and (fn-bpc-row-carryp old-row) (fn-bpc-row-livep nonce old-row)
                (true-listp next-current) (fn-bpnp-step-guard-premisesp next-current))
           (fn-bpc-row-carryp (list nonce :live next-current receipt nil)))
  :hints (("Goal" :in-theory (e/d (fn-bpc-row-carryp fn-bpc-row-livep)
                                   (fn-bpnp-step-guard-premisesp)))))

(defthm fn-bpc-leaf-replace-preserves-current-carry
  (let* ((segment (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node (create-fn-bpc-segment)))
         (old-row (fn-bpcs-rowsi slot segment)))
    (implies (and (zp depth) (natp slot) (< slot 64)
                  (fn-bpc-node-carryp depth fn-bpc-node)
                  (fn-bpcn-children-boundp 'fn-bpc-segment fn-bpc-node)
                  (fn-bpc-row-livep nonce old-row)
                  (true-listp next-current) (fn-bpnp-step-guard-premisesp next-current))
             (fn-bpc-node-carryp depth
               (fn-bpcn-children-put 'fn-bpc-segment
                 (update-fn-bpcs-rowsi slot
                   (list nonce :live next-current (fn-bpn-nth 3 old-row) nil) segment)
                 fn-bpc-node))))
  :hints (("Goal"
    :use ((:instance fn-bpc-segment-carry-covers-slot
            (fn-bpc-segment (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node (create-fn-bpc-segment))))
          (:instance fn-bpc-replaced-row-carries-current
            (old-row (fn-bpcs-rowsi slot (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node (create-fn-bpc-segment))))
            (receipt (fn-bpn-nth 3 (fn-bpcs-rowsi slot (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node (create-fn-bpc-segment)))))))
    :in-theory (disable fn-bpc-node-carryp fn-bpc-segment-carry-loop fn-bpc-row-carryp
                         fn-bpcs-rowsi update-fn-bpcs-rowsi fn-bpc-row-livep fn-bpnp-step-guard-premisesp
                         fn-bpcn-children-get fn-bpcn-children-put fn-bpcn-children-boundp
                         create-fn-bpc-segment fn-bpc-segment-carry-covers-slot fn-bpc-replaced-row-carries-current))))

(defthm fn-bpc-node-replace-preserves-current-carry
  (implies (and (natp local-slot) (< local-slot 64)
                (true-listp next-current) (fn-bpnp-step-guard-premisesp next-current)
                (fn-bpc-node-carryp depth fn-bpc-node))
           (fn-bpc-node-carryp depth
             (mv-nth 2 (fn-bpc-node-replace nonce local-slot physical-segment depth
                            expected-epoch expected-issued next-current fuel fn-bpc-node))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bpc-node-replace nonce local-slot physical-segment depth
                            expected-epoch expected-issued next-current fuel fn-bpc-node)
           :in-theory (e/d (fn-bpc-node-replace)
                            (fn-bpc-node-carryp fn-bpc-segment-carry-loop fn-bpnp-step-guard-premisesp
                             fn-bpcn-children-get fn-bpcn-children-put fn-bpcn-children-boundp
                             fn-bpcs-rowsi update-fn-bpcs-rowsi fn-bpc-row-carryp fn-bpc-row-livep fn-bpc-issued-fencep
                             create-fn-bpc-left create-fn-bpc-right create-fn-bpc-segment)))))

(defthm fn-bpc-child-put-preserves-node-shape
  (implies (fn-bpc-nodep fn-bpc-node)
           (fn-bpc-nodep (fn-bpcn-children-put key value fn-bpc-node)))
  :hints (("Goal" :in-theory (enable fn-bpc-nodep fn-bpcn-children-put fn-bpcn-childrenp))))
(defthm fn-bpc-node-replace-preserves-node-shape
  (implies (fn-bpc-nodep fn-bpc-node)
           (fn-bpc-nodep (mv-nth 2 (fn-bpc-node-replace nonce local-slot physical-segment depth
                            expected-epoch expected-issued next-current fuel fn-bpc-node))))
  :hints (("Goal" :expand ((fn-bpc-node-replace nonce local-slot physical-segment depth
                            expected-epoch expected-issued next-current fuel fn-bpc-node))
           :in-theory (disable fn-bpc-node-replace fn-bpc-nodep fn-bpcn-children-put
                                fn-bpcn-children-get fn-bpcn-children-boundp
                                create-fn-bpc-left create-fn-bpc-right create-fn-bpc-segment))))
(defthm fn-bpc-current-replace-preserves-registry-carry
  (implies (and (fn-bpc-registry-carryp fn-bp-controller-registry)
                (true-listp next-current) (fn-bpnp-step-guard-premisesp next-current))
           (fn-bpc-registry-carryp
             (mv-nth 2 (fn-bpc-current-replace token expected-epoch expected-issued next-current fuel fn-bp-controller-registry))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bpc-node-replace-preserves-current-carry
                   (nonce (cadr token)) (local-slot (mod (caddr token) 64))
                   (physical-segment (floor (caddr token) 64))
                   (depth (fn-bpcr-depth fn-bp-controller-registry))
                   (fn-bpc-node (fn-bpcr-root fn-bp-controller-registry))))
           :in-theory (e/d (fn-bpc-current-replace fn-bpc-registry-carryp fn-bpc-tokenp)
                            (fn-bpc-node-replace fn-bpc-node-carryp fn-bpnp-step-guard-premisesp)))))
