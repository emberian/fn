; Connect typed checkpoint handoffs to the actual durable delivery producer.
; Proof-side source carry is not a served whole-row revalidation.
(in-package "ACL2")
(include-book "bp-node-foundation")
(include-book "bp-handoff-recovery-shape")

(defun fn-bphs-held-sourcep (h)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bpnf-heldp h) (fn-bpnf-cl-ingressp (fn-bpn-nth 4 h))))
(defun fn-bphs-held-sourcesp (held)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom held) (null held)
    (and (fn-bphs-held-sourcep (car held)) (fn-bphs-held-sourcesp (cdr held)))))

(verify-guards fn-bphs-held-sourcep)
(verify-guards fn-bphs-held-sourcesp)

; The delivery mutation preserves the received source carried by its row.
; This is a structural helper; the actual apply-delivery boundary follows.
(defthm fn-bphs-delivered-held-preserves-source-by-definition
  (implies (fn-bphs-held-sourcep h)
           (fn-bphs-held-sourcep (fn-bpah-delivered-held h record)))
  :hints (("Goal" :in-theory
    (union-theories
      '(fn-bphs-held-sourcep fn-bpah-delivered-held fn-bpnf-held
        fn-bpnf-heldp fn-bpnf-held-principal fn-bpnf-held-id
        fn-bpnf-held-bundle fn-bpnf-held-wire fn-bpn-nth
        fn-cbor-ag-car fn-cbor-ag-cdr true-listp nth len nfix zp
        cons car cdr consp equal not binary-+ integerp < natp
        car-cons cdr-cons)
      (theory 'minimal-theory)))))

(defthm fn-bphs-delivery-handoff-constructor-has-typed-shape
  (implies (and (fn-bphs-held-sourcep h) (fn-bpah-delivery-recordp record))
    (fn-bphs-handoffp
     (fn-bpnf-handoff (fn-bpn-nth 6 record)
       (fn-bpnf-held-key (fn-bpnf-held-principal h) (fn-bpnf-held-id h)) :owed)))
  :hints (("Goal"
    :use ((:instance fn-bphs-real-bundle-id-has-recovery-shape
          (primary (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
          (payload-length (len (fn-bpb-payload (fn-bpnf-held-bundle h))))))
    :in-theory (union-theories
      '(fn-bphs-held-sourcep fn-bpnf-heldp fn-bpnf-cl-ingressp
        fn-bpnf-ingress-principal fn-bpnf-held-key fn-bpnf-handoff
        fn-bpnf-held-principal fn-bpnf-held-id fn-bpnf-held-bundle
        fn-bphs-handoffp fn-bphs-triggerp fn-bphs-exact-listp
        fn-bpah-delivery-recordp fn-bpb-bundlep fn-bpb-bundle-primary
        fn-bpb-bundle-id fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr
        true-listp nth natp nfix zp cons car cdr consp equal not
        binary-+ < integerp len (:type-prescription len) car-cons cdr-cons)
      (theory 'minimal-theory))))
  :rule-classes :rewrite)

(defthm fn-bpah-apply-delivery-produces-typed-checkpoint-handoff
  (implies (and (fn-bphs-held-sourcesp held) (fn-bpah-delivery-recordp record))
    (let ((handoff (mv-nth 2 (fn-bpah-apply-delivery record held))))
      (or (null handoff) (fn-bphs-handoffp handoff))))
  :hints (("Goal" :induct (fn-bpah-apply-delivery record held)
     :in-theory (e/d
       (fn-bpah-apply-delivery fn-bphs-held-sourcesp)
       (fn-bphs-handoffp fn-bphs-held-sourcep fn-bpah-delivery-recordp
        fn-bpah-delivery-matches-heldp fn-bpah-delivered-held fn-bpnf-handoff
        fn-bpnf-held-key fn-bpnf-held-principal fn-bpnf-held-id))))
  :rule-classes nil)
