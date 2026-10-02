; UNHOOKED stage 0 (2026-10-01): depends on the reverted FNCE consumer-authority event kinds in the wire-event grammar (planning/design-store-representation-2026-10-01.md section 4)
; Bounded node phase for the complete consumer-authority E family.
; The configured-node/event invariants are carried by the registered producer.
; This kernel grants no issuer, BODY, or native execution authority.
(in-package "ACL2")
(include-book "config-physical-replay")
(include-book "store-events-carried")

(defun fn-asn-authority-node-one (fuel node event)
 (declare (xargs :guard (and (natp fuel) (fn-node-statep node)
                             (fn-store-event-p event))
                 :verify-guards nil))
 (cond ((zp fuel) (mv :yield node nil 0))
       ((not (fn-evc-authorityp event))
        (mv :semantic-family-unavailable node nil (1- fuel)))
       ((fn-node-stage node) (mv :refused node nil (1- fuel)))
       (t
        (let* ((txid (fn-evc-txid event))
               (advanced (fn-replay-advance-txid node txid)))
         (if (equal (fn-state-next-txid (fn-node-acceptance advanced)) txid)
             (mv :node-ready (fn-replay-advance-txid advanced (1+ txid))
                 '(:same) (1- fuel))
           (mv :refused node nil (1- fuel)))))))

(verify-guards fn-asn-authority-node-one
 :hints (("Goal"
          :use ((:instance fn-replay-record-counters-are-natural (record event))
                (:instance fn-replay-advance-preserves-node-statep
                           (recorded-txid (fn-evc-txid event))))
          :in-theory (e/d (fn-evc-txid)
                          (fn-node-statep fn-store-event-p
                           fn-replay-advance-txid fn-evc-authorityp)))))

(defthm fn-asn-authority-node-one-is-replay-apply-record
 (implies (and (posp fuel) (fn-node-statep node)
               (fn-store-event-p event) (fn-evc-authorityp event))
  (equal (fn-replay-apply-record node event)
         (if (eq (mv-nth 0 (fn-asn-authority-node-one fuel node event)) :node-ready)
             (mv-nth 1 (fn-asn-authority-node-one fuel node event)) nil)))
 :hints (("Goal"
          :in-theory (e/d (fn-asn-authority-node-one fn-replay-apply-record
                           fn-replay-apply-identity-neutral fn-store-retention-event-p
                           fn-evc-authorityp fn-evc-txid)
                          (fn-replay-advance-txid fn-node-statep
                           fn-store-event-p)))))

(defthm fn-asn-authority-node-one-preserves-node-statep
 (implies (fn-node-statep node)
          (fn-node-statep (mv-nth 1 (fn-asn-authority-node-one fuel node event))))
 :hints (("Goal" :in-theory (e/d (fn-asn-authority-node-one)
                                 (fn-node-statep fn-replay-advance-txid)))))

(defthm fn-asn-authority-node-one-keeps-groups
 (equal (fn-state-groups
         (fn-node-acceptance (mv-nth 1 (fn-asn-authority-node-one fuel node event))))
        (fn-state-groups (fn-node-acceptance node)))
 :hints (("Goal" :in-theory
          (e/d (fn-asn-authority-node-one fn-replay-advance-txid
                fn-node-make-state fn-node-acceptance fn-make-state fn-state-groups)
               (fn-node-statep fn-store-event-p)))))

(defthm fn-asn-authority-node-one-keeps-retention
 (equal (fn-node-retention (mv-nth 1 (fn-asn-authority-node-one fuel node event)))
        (fn-node-retention node))
 :hints (("Goal" :in-theory (enable fn-asn-authority-node-one))))

(defun fn-asn-authority-one (fuel cn event)
 (declare (xargs :guard (and (natp fuel) (fn-cnode-statep cn)
                             (fn-store-event-p event))
                 :verify-guards nil))
 (mv-let (word next delta left)
   (fn-asn-authority-node-one fuel (fn-cnode-node cn) event)
  (mv word (if (eq word :node-ready)
               (fn-cnode-make next (fn-cnode-config cn)) cn)
      delta left)))

; Separate guard and refinement frontier: the body never invokes the
; general interpreter or validates the complete node/event again.
(verify-guards fn-asn-authority-one
 :hints (("Goal"
          :use ((:instance fn-replay-advance-preserves-node-statep
                           (node (fn-cnode-node cn))
                           (recorded-txid (fn-evc-txid event))))
          :in-theory (e/d (fn-cnode-statep)
                          (fn-node-statep fn-store-event-p
                           fn-replay-advance-txid fn-evc-txid
                           fn-evc-authorityp)))))

(defthm fn-asn-authority-one-keeps-config
 (equal (fn-cnode-config (mv-nth 1 (fn-asn-authority-one fuel cn event)))
        (fn-cnode-config cn))
 :hints (("Goal" :in-theory (enable fn-asn-authority-one fn-asn-authority-node-one))))

(defthm fn-asn-authority-one-keeps-bindings
 (equal (fn-node-bindings
         (fn-cnode-node (mv-nth 1 (fn-asn-authority-one fuel cn event))))
        (fn-node-bindings (fn-cnode-node cn)))
 :hints (("Goal" :in-theory (enable fn-asn-authority-one fn-asn-authority-node-one))))

(defthm fn-asn-authority-one-keeps-retention
 (equal (fn-node-retention
         (fn-cnode-node (mv-nth 1 (fn-asn-authority-one fuel cn event))))
        (fn-node-retention (fn-cnode-node cn)))
 :hints (("Goal" :in-theory (enable fn-asn-authority-one fn-asn-authority-node-one))))

(defthm fn-asn-authority-one-preserves-cnode-statep
 (implies (fn-cnode-statep cn)
          (fn-cnode-statep (mv-nth 1 (fn-asn-authority-one fuel cn event))))
 :hints (("Goal" :in-theory
          (e/d (fn-asn-authority-one fn-cnode-statep fn-cnode-domain
                fn-cnode-domain-of fn-cnode-node fn-cnode-config fn-cnode-make)
               (fn-asn-authority-node-one fn-node-statep fn-cfgp)))))

; Full reference result, including refusal: the bounded word distinguishes
; a retained unchanged state from the reference interpreter's NIL refusal.
(defthm fn-asn-authority-one-is-cpr-apply-event
 (implies (and (posp fuel) (fn-cnode-statep cn)
               (fn-store-event-p event) (fn-evc-authorityp event))
  (equal (fn-cpr-apply-event cn event)
         (if (eq (mv-nth 0 (fn-asn-authority-one fuel cn event)) :node-ready)
             (mv-nth 1 (fn-asn-authority-one fuel cn event)) nil)))
 :hints (("Goal"
          :use ((:instance fn-asn-authority-node-one-is-replay-apply-record
                           (node (fn-cnode-node cn)))
                (:instance fn-asn-authority-node-one-preserves-node-statep
                           (node (fn-cnode-node cn))))
          :in-theory (e/d (fn-asn-authority-one fn-cpr-apply-event
                           fn-cpr-event-servedp fn-cnode-statep fn-evc-authorityp)
                          (fn-asn-authority-node-one fn-replay-apply-record
                           fn-replay-advance-txid fn-node-statep
                           fn-store-event-p)))))

(defthm fn-asn-authority-one-ready-has-same-obligations
 (implies (eq (mv-nth 0 (fn-asn-authority-one fuel cn event)) :node-ready)
  (equal (mv-nth 2 (fn-asn-authority-one fuel cn event)) '(:same)))
 :hints (("Goal" :in-theory (enable fn-asn-authority-one fn-asn-authority-node-one))))
