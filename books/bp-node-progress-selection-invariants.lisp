; Called-path A1 progress invariant.  The native BP service calls
; fn-bpnp-step after fn-bpnp-host-eventp, not a sibling selector.
(in-package "ACL2")
(include-book "bp-node-progress")

; Selection scans all held rows; a blocked older row cannot replace an
; eligible newer row.  The N03 teeth book supplies the reachable route-wait
; and local-ready antecedent through the actual outer transition.
(defthm fn-bpnp-oldest-eligible-skips-blocked-older
  (implies
   (and (consp newer)
        (fn-bpnp-live-pendingp newer node observation)
        (not (fn-bpnp-blockedp newer node routes generation waits))
        (fn-bpnp-blockedp older node routes generation waits))
   (equal
    (fn-bpnp-oldest-eligible
     (list newer older) node observation routes generation waits nil)
    newer))
  :hints (("Goal" :in-theory (disable fn-bpnp-live-pendingp
                                     fn-bpnp-blockedp))))

(local
 (defthm fn-bpnp-nth-is-nth
   (implies (natp n)
            (equal (fn-bpn-nth n xs) (nth n xs)))
   :hints (("Goal" :induct (fn-bpn-nth n xs)
            :in-theory (enable fn-bpn-nth nth fn-cbor-ag-car)))))

(defthm fn-bpnp-with-waits-preserves-held-and-issued
  (and (equal (fn-bpnf-held-list (fn-bpnp-with-waits st waits))
              (fn-bpnf-held-list st))
       (equal (fn-bpnf-issued (fn-bpnp-with-waits st waits))
              (fn-bpnf-issued st)))
  :hints (("Goal" :in-theory (union-theories
                              (theory 'minimal-theory)
                              '(fn-bpnp-with-waits fn-bpnf-held-list fn-bpnf-issued
                                fn-bpnp-nth-is-nth nth-update-nth
                                (:executable-counterpart natp)
                                (:executable-counterpart nfix)
                                (:executable-counterpart equal))))))

(defthm fn-bpnp-deliver-step-preserves-held-and-issued
  (and (equal (fn-bpnf-held-list (fn-bpnf-answer-state
                                   (fn-bpah-deliver-step st key node)))
              (fn-bpnf-held-list st))
       (equal (fn-bpnf-issued (fn-bpnf-answer-state
                               (fn-bpah-deliver-step st key node)))
              (fn-bpnf-issued st)))
  :hints (("Goal" :in-theory
           (e/d (fn-bpah-deliver-step)
                (fn-bpnf-heldp fn-bpb-bundlep fn-bpp-blockp
                 fn-bpp-eidp fn-bpah-held-delivery-pendingp
                 fn-bpnf-find-held fn-bpnf-ingress-principal)))))

(local
 (defthm fn-bpnp-answer-state-of-answer
   (equal (fn-bpnf-answer-state (fn-bpnf-answer st effects)) st)
   :hints (("Goal" :in-theory (enable fn-bpnf-answer-state
                                      fn-bpnf-answer)))))

;; The field lemmas below are proved in the minimal theory: the ambient
;; true-listp and fragment rules backchain on every update-nth term.
;; Shape facts for the outer :progress arm.  fn-bpnp-step writes the credit
;; counters (fields 12, 13) and runtime fields (14, 15) back around the inner
;; answer, and the transit-dispatch arm rebuilds the foundation record with
;; fn-bpnf-state-with-arrival.  The held list is field 2, issued field 6.
(defthm fn-bpnp-with-credit-preserves-held-and-issued
  (and (equal (fn-bpnf-held-list (fn-bpnp-with-credit st used debt))
              (fn-bpnf-held-list st))
       (equal (fn-bpnf-issued (fn-bpnp-with-credit st used debt))
              (fn-bpnf-issued st)))
  :hints (("Goal" :in-theory (union-theories
                              (theory 'minimal-theory)
                              '(fn-bpnp-with-credit fn-bpnf-held-list fn-bpnf-issued
                                fn-bpnp-nth-is-nth nth-update-nth
                                (:executable-counterpart natp)
                                (:executable-counterpart nfix)
                                (:executable-counterpart equal))))))

(defthm fn-bpnp-with-runtime-preserves-held-and-issued
  (and (equal (fn-bpnf-held-list
               (fn-bpnp-with-runtime st sessions pending-image))
              (fn-bpnf-held-list st))
       (equal (fn-bpnf-issued
               (fn-bpnp-with-runtime st sessions pending-image))
              (fn-bpnf-issued st)))
  :hints (("Goal" :in-theory (union-theories
                              (theory 'minimal-theory)
                              '(fn-bpnp-with-runtime fn-bpnf-held-list fn-bpnf-issued
                                fn-bpnp-nth-is-nth nth-update-nth
                                (:executable-counterpart natp)
                                (:executable-counterpart nfix)
                                (:executable-counterpart equal))))))

(local
 (defthm fn-bpnp-state-with-arrival-held-and-issued
   (and (equal (fn-bpnf-held-list
                (fn-bpnf-state-with-arrival
                 base held outcomes handoffs correlation issued waits epoch
                 next-op next-arrival))
               held)
        (equal (fn-bpnf-issued
                (fn-bpnf-state-with-arrival
                 base held outcomes handoffs correlation issued waits epoch
                 next-op next-arrival))
               issued))
   :hints (("Goal" :in-theory (enable fn-bpnf-state-with-arrival
                                      fn-bpnf-held-list fn-bpnf-issued
                                      fn-bpn-nth)))))

;; The dispatch arm reads epoch and next operation id after the waits update.
(local
 (defthm fn-bpnp-with-waits-preserves-epoch-and-next-op
   (and (equal (fn-bpnf-epoch (fn-bpnp-with-waits st waits))
               (fn-bpnf-epoch st))
        (equal (fn-bpnf-next-op (fn-bpnp-with-waits st waits))
               (fn-bpnf-next-op st)))
   :hints (("Goal" :in-theory (union-theories
                               (theory 'minimal-theory)
                               '(fn-bpnp-with-waits fn-bpnf-epoch fn-bpnf-next-op
                                 fn-bpnp-nth-is-nth nth-update-nth
                                 (:executable-counterpart natp)
                                 (:executable-counterpart nfix)
                                 (:executable-counterpart equal)))))))

(local
 (defthm fn-bpnp-operation-key-by-definition
   (equal (nth 4 (fn-bpnf-operation epoch op kind key status)) key)
   :hints (("Goal" :in-theory (enable fn-bpnf-operation)))))

;; The forwarding arm, kept closed in the step theorems: it rebuilds the
;; foundation record around the same held list, and the only operation it
;; can install over an empty slot is its own :pending :dispatch.
(defthm fn-bpnp-transit-dispatch-preserves-held
  (equal (fn-bpnf-held-list
          (fn-bpnf-answer-state (fn-bpnp-transit-dispatch-step st h peer node)))
         (fn-bpnf-held-list st))
  :hints (("Goal" :in-theory
           (e/d (fn-bpnp-transit-dispatch-step)
                (fn-bpnp-with-waits fn-bpnf-state-with-arrival
                 fn-bpnf-answer-state fn-bpnf-answer
                 fn-bpnf-held-list fn-bpnf-issued fn-bpnf-operation
                 fn-bpnf-epoch fn-bpnf-next-op
                 fn-bpnp-dispatch-record fn-bpnp-dispatch-apply
                 fn-bpnp-dispatch-recordp fn-bpnp-dispatch-frame
                 fn-bpnd-admitp fn-bpnd-held-delta fn-bpnd-free
                 fn-bpah-held-primary-identity fn-bpnp-remove-wait
                 fn-bpnp-wait-key)))))

(defthm fn-bpnp-transit-dispatch-installs-only-pending-dispatch
  (implies (and (not (fn-bpnf-issued st))
                (fn-bpnf-issued
                 (fn-bpnf-answer-state
                  (fn-bpnp-transit-dispatch-step st h peer node))))
           (equal (fn-bpnf-issued
                   (fn-bpnf-answer-state
                    (fn-bpnp-transit-dispatch-step st h peer node)))
                  (fn-bpnf-operation
                   (fn-bpnf-epoch st) (fn-bpnf-next-op st) :dispatch
                   (fn-bpnp-dispatch-record
                    (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                    (fn-bpn-nth 3 h) (fn-bpah-held-primary-identity h) peer)
                   :pending)))
  :hints (("Goal" :in-theory
           (e/d (fn-bpnp-transit-dispatch-step)
                (fn-bpnp-with-waits fn-bpnf-state-with-arrival
                 fn-bpnf-answer-state fn-bpnf-answer
                 fn-bpnf-held-list fn-bpnf-issued fn-bpnf-operation
                 fn-bpnf-epoch fn-bpnf-next-op
                 fn-bpnp-dispatch-record fn-bpnp-dispatch-apply
                 fn-bpnp-dispatch-recordp fn-bpnp-dispatch-frame
                 fn-bpnd-admitp fn-bpnd-held-delta fn-bpnd-free
                 fn-bpah-held-primary-identity fn-bpnp-remove-wait
                 fn-bpnp-wait-key)))))

;; Rules that answer a true-listp or length goal by backchaining into the
;; fragment, report, identity and response-text recognizers.  None applies
;; to a :progress step; left enabled they spent over 2 s per step theorem.
(local
 (deftheory fn-bpnp-true-listp-backchain
   '(true-listp fn-cp-idp fn-cp-id-length-bound fn-bpf-fragmentp
     fn-bpf-fragment-listp fn-bpf-fragment-listp-is-a-true-list
     fn-cbor-at-mostp fn-bpn-report-bounded-append-suffix
     fn-nntp-response-text-true-listp fn-bpp-dtn-sspp
     fn-nntp-article-idp-is-consp)))

; A progress event may create a per-key volatile route or credit wait, a
; volatile delivery marker, or propose one forwarding dispatch.  It never
; changes a held obligation.  The only issued operation it can install is a
; :pending :dispatch at the current epoch and next operation id, and only
; when nothing was issued; its durability is decided by the later matched
; :persist-result.  The host must drive the later delivery result and matched
; publication callback before reporting durable application delivery.
(defthm fn-bpnp-step-progress-preserves-held
  (implies (equal (fn-cbor-ag-car event) :progress)
           (equal
            (fn-bpnf-held-list
             (fn-bpnf-answer-state (fn-bpnp-step st event)))
            (fn-bpnf-held-list st)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpnp-step fn-bpnp-progress-step)
                (fn-bpnp-with-waits fn-bpnp-with-credit fn-bpnp-with-runtime
                 fn-bpnp-transit-dispatch-step fn-bpnd-free fn-bpnd-remaining
                 fn-bpnp-wait-key fn-bpnp-used fn-bpnp-debt fn-bpnf-waits
                 fn-bpnp-waits fn-bpnf-base fn-bpn-machine-state-fenced
                 fn-clock-observationp fn-frame-natp
                 fn-bpnf-state-with-arrival fn-bpah-deliver-step
                 fn-bpnf-answer-state fn-bpnf-answer
                 fn-bpnf-held-list fn-bpnf-issued
                 fn-bpnp-oldest-eligible fn-bpnp-oldest-eligible-with-credit
                 fn-bpnp-oldest-uncertain-local
                 fn-bpnp-live-pendingp fn-bpnp-blockedp fn-bpnp-prune-waits
                 fn-bpnp-local-class fn-bpnp-primary fn-bpnp-payload
                 fn-bpnp-remove-wait fn-bpnp-route-peer
                 fn-bpah-pending-decision-at fn-bpnp-routesp
                 fn-bpp-eidp fn-bpb-bundlep fn-bpnf-heldp
                 fn-bpnp-true-listp-backchain)))))

(defthm fn-bpnp-step-progress-issued-unchanged-or-pending-dispatch
  (implies (equal (fn-cbor-ag-car event) :progress)
           (let ((issued (fn-bpnf-issued
                          (fn-bpnf-answer-state (fn-bpnp-step st event)))))
             (or (equal issued (fn-bpnf-issued st))
                 (and (null (fn-bpnf-issued st))
                      (equal issued
                             (fn-bpnf-operation
                              (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                              :dispatch (fn-bpn-nth 4 issued) :pending))))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpnp-step fn-bpnp-progress-step)
                (fn-bpnp-with-waits fn-bpnp-with-credit fn-bpnp-with-runtime
                 fn-bpnp-transit-dispatch-step fn-bpnd-free fn-bpnd-remaining
                 fn-bpnp-wait-key fn-bpnp-used fn-bpnp-debt fn-bpnf-waits
                 fn-bpnp-waits fn-bpnf-base fn-bpn-machine-state-fenced
                 fn-clock-observationp fn-frame-natp
                 fn-bpnf-state-with-arrival fn-bpah-deliver-step
                 fn-bpnf-answer-state fn-bpnf-answer
                 fn-bpnf-held-list fn-bpnf-issued fn-bpnf-operation
                 fn-bpnf-epoch fn-bpnf-next-op
                 fn-bpnp-dispatch-record fn-bpah-held-primary-identity
                 fn-bpnp-oldest-eligible fn-bpnp-oldest-eligible-with-credit
                 fn-bpnp-oldest-uncertain-local
                 fn-bpnp-live-pendingp fn-bpnp-blockedp fn-bpnp-prune-waits
                 fn-bpnp-local-class fn-bpnp-primary fn-bpnp-payload
                 fn-bpnp-remove-wait fn-bpnp-route-peer
                 fn-bpah-pending-decision-at fn-bpnp-routesp
                 fn-bpp-eidp fn-bpb-bundlep fn-bpnf-heldp
                 fn-bpnp-true-listp-backchain)))))
