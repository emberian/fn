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
  :hints (("Goal" :in-theory (enable fn-bpnp-with-waits
                                    fn-bpnf-held-list fn-bpnf-issued
                                    fn-bpn-nth update-nth))))

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

; A progress event may create a per-key volatile route wait or a volatile
; delivery marker.  It never changes a held obligation or installs a durable
; issued FNBS operation.  The host must drive the later delivery result and
; matched publication callback before reporting durable application delivery.
(defthm fn-bpnp-step-progress-preserves-held-and-issued
  (implies (equal (fn-cbor-ag-car event) :progress)
           (and (equal
                 (fn-bpnf-held-list
                  (fn-bpnf-answer-state (fn-bpnp-step st event)))
                 (fn-bpnf-held-list st))
                (equal
                 (fn-bpnf-issued
                  (fn-bpnf-answer-state (fn-bpnp-step st event)))
                 (fn-bpnf-issued st))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpnp-step fn-bpnp-progress-step)
                (fn-bpnp-with-waits fn-bpah-deliver-step
                 fn-bpnf-answer-state fn-bpnf-answer
                 fn-bpnf-held-list fn-bpnf-issued
                 fn-bpnp-oldest-eligible fn-bpnp-live-pendingp
                 fn-bpnp-blockedp fn-bpnp-prune-waits
                 fn-bpah-pending-decision-at fn-bpnp-routesp
                 fn-bpp-eidp fn-bpb-bundlep fn-bpnf-heldp)))))
