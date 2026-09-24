; Guard closure for the exact BP service progress caller.  The state premise
; is carried from open; no whole-state recognizer runs inside a served step.
(in-package "ACL2")
(include-book "bp-report-guards")
(include-book "bp-node-progress")

(verify-guards fn-bpnp-routep)
(verify-guards fn-bpnp-routesp)
(verify-guards fn-bpnp-route-peer)
(verify-guards fn-bpnp-waits)
(verify-guards fn-bpnp-used)
(verify-guards fn-bpnp-debt)
(verify-guards fn-bpnp-with-credit)
(verify-guards fn-bpnp-with-waits)
(verify-guards fn-bpnp-wait-for)
(verify-guards fn-bpnp-remove-wait)
(verify-guards fn-bpnp-prune-waits)
(verify-guards fn-bpnp-wait-key)
(verify-guards fn-bpnp-primary)
(verify-guards fn-bpnp-payload)
(verify-guards fn-bpnp-held-expiry)
(verify-guards fn-bpnp-local-class)
(verify-guards fn-bpnp-live-pendingp)
(verify-guards fn-bpnp-blockedp)
(verify-guards fn-bpnp-oldest-eligible)
(verify-guards fn-bpnp-oldest-uncertain-local)
(verify-guards fn-bpnp-delivery-view)
(verify-guards fn-bpnp-transit-dispatch-step)
(verify-guards fn-bpnp-progress-step)
(verify-guards fn-bpnp-dispatch-persist-step)
(verify-guards fn-bpnp-host-eventp)
(local
 (defthm fn-bpnp-delegate-event-guard
   (implies (and (fn-bpnp-host-eventp event)
                 (not (equal (fn-cbor-ag-car event) :progress)))
            (and (or (not (equal (fn-cbor-ag-car event) :base))
                     (fn-bpn-machine-eventp (fn-bpn-nth 1 event)))
                 (or (not (equal (fn-cbor-ag-car event) :recover-fnbs))
                     (and (true-listp (fn-bpn-nth 2 event))
                          (<= (len (fn-bpn-nth 2 event))
                              *fn-bpn-machine-max-records*)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnp-host-eventp fn-bpnf-host-eventp)
                            (fn-bpn-machine-eventp fn-bpb-bundlep
                             fn-bpp-blockp))))
   :rule-classes nil))
(verify-guards fn-bpnp-step
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-delegate-event-guard))
           :in-theory (disable fn-bpnp-host-eventp fn-bpnf-host-eventp
                               fn-bpn-machine-eventp fn-bpn-machine-statep))))
