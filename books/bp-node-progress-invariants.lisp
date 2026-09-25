; The served selector reads fixed slots of a row that admission/replay already
; validated.  These facts connect that bounded projection to the old A3
; class/clock decisions without re-encoding retained wire on each tick.
(in-package "ACL2")
(include-book "bp-node-progress")

(defthm fn-bpnp-primary-of-held
  (implies (fn-bpnf-heldp h)
           (equal (fn-bpnp-primary h)
                  (fn-bpb-bundle-primary (fn-bpnf-held-bundle h))))
  :hints (("Goal" :in-theory (disable fn-bpnf-heldp)))
  :rule-classes nil)

(defthm fn-bpnp-payload-of-held
  (implies (fn-bpnf-heldp h)
           (equal (fn-bpnp-payload h)
                  (fn-bpb-payload (fn-bpnf-held-bundle h))))
  :hints (("Goal" :in-theory (e/d (fn-bpb-payload)
                                     (fn-bpnf-heldp fn-bpb-bundlep))))
  :rule-classes nil)

(defthm fn-bpnp-held-primary-true-listp
  (implies (fn-bpnf-heldp h)
           (true-listp (fn-bpnp-primary h)))
  :hints (("Goal" :use ((:instance fn-bpn-report-held-bundle-for-guard
                                   (held h))
                         (:instance fn-bpn-bundle-primary-true-list-for-guard
                                   (bundle (fn-bpnf-held-bundle h))))
           :in-theory (e/d (fn-bpnp-primary)
                           (fn-bpnf-heldp fn-bpb-bundlep))))
  :rule-classes nil)

(defthm fn-bpnp-held-expiry-refines-a3
  (implies (fn-bpnf-heldp h)
           (equal (fn-bpnp-held-expiry h obs)
                  (fn-bpah-held-expiry h obs)))
  :hints (("Goal" :use ((:instance fn-bpnp-primary-of-held)
                         (:instance fn-bpnp-held-primary-true-listp))
           :in-theory (e/d (fn-bpnp-held-expiry fn-bpah-held-expiry)
                           (fn-bpnf-heldp fn-bpb-bundlep
                            fn-bpnp-primary
                            fn-bpf-fragment-listp-is-a-true-list
                            fn-cp-idp-true-listp
                            fn-nntp-response-text-true-listp
                            fn-bpn-report-bounded-append-suffix
                            fn-bpf-fragment-listp-car-and-cdr
                            fn-bpf-fragmentp-fields))))
  :rule-classes nil)

(defthm fn-bpnp-local-class-refines-a3
  (implies (fn-bpnf-heldp h)
           (equal (fn-bpnp-local-class h)
                  (fn-bpah-held-class h)))
  :hints (("Goal" :use ((:instance fn-bpnp-payload-of-held))
           :in-theory (e/d (fn-bpnp-local-class fn-bpah-held-class
                            fn-bpah-held-adu-result)
                           (fn-bpnf-heldp fn-bpb-bundlep
                            fn-bpnp-payload fn-bpa-decode-exact
                            fn-bpf-fragment-listp-is-a-true-list
                            fn-cp-idp-true-listp
                            fn-nntp-response-text-true-listp
                            fn-bpn-report-bounded-append-suffix
                            fn-bpf-fragment-listp-car-and-cdr
                            fn-bpf-fragmentp-fields))))
  :rule-classes nil)
