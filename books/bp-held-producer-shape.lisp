; Real producer preservation for the typed held auxiliary recovery grammar.
; Source WIP: recovery is not tightened until all actual producers compose.
(in-package "ACL2")
(include-book "bp-held-recovery-shape")
(include-book "bp-node-job-offer-guards")

(local (defthm fn-bphgp-exact-list-by-definition
 (equal (fn-bphs-exact-listp x n)
        (and (true-listp x) (equal (len x) (nfix n))))
 :hints (("Goal" :induct (fn-bphs-exact-listp x n)
  :in-theory (enable fn-bphs-exact-listp true-listp len nfix zp)))))

(defthm fn-bpnp-dispatched-held-preserves-typed-auxiliary
 (implies (and (fn-bphg-held-auxp held) (fn-bpp-eidp peer))
  (fn-bphg-held-auxp (fn-bpnp-dispatched-held held peer)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpnp-dispatched-held fn-bphg-held-auxp)
   (fn-bphg-lineagep fn-bphg-anchorp fn-bphg-dispatchp fn-bphg-attemptp
    fn-bphg-deletionp fn-bpp-eidp))))
 :rule-classes nil)

(defthm fn-bpah-delivered-held-preserves-typed-auxiliary
 (implies (and (fn-bphg-held-auxp held) (fn-bpah-delivery-recordp record))
  (fn-bphg-held-auxp (fn-bpah-delivered-held held record)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpah-delivered-held fn-bphg-held-auxp
                   fn-bpnf-held fn-bpah-delivery-recordp fn-bpah-disposition-code
                   fn-bphg-dispatchp)
   (fn-bphg-lineagep fn-bphg-anchorp fn-bphg-attemptp fn-bphg-deletionp fn-bpp-eidp))))
 :rule-classes nil)

(local (defthm fn-bphgp-forwarding-constructor-by-definition
 (implies (and (natp epoch) (natp op) (fn-bpp-eidp peer)
               (fn-bpnp-session-idp session) (natp retries))
  (fn-bphg-attemptp (list :forwarding epoch op peer session retries)))
 :hints (("Goal" :in-theory (enable fn-bphg-attemptp fn-bpnp-session-idp)))))
(local (defthm fn-bphgp-busy-constructor-by-definition
 (fn-bphg-attemptp (fn-bpnp-busy-slot count))
 :hints (("Goal" :in-theory (enable fn-bpnp-busy-slot fn-bphg-attemptp)))))

(defthm fn-bpnp-attempted-held-preserves-typed-auxiliary
 (implies (and (fn-bphg-held-auxp held) (fn-bpnp-forward-attempt-recordp record))
  (fn-bphg-held-auxp (fn-bpnp-attempted-held held record)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpnp-attempted-held fn-bphg-held-auxp
                   fn-bpnp-forward-attempt-recordp fn-frame-natp
                   fn-bpnp-attempt-retries)
   (fn-bphg-lineagep fn-bphg-anchorp fn-bphg-dispatchp fn-bphg-attemptp fn-bphg-deletionp fn-bpp-eidp fn-bpnp-session-idp))))
 :rule-classes nil)

(defthm fn-bpnp-deferred-held-preserves-typed-auxiliary
 (implies (fn-bphg-held-auxp held)
  (fn-bphg-held-auxp (fn-bpnp-deferred-held held count)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpnp-deferred-held fn-bphg-held-auxp)
   (fn-bphg-lineagep fn-bphg-anchorp fn-bphg-dispatchp fn-bphg-attemptp fn-bpnp-busy-slot fn-bphg-deletionp fn-bpp-eidp))))
 :rule-classes nil)

(defthm fn-bpn-report-tombstone-held-preserves-typed-auxiliary
 (implies (and (fn-bphg-held-auxp held) (fn-bpn-report-delete-recordp record))
  (fn-bphg-held-auxp (fn-bpn-report-tombstone-held held record)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpn-report-tombstone-held fn-bpn-report-delete-recordp
                   fn-bphg-held-auxp fn-bpnf-held fn-bphg-deletionp)
   (fn-bphg-lineagep fn-bphg-anchorp fn-bphg-dispatchp fn-bphg-attemptp fn-bpp-eidp))))
 :rule-classes nil)

(local (defthm fn-bphgp-settle-attempt-by-definition
 (implies (and (fn-bphg-attemptp slot)
               (or (not (equal outcome :uncertain))
                   (not (equal (car slot) :busy))))
  (fn-bphg-attemptp (fn-bpnp-forward-result-slot slot outcome)))
 :hints (("Goal" :do-not-induct t
  :in-theory (enable fn-bphg-attemptp fn-bpnp-forward-result-slot)))))

(defthm fn-bpnp-forward-result-held-preserves-typed-auxiliary
 (implies (and (fn-bphg-held-auxp held)
               (fn-bpnp-forward-result-matches-heldp record held))
  (fn-bphg-held-auxp
   (fn-bpnp-forward-result-held held (fn-bpn-nth 8 record))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpnp-forward-result-held fn-bphg-held-auxp
                   fn-bpnp-forward-result-matches-heldp fn-bpnp-attempt-slot-namesp)
   (fn-bphg-lineagep fn-bphg-anchorp fn-bphg-dispatchp fn-bphg-attemptp
    fn-bphg-deletionp fn-bpp-eidp fn-bpnp-forward-result-slot
    fn-bpnp-forward-result-recordp fn-bpnp-resume-slot-namesp))))
 :rule-classes nil)

(defthm fn-bpnf-frame-held-with-anchor-has-typed-auxiliary
 (implies (fn-bphg-anchorp anchor)
  (fn-bphg-held-auxp
   (fn-bpnf-frame-held-with-anchor ingress arrival bundle wire anchor)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpnf-frame-held-with-anchor fn-bpnf-held fn-bphg-held-auxp)
   (fn-bphg-anchorp fn-bphg-lineagep fn-bphg-dispatchp fn-bphg-attemptp fn-bphg-deletionp))))
 :rule-classes nil)
