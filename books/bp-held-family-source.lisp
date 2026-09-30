; Actual reassembly key/source carry needed before tightening CK7 recovery.
(in-package "ACL2")
(include-book "bp-held-producer-shape")
(include-book "bp-handoff-producer-shape")

(local (defthm fn-bphgf-source-key-by-definition
 (implies (fn-bphs-held-sourcep h)
  (fn-bphg-consumed-rowp
   (list (fn-bpnf-held-principal h) (fn-bpnf-held-id h) (fn-bpn-nth 3 h))))
 :hints (("Goal"
 :use ((:instance fn-bphs-real-bundle-id-has-recovery-shape
   (primary (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
   (payload-length (len (fn-bpb-payload (fn-bpnf-held-bundle h))))))
 :in-theory (union-theories
  '(fn-bphs-held-sourcep fn-bpnf-heldp fn-bpnf-cl-ingressp
    fn-bpnf-ingress-principal fn-bpnf-held-principal fn-bpnf-held-id
    fn-bpnf-held-bundle fn-bpb-bundle-id fn-bpb-bundle-primary
    fn-bpb-bundlep fn-bphg-consumed-rowp fn-bphs-exact-listp
    fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr nth true-listp len
    natp nfix zp cons car cdr consp equal not binary-+ < integerp
    car-cons cdr-cons (:type-prescription len))
  (theory 'minimal-theory))))))

(defthm fn-bpnf-family-consumed-ids-have-typed-recovery-keys
 (implies (fn-bphs-held-sourcesp rows)
  (fn-bphg-consumed-rowsp (fn-bpnf-family-consumed-ids rows)))
 :hints (("Goal" :induct (fn-bpnf-family-consumed-ids rows)
  :in-theory (e/d (fn-bpnf-family-consumed-ids fn-bphs-held-sourcesp
                   fn-bphg-consumed-rowsp)
                  (fn-bphs-held-sourcep fn-bphg-consumed-rowp
                   fn-bpnf-held-principal fn-bpnf-held-id fn-bpn-nth))))
 :rule-classes nil)

(local (defthm fn-bphgf-frame-source-by-definition
 (implies (and (fn-bpnf-cl-ingressp ingress) (natp arrival)
               (fn-bpb-bundlep bundle) (fn-cbor-octet-listp wire)
               (equal wire (fn-bpb-encode bundle)))
  (fn-bphs-held-sourcep
   (fn-bpnf-frame-held-with-anchor ingress arrival bundle wire anchor)))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bphs-held-sourcep fn-bpnf-frame-held-with-anchor
                   fn-bpnf-held fn-bpnf-heldp fn-bpnf-held-principal
                   fn-bpnf-held-id fn-bpnf-held-bundle fn-bpnf-held-wire)
                  (fn-bpnf-cl-ingressp fn-bpb-bundlep fn-bpb-bundle-id
                   fn-bpb-encode fn-cbor-octet-listp fn-bpnf-ingress-principal))))
 :rule-classes nil))

(defthm fn-bpnf-received-anchor-has-typed-recovery-shape
 (fn-bphg-anchorp (fn-bpnf-received-anchor bundle observation))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-bpnf-received-anchor fn-bphg-anchorp
                   fn-clock-observationp fn-clock-monotonic)
                  (fn-bpb-bundlep fn-bpb-bundle-age))))
 :rule-classes nil)

(local (defthm fn-bphgf-source-active-by-definition
 (implies (fn-bphs-held-sourcesp held) (fn-bphs-held-sourcesp (fn-bpnf-active-set-rows held anchor)))
 :hints (("Goal" :induct (fn-bpnf-active-set-rows held anchor)
 :in-theory (e/d (fn-bpnf-active-set-rows fn-bphs-held-sourcesp) (fn-bphs-held-sourcep fn-bpnf-same-fragment-family-p fn-ag-member))))))

(local (defthm fn-bphgf-source-retain-by-definition
 (implies (fn-bphs-held-sourcesp held) (fn-bphs-held-sourcesp (fn-bpnf-family-retain-other-rows held consumed)))
 :hints (("Goal" :induct (fn-bpnf-family-retain-other-rows held consumed)
 :in-theory (e/d (fn-bpnf-family-retain-other-rows fn-bphs-held-sourcesp) (fn-bphs-held-sourcep fn-bpnf-same-fragment-family-p fn-ag-member))))))

(local (defthm fn-bphgf-source-zero-by-definition
 (implies (and (fn-bphs-held-sourcesp held) (fn-bpnf-offset-zero-source held))
  (fn-bphs-held-sourcep (fn-bpnf-offset-zero-source held)))
 :hints (("Goal" :induct (fn-bpnf-offset-zero-source held)
 :in-theory (e/d (fn-bpnf-offset-zero-source fn-bphs-held-sourcesp)
 (fn-bphs-held-sourcep fn-bpp-fragment-offset fn-bpb-bundle-primary fn-bpnf-held-bundle))))))

(local (defthm fn-bphgf-aux-active-by-definition
 (implies (fn-bphg-held-auxsp held) (fn-bphg-held-auxsp (fn-bpnf-active-set-rows held anchor)))
 :hints (("Goal" :induct (fn-bpnf-active-set-rows held anchor)
 :in-theory (e/d (fn-bpnf-active-set-rows fn-bphg-held-auxsp) (fn-bphg-held-auxp fn-bpnf-same-fragment-family-p fn-ag-member))))))

(local (defthm fn-bphgf-aux-retain-by-definition
 (implies (fn-bphg-held-auxsp held) (fn-bphg-held-auxsp (fn-bpnf-family-retain-other-rows held consumed)))
 :hints (("Goal" :induct (fn-bpnf-family-retain-other-rows held consumed)
 :in-theory (e/d (fn-bpnf-family-retain-other-rows fn-bphg-held-auxsp) (fn-bphg-held-auxp fn-bpnf-same-fragment-family-p fn-ag-member))))))

(local (defthm fn-bphgf-aux-zero-by-definition
 (implies (and (fn-bphg-held-auxsp held) (fn-bpnf-offset-zero-source held))
  (fn-bphg-held-auxp (fn-bpnf-offset-zero-source held)))
 :hints (("Goal" :induct (fn-bpnf-offset-zero-source held)
 :in-theory (e/d (fn-bpnf-offset-zero-source fn-bphg-held-auxsp)
 (fn-bphg-held-auxp fn-bpp-fragment-offset fn-bpb-bundle-primary fn-bpnf-held-bundle))))))

(local (defthm fn-bphgf-ready-plan-carry-by-definition
 (implies (and (fn-bphs-held-sourcesp (fn-bpnf-held-list st))
               (fn-bphg-held-auxsp (fn-bpnf-held-list st))
               (equal (car (fn-bpnf-family-plan st anchor)) :ready))
  (and (fn-bphs-held-sourcep (fn-bpn-nth 4 (fn-bpnf-family-plan st anchor)))
       (fn-bphg-held-auxp (fn-bpn-nth 4 (fn-bpnf-family-plan st anchor)))
       (fn-bphg-consumed-rowsp (fn-bpn-nth 3 (fn-bpnf-family-plan st anchor)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpnf-family-ready-has-valid-whole)
        (:instance fn-bpnf-family-consumed-ids-have-typed-recovery-keys
         (rows (fn-bpnf-active-set st anchor))))
  :in-theory (e/d (fn-bpnf-family-plan fn-bpnf-active-set)
    (fn-bpnf-held-list fn-bpnf-active-set-rows fn-bpnf-active-fragmentp
     fn-bpnf-family-member fn-bpnf-fragment-query fn-bpnf-family-whole-bundle
     fn-bpnf-offset-zero-source fn-bpnf-family-consumed-ids fn-bpb-bundlep
     fn-bpb-encode fn-bpnf-held-octets fn-cbor-octet-listp
     fn-bphs-held-sourcep fn-bphg-held-auxp fn-bphg-consumed-rowsp))))))

(defthm fn-bpnf-family-apply-preserves-typed-held-auxiliaries
 (implies (and (fn-bphs-held-sourcesp (fn-bpnf-held-list st))
               (fn-bphg-held-auxsp (fn-bpnf-held-list st))
               (equal (car (fn-bpnf-family-apply st record arrival)) :ready))
  (fn-bphg-held-auxsp (fn-bpn-nth 1 (fn-bpnf-family-apply st record arrival))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bphgf-ready-plan-carry-by-definition
   (anchor (fn-bpnf-find-arrival (fn-bpn-nth 3 record) (fn-bpnf-held-list st)))))
  :in-theory (e/d (fn-bpnf-family-apply fn-bpnf-held fn-bphg-held-auxsp
                   fn-bphg-held-auxp fn-bphg-lineagep)
    (fn-bpnf-held-list fn-bpnf-held-principal fn-bpnf-held-id fn-bpb-bundle-id
     fn-bpnf-family-plan fn-bpnf-find-arrival fn-bpnf-arrival-count
     fn-bpnf-active-fragmentp fn-bpnf-find-held fn-bpnf-held-key fn-bpnf-heldp
     fn-bpnf-active-set fn-bpnf-family-retain-other-rows
     fn-bpnf-family-recordp fn-bpnf-family-record-atp fn-frame-natp
     fn-bphs-held-sourcep fn-bphs-held-sourcesp fn-bphg-consumed-rowsp
     fn-bphg-anchorp fn-bphg-attemptp fn-bphg-deletionp fn-bphg-dispatchp))))
 :rule-classes nil)

(local (defthm fn-bphgf-ready-plan-source-by-definition
 (implies (and (fn-bphs-held-sourcesp (fn-bpnf-held-list st))
               (equal (car (fn-bpnf-family-plan st anchor)) :ready))
  (fn-bphs-held-sourcep (fn-bpn-nth 4 (fn-bpnf-family-plan st anchor))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpnf-family-ready-has-valid-whole))
  :in-theory (e/d (fn-bpnf-family-plan fn-bpnf-active-set)
    (fn-bpnf-held-list fn-bpnf-active-set-rows fn-bpnf-active-fragmentp
     fn-bpnf-family-member fn-bpnf-fragment-query fn-bpnf-family-whole-bundle
     fn-bpnf-offset-zero-source fn-bpnf-family-consumed-ids fn-bpb-bundlep
     fn-bpb-encode fn-bpnf-held-octets fn-cbor-octet-listp fn-bphs-held-sourcep))))))

(defthm fn-bpnf-family-apply-preserves-received-source-carry
 (implies (and (fn-bphs-held-sourcesp (fn-bpnf-held-list st))
               (equal (car (fn-bpnf-family-apply st record arrival)) :ready))
  (fn-bphs-held-sourcesp (fn-bpn-nth 1 (fn-bpnf-family-apply st record arrival))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bphgf-ready-plan-source-by-definition
   (anchor (fn-bpnf-find-arrival (fn-bpn-nth 3 record) (fn-bpnf-held-list st)))))
  :in-theory (e/d (fn-bpnf-family-apply fn-bpnf-held fn-bphs-held-sourcesp
                   fn-bphs-held-sourcep)
    (fn-bpnf-held-list fn-bpnf-held-principal fn-bpnf-held-id fn-bpb-bundle-id
     fn-bpnf-family-plan fn-bpnf-find-arrival fn-bpnf-arrival-count
     fn-bpnf-active-fragmentp fn-bpnf-find-held fn-bpnf-held-key fn-bpnf-heldp
     fn-bpnf-active-set fn-bpnf-family-retain-other-rows
     fn-bpnf-family-recordp fn-bpnf-family-record-atp fn-frame-natp
     fn-bpnf-cl-ingressp fn-bphg-held-auxp fn-bphg-held-auxsp
     fn-bphg-consumed-rowsp))))
 :rule-classes nil)

(defthm fn-bpnf-frame-held-with-anchor-has-received-source
 (implies (and (fn-bpnf-cl-ingressp ingress) (natp arrival)
               (fn-bpb-bundlep bundle) (equal wire (fn-bpb-encode bundle)))
  (fn-bphs-held-sourcep
   (fn-bpnf-frame-held-with-anchor ingress arrival bundle wire anchor)))
 :hints (("Goal"
  :use ((:instance fn-bphgf-frame-source-by-definition)
        (:instance fn-bpb-encode-is-an-octet-list (bundle bundle)))
  :in-theory (theory 'minimal-theory)))
 :rule-classes nil)
