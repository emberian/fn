; Guard obligations for the exact native fragment-step call. The base-state
; invariant is maintained by the owner; no whole-held-list recognizer is
; inserted into the served event body.
(in-package "ACL2")
(include-book "bp-node-fragment-step")
(include-book "bp-node-machine-guards")

(local
 (defthm fn-bpnfg-total-nth-is-nth
   (implies (natp n)
            (equal (fn-bpn-nth n xs) (nth n xs)))
   :hints (("Goal" :induct (fn-bpn-nth n xs)
            :in-theory (enable fn-bpn-nth fn-cbor-ag-car)))))

(local
 (defthm fn-bpnfg-bundle-primary-blockp
   (implies (fn-bpb-bundlep bundle)
            (fn-bpp-blockp (fn-bpb-bundle-primary bundle)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpb-bundlep)
                            (fn-bpp-blockp fn-bpp-eidp
                             fn-bpp-vchar-listp fn-bpp-vcharp))))))

(local
 (defthm fn-bpnfg-held-bundlep
   (implies (fn-bpnf-heldp h)
            (fn-bpb-bundlep (fn-bpnf-held-bundle h)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnf-heldp)
                            (fn-bpb-bundlep fn-bpb-encode))))))

(local
 (defthm fn-bpnfg-held-true-listp
   (implies (fn-bpnf-heldp h) (true-listp h))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnf-heldp)
                            (fn-bpb-bundlep fn-bpb-encode
                             fn-bpp-blockp fn-bpp-eidp))))))

(local
 (defthm fn-bpnfg-held-primary-guard-fields
   (implies (fn-bpnf-heldp h)
            (and (true-listp h)
                 (true-listp
                  (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
                 (natp
                  (fn-bpp-flags
                   (fn-bpb-bundle-primary (fn-bpnf-held-bundle h))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bpnfg-held-true-listp)
                  (:instance fn-bpnfg-held-bundlep)
                  (:instance fn-bpnfg-bundle-primary-blockp
                             (bundle (fn-bpnf-held-bundle h)))
                  (:instance fn-bpn-bundle-primary-true-list-for-guard
                             (bundle (fn-bpnf-held-bundle h)))
                  (:instance fn-bpn-report-primary-flags-natural-for-guard
                             (primary
                              (fn-bpb-bundle-primary
                               (fn-bpnf-held-bundle h)))))
            :in-theory (union-theories
                        '(fn-bpnfg-held-true-listp)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnfg-held-octets-natp
   (natp (fn-bpnf-held-octets held))
   :hints (("Goal" :induct (fn-bpnf-held-octets held)
            :in-theory (enable fn-bpnf-held-octets)))))

(local
 (defthm fn-bpnfg-fragment-query-true-listp
   (true-listp (fn-bpnf-fragment-query st anchor))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnf-fragment-query)
                            (fn-bpnf-active-set fn-bpnf-fragment-cells
                             fn-bpfw-spec fn-bpf-canvas))))))

(verify-guards fn-bpnf-arrival-count)
(verify-guards fn-bpnf-find-arrival)
(verify-guards fn-bpnf-family-retain-other-rows)
(verify-guards fn-bpnf-family-member)
(verify-guards fn-bpnf-fragment-coherence-key)
(verify-guards fn-bpnf-active-fragmentp
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnfg-held-primary-guard-fields))
           :in-theory (disable fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpnfg-held-primary-guard-fields))))
(verify-guards fn-bpnf-same-fragment-family-p)
(verify-guards fn-bpnf-active-set-rows)
(verify-guards fn-bpnf-active-set)
(verify-guards fn-bpnf-fragment-cells
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpn-nth fn-bpb-bundle-primary
                              fn-bpb-bundle-payload fn-bpb-block-data
                              fn-bpb-payload))))
(verify-guards fn-bpnf-fragment-query)
(verify-guards fn-bpnf-offset-zero-source
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpn-nth fn-bpp-fragment-offset))))
(verify-guards fn-bpnf-family-whole-bundle
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnfg-held-primary-guard-fields (h zero))
                 (:instance fn-bpnfg-held-bundlep (h zero))
                 (:instance fn-bpnfg-bundle-primary-blockp
                            (bundle (fn-bpnf-held-bundle zero))))
           :in-theory (disable fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpp-blockp
                               fn-bpnfg-held-primary-guard-fields
                               fn-bpnfg-held-bundlep
                               fn-bpnfg-bundle-primary-blockp))))
(verify-guards fn-bpnf-family-plan
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-state-field-types-for-guard
                            (st (fn-bpnf-base st)))
                 (:instance fn-bpnfg-held-octets-natp
                            (held (fn-bpnf-held-list st)))
                 (:instance fn-bpnfg-held-octets-natp
                            (held (fn-bpnf-active-set st anchor))))
           :in-theory (disable fn-bpnf-fragment-query-is-reference
                               fn-bpnf-fragment-query fn-bpnf-active-set
                               fn-bpnf-family-whole-bundle
                               fn-bpnf-held-octets
                               fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpb-bundlep fn-bpb-encode
                               fn-bpn-state-field-types-for-guard
                               fn-bpnfg-held-octets-natp))))
(verify-guards fn-bpnf-family-record)
(verify-guards fn-bpnf-family-recordp)
(verify-guards fn-bpnf-family-record-atp)

; The family-plan theorem is stated with car/cadr.  The executable apply
; guard uses the total selectors, so bridge just those two fields while the
; expensive plan body stays closed.
(local
 (defthm fn-bpnfg-second-is-cadr
   (equal (fn-bpn-nth 1 xs) (cadr xs))
   ; Two unfoldings and nothing else; the enabled world spent 4 s here.
   :hints (("Goal" :expand ((fn-bpn-nth 1 xs) (fn-bpn-nth 0 (cdr xs)))
            :in-theory (union-theories
                        '(fn-cbor-ag-car natp zp (natp) (zp) (binary-+)
                          (unary--) (not) default-car default-cdr)
                        (theory 'minimal-theory))))))
(local
 (defthm fn-bpnfg-car-is-car
   (equal (fn-cbor-ag-car xs) (car xs))
   :hints (("Goal" :in-theory (enable fn-cbor-ag-car)))))
(local
 (defthm fn-bpnfg-ready-plan-bundlep
   (implies (equal (fn-cbor-ag-car (fn-bpnf-family-plan st anchor)) :ready)
            (fn-bpb-bundlep
             (fn-bpn-nth 1 (fn-bpnf-family-plan st anchor))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bpnf-family-ready-has-valid-whole))
            :in-theory (union-theories
                        '(fn-bpnfg-second-is-cadr fn-bpnfg-car-is-car)
                        (theory 'minimal-theory))))))
(verify-guards fn-bpnf-family-apply
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnfg-ready-plan-bundlep
                            (anchor (fn-bpnf-find-arrival
                                     (fn-bpn-nth 3 record)
                                     (fn-bpnf-held-list st)))))
           :in-theory (disable fn-bpnf-family-plan
                               fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpn-machine-statep
                               fn-bpnfg-ready-plan-bundlep))))
(verify-guards fn-bpnf-family-rows-livep)
(verify-guards fn-bpnf-family-plan-at)
(verify-guards fn-bpnf-family-record-at)
(verify-guards fn-bpnf-family-v1-values)
(verify-guards fn-bpnf-family-v1-frame)
(verify-guards fn-bpnf-family-apply-at
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpnf-family-record-atp
                               fn-bpnf-family-plan-at
                               fn-bpnf-family-apply))))
; Recovery calls the inherited unverified kind-5 decoder and row predicate.
; Its guard closure remains a separate A2 codec obligation.
(verify-guards fn-bpnf-family-issuedp)
(verify-guards fn-bpnf-family-propose-step
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-state-config-for-guard
                            (st (fn-bpnf-base st)))
                 (:instance fn-bpn-state-field-types-for-guard
                            (st (fn-bpnf-base st))))
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpn-state-config-for-guard
                               fn-bpn-state-field-types-for-guard
                               fn-bpnf-family-plan fn-bpnf-family-apply
                               fn-bpnf-family-frame))))
(verify-guards fn-bpnf-family-persist-step
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpnf-family-apply
                               fn-bpnf-family-plan))))
(verify-guards fn-bpnf-family-next-aux
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpnf-family-plan))))
(verify-guards fn-bpnf-family-tried-p)
(verify-guards fn-bpnf-family-next-memo
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpnf-family-plan))))
(verify-guards fn-bpnf-family-next
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-family-next-memo-is-aux
                            (held (fn-bpnf-held-list st)) (tried nil)))
           :in-theory (union-theories
                       '(fn-bpnf-subsetp-equal-reflexive
                         (:executable-counterpart fn-bpnf-family-tried-okp))
                       (theory 'minimal-theory)))))
(verify-guards fn-bpnf-fragment-step)
