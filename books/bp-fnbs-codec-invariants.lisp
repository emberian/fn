; FNBS kind-5 byte and held-row correspondence.
(in-package "ACL2")
(include-book "bp-fnbs-codec")
(include-book "bp-bundle-invariants")
(include-book "bp-primary-invariants")

(defthm fn-bpnf-peer-octets-reconstruct-eid
  (implies (and (fn-bpp-eidp peer)
                (equal (fn-bpc-decode-exact
                        (fn-bpc-encode (fn-bpp-eid-value peer)))
                       (fn-cbor-ok (fn-bpp-eid-value peer) nil)))
           (equal (fn-bpn-peer-from-octets (fn-bpn-peer-octets peer))
                  peer))
  :hints (("Goal"
           :use ((:instance fn-bpp-value-eid-of-eid-value (e peer)))
           :in-theory (enable fn-bpn-peer-from-octets fn-bpn-peer-octets))))

(defthm fn-bpnf-six-field-ingress-reconstructs
  (implies (and (true-listp ingress)
                (equal (len ingress) 6)
                (equal (car ingress) :cl))
           (equal (list :cl (fn-bpn-nth 1 ingress)
                        (fn-bpn-nth 2 ingress)
                        (fn-bpn-nth 3 ingress)
                        (fn-bpn-nth 4 ingress)
                        (fn-bpn-nth 5 ingress))
                  ingress))
  :hints (("Goal" :in-theory (enable fn-bpn-nth)
           :expand ((len ingress) (len (cdr ingress))
                    (len (cddr ingress)) (len (cdddr ingress))
                    (len (cddddr ingress)) (len (cdr (cddddr ingress)))))))

(defthm fn-bpnf-stored-values-reconstruct-held
  (implies (and (fn-bpnf-frame-ingressp ingress)
                (equal ingress
                       (list :cl (fn-bpn-nth 1 ingress)
                             (fn-bpn-nth 2 ingress)
                             (fn-bpn-nth 3 ingress)
                             (fn-bpn-nth 4 ingress)
                             (fn-bpn-nth 5 ingress)))
                (fn-cbor-octet-listp wire)
                (<= (len wire) *fn-bpnf-max-held-image*)
                (fn-bpb-bundlep bundle)
                (fn-bpnf-stored-recordp
                 (fn-bpnf-stored-record
                  epoch operation-id
                  (fn-bpnf-frame-held ingress arrival bundle wire)))
                (equal (fn-bpn-peer-from-octets
                        (fn-bpn-peer-octets (fn-bpn-nth 3 ingress)))
                       (fn-bpn-nth 3 ingress))
                (equal (fn-bpb-decode wire *fn-bpnf-max-held-image*)
                       (fn-cbor-ok bundle nil)))
           (equal (fn-bpnf-stored-from-values
                   (fn-bpnf-stored-record-values
                    (fn-bpnf-stored-record
                     epoch operation-id
                     (fn-bpnf-frame-held ingress arrival bundle wire))))
                  (fn-bpnf-stored-record
                   epoch operation-id
                   (fn-bpnf-frame-held ingress arrival bundle wire))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnf-stored-from-values
                                    fn-bpnf-stored-record-values
                                    fn-bpnf-frame-held
                                    fn-bpnf-cl-ingressp)
                                   (fn-bpnf-stored-recordp
                                    fn-bpnf-heldp
                                    fn-bpn-peer-octets
                                    fn-bpn-peer-from-octets
                                    fn-bpb-decode fn-bpb-encode
                                    fn-bpp-eid-value fn-bpc-enc)))))

(defthm fn-bpnf-stored-protected-is-octets
  (implies (and (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-bpn-lifecycle-max-payload*))
           (fn-cbor-octet-listp
            (fn-frame-protected *fn-frame-magic-bundle-store*
                                *fn-frame-version*
                                *fn-bpnf-stored-code* payload)))
  :hints (("Goal" :use ((:instance fn-frame-header-octets
                                   (magic *fn-frame-magic-bundle-store*)
                                   (version *fn-frame-version*)
                                   (kind *fn-bpnf-stored-code*)
                                   (length (len payload))))
           :in-theory (enable fn-frame-protected fn-frame-magicp))))

(defthm fn-bpnf-stored-frame-is-fnbs-seal
  (implies (and (fn-bpnf-stored-recordp record)
                (fn-frame-values-okp
                 *fn-bpnf-stored-fields*
                 (fn-bpnf-stored-record-values record))
                (fn-cbor-octet-listp
                 (fn-frame-fields-octets
                  *fn-bpnf-stored-fields*
                  (fn-bpnf-stored-record-values record)))
                (fn-cbor-at-mostp
                 (fn-frame-fields-octets
                  *fn-bpnf-stored-fields*
                  (fn-bpnf-stored-record-values record))
                 *fn-bpn-lifecycle-max-payload*)
                (<= (len (fn-frame-fields-octets
                          *fn-bpnf-stored-fields*
                          (fn-bpnf-stored-record-values record)))
                    *fn-bpn-lifecycle-max-payload*))
           (equal (fn-bpnf-stored-record-frame record)
                  (fn-frame-seal
                   *fn-frame-magic-bundle-store* *fn-frame-version*
                   *fn-bpnf-stored-code*
                   (fn-frame-fields-octets
                    *fn-bpnf-stored-fields*
                    (fn-bpnf-stored-record-values record)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpnf-stored-protected-is-octets
                                   (payload (fn-frame-fields-octets
                                             *fn-bpnf-stored-fields*
                                             (fn-bpnf-stored-record-values record)))))
           :in-theory
           (e/d (fn-bpnf-stored-record-frame
                 fn-bpnf-stored-record-protected
                 fn-frame-trailer fn-frame-seal fn-frame-encode)
                (fn-bpnf-stored-recordp
                 fn-bpnf-stored-record-values
                 fn-bpn-peer-octets fn-bpp-eid-value fn-bpc-enc)))))
