; FNBS kind-5 byte and held-row correspondence.
(in-package "ACL2")
(include-book "bp-fnbs-codec")
(include-book "bp-bundle-invariants")
(include-book "bp-primary-invariants")
(include-book "frame-trailer")

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

(defthm fn-bpnf-kind-five-payload-length
  (implies (fn-frame-values-okp *fn-bpnf-stored-fields* values)
           (equal (len (fn-frame-fields-octets
                        *fn-bpnf-stored-fields* values))
                  (+ 76 (len (nth 6 values))
                     (len (nth 8 values)) (len (nth 10 values)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-frame-fields-octets
                              fn-frame-field-octets
                              fn-frame-len-of-append
                              fn-frame-u64-bytes-len
                              fn-frame-u32-bytes-len))))

(defthm fn-bpnf-kind-five-fits-with-peer-bound
  (implies (and (fn-frame-values-okp *fn-bpnf-stored-fields* values)
                (<= (len (nth 6 values)) 2048)
                (<= (len (nth 8 values)) 512)
                (<= (len (nth 10 values)) *fn-bpnf-max-held-image*))
           (and (<= (len (fn-frame-fields-octets
                         *fn-bpnf-stored-fields* values))
                    *fn-bpn-lifecycle-max-payload*)
                (fn-cbor-at-mostp
                 (fn-frame-fields-octets *fn-bpnf-stored-fields* values)
                 *fn-bpn-lifecycle-max-payload*)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-kind-five-payload-length)
                 (:instance fn-frame-fields-octets-are-octets
                            (specs *fn-bpnf-stored-fields*))
                 (:instance fn-cbor-at-mostp-from-length
                            (xs (fn-frame-fields-octets
                                 *fn-bpnf-stored-fields* values))
                            (bound *fn-bpn-lifecycle-max-payload*)))
           :in-theory (disable fn-frame-fields-octets
                               fn-frame-values-okp))))

(defthm fn-bpnf-eid-encoded-peer-fits
  (implies (fn-bpp-eidp peer)
           (<= (len (fn-bpn-peer-octets peer)) 2048))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :cases ((equal peer '(:dtn-none))
                   (equal (car peer) :ipn))
           :use ((:instance fn-bpc-argument-length-bound
                            (major 4) (n 2))
                 (:instance fn-bpc-argument-length-bound
                            (major 3) (n (len (cdr peer))))
                 (:instance fn-bpc-argument-length-bound
                            (major 0) (n (nth 1 peer)))
                 (:instance fn-bpc-argument-length-bound
                            (major 0) (n (nth 2 peer))))
           :in-theory (e/d (fn-bpn-peer-octets fn-bpp-eid-value
                            fn-bpc-enc fn-bpp-eidp fn-bpp-dtn-sspp
                            fn-frame-len-of-append)
                           (fn-bpc-argument fn-bpc-argument-length-bound)))))

(defthm fn-bpnf-at-mostp-implies-length-bound
  (implies (and (natp bound) (fn-cbor-at-mostp xs bound))
           (<= (len xs) bound))
  :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
           :in-theory (enable fn-cbor-at-mostp))))

(defthm fn-bpnf-ingress-principal-fits
  (implies (fn-bpnf-cl-ingressp ingress)
           (<= (len (if (fn-bpn-nth 4 ingress)
                        (fn-bpn-nth 4 ingress) '(0))) 512))
  :hints (("Goal" :use ((:instance fn-bpnf-at-mostp-implies-length-bound
                                   (xs (fn-bpn-nth 4 ingress))
                                   (bound *fn-frame-max-text*)))
           :in-theory (enable fn-bpnf-cl-ingressp
                              fn-bpn-machine-textp fn-frame-textp))))

(defthm fn-bpnf-stored-values-fit-frame
  (implies
   (and (fn-bpnf-stored-recordp record)
        (fn-frame-values-okp
         *fn-bpnf-stored-fields* (fn-bpnf-stored-record-values record)))
   (fn-cbor-at-mostp
    (fn-frame-fields-octets
     *fn-bpnf-stored-fields* (fn-bpnf-stored-record-values record))
    *fn-bpn-lifecycle-max-payload*))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-kind-five-fits-with-peer-bound
                            (values (fn-bpnf-stored-record-values record)))
                 (:instance fn-bpnf-eid-encoded-peer-fits
                            (peer (fn-bpn-nth 3 (nth 4 (nth 3 record)))))
                 (:instance fn-bpnf-ingress-principal-fits
                            (ingress (nth 4 (nth 3 record)))))
           :in-theory (e/d (fn-bpnf-stored-recordp
                            fn-bpnf-stored-record-values
                            fn-bpnf-frame-ingressp)
                           (fn-bpnf-heldp fn-frame-values-okp
                            fn-frame-fields-octets fn-bpn-peer-octets
                            fn-bpnf-kind-five-fits-with-peer-bound
                            fn-bpnf-eid-encoded-peer-fits
                            fn-bpnf-ingress-principal-fits)))))

(defthm fn-bpnf-valid-kind-five-encodes
  (implies
   (and (fn-bpnf-stored-recordp record)
        (fn-frame-values-okp
         *fn-bpnf-stored-fields* (fn-bpnf-stored-record-values record)))
   (not (equal (fn-bpnf-stored-record-frame record) :bad)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-stored-values-fit-frame))
           :in-theory (e/d (fn-bpnf-stored-record-frame
                            fn-bpnf-stored-record-protected
                            fn-frame-protected)
                           (fn-bpnf-stored-recordp
                            fn-bpnf-stored-record-values
                            fn-frame-values-okp fn-frame-fields-octets)))))

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

(defthm fn-bpnf-stored-seal-is-octets
  (implies
   (fn-frame-inputp *fn-frame-magic-bundle-store* *fn-frame-version*
                    *fn-bpnf-stored-code* payload
                    *fn-bpn-lifecycle-max-payload*)
   (fn-cbor-octet-listp
    (fn-frame-seal *fn-frame-magic-bundle-store* *fn-frame-version*
                   *fn-bpnf-stored-code* payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-header-octets
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-frame-version*)
                            (kind *fn-bpnf-stored-code*)
                            (length (len payload))))
           :in-theory (enable fn-frame-seal fn-frame-encode
                              fn-frame-protected fn-frame-inputp
                              fn-frame-digestp fn-frame-magicp))))

(defthm fn-bpnf-stored-decode-of-seal
  (implies (fn-frame-inputp *fn-frame-magic-bundle-store*
                            *fn-frame-version* *fn-bpnf-stored-code*
                            payload *fn-bpn-lifecycle-max-payload*)
           (equal
            (fn-frame-decode
             (fn-frame-seal *fn-frame-magic-bundle-store*
                            *fn-frame-version* *fn-bpnf-stored-code* payload)
             (fn-frame-trailer
              (fn-frame-protected-prefix
               (fn-frame-seal *fn-frame-magic-bundle-store*
                              *fn-frame-version* *fn-bpnf-stored-code* payload)))
             *fn-bpn-lifecycle-max-payload*)
            (fn-frame-ok *fn-frame-magic-bundle-store*
                         *fn-frame-version* *fn-bpnf-stored-code* payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-host-framing
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-frame-version*)
                            (kind *fn-bpnf-stored-code*)
                            (max-payload *fn-bpn-lifecycle-max-payload*))
                 (:instance fn-frame-protected-plus-trailer-is-seal
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-frame-version*)
                            (kind *fn-bpnf-stored-code*)
                            (max-payload *fn-bpn-lifecycle-max-payload*)))
           :in-theory (disable fn-frame-decode fn-frame-seal))))

(defthm fn-bpnf-stored-unframe-of-canonical-frame
  (implies
   (and (fn-bpnf-stored-recordp record)
        (fn-frame-values-okp *fn-bpnf-stored-fields*
                             (fn-bpnf-stored-record-values record))
        (fn-frame-inputp
         *fn-frame-magic-bundle-store* *fn-frame-version*
         *fn-bpnf-stored-code*
         (fn-frame-fields-octets *fn-bpnf-stored-fields*
                                 (fn-bpnf-stored-record-values record))
         *fn-bpn-lifecycle-max-payload*)
        (equal (fn-bpnf-stored-from-values
                (fn-bpnf-stored-record-values record)) record)
        (equal (fn-bpnf-stored-record-frame record)
               (fn-frame-seal
                *fn-frame-magic-bundle-store* *fn-frame-version*
                *fn-bpnf-stored-code*
                (fn-frame-fields-octets *fn-bpnf-stored-fields*
                                        (fn-bpnf-stored-record-values record)))))
   (equal (fn-bpnf-stored-record-unframe
           (fn-bpnf-stored-record-frame record))
          record))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-stored-decode-of-seal
                            (payload (fn-frame-fields-octets
                                      *fn-bpnf-stored-fields*
                                      (fn-bpnf-stored-record-values record))))
                 (:instance fn-frame-fields-parse-of-octets
                            (specs *fn-bpnf-stored-fields*)
                            (values (fn-bpnf-stored-record-values record)))
                 (:instance fn-bpnf-stored-seal-is-octets
                            (payload (fn-frame-fields-octets
                                      *fn-bpnf-stored-fields*
                                      (fn-bpnf-stored-record-values record)))))
           :in-theory (e/d (fn-bpnf-stored-record-unframe)
                           (fn-bpnf-stored-recordp
                            fn-bpnf-stored-record-frame
                            fn-bpnf-stored-record-values
                            fn-bpnf-stored-from-values
                            fn-frame-decode fn-frame-fields-parse
                            fn-frame-fields-octets)))))
