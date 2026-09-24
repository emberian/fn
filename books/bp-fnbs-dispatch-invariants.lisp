; Canonical version-2 received-dispatch frame, kept distinct from the
; version-1 clock-domain marker with the same numeric kind.
(in-package "ACL2")
(include-book "bp-fnbs-dispatch-codec")
(include-book "bp-primary-invariants")
(include-book "frame-trailer")
(include-book "frame-invariants")

(defthm fn-bpnp-dispatch-peer-reconstructs
  (implies (fn-bpp-eidp peer)
           (equal (fn-bpn-peer-from-octets (fn-bpn-peer-octets peer))
                  peer))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpc-value-round-trip
                            (x (fn-bpp-eid-value peer)))
                 (:instance fn-bpp-eid-value-is-shape (e peer))
                 (:instance fn-bpp-eid-value-cost (e peer))
                 (:instance fn-bpc-enc-length-bound
                            (flg :item) (x (fn-bpp-eid-value peer)))
                 (:instance fn-cbor-at-mostp-from-length
                            (xs (fn-bpn-peer-octets peer))
                            (bound *fn-bpc-max-input*)))
           :in-theory (e/d (fn-bpc-valuep fn-bpn-peer-octets
                            fn-bpn-peer-from-octets)
                           (fn-bpp-eidp fn-bpp-eid-value fn-bpc-enc
                            fn-bpc-decode-exact)))))

(defthm fn-bpnp-dispatch-peer-blob-nonempty
  (implies (fn-bpp-eidp peer)
           (consp (fn-bpn-peer-octets peer)))
  :hints (("Goal" :do-not-induct t
           :use (fn-bpnp-dispatch-peer-reconstructs)
           :in-theory (e/d (fn-bpn-peer-from-octets)
                           (fn-bpp-eidp fn-bpn-peer-octets)))))

(defthm fn-bpnp-dispatch-peer-blob-fits
  (implies (fn-bpp-eidp peer)
           (<= (len (fn-bpn-peer-octets peer)) 11363))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpp-eid-value-is-shape (e peer))
                 (:instance fn-bpp-eid-value-cost (e peer))
                 (:instance fn-bpc-enc-length-bound
                            (flg :item) (x (fn-bpp-eid-value peer))))
           :in-theory (e/d (fn-bpn-peer-octets)
                           (fn-bpp-eidp fn-bpp-eid-value fn-bpc-enc)))))

(defthm fn-bpnp-dispatch-record-values-ok
  (implies (fn-bpnp-dispatch-recordp row)
           (fn-frame-values-okp *fn-bpnp-dispatch-fields*
                                (fn-bpnp-dispatch-values row)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-dispatch-peer-blob-nonempty
                            (peer (fn-bpn-nth 5 row)))
                 (:instance fn-bpnp-dispatch-peer-blob-fits
                            (peer (fn-bpn-nth 5 row)))
                 (:instance fn-bpc-enc-is-true-list
                            (flg :item)
                            (x (fn-bpp-eid-value (fn-bpn-nth 5 row))))
                 (:instance fn-cbor-at-mostp-from-length
                            (xs (fn-bpn-nth 4 row))
                            (bound *fn-frame-max-blob*))
                 (:instance fn-cbor-at-mostp-from-length
                            (xs (fn-bpn-peer-octets (fn-bpn-nth 5 row)))
                            (bound *fn-frame-max-blob*)))
           :in-theory (e/d (fn-bpnp-dispatch-recordp fn-bpn-peer-octets
                            fn-bpnp-dispatch-values fn-frame-values-okp
                            fn-frame-field-okp fn-frame-blobp)
                           (fn-bpp-eidp fn-bpp-eid-value
                            fn-cbor-at-mostp)))))

(defthm fn-bpnp-dispatch-payload-length
  (implies (fn-frame-values-okp *fn-bpnp-dispatch-fields* values)
           (equal (len (fn-frame-fields-octets
                        *fn-bpnp-dispatch-fields* values))
                  (+ 32 (len (nth 3 values)) (len (nth 4 values)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-frame-fields-octets
                              fn-frame-field-octets
                              fn-frame-len-of-append
                              fn-frame-u64-bytes-len
                              fn-frame-u32-bytes-len))))

(defthm fn-bpnp-dispatch-record-frame-input
  (implies (fn-bpnp-dispatch-recordp row)
           (fn-frame-inputp
            *fn-frame-magic-bundle-store*
            *fn-bpnp-dispatch-frame-version*
            *fn-bpnp-dispatch-kind*
            (fn-frame-fields-octets *fn-bpnp-dispatch-fields*
                                    (fn-bpnp-dispatch-values row))
            *fn-bpn-lifecycle-max-payload*))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-dispatch-record-values-ok)
                 (:instance fn-bpnp-dispatch-payload-length
                            (values (fn-bpnp-dispatch-values row)))
                 (:instance fn-bpnp-dispatch-peer-blob-fits
                            (peer (fn-bpn-nth 5 row)))
                 (:instance fn-frame-fields-octets-are-octets
                            (specs *fn-bpnp-dispatch-fields*)
                            (values (fn-bpnp-dispatch-values row))))
           :in-theory (e/d (fn-frame-inputp fn-bpnp-dispatch-recordp
                            fn-bpnp-dispatch-values)
                           (fn-frame-fields-octets fn-frame-values-okp
                            fn-bpn-peer-octets fn-bpp-eidp)))))

(defthm fn-bpnp-dispatch-six-field-reconstructs
  (implies (and (true-listp row) (equal (len row) 6))
           (equal (list (car row) (fn-bpn-nth 1 row)
                        (fn-bpn-nth 2 row) (fn-bpn-nth 3 row)
                        (fn-bpn-nth 4 row) (fn-bpn-nth 5 row))
                  row))
  :hints (("Goal" :in-theory (enable fn-bpn-nth)
           :expand ((len row) (len (cdr row))
                    (len (cddr row)) (len (cdddr row))
                    (len (cddddr row)) (len (cdr (cddddr row)))))))

(defthm fn-bpnp-dispatch-record-reconstructs
  (implies (fn-bpnp-dispatch-recordp row)
           (equal (fn-bpnp-dispatch-from-values
                   (fn-bpnp-dispatch-values row))
                  row))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-dispatch-peer-reconstructs
                            (peer (fn-bpn-nth 5 row)))
                 (:instance fn-bpnp-dispatch-six-field-reconstructs))
           :in-theory (e/d (fn-bpnp-dispatch-from-values
                            fn-bpnp-dispatch-values
                            fn-bpnp-dispatch-recordp)
                           (fn-bpn-peer-octets fn-bpn-peer-from-octets
                            fn-bpp-eidp)))))

(defthm fn-bpnp-dispatch-seal-is-octets
  (implies
   (fn-frame-inputp *fn-frame-magic-bundle-store*
                    *fn-bpnp-dispatch-frame-version*
                    *fn-bpnp-dispatch-kind* payload
                    *fn-bpn-lifecycle-max-payload*)
   (fn-cbor-octet-listp
    (fn-frame-seal *fn-frame-magic-bundle-store*
                   *fn-bpnp-dispatch-frame-version*
                   *fn-bpnp-dispatch-kind* payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-header-octets
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-bpnp-dispatch-frame-version*)
                            (kind *fn-bpnp-dispatch-kind*)
                            (length (len payload))))
           :in-theory (enable fn-frame-seal fn-frame-encode
                              fn-frame-protected fn-frame-inputp
                              fn-frame-digestp fn-frame-magicp))))

(defthm fn-bpnp-dispatch-decode-of-seal
  (implies
   (fn-frame-inputp *fn-frame-magic-bundle-store*
                    *fn-bpnp-dispatch-frame-version*
                    *fn-bpnp-dispatch-kind* payload
                    *fn-bpn-lifecycle-max-payload*)
   (equal
    (fn-frame-decode
     (fn-frame-seal *fn-frame-magic-bundle-store*
                    *fn-bpnp-dispatch-frame-version*
                    *fn-bpnp-dispatch-kind* payload)
     (fn-frame-trailer
      (fn-frame-protected-prefix
       (fn-frame-seal *fn-frame-magic-bundle-store*
                      *fn-bpnp-dispatch-frame-version*
                      *fn-bpnp-dispatch-kind* payload)))
     *fn-bpn-lifecycle-max-payload*)
    (fn-frame-ok *fn-frame-magic-bundle-store*
                 *fn-bpnp-dispatch-frame-version*
                 *fn-bpnp-dispatch-kind* payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-host-framing
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-bpnp-dispatch-frame-version*)
                            (kind *fn-bpnp-dispatch-kind*)
                            (max-payload *fn-bpn-lifecycle-max-payload*))
                 (:instance fn-frame-protected-plus-trailer-is-seal
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-bpnp-dispatch-frame-version*)
                            (kind *fn-bpnp-dispatch-kind*)
                            (max-payload *fn-bpn-lifecycle-max-payload*)))
           :in-theory (disable fn-frame-decode fn-frame-seal))))

(defthm fn-bpnp-dispatch-frame-is-seal
  (implies
   (and (fn-bpnp-dispatch-recordp row)
        (fn-frame-values-okp *fn-bpnp-dispatch-fields*
                             (fn-bpnp-dispatch-values row))
        (fn-frame-inputp
         *fn-frame-magic-bundle-store*
         *fn-bpnp-dispatch-frame-version*
         *fn-bpnp-dispatch-kind*
         (fn-frame-fields-octets *fn-bpnp-dispatch-fields*
                                 (fn-bpnp-dispatch-values row))
         *fn-bpn-lifecycle-max-payload*))
   (equal (fn-bpnp-dispatch-frame row)
          (fn-frame-seal
           *fn-frame-magic-bundle-store*
           *fn-bpnp-dispatch-frame-version*
           *fn-bpnp-dispatch-kind*
           (fn-frame-fields-octets *fn-bpnp-dispatch-fields*
                                   (fn-bpnp-dispatch-values row)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-protected-plus-trailer-is-seal
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-bpnp-dispatch-frame-version*)
                            (kind *fn-bpnp-dispatch-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-bpnp-dispatch-fields*
                                      (fn-bpnp-dispatch-values row)))
                            (max-payload *fn-bpn-lifecycle-max-payload*)))
           :in-theory (e/d (fn-bpnp-dispatch-frame fn-frame-inputp)
                           (fn-bpnp-dispatch-recordp
                            fn-bpnp-dispatch-values
                            fn-frame-fields-octets)))))

(defthm fn-bpnp-dispatch-unframe-of-canonical-frame
  (implies
   (and (fn-bpnp-dispatch-recordp row)
        (fn-frame-values-okp *fn-bpnp-dispatch-fields*
                             (fn-bpnp-dispatch-values row))
        (fn-frame-inputp
         *fn-frame-magic-bundle-store*
         *fn-bpnp-dispatch-frame-version*
         *fn-bpnp-dispatch-kind*
         (fn-frame-fields-octets *fn-bpnp-dispatch-fields*
                                 (fn-bpnp-dispatch-values row))
         *fn-bpn-lifecycle-max-payload*)
        (equal (fn-bpnp-dispatch-frame row)
               (fn-frame-seal
                *fn-frame-magic-bundle-store*
                *fn-bpnp-dispatch-frame-version*
                *fn-bpnp-dispatch-kind*
                (fn-frame-fields-octets *fn-bpnp-dispatch-fields*
                                        (fn-bpnp-dispatch-values row))))
        (equal (fn-bpnp-dispatch-from-values
                (fn-bpnp-dispatch-values row)) row))
   (equal (fn-bpnp-dispatch-unframe (fn-bpnp-dispatch-frame row))
          row))
  :rule-classes nil
  :hints
  (("Goal" :do-not-induct t
    :use ((:instance fn-bpnp-dispatch-decode-of-seal
                     (payload (fn-frame-fields-octets
                               *fn-bpnp-dispatch-fields*
                               (fn-bpnp-dispatch-values row))))
          (:instance fn-frame-fields-parse-of-octets
                     (specs *fn-bpnp-dispatch-fields*)
                     (values (fn-bpnp-dispatch-values row)))
          (:instance fn-bpnp-dispatch-seal-is-octets
                     (payload (fn-frame-fields-octets
                               *fn-bpnp-dispatch-fields*
                               (fn-bpnp-dispatch-values row)))))
    :in-theory
    (e/d (fn-bpnp-dispatch-unframe fn-frame-inputp)
         (fn-bpnp-dispatch-frame fn-bpnp-dispatch-recordp fn-bpnp-dispatch-values
          fn-bpnp-dispatch-from-values fn-frame-decode
          fn-frame-fields-parse fn-frame-fields-octets)))))

(defthm fn-bpnp-dispatch-unframe-of-valid-frame
  (implies
   (and (fn-bpnp-dispatch-recordp row)
        (fn-frame-values-okp *fn-bpnp-dispatch-fields*
                             (fn-bpnp-dispatch-values row))
        (fn-frame-inputp
         *fn-frame-magic-bundle-store*
         *fn-bpnp-dispatch-frame-version*
         *fn-bpnp-dispatch-kind*
         (fn-frame-fields-octets *fn-bpnp-dispatch-fields*
                                 (fn-bpnp-dispatch-values row))
         *fn-bpn-lifecycle-max-payload*)
        (equal (fn-bpnp-dispatch-from-values
                (fn-bpnp-dispatch-values row)) row))
   (equal (fn-bpnp-dispatch-unframe (fn-bpnp-dispatch-frame row))
          row))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bpnp-dispatch-frame-is-seal
                 fn-bpnp-dispatch-unframe-of-canonical-frame)
           :in-theory (disable fn-bpnp-dispatch-recordp
                               fn-bpnp-dispatch-frame
                               fn-bpnp-dispatch-unframe
                               fn-bpnp-dispatch-values
                               fn-bpnp-dispatch-from-values
                               fn-frame-fields-octets))))

(defthm fn-bpnp-dispatch-record-round-trip
  (implies (fn-bpnp-dispatch-recordp row)
           (equal (fn-bpnp-dispatch-unframe (fn-bpnp-dispatch-frame row))
                  row))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bpnp-dispatch-record-values-ok
                 fn-bpnp-dispatch-record-frame-input
                 fn-bpnp-dispatch-record-reconstructs
                 fn-bpnp-dispatch-unframe-of-valid-frame)
           :in-theory (disable fn-bpnp-dispatch-recordp
                               fn-bpnp-dispatch-values
                               fn-bpnp-dispatch-from-values
                               fn-bpnp-dispatch-frame
                               fn-bpnp-dispatch-unframe
                               fn-frame-fields-octets))))

(verify-guards fn-bpn-peer-octets)
(verify-guards fn-bpn-peer-from-octets)
(verify-guards fn-bpnp-dispatch-record)
(verify-guards fn-bpnp-dispatch-recordp)
(verify-guards fn-bpnp-dispatch-values)
(verify-guards fn-bpnp-dispatch-frame)
(verify-guards fn-bpnp-dispatch-from-values)
(verify-guards fn-bpnp-dispatch-unframe)
