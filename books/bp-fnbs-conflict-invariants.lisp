; The kind-14 conflict frame decodes to exactly the record it encodes.
(in-package "ACL2")
(include-book "bp-fnbs-conflict-codec")
(include-book "bp-fnbs-dispatch-invariants")

(defthm fn-bpnf-conflict-record-values-ok
  (implies (fn-bpnf-conflict-recordp row)
           (fn-frame-values-okp *fn-bpnf-conflict-fields*
                                (fn-bpnf-conflict-values row)))
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
                            (xs (fn-bpn-nth 8 row))
                            (bound *fn-frame-max-blob*))
                 (:instance fn-cbor-at-mostp-from-length
                            (xs (fn-bpn-peer-octets (fn-bpn-nth 5 row)))
                            (bound *fn-frame-max-blob*)))
           :in-theory (e/d (fn-bpnf-conflict-recordp fn-bpn-peer-octets
                            fn-bpnf-conflict-values fn-frame-values-okp
                            fn-frame-field-okp fn-frame-blobp)
                           (fn-bpp-eidp fn-bpp-eid-value
                            fn-cbor-at-mostp)))))

(defthm fn-bpnf-conflict-payload-length
  (implies (fn-frame-values-okp *fn-bpnf-conflict-fields* values)
           (equal (len (fn-frame-fields-octets
                        *fn-bpnf-conflict-fields* values))
                  (+ 60 (len (nth 3 values)) (len (nth 4 values))
                     (len (nth 8 values)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-frame-fields-octets
                              fn-frame-field-octets
                              fn-frame-len-of-append
                              fn-frame-u64-bytes-len
                              fn-frame-u32-bytes-len))))

(defthm fn-bpnf-conflict-record-frame-input
  (implies (fn-bpnf-conflict-recordp row)
           (fn-frame-inputp
            *fn-frame-magic-bundle-store*
            *fn-bpnf-conflict-frame-version*
            *fn-bpnf-conflict-kind*
            (fn-frame-fields-octets *fn-bpnf-conflict-fields*
                                    (fn-bpnf-conflict-values row))
            *fn-bpn-lifecycle-max-payload*))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-conflict-record-values-ok)
                 (:instance fn-bpnf-conflict-payload-length
                            (values (fn-bpnf-conflict-values row)))
                 (:instance fn-bpnp-dispatch-peer-blob-fits
                            (peer (fn-bpn-nth 5 row)))
                 (:instance fn-frame-fields-octets-are-octets
                            (specs *fn-bpnf-conflict-fields*)
                            (values (fn-bpnf-conflict-values row))))
           :in-theory (e/d (fn-frame-inputp fn-bpnf-conflict-recordp
                            fn-bpnf-conflict-values)
                           (fn-frame-fields-octets fn-frame-values-okp
                            fn-bpn-peer-octets fn-bpp-eidp)))))

(defthm fn-bpnf-conflict-nine-field-reconstructs
  (implies (and (true-listp row) (equal (len row) 9))
           (equal (list (car row) (fn-bpn-nth 1 row)
                        (fn-bpn-nth 2 row) (fn-bpn-nth 3 row)
                        (fn-bpn-nth 4 row) (fn-bpn-nth 5 row)
                        (fn-bpn-nth 6 row) (fn-bpn-nth 7 row)
                        (fn-bpn-nth 8 row))
                  row))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bpn-nth)
           :expand ((len row) (len (cdr row))
                    (len (cddr row)) (len (cdddr row))
                    (len (cddddr row)) (len (cdr (cddddr row)))
                    (len (cddr (cddddr row))) (len (cdddr (cddddr row)))
                    (len (cddddr (cddddr row)))))))

(defthm fn-bpnf-conflict-record-reconstructs
  (implies (fn-bpnf-conflict-recordp row)
           (equal (fn-bpnf-conflict-from-values
                   (fn-bpnf-conflict-values row))
                  row))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-dispatch-peer-reconstructs
                            (peer (fn-bpn-nth 5 row)))
                 (:instance fn-bpnf-conflict-nine-field-reconstructs))
           :in-theory (e/d (fn-bpnf-conflict-from-values
                            fn-bpnf-conflict-values
                            fn-bpnf-conflict-recordp)
                           (fn-bpn-peer-octets fn-bpn-peer-from-octets
                            fn-bpp-eidp)))))

(defthm fn-bpnf-conflict-seal-is-octets
  (implies
   (fn-frame-inputp *fn-frame-magic-bundle-store*
                    *fn-bpnf-conflict-frame-version*
                    *fn-bpnf-conflict-kind* payload
                    *fn-bpn-lifecycle-max-payload*)
   (fn-cbor-octet-listp
    (fn-frame-seal *fn-frame-magic-bundle-store*
                   *fn-bpnf-conflict-frame-version*
                   *fn-bpnf-conflict-kind* payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-header-octets
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-bpnf-conflict-frame-version*)
                            (kind *fn-bpnf-conflict-kind*)
                            (length (len payload))))
           :in-theory (enable fn-frame-seal fn-frame-encode
                              fn-frame-protected fn-frame-inputp
                              fn-frame-digestp fn-frame-magicp))))

(defthm fn-bpnf-conflict-decode-of-seal
  (implies
   (fn-frame-inputp *fn-frame-magic-bundle-store*
                    *fn-bpnf-conflict-frame-version*
                    *fn-bpnf-conflict-kind* payload
                    *fn-bpn-lifecycle-max-payload*)
   (equal
    (fn-frame-decode
     (fn-frame-seal *fn-frame-magic-bundle-store*
                    *fn-bpnf-conflict-frame-version*
                    *fn-bpnf-conflict-kind* payload)
     (fn-frame-trailer
      (fn-frame-protected-prefix
       (fn-frame-seal *fn-frame-magic-bundle-store*
                      *fn-bpnf-conflict-frame-version*
                      *fn-bpnf-conflict-kind* payload)))
     *fn-bpn-lifecycle-max-payload*)
    (fn-frame-ok *fn-frame-magic-bundle-store*
                 *fn-bpnf-conflict-frame-version*
                 *fn-bpnf-conflict-kind* payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-host-framing
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-bpnf-conflict-frame-version*)
                            (kind *fn-bpnf-conflict-kind*)
                            (max-payload *fn-bpn-lifecycle-max-payload*))
                 (:instance fn-frame-protected-plus-trailer-is-seal
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-bpnf-conflict-frame-version*)
                            (kind *fn-bpnf-conflict-kind*)
                            (max-payload *fn-bpn-lifecycle-max-payload*)))
           :in-theory (disable fn-frame-decode fn-frame-seal))))

(defthm fn-bpnf-conflict-frame-is-seal
  (implies
   (and (fn-bpnf-conflict-recordp row)
        (fn-frame-values-okp *fn-bpnf-conflict-fields*
                             (fn-bpnf-conflict-values row))
        (fn-frame-inputp
         *fn-frame-magic-bundle-store*
         *fn-bpnf-conflict-frame-version*
         *fn-bpnf-conflict-kind*
         (fn-frame-fields-octets *fn-bpnf-conflict-fields*
                                 (fn-bpnf-conflict-values row))
         *fn-bpn-lifecycle-max-payload*))
   (equal (fn-bpnf-conflict-frame row)
          (fn-frame-seal
           *fn-frame-magic-bundle-store*
           *fn-bpnf-conflict-frame-version*
           *fn-bpnf-conflict-kind*
           (fn-frame-fields-octets *fn-bpnf-conflict-fields*
                                   (fn-bpnf-conflict-values row)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-protected-plus-trailer-is-seal
                            (magic *fn-frame-magic-bundle-store*)
                            (version *fn-bpnf-conflict-frame-version*)
                            (kind *fn-bpnf-conflict-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-bpnf-conflict-fields*
                                      (fn-bpnf-conflict-values row)))
                            (max-payload *fn-bpn-lifecycle-max-payload*)))
           :in-theory (e/d (fn-bpnf-conflict-frame fn-frame-inputp)
                           (fn-bpnf-conflict-recordp
                            fn-bpnf-conflict-values
                            fn-frame-fields-octets)))))

(defthm fn-bpnf-conflict-unframe-of-canonical-frame
  (implies
   (and (fn-bpnf-conflict-recordp row)
        (fn-frame-values-okp *fn-bpnf-conflict-fields*
                             (fn-bpnf-conflict-values row))
        (fn-frame-inputp
         *fn-frame-magic-bundle-store*
         *fn-bpnf-conflict-frame-version*
         *fn-bpnf-conflict-kind*
         (fn-frame-fields-octets *fn-bpnf-conflict-fields*
                                 (fn-bpnf-conflict-values row))
         *fn-bpn-lifecycle-max-payload*)
        (equal (fn-bpnf-conflict-frame row)
               (fn-frame-seal
                *fn-frame-magic-bundle-store*
                *fn-bpnf-conflict-frame-version*
                *fn-bpnf-conflict-kind*
                (fn-frame-fields-octets *fn-bpnf-conflict-fields*
                                        (fn-bpnf-conflict-values row))))
        (equal (fn-bpnf-conflict-from-values
                (fn-bpnf-conflict-values row)) row))
   (equal (fn-bpnf-conflict-unframe (fn-bpnf-conflict-frame row))
          row))
  :rule-classes nil
  :hints
  (("Goal" :do-not-induct t
    :use ((:instance fn-bpnf-conflict-decode-of-seal
                     (payload (fn-frame-fields-octets
                               *fn-bpnf-conflict-fields*
                               (fn-bpnf-conflict-values row))))
          (:instance fn-frame-fields-parse-of-octets
                     (specs *fn-bpnf-conflict-fields*)
                     (values (fn-bpnf-conflict-values row)))
          (:instance fn-bpnf-conflict-seal-is-octets
                     (payload (fn-frame-fields-octets
                               *fn-bpnf-conflict-fields*
                               (fn-bpnf-conflict-values row)))))
    :in-theory
    (e/d (fn-bpnf-conflict-unframe fn-frame-inputp)
         (fn-bpnf-conflict-frame fn-bpnf-conflict-recordp
          fn-bpnf-conflict-values
          fn-bpnf-conflict-from-values fn-frame-decode
          fn-frame-fields-parse fn-frame-fields-octets)))))

; Round trip: every well-formed kind-14 record is exactly what its frame
; decodes to.
(defthm fn-bpnf-conflict-record-round-trip
  (implies (fn-bpnf-conflict-recordp row)
           (equal (fn-bpnf-conflict-unframe (fn-bpnf-conflict-frame row))
                  row))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bpnf-conflict-record-values-ok
                 fn-bpnf-conflict-record-frame-input
                 fn-bpnf-conflict-record-reconstructs
                 fn-bpnf-conflict-frame-is-seal
                 fn-bpnf-conflict-unframe-of-canonical-frame)
           :in-theory (disable fn-bpnf-conflict-recordp
                               fn-bpnf-conflict-values
                               fn-bpnf-conflict-from-values
                               fn-bpnf-conflict-frame
                               fn-bpnf-conflict-unframe
                               fn-frame-fields-octets))))

; A kind-14 frame is not a kind-6, -8/-9 or kind-5 frame: its decoder alone
; accepts it, so the ordered replay's first-match dispatch is unambiguous.
(defthm fn-bpnf-conflict-frame-has-kind-fourteen
  (implies (fn-bpnf-conflict-unframe octets)
           (equal (fn-frame-result-kind
                   (fn-frame-decode
                    octets
                    (fn-frame-trailer (fn-frame-protected-prefix octets))
                    *fn-bpn-lifecycle-max-payload*))
                  14))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnf-conflict-unframe)
                           (fn-frame-decode fn-bpnf-conflict-frame
                            fn-bpnf-conflict-from-values
                            fn-frame-fields-parse)))))

(verify-guards fn-bpnf-conflict-record)
(verify-guards fn-bpnf-conflict-recordp)
(verify-guards fn-bpnf-conflict-values)
(verify-guards fn-bpnf-conflict-frame)
(verify-guards fn-bpnf-conflict-from-values)
(verify-guards fn-bpnf-conflict-unframe)
(verify-guards fn-bpnf-conflict-of)
