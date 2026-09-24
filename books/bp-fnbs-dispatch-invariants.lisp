; Canonical version-2 received-dispatch frame, kept distinct from the
; version-1 clock-domain marker with the same numeric kind.
(in-package "ACL2")
(include-book "bp-fnbs-dispatch-codec")
(include-book "frame-trailer")
(include-book "frame-invariants")

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
