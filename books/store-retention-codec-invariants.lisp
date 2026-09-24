; Canonical FNST retention event representation for the called owner writer.
; A retention prepare produces this event, and fn-owner-pending-octets passes
; its fn-store-event-encode bytes to fnn-publish.  The round trip below is the
; missing input fact for a byte-store P-RECORD proof over that caller.
(in-package "ACL2")
(include-book "store-events")
(include-book "statement-seam")
(include-book "cbor-invariants")

(defun fn-srci-retention-items (event)
  (declare (xargs :guard t :verify-guards nil))
  (list (cons :bytes *fn-store-event-magic*)
        (cons :uint *fn-store-event-version*)
        (cons :uint (fn-store-event-kind-code (fn-store-event-kind event)))
        (cons :uint (fn-store-event-sequence event))
        (cons :uint (fn-store-event-txid event))
        (cons :uint (fn-store-event-generation event))
        (cons :bytes (fn-record-string-octets
                      (fn-store-event-obligation-id event)))
        (cons :bytes (fn-record-string-octets
                      (fn-store-event-subject event)))
        (cons :bytes (fn-record-string-octets
                      (fn-store-event-evidence event)))
        (cons :uint (fn-store-event-charge event))))

(local (defthm fn-srci-append-nil
         (implies (true-listp xs) (equal (append xs nil) xs))))

(defthm fn-srci-retention-encoding-is-items
  (implies (fn-store-retention-event-p event)
           (equal (fn-store-retention-event-encode event)
                  (fn-stmt-encode-items (fn-srci-retention-items event))))
  :hints (("Goal" :in-theory
           (e/d (fn-store-retention-event-encode fn-srci-retention-items
                 fn-stmt-encode-items-when-consp
                 fn-cbor-encoding-is-true-list)
                (fn-cbor-encode fn-record-string-octets
                 fn-store-retention-event-p fn-store-event-kind
                 fn-store-event-sequence fn-store-event-txid
                 fn-store-event-generation fn-store-event-charge
                 fn-store-event-obligation-id fn-store-event-subject
                 fn-store-event-evidence)))))

(local (defthm fn-srci-retention-is-not-article
         (implies (fn-store-retention-event-p event)
                  (not (fn-record-p event)))
         :hints (("Goal" :in-theory
                  (enable fn-store-retention-event-p fn-record-p
                          fn-record-shapep)))))

(defthm fn-srci-retention-items-well-formed
  (implies (fn-store-retention-event-p event)
           (fn-stmt-item-listp (fn-srci-retention-items event)))
  :hints (("Goal" :in-theory
           (e/d (fn-srci-retention-items fn-stmt-item-listp
                 fn-cbor-valuep fn-cbor-valuep-bounded
                 fn-store-retention-event-p
                 fn-store-event-kind fn-store-event-sequence
                 fn-store-event-txid fn-store-event-generation
                 fn-store-event-charge fn-store-event-obligation-id
                 fn-store-event-subject fn-store-event-evidence
                 fn-record-metadata-bytes-p fn-record-octet-stringp
                 fn-record-nonempty-at-mostp)
                (fn-record-string-octets fn-cbor-octet-listp)))))

(defthm fn-srci-retention-encoding-is-octets
  (implies (fn-store-retention-event-p event)
           (fn-cbor-octet-listp (fn-store-retention-event-encode event)))
  :hints (("Goal"
           :use (fn-srci-retention-encoding-is-items
                 (:instance fn-stmt-encode-items-is-octet-list
                  (items (fn-srci-retention-items event))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-srci-retention-encoding-bounded
  (implies (fn-store-retention-event-p event)
           (<= (len (fn-store-retention-event-encode event))
               *fn-store-event-max-octets*))
  :hints (("Goal" :in-theory
           (e/d (fn-store-retention-event-encode
                 fn-store-retention-event-p fn-record-metadata-bytes-p
                 fn-record-nonempty-at-mostp fn-store-event-kind
                 fn-store-event-sequence fn-store-event-txid
                 fn-store-event-generation fn-store-event-obligation-id
                 fn-store-event-subject fn-store-event-evidence
                 fn-store-event-charge fn-record-length-append
                 fn-record-cbor-uint-encoding-bound
                 fn-record-cbor-byte-encoding-bound)
                (fn-cbor-encode fn-record-string-octets)))))

(local
 (defthm fn-srci-chars-octets-chars
   (implies (character-listp chars)
            (equal (fn-record-octets-chars
                    (fn-record-string-octets-aux chars))
                   chars))))

(local
 (defthm fn-srci-string-round-trip
   (implies (fn-record-octet-stringp text)
            (equal (fn-record-octets-string
                    (fn-record-string-octets text))
                   text))))

(local
 (defthm fn-srci-retention-values-reconstruct
   (implies (fn-store-retention-event-p event)
            (equal (fn-store-retention-event-from-values
                    (fn-srci-retention-items event))
                   event))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-store-retention-event-from-values
                             fn-srci-retention-items
                             fn-store-retention-event-p
                             fn-store-retention-event-make
                             fn-store-event-item-tagp
                             fn-store-event-item-value
                             fn-store-event-kind-code
                             fn-store-event-kind
                             fn-store-event-sequence
                             fn-store-event-txid
                             fn-store-event-generation
                             fn-store-event-obligation-id
                             fn-store-event-subject
                             fn-store-event-evidence
                             fn-store-event-charge
                             fn-record-metadata-bytes-p
                             fn-record-octet-stringp)
                            (fn-record-string-octets
                             fn-record-octets-string))))))

(defthm fn-srci-retention-codec-round-trip
  (implies (fn-store-retention-event-p event)
           (equal (fn-store-retention-event-decode-exact
                   (fn-store-retention-event-encode event))
                  (list :ok event)))
  :hints (("Goal" :do-not-induct t
           :use (fn-srci-retention-encoding-is-items
                 fn-srci-retention-items-well-formed
                 fn-srci-retention-encoding-is-octets
                 fn-srci-retention-encoding-bounded
                 fn-srci-retention-values-reconstruct
                 (:instance fn-stmt-decode-items-of-encode-items
                  (items (fn-srci-retention-items event)) (fuel 10)))
           :in-theory (e/d (fn-store-retention-event-decode-exact
                            fn-cbor-at-mostp
                            fn-stmt-okp fn-stmt-value)
                           (fn-stmt-decode-items
                            fn-store-retention-event-from-values
                            fn-store-retention-event-encode)))))
