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

(defthm fn-srci-retention-is-not-article
         (implies (fn-store-retention-event-p event)
                  (not (fn-record-p event)))
         :hints (("Goal" :in-theory
                  (enable fn-store-retention-event-p fn-record-p
                          fn-record-shapep))))

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

(defthm fn-srci-retention-encoding-at-most
  (implies (fn-store-retention-event-p event)
           (fn-cbor-at-mostp (fn-store-retention-event-encode event)
                             *fn-store-event-max-octets*))
  :hints (("Goal" :use (fn-srci-retention-encoding-bounded
                         fn-srci-retention-encoding-is-octets
                         (:instance fn-cbor-octet-listp-implies-true-listp
                          (xs (fn-store-retention-event-encode event)))
                         (:instance fn-cbor-at-mostp-from-length
                          (xs (fn-store-retention-event-encode event))
                          (bound *fn-store-event-max-octets*)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(natp)))))

(defthm fn-srci-retention-items-count
  (equal (len (fn-srci-retention-items event)) 10)
  :hints (("Goal" :in-theory (enable fn-srci-retention-items))))

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
                   text))
   :hints (("Goal" :in-theory
            (enable fn-record-octet-stringp fn-record-string-octets
                    fn-record-octets-string)))))

(local
 (defthm fn-srci-event-nth-is-nth
   (equal (fn-store-event-nth n x) (nth n x))
   :hints (("Goal" :induct (fn-store-event-nth n x)
            :in-theory (enable fn-store-event-nth nth)))))

(local
 (defthm fn-srci-nine-nths-are-take
   (equal (list (nth 0 x) (nth 1 x) (nth 2 x)
                (nth 3 x) (nth 4 x) (nth 5 x)
                (nth 6 x) (nth 7 x) (nth 8 x))
          (take 9 x))
   :hints (("Goal" :do-not-induct t
            :expand ((take 9 x)
                     (take 8 (cdr x))
                     (take 7 (cdr (cdr x)))
                     (take 6 (cdr (cdr (cdr x))))
                     (take 5 (cdr (cdr (cdr (cdr x)))))
                     (take 4 (cdr (cdr (cdr (cdr (cdr x))))))
                     (take 3 (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
                     (take 2 (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))
                     (take 1 (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))
                     (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)
                     (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x))
            :in-theory (enable take nth)))))

(local
 (defthm fn-srci-nine-fields-are-take
   (equal (list (fn-store-event-nth 0 x)
                (fn-store-event-nth 1 x)
                (fn-store-event-nth 2 x)
                (fn-store-event-nth 3 x)
                (fn-store-event-nth 4 x)
                (fn-store-event-nth 5 x)
                (fn-store-event-nth 6 x)
                (fn-store-event-nth 7 x)
                (fn-store-event-nth 8 x))
          (take 9 x))
   :hints (("Goal" :use fn-srci-nine-nths-are-take
            :in-theory (e/d (fn-srci-event-nth-is-nth)
                            (take nth fn-store-event-nth))))))

(local
 (defthm fn-srci-nine-fields-reconstruct
   (implies (and (true-listp x) (equal (len x) 9))
            (equal (list (fn-store-event-nth 0 x)
                         (fn-store-event-nth 1 x)
                         (fn-store-event-nth 2 x)
                         (fn-store-event-nth 3 x)
                         (fn-store-event-nth 4 x)
                         (fn-store-event-nth 5 x)
                         (fn-store-event-nth 6 x)
                         (fn-store-event-nth 7 x)
                         (fn-store-event-nth 8 x))
                   x))
   :hints (("Goal" :use (fn-srci-nine-fields-are-take
                           (:instance fn-cbor-take-whole-list (xs x)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-srci-retention-fields-reconstruct
   (implies (and (true-listp x) (equal (len x) 9)
                 (equal (nth 0 x) :retention))
            (equal (list :retention (nth 1 x) (nth 2 x)
                         (nth 3 x) (nth 4 x) (nth 5 x)
                         (nth 6 x) (nth 7 x) (nth 8 x))
                   x))
   :hints (("Goal" :use (fn-srci-nine-nths-are-take
                           (:instance fn-cbor-take-whole-list (xs x)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-srci-retention-values-reconstruct
   (implies (fn-store-retention-event-p event)
            (equal (fn-store-retention-event-from-values
                    (fn-srci-retention-items event))
                   event))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-srci-nine-fields-reconstruct (x event))
                  (:instance fn-srci-retention-fields-reconstruct (x event)))
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
                             fn-store-event-nth
                             fn-record-metadata-bytes-p
                             fn-record-octet-stringp)
                            (fn-record-string-octets
                             fn-record-octets-string
                             fn-srci-nine-nths-are-take
                             fn-srci-nine-fields-are-take
                             fn-srci-nine-fields-reconstruct
                             fn-srci-retention-fields-reconstruct))))))

(local
 (defthm fn-srci-retention-event-consp
   (implies (fn-store-retention-event-p event) (consp event))
   :hints (("Goal" :in-theory (enable fn-store-retention-event-p)))))

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
                 fn-srci-retention-encoding-at-most
                 fn-srci-retention-items-count
                 fn-srci-retention-values-reconstruct
                 fn-srci-retention-event-consp
                 (:instance fn-stmt-decode-items-of-encode-items
                  (items (fn-srci-retention-items event)) (fuel 10)))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-store-retention-event-decode-exact
              fn-stmt-ok fn-stmt-okp fn-stmt-value
              car-cons cdr-cons natp
              fn-srci-retention-items-count)))))

(local
 (defthm fn-srci-retention-encoding-has-disjoint-magic
   (implies (fn-store-retention-event-p event)
            (equal (take 5 (fn-store-retention-event-encode event))
                   '(68 102 110 45 101)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-store-retention-event-encode)
                            (fn-store-retention-event-p
                             fn-store-event-kind
                             fn-store-event-sequence
                             fn-store-event-txid
                             fn-store-event-generation
                             fn-store-event-obligation-id
                             fn-store-event-subject
                             fn-store-event-evidence
                             fn-store-event-charge))))))

(local
 (defthm fn-srci-retention-encoding-is-not-legacy-record
   (implies (fn-store-retention-event-p event)
            (not (fn-record-result-okp
                  (fn-record-decode-exact
                   (fn-store-retention-event-encode event)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-record-accepted-input-magic
                   (octets (fn-store-retention-event-encode event)))
                  fn-srci-retention-encoding-has-disjoint-magic)
            :in-theory (theory 'minimal-theory)))))

(defthm fn-srci-store-retention-event-round-trip
  (implies (fn-store-retention-event-p event)
           (equal (fn-store-event-decode-exact
                   (fn-store-event-encode event))
                  (list :ok event)))
  :hints (("Goal" :do-not-induct t
           :use (fn-srci-retention-is-not-article
                 fn-srci-retention-codec-round-trip
                 fn-srci-retention-encoding-is-not-legacy-record)
           :in-theory (e/d (fn-store-event-decode-exact
                            fn-store-event-encode
                            fn-record-result-okp)
                           (fn-store-retention-event-decode-exact
                            fn-record-p
                            fn-store-retention-event-p)))))
