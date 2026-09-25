;; fn: the schema-0/1 transaction-record decoder as it was before packet P6,
;; frozen, and the translation keystone (D27, design 2026-09-25-bounds 2.3,
;; packet P6).
;;
;; Packet P6 widened the record's integer fields to u64 and gave a record
;; with a field above 2^32 - 1 the schema octet 2 (records-shape
;; `fn-record-schema-octet').  A store written before it holds only schema-0
;; and schema-1 records.  The translation of such a store into the new schema
;; is the identity on its bytes: every record the old decoder accepted is
;; decoded by the new one to the same record
;; (`fn-record-v1-bytes-decode-identically'), and the new encoder writes that
;; record back to exactly the same octets
;; (`fn-record-v1-bytes-are-their-translation').  So an open of an old store
;; by the new image reads the records the old image read, and nothing is
;; rewritten at open.  The host reaches the decoder through
;; `fn-store-event-decode-exact' (host/store-host.lisp `fn-store-decode-records'),
;; whose record kind is the seam's `fn-record-decode-exact', attached to
;; `fn-record-decode-exact-impl' by books/records-attach.lisp.
;;
;; The frozen definitions below are the text of books/records.lisp at dev
;; e366c633 with the four names prefixed `fn-record-v1-' and their guards
;; dropped (they are proof subjects only; no host line calls them).
(in-package "ACL2")
(include-book "records-canonicality")

; Records and parse results stay opaque here; the two reader lemmas open
; exactly the readers they compare.

(defun fn-record-v1-read-uint (octets)
  (declare (xargs :verify-guards nil))
  (let ((decoded (fn-record-item-decode octets)))
    (if (not (fn-cbor-result-okp decoded))
        (fn-record-parse-error (car (cdr decoded)))
      (let ((value (fn-cbor-result-value decoded)))
        (if (and (consp value) (equal (car value) :uint))
            (fn-record-parse-ok (cdr value) (fn-cbor-result-rest decoded))
          (fn-record-parse-error :field-type))))))

(defun fn-record-v1-decode-tail (schema sequence txid generation msgid payload octets)
  (declare (xargs :verify-guards nil))
  (let ((count-result (fn-record-v1-read-uint octets)))
    (if (not (fn-record-parse-okp count-result))
        (fn-record-parse-error :group-count)
      (let ((count (fn-record-parse-value count-result)))
        (if (< *fn-record-max-groups* count)
            (fn-record-parse-error :groups-limit)
          (let ((groups-result
                 (fn-record-parse-groups count
                                         (fn-record-parse-rest count-result))))
            (if (not (fn-record-parse-okp groups-result))
                groups-result
              (let ((id-result
                     (fn-record-read-bytes (fn-record-parse-rest groups-result))))
                (if (not (fn-record-parse-okp id-result))
                    id-result
                  (let ((subject-result
                         (fn-record-read-bytes (fn-record-parse-rest id-result))))
                    (if (not (fn-record-parse-okp subject-result))
                        subject-result
                      (let ((evidence-result
                             (fn-record-read-bytes
                              (fn-record-parse-rest subject-result))))
                        (if (not (fn-record-parse-okp evidence-result))
                            evidence-result
                          (let ((charge-result
                                 (fn-record-v1-read-uint
                                  (fn-record-parse-rest evidence-result))))
                            (if (not (fn-record-parse-okp charge-result))
                                charge-result
                              (let* ((stamp-result
                                      (if (equal schema 0)
                                          (fn-record-parse-ok :legacy
                                                              (fn-record-parse-rest charge-result))
                                        (fn-record-v1-read-uint
                                         (fn-record-parse-rest charge-result))))
                                     (id (fn-record-octets-string
                                          (fn-record-parse-value id-result)))
                                     (subject (fn-record-octets-string
                                               (fn-record-parse-value subject-result)))
                                     (evidence (fn-record-octets-string
                                                (fn-record-parse-value evidence-result)))
                                     (record
                                      (fn-record-make
                                       sequence txid generation msgid payload
                                       (fn-record-parse-value groups-result)
                                       id subject evidence
                                       (fn-record-parse-value charge-result)
                                       (fn-record-parse-value stamp-result))))
                                (if (not (fn-record-parse-okp stamp-result))
                                    stamp-result
                                  (if (not (null (fn-record-parse-rest stamp-result)))
                                    (fn-record-parse-error :trailing)
                                  (if (fn-record-p record)
                                      (fn-record-parse-ok record nil)
                                    (fn-record-parse-error :invalid))))))))))))))))))))

(defun fn-record-v1-decode-after-header (schema octets)
  (declare (xargs :verify-guards nil))
  (let ((sequence-result (fn-record-v1-read-uint octets)))
    (if (not (fn-record-parse-okp sequence-result))
        sequence-result
      (let ((txid-result
             (fn-record-v1-read-uint (fn-record-parse-rest sequence-result))))
        (if (not (fn-record-parse-okp txid-result))
            txid-result
          (let ((generation-result
                 (fn-record-v1-read-uint (fn-record-parse-rest txid-result))))
            (if (not (fn-record-parse-okp generation-result))
                generation-result
              (let ((msgid-result
                     (fn-record-read-bytes
                      (fn-record-parse-rest generation-result))))
                (if (not (fn-record-parse-okp msgid-result))
                    msgid-result
                  (let ((msgid (fn-record-octets-string
                                (fn-record-parse-value msgid-result))))
                    (if (not (fn-record-msgidp msgid))
                        (fn-record-parse-error :msgid)
                      (let ((payload-result
                             (fn-record-read-bytes
                              (fn-record-parse-rest msgid-result))))
                        (if (not (fn-record-parse-okp payload-result))
                            payload-result
                          (let ((payload (fn-record-parse-value payload-result)))
                            (if (not (fn-record-payloadp payload))
                                (fn-record-parse-error :payload)
                              (fn-record-v1-decode-tail
                               schema
                               (fn-record-parse-value sequence-result)
                               (fn-record-parse-value txid-result)
                               (fn-record-parse-value generation-result)
                               msgid payload
                               (fn-record-parse-rest payload-result)))))))))))))))))

(defun fn-record-v1-decode-exact (octets)
  (if (not (fn-cbor-at-mostp octets *fn-record-max-octets*))
      (fn-record-parse-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-record-parse-error :malformed)
      (let ((magic-result (fn-record-read-bytes octets)))
        (if (not (fn-record-parse-okp magic-result))
            magic-result
          (if (not (equal (fn-record-parse-value magic-result)
                          *fn-record-magic*))
              (fn-record-parse-error :magic)
            (let ((version-result
                   (fn-record-v1-read-uint (fn-record-parse-rest magic-result))))
              (if (not (fn-record-parse-okp version-result))
                  version-result
                (if (not (member-equal (fn-record-parse-value version-result)
                                       '(0 1)))
                    (fn-record-parse-error :unknown-version)
                  (let ((parsed
                         (fn-record-v1-decode-after-header
                          (fn-record-parse-value version-result)
                          (fn-record-parse-rest version-result))))
                    (if (fn-record-parse-okp parsed)
                        (fn-record-result-ok (fn-record-parse-value parsed))
                      parsed)))))))))))


; -----------------------------------------------------------------------------
; Field by field: wherever the frozen uint reader accepts, the wide one
; returns the same result, and the value fits u32.

(defthm fn-record-v1-read-uint-agrees
  (implies (fn-record-parse-okp (fn-record-v1-read-uint x))
           (equal (fn-record-read-uint x) (fn-record-v1-read-uint x)))
  :hints (("Goal" :cases ((fn-cbor-octet-listp x))
           :use ((:instance fn-cbor-decode-prechecked-wide-extends-narrow
                  (octets x) (budget *fn-record-max-octets*)))
           :in-theory (e/d (fn-record-read-uint fn-record-v1-read-uint
                            fn-record-uint-decode fn-record-item-decode
                            fn-record-parse-okp fn-record-parse-ok
                            fn-record-parse-error)
                           (fn-cbor-decode-prechecked-wide-extends-narrow
                            fn-cbor-decode-prechecked-wide
                            fn-cbor-decode-prechecked)))))

(defthm fn-record-v1-read-uint-is-u32
  (implies (fn-record-parse-okp (fn-record-v1-read-uint x))
           (and (natp (fn-record-parse-value (fn-record-v1-read-uint x)))
                (<= (fn-record-parse-value (fn-record-v1-read-uint x))
                    *fn-cbor-max-uint*)))
  :hints (("Goal" :use ((:instance fn-record-item-decode-success-domain (octets x)))
           :in-theory (e/d (fn-record-v1-read-uint fn-record-uint32p
                            fn-cbor-valuep-bounded fn-record-parse-okp
                            fn-record-parse-ok fn-record-parse-error
                            fn-record-parse-value)
                           (fn-record-item-decode-success-domain
                            fn-record-item-decode)))))

(defthm fn-record-v1-read-uint-is-not-legacy
  (implies (fn-record-parse-okp (fn-record-v1-read-uint x))
           (not (equal (fn-record-parse-value (fn-record-v1-read-uint x)) :legacy)))
  :hints (("Goal" :use fn-record-v1-read-uint-is-u32
           :in-theory (disable fn-record-v1-read-uint-is-u32 fn-record-v1-read-uint))))

(local (in-theory (disable fn-record-read-uint fn-record-v1-read-uint
                           fn-record-read-bytes fn-record-parse-groups
                           fn-record-octets-string fn-record-p
                           fn-record-msgidp fn-record-payloadp)))

(defthm fn-record-v1-decode-tail-agrees
  (implies (fn-record-parse-okp
            (fn-record-v1-decode-tail schema sequence txid generation msgid payload x))
           (equal (fn-record-decode-tail schema sequence txid generation msgid payload x)
                  (fn-record-v1-decode-tail schema sequence txid generation msgid payload x)))
  :hints (("Goal" :in-theory (enable fn-record-decode-tail fn-record-v1-decode-tail))))

(defthm fn-record-v1-decode-tail-schema
  (implies (and (member-equal schema '(0 1))
                (fn-record-uint32p sequence)
                (fn-record-uint32p txid)
                (fn-record-uint32p generation)
                (fn-record-parse-okp
                 (fn-record-v1-decode-tail schema sequence txid generation msgid payload x)))
           (equal (fn-record-schema-octet
                   (fn-record-parse-value
                    (fn-record-v1-decode-tail schema sequence txid generation msgid
                                              payload x)))
                  schema))
  :hints (("Goal" :in-theory (enable fn-record-v1-decode-tail fn-record-schema-octet
                                     fn-record-widep fn-record-uint32p))))

(defthm fn-record-v1-decode-after-header-agrees
  (implies (fn-record-parse-okp (fn-record-v1-decode-after-header schema x))
           (equal (fn-record-decode-after-header schema x)
                  (fn-record-v1-decode-after-header schema x)))
  :hints (("Goal" :in-theory (e/d (fn-record-decode-after-header
                                   fn-record-v1-decode-after-header)
                                  (fn-record-decode-tail fn-record-v1-decode-tail)))))

(defthm fn-record-v1-decode-after-header-schema
  (implies (and (member-equal schema '(0 1))
                (fn-record-parse-okp (fn-record-v1-decode-after-header schema x)))
           (equal (fn-record-schema-octet
                   (fn-record-parse-value (fn-record-v1-decode-after-header schema x)))
                  schema))
  :hints (("Goal" :in-theory (e/d (fn-record-v1-decode-after-header
                                   fn-record-uint32p)
                                  (fn-record-decode-tail fn-record-v1-decode-tail
                                   fn-record-schema-octet)))))

; -----------------------------------------------------------------------------
; The translation keystone.

(defthm fn-record-v1-bytes-decode-identically
  (implies (fn-record-result-okp (fn-record-v1-decode-exact octets))
           (equal (fn-record-decode-exact-impl octets)
                  (fn-record-v1-decode-exact octets)))
  :hints (("Goal" :in-theory (e/d (fn-record-decode-exact-impl fn-record-v1-decode-exact
                                   fn-record-result-okp-is-parse-okp
                                   fn-record-parse-error-is-failure)
                                  (fn-record-decode-after-header
                                   fn-record-v1-decode-after-header
                                   fn-record-schema-octet)))))

(defthm fn-record-v1-bytes-are-their-translation
  (implies (fn-record-result-okp (fn-record-v1-decode-exact octets))
           (equal (fn-record-encode-impl
                   (fn-record-result-record (fn-record-v1-decode-exact octets)))
                  octets))
  :hints (("Goal" :use (fn-record-v1-bytes-decode-identically
                        fn-record-impl-accepted-input-is-canonical)
           :in-theory (disable fn-record-v1-bytes-decode-identically
                               fn-record-impl-accepted-input-is-canonical
                               fn-record-decode-exact-impl
                               fn-record-v1-decode-exact
                               fn-record-encode-impl))))
