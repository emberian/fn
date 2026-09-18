; Experimental BP application-data-unit codec for the laboratory workflow.
;
; This is not the D01 native article schema, a D09 signature container, or a
; BP security-block profile.  It only gives the current lab workflow a bounded,
; canonical wrapper for an exact legacy article and for its application receipt.
(in-package "ACL2")
(include-book "records-invariants")

(defconst *fn-bpa-magic* '(70 78 45 66 80 45 65 68 85)) ; "FN-BP-ADU"
(defconst *fn-bpa-version* 0)
(defconst *fn-bpa-request-kind* 0)
(defconst *fn-bpa-receipt-kind* 1)
(defconst *fn-bpa-field-count* 9)
(defconst *fn-bpa-max-metadata* 256)
(defconst *fn-bpa-max-octets* 65538)

; Total selectors preserve malformed-input behavior without a Lisp reader.
(defun fn-bpa-car (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (if (consp x) (car x) nil)))

(defun fn-bpa-cdr (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cdr x) :exec (if (consp x) (cdr x) nil)))

(verify-guards fn-bpa-car)
(verify-guards fn-bpa-cdr)

(defun fn-bpa-nth (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (not (and (integerp n) (< 0 n)))
      (fn-bpa-car x)
    (fn-bpa-nth (1- n) (fn-bpa-cdr x))))

; Request:
; (:request work-id subject source-eid destination-eid policy-id
;           origin-incarnation authorization-context terms-id article-octets)
(defun fn-bpa-request-work-id (x) (declare (xargs :guard t)) (fn-bpa-nth 1 x))
(defun fn-bpa-request-subject (x) (declare (xargs :guard t)) (fn-bpa-nth 2 x))
(defun fn-bpa-request-source-eid (x) (declare (xargs :guard t)) (fn-bpa-nth 3 x))
(defun fn-bpa-request-destination-eid (x) (declare (xargs :guard t)) (fn-bpa-nth 4 x))
(defun fn-bpa-request-policy-id (x) (declare (xargs :guard t)) (fn-bpa-nth 5 x))
(defun fn-bpa-request-incarnation (x) (declare (xargs :guard t)) (fn-bpa-nth 6 x))
(defun fn-bpa-request-auth-context (x) (declare (xargs :guard t)) (fn-bpa-nth 7 x))
(defun fn-bpa-request-terms-id (x) (declare (xargs :guard t)) (fn-bpa-nth 8 x))
(defun fn-bpa-request-article (x) (declare (xargs :guard t)) (fn-bpa-nth 9 x))

(defun fn-bpa-make-request (work-id subject source-eid destination-eid
                                    policy-id incarnation auth-context terms-id
                                    article)
  (declare (xargs :guard t))
  (list :request work-id subject source-eid destination-eid policy-id
        incarnation auth-context terms-id article))

; Receipt fields deliberately match fn-bp-make-receipt exactly:
; (:receipt receipt-id work-id subject issuer-eid peer-eid policy-id
;           incarnation authorization-context terms-id)
(defun fn-bpa-receipt-id (x) (declare (xargs :guard t)) (fn-bpa-nth 1 x))
(defun fn-bpa-receipt-work-id (x) (declare (xargs :guard t)) (fn-bpa-nth 2 x))
(defun fn-bpa-receipt-subject (x) (declare (xargs :guard t)) (fn-bpa-nth 3 x))
(defun fn-bpa-receipt-issuer (x) (declare (xargs :guard t)) (fn-bpa-nth 4 x))
(defun fn-bpa-receipt-peer-eid (x) (declare (xargs :guard t)) (fn-bpa-nth 5 x))
(defun fn-bpa-receipt-policy-id (x) (declare (xargs :guard t)) (fn-bpa-nth 6 x))
(defun fn-bpa-receipt-incarnation (x) (declare (xargs :guard t)) (fn-bpa-nth 7 x))
(defun fn-bpa-receipt-auth-context (x) (declare (xargs :guard t)) (fn-bpa-nth 8 x))
(defun fn-bpa-receipt-terms-id (x) (declare (xargs :guard t)) (fn-bpa-nth 9 x))

(defun fn-bpa-make-receipt (receipt-id work-id subject issuer peer-eid
                                       policy-id incarnation auth-context terms-id)
  (declare (xargs :guard t))
  (list :receipt receipt-id work-id subject issuer peer-eid policy-id
        incarnation auth-context terms-id))

(defun fn-bpa-metadatap (x)
  (declare (xargs :guard t))
  (and (fn-record-octet-stringp x)
       (consp (fn-record-string-octets x))
       (<= (len (fn-record-string-octets x)) *fn-bpa-max-metadata*)))

(defun fn-bpa-requestp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 10) (equal (fn-bpa-nth 0 x) :request)
       (equal x
              (fn-bpa-make-request
               (fn-bpa-request-work-id x) (fn-bpa-request-subject x)
               (fn-bpa-request-source-eid x)
               (fn-bpa-request-destination-eid x)
               (fn-bpa-request-policy-id x) (fn-bpa-request-incarnation x)
               (fn-bpa-request-auth-context x) (fn-bpa-request-terms-id x)
               (fn-bpa-request-article x)))
       (fn-bpa-metadatap (fn-bpa-request-work-id x))
       (fn-bpa-metadatap (fn-bpa-request-subject x))
       (fn-bpa-metadatap (fn-bpa-request-source-eid x))
       (fn-bpa-metadatap (fn-bpa-request-destination-eid x))
       (fn-bpa-metadatap (fn-bpa-request-policy-id x))
       (fn-bpa-metadatap (fn-bpa-request-incarnation x))
       (fn-bpa-metadatap (fn-bpa-request-auth-context x))
       (fn-bpa-metadatap (fn-bpa-request-terms-id x))
       (fn-record-payloadp (fn-bpa-request-article x))))

(defun fn-bpa-receiptp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 10) (equal (fn-bpa-nth 0 x) :receipt)
       (equal x
              (fn-bpa-make-receipt
               (fn-bpa-receipt-id x) (fn-bpa-receipt-work-id x)
               (fn-bpa-receipt-subject x) (fn-bpa-receipt-issuer x)
               (fn-bpa-receipt-peer-eid x) (fn-bpa-receipt-policy-id x)
               (fn-bpa-receipt-incarnation x)
               (fn-bpa-receipt-auth-context x)
               (fn-bpa-receipt-terms-id x)))
       (fn-bpa-metadatap (fn-bpa-receipt-id x))
       (fn-bpa-metadatap (fn-bpa-receipt-work-id x))
       (fn-bpa-metadatap (fn-bpa-receipt-subject x))
       (fn-bpa-metadatap (fn-bpa-receipt-issuer x))
       (fn-bpa-metadatap (fn-bpa-receipt-peer-eid x))
       (fn-bpa-metadatap (fn-bpa-receipt-policy-id x))
       (fn-bpa-metadatap (fn-bpa-receipt-incarnation x))
       (fn-bpa-metadatap (fn-bpa-receipt-auth-context x))
       (fn-bpa-metadatap (fn-bpa-receipt-terms-id x))))

(defun fn-bpa-messagep (x)
  (declare (xargs :guard t))
  (or (fn-bpa-requestp x) (fn-bpa-receiptp x)))

; ----------------------------------------------------------------------------
; Canonical encoding

(defun fn-bpa-encode-fields (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (append (fn-cbor-encode (cons :bytes (car fields)))
              (fn-bpa-encode-fields (cdr fields)))
    nil))

(defun fn-bpa-request-fields (x)
  (declare (xargs :guard t))
  (list (fn-record-string-octets (fn-bpa-request-work-id x))
        (fn-record-string-octets (fn-bpa-request-subject x))
        (fn-record-string-octets (fn-bpa-request-source-eid x))
        (fn-record-string-octets (fn-bpa-request-destination-eid x))
        (fn-record-string-octets (fn-bpa-request-policy-id x))
        (fn-record-string-octets (fn-bpa-request-incarnation x))
        (fn-record-string-octets (fn-bpa-request-auth-context x))
        (fn-record-string-octets (fn-bpa-request-terms-id x))
        (fn-bpa-request-article x)))

(defun fn-bpa-receipt-fields (x)
  (declare (xargs :guard t))
  (list (fn-record-string-octets (fn-bpa-receipt-id x))
        (fn-record-string-octets (fn-bpa-receipt-work-id x))
        (fn-record-string-octets (fn-bpa-receipt-subject x))
        (fn-record-string-octets (fn-bpa-receipt-issuer x))
        (fn-record-string-octets (fn-bpa-receipt-peer-eid x))
        (fn-record-string-octets (fn-bpa-receipt-policy-id x))
        (fn-record-string-octets (fn-bpa-receipt-incarnation x))
        (fn-record-string-octets (fn-bpa-receipt-auth-context x))
        (fn-record-string-octets (fn-bpa-receipt-terms-id x))))

(defun fn-bpa-encode (message)
  (declare (xargs :guard t))
  (if (not (fn-bpa-messagep message))
      nil
    (let ((kind (if (fn-bpa-requestp message)
                    *fn-bpa-request-kind* *fn-bpa-receipt-kind*))
          (fields (if (fn-bpa-requestp message)
                      (fn-bpa-request-fields message)
                    (fn-bpa-receipt-fields message))))
      (append (fn-cbor-encode (cons :bytes *fn-bpa-magic*))
              (fn-cbor-encode (cons :uint *fn-bpa-version*))
              (fn-cbor-encode (cons :uint kind))
              (fn-cbor-encode (cons :uint *fn-bpa-field-count*))
              (fn-bpa-encode-fields fields)))))

; ----------------------------------------------------------------------------
; Bounded streaming decode

(defun fn-bpa-read-fields (count octets)
  (declare (xargs :guard (and (natp count)
                              (fn-cbor-octet-listp octets))
                  :verify-guards nil :measure (nfix count)))
  (if (not (natp count))
      (fn-record-parse-error :count)
    (if (zp count)
        (fn-record-parse-ok nil octets)
      (let ((first (fn-record-read-bytes octets)))
        (if (not (fn-record-parse-okp first))
            first
          (let ((tail (fn-bpa-read-fields
                       (1- count) (fn-record-parse-rest first))))
            (if (not (fn-record-parse-okp tail))
                tail
              (fn-record-parse-ok
               (cons (fn-record-parse-value first)
                     (fn-record-parse-value tail))
               (fn-record-parse-rest tail)))))))))

(defun fn-bpa-request-from-fields (fields)
  (declare (xargs :guard t))
  (fn-bpa-make-request
   (fn-record-octets-string (fn-bpa-nth 0 fields))
   (fn-record-octets-string (fn-bpa-nth 1 fields))
   (fn-record-octets-string (fn-bpa-nth 2 fields))
   (fn-record-octets-string (fn-bpa-nth 3 fields))
   (fn-record-octets-string (fn-bpa-nth 4 fields))
   (fn-record-octets-string (fn-bpa-nth 5 fields))
   (fn-record-octets-string (fn-bpa-nth 6 fields))
   (fn-record-octets-string (fn-bpa-nth 7 fields))
   (fn-bpa-nth 8 fields)))

(defun fn-bpa-receipt-from-fields (fields)
  (declare (xargs :guard t))
  (fn-bpa-make-receipt
   (fn-record-octets-string (fn-bpa-nth 0 fields))
   (fn-record-octets-string (fn-bpa-nth 1 fields))
   (fn-record-octets-string (fn-bpa-nth 2 fields))
   (fn-record-octets-string (fn-bpa-nth 3 fields))
   (fn-record-octets-string (fn-bpa-nth 4 fields))
   (fn-record-octets-string (fn-bpa-nth 5 fields))
   (fn-record-octets-string (fn-bpa-nth 6 fields))
   (fn-record-octets-string (fn-bpa-nth 7 fields))
   (fn-record-octets-string (fn-bpa-nth 8 fields))))

(defun fn-bpa-decode-fields (kind octets)
  (declare (xargs :guard (and (natp kind)
                              (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (let ((count-result (fn-record-read-uint octets)))
    (if (not (fn-record-parse-okp count-result))
        count-result
      (if (not (equal (fn-record-parse-value count-result)
                      *fn-bpa-field-count*))
          (fn-record-parse-error :field-count)
        (let ((fields-result
               (fn-bpa-read-fields *fn-bpa-field-count*
                                   (fn-record-parse-rest count-result))))
          (if (not (fn-record-parse-okp fields-result))
              fields-result
            (if (not (null (fn-record-parse-rest fields-result)))
                (fn-record-parse-error :trailing)
              (let ((message
                     (if (equal kind *fn-bpa-request-kind*)
                         (fn-bpa-request-from-fields
                          (fn-record-parse-value fields-result))
                       (fn-bpa-receipt-from-fields
                        (fn-record-parse-value fields-result)))))
                (if (fn-bpa-messagep message)
                    (fn-record-parse-ok message nil)
                  (fn-record-parse-error :invalid))))))))))

(defun fn-bpa-decode-after-magic (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :verify-guards nil))
  (let ((version-result (fn-record-read-uint octets)))
    (if (not (fn-record-parse-okp version-result))
        version-result
      (if (not (equal (fn-record-parse-value version-result)
                      *fn-bpa-version*))
          (fn-record-parse-error :unknown-version)
        (let ((kind-result
               (fn-record-read-uint (fn-record-parse-rest version-result))))
          (if (not (fn-record-parse-okp kind-result))
              kind-result
            (let ((kind (fn-record-parse-value kind-result)))
              (if (not (or (equal kind *fn-bpa-request-kind*)
                           (equal kind *fn-bpa-receipt-kind*)))
                  (fn-record-parse-error :unknown-kind)
                (fn-bpa-decode-fields
                 kind (fn-record-parse-rest kind-result))))))))))

(defun fn-bpa-decode-candidate (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :verify-guards nil))
  (let ((magic-result (fn-record-read-bytes octets)))
    (if (not (fn-record-parse-okp magic-result))
        magic-result
      (if (not (equal (fn-record-parse-value magic-result) *fn-bpa-magic*))
          (fn-record-parse-error :magic)
        (fn-bpa-decode-after-magic (fn-record-parse-rest magic-result))))))

; The public decoder bounds the complete ADU before octet traversal.  The
; re-encode check is an executable exact-canonicality check over all fields.
(defun fn-bpa-decode-exact (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-at-mostp octets *fn-bpa-max-octets*))
      (fn-record-parse-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-record-parse-error :malformed)
      (let ((candidate (fn-bpa-decode-candidate octets)))
        (if (not (fn-record-parse-okp candidate))
            candidate
          (let ((message (fn-record-parse-value candidate)))
            (if (equal (fn-bpa-encode message) octets)
                (list :ok message)
              (fn-record-parse-error :noncanonical))))))))

(defun fn-bpa-result-okp (result)
  (declare (xargs :guard t))
  (and (consp result) (equal (fn-bpa-car result) :ok)))

(defun fn-bpa-result-message (result)
  (declare (xargs :guard t))
  (fn-bpa-car (fn-bpa-cdr result)))

; ----------------------------------------------------------------------------
; General codec properties

(defun fn-bpa-byte-field-listp (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (fn-record-payloadp (car fields))
           (fn-bpa-byte-field-listp (cdr fields)))
    (null fields)))

(defthm fn-bpa-encoded-fields-are-octets
  (fn-cbor-octet-listp (fn-bpa-encode-fields fields))
  :hints (("Goal" :induct (fn-bpa-encode-fields fields)
           :in-theory (disable fn-cbor-encode))))

(defthm fn-bpa-read-encoded-fields
  (implies
   (and (fn-bpa-byte-field-listp fields)
        (fn-cbor-octet-listp rest)
        (<= (+ (len (fn-bpa-encode-fields fields)) (len rest))
            *fn-cbor-max-input*))
   (equal (fn-bpa-read-fields
           (len fields) (append (fn-bpa-encode-fields fields) rest))
          (fn-record-parse-ok fields rest)))
  :hints (("Goal" :induct (fn-bpa-encode-fields fields)
           :in-theory (disable fn-record-read-bytes fn-cbor-encode))))

(defthm fn-bpa-read-magic-prefix
  (implies
   (and (fn-cbor-octet-listp rest)
        (<= (+ 10 (len rest)) *fn-cbor-max-input*))
   (equal (fn-record-read-bytes
           (list* 73 70 78 45 66 80 45 65 68 85 rest))
          (fn-record-parse-ok *fn-bpa-magic* rest)))
  :hints (("Goal"
           :use ((:instance fn-record-read-bytes-encoded
                            (xs *fn-bpa-magic*)))
           :in-theory (disable fn-record-read-bytes))))

(defthm fn-bpa-read-small-uint-prefix
  (implies
   (and (natp n) (< n 24)
        (fn-cbor-octet-listp rest)
        (<= (+ 1 (len rest)) *fn-cbor-max-input*))
   (equal (fn-record-read-uint (cons n rest))
          (fn-record-parse-ok n rest)))
  :hints (("Goal"
           :use ((:instance fn-record-read-uint-encoded))
           :in-theory (disable fn-record-read-uint))))

(defthm fn-bpa-request-fields-reconstruct
  (implies (fn-bpa-requestp request)
           (equal (fn-bpa-request-from-fields
                   (fn-bpa-request-fields request))
                  request)))

(defthm fn-bpa-receipt-fields-reconstruct
  (implies (fn-bpa-receiptp receipt)
           (equal (fn-bpa-receipt-from-fields
                   (fn-bpa-receipt-fields receipt))
                  receipt)))

(defthm fn-bpa-request-fields-domain
  (implies (fn-bpa-requestp request)
           (and (fn-bpa-byte-field-listp
                 (fn-bpa-request-fields request))
                (equal (len (fn-bpa-request-fields request))
                       *fn-bpa-field-count*))))

(defthm fn-bpa-receipt-fields-domain
  (implies (fn-bpa-receiptp receipt)
           (and (fn-bpa-byte-field-listp
                 (fn-bpa-receipt-fields receipt))
                (equal (len (fn-bpa-receipt-fields receipt))
                       *fn-bpa-field-count*))))

(defthm fn-bpa-request-receipt-exclusive
  (implies (fn-bpa-receiptp message)
           (not (fn-bpa-requestp message)))
  :hints (("Goal" :in-theory (enable fn-bpa-receiptp
                                      fn-bpa-requestp))))

(defthm fn-bpa-encoding-bound
  (implies (fn-bpa-messagep message)
           (<= (len (fn-bpa-encode message)) *fn-bpa-max-octets*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-bpa-read-request-fields-encoded
  (implies
   (and (fn-bpa-requestp request)
        (<= (+ 13 (len (fn-bpa-encode-fields
                        (fn-bpa-request-fields request))))
            *fn-bpa-max-octets*))
   (equal (fn-bpa-read-fields
           *fn-bpa-field-count*
           (fn-bpa-encode-fields (fn-bpa-request-fields request)))
          (fn-record-parse-ok (fn-bpa-request-fields request) nil)))
  :hints (("Goal"
           :use ((:instance fn-bpa-read-encoded-fields
                            (fields (fn-bpa-request-fields request))
                            (rest nil)))
           :in-theory (disable fn-bpa-read-fields
                               fn-bpa-encode-fields))))

(defthm fn-bpa-read-receipt-fields-encoded
  (implies
   (and (fn-bpa-receiptp receipt)
        (<= (+ 13 (len (fn-bpa-encode-fields
                        (fn-bpa-receipt-fields receipt))))
            *fn-bpa-max-octets*))
   (equal (fn-bpa-read-fields
           *fn-bpa-field-count*
           (fn-bpa-encode-fields (fn-bpa-receipt-fields receipt)))
          (fn-record-parse-ok (fn-bpa-receipt-fields receipt) nil)))
  :hints (("Goal"
           :use ((:instance fn-bpa-read-encoded-fields
                            (fields (fn-bpa-receipt-fields receipt))
                            (rest nil)))
           :in-theory (disable fn-bpa-read-fields
                               fn-bpa-encode-fields))))

(defthm fn-bpa-decode-request-fields-encoded
  (implies
   (and (fn-bpa-requestp request)
        (<= (+ 13 (len (fn-bpa-encode-fields
                        (fn-bpa-request-fields request))))
            *fn-bpa-max-octets*))
   (equal (fn-bpa-decode-fields
           *fn-bpa-request-kind*
           (cons *fn-bpa-field-count*
                 (fn-bpa-encode-fields (fn-bpa-request-fields request))))
          (fn-record-parse-ok request nil)))
  :hints (("Goal"
           :use ((:instance fn-bpa-read-request-fields-encoded)
                 (:instance fn-bpa-request-fields-reconstruct))
           :in-theory (disable fn-bpa-read-fields
                               fn-bpa-encode-fields
                               fn-bpa-requestp
                               fn-bpa-receiptp
                               fn-record-octets-string
                               fn-record-string-octets))))

(defthm fn-bpa-decode-receipt-fields-encoded
  (implies
   (and (fn-bpa-receiptp receipt)
        (<= (+ 13 (len (fn-bpa-encode-fields
                        (fn-bpa-receipt-fields receipt))))
            *fn-bpa-max-octets*))
   (equal (fn-bpa-decode-fields
           *fn-bpa-receipt-kind*
           (cons *fn-bpa-field-count*
                 (fn-bpa-encode-fields (fn-bpa-receipt-fields receipt))))
          (fn-record-parse-ok receipt nil)))
  :hints (("Goal"
           :use ((:instance fn-bpa-read-receipt-fields-encoded)
                 (:instance fn-bpa-receipt-fields-reconstruct))
           :in-theory (disable fn-bpa-read-fields
                               fn-bpa-encode-fields
                               fn-bpa-requestp
                               fn-bpa-receiptp
                               fn-record-octets-string
                               fn-record-string-octets))))

(defthm fn-bpa-request-round-trip
  (implies (fn-bpa-requestp request)
           (equal (fn-bpa-decode-exact (fn-bpa-encode request))
                  (list :ok request)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpa-encoding-bound (message request))
                 (:instance fn-bpa-decode-request-fields-encoded))
           :in-theory (disable fn-cbor-encode fn-cbor-decode
                               fn-record-read-uint fn-record-read-bytes
                               fn-bpa-decode-fields
                               fn-bpa-read-fields fn-bpa-encode-fields
                               fn-bpa-requestp fn-bpa-receiptp
                               fn-record-octets-string
                               fn-record-string-octets
                               fn-record-string-octets-aux))))

(defthm fn-bpa-receipt-round-trip
  (implies (fn-bpa-receiptp receipt)
           (equal (fn-bpa-decode-exact (fn-bpa-encode receipt))
                  (list :ok receipt)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpa-encoding-bound (message receipt))
                 (:instance fn-bpa-decode-receipt-fields-encoded)
                 (:instance fn-bpa-request-receipt-exclusive
                            (message receipt)))
           :in-theory (disable fn-cbor-encode fn-cbor-decode
                               fn-record-read-uint fn-record-read-bytes
                               fn-bpa-decode-fields
                               fn-bpa-read-fields fn-bpa-encode-fields
                               fn-bpa-requestp fn-bpa-receiptp
                               fn-record-octets-string
                               fn-record-string-octets
                               fn-record-string-octets-aux))))

(defthm fn-bpa-round-trip
  (implies (fn-bpa-messagep message)
           (equal (fn-bpa-decode-exact (fn-bpa-encode message))
                  (list :ok message)))
  :hints (("Goal"
           :use ((:instance fn-bpa-request-round-trip (request message))
                 (:instance fn-bpa-receipt-round-trip (receipt message)))
           :in-theory (disable fn-bpa-decode-exact fn-bpa-encode))))

; Every success is exact and canonical for this experimental profile.  This
; follows from the decoder's explicit whole-input re-encode check; it is not a
; cryptographic authenticity or freshness statement.
(defthm fn-bpa-success-is-canonical
  (implies (fn-bpa-result-okp (fn-bpa-decode-exact octets))
           (equal (fn-bpa-encode
                   (fn-bpa-result-message (fn-bpa-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpa-decode-exact
                 fn-bpa-result-okp
                 fn-bpa-result-message)
                (fn-bpa-decode-candidate
                 fn-bpa-encode
                 fn-cbor-at-mostp
                 fn-cbor-octet-listp)))))
