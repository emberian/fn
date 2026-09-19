; Codec and signing invariants for fn statements (books/statement.lisp).
;
; Keystones:
;   fn-stmt-decode-items-of-encode-items / fn-stmt-encode-items-of-decode-items
;     the generic item-sequence codec is a round trip and every accepted input
;     re-encodes to itself (hypothesis-free canonicality);
;   fn-stmt-header-round-trip / fn-stmt-header-accepted-input-is-canonical
;   fn-stmt-round-trip / fn-stmt-accepted-input-is-canonical
;   fn-stmt-receipt-round-trip / fn-stmt-receipt-accepted-input-is-canonical
;     the same two directions lifted to headers, statements and receipts;
;   fn-stmt-sign-is-verified
;     a statement signed with seed sk verifies under (fn-sig-public-key sk),
;     the only use of the seam's correctness constraint;
;   fn-stmt-receipt-bytes-determine-term
;     equal receipt payload bytes carry equal policy terms.
; Nothing here relates two DIFFERENT byte strings with equal digests; that is
; A-CRYPTO and stays outside the logic.

(in-package "ACL2")
(include-book "statement")

; -----------------------------------------------------------------------------
; Result algebra

(defthm fn-stmt-okp-of-ok
  (fn-stmt-okp (fn-stmt-ok v)))
(defthm fn-stmt-value-of-ok
  (equal (fn-stmt-value (fn-stmt-ok v)) v))
(defthm fn-stmt-okp-of-ok2
  (fn-stmt-okp (fn-stmt-ok2 v r)))
(defthm fn-stmt-value-of-ok2
  (equal (fn-stmt-value (fn-stmt-ok2 v r)) v))
(defthm fn-stmt-rest-of-ok2
  (equal (fn-stmt-rest (fn-stmt-ok2 v r)) r))
(defthm fn-stmt-error-is-not-ok
  (not (fn-stmt-okp (fn-stmt-error c))))
(defthm fn-stmt-ok-is-not-error-shaped
  (and (not (equal (fn-stmt-ok v) (fn-stmt-error c)))
       (not (equal (fn-stmt-ok2 v r) (fn-stmt-error c)))))

(defthm fn-stmt-append-nil
  (implies (true-listp x)
           (equal (append x nil) x)))

(defthm fn-stmt-bytes-item-reconstruct
  (implies (fn-stmt-bytes-item-p x)
           (equal (cons :bytes (cdr x)) x)))

(defthm fn-stmt-uint-item-reconstruct
  (implies (fn-stmt-uint-item-p x)
           (equal (cons :uint (cdr x)) x)))

; -----------------------------------------------------------------------------
; The item-sequence codec

(defthm fn-stmt-encode-value-consp
  (implies (fn-cbor-valuep v)
           (consp (fn-cbor-encode v)))
  :hints (("Goal" :in-theory (enable fn-cbor-encode fn-cbor-encode-argument))))

(defthm fn-stmt-encode-uint-item-consp
  (implies (and (consp v) (equal (car v) :uint)
                (natp (cdr v)) (<= (cdr v) *fn-cbor-max-uint*))
           (consp (fn-cbor-encode v)))
  :hints (("Goal" :use fn-stmt-encode-value-consp
           :in-theory (disable fn-stmt-encode-value-consp fn-cbor-encode))))

(defthm fn-stmt-encode-bytes-item-consp
  (implies (and (consp v) (equal (car v) :bytes)
                (fn-cbor-octet-listp (cdr v))
                (<= (len (cdr v)) *fn-cbor-max-bytes*))
           (consp (fn-cbor-encode v)))
  :hints (("Goal" :use fn-stmt-encode-value-consp
           :in-theory (disable fn-stmt-encode-value-consp fn-cbor-encode))))

(defthm fn-stmt-consp-of-append
  (implies (consp a)
           (consp (append a b))))

(defthm fn-stmt-cbor-stream-round-trip
  (implies (and (fn-cbor-valuep v)
                (fn-cbor-octet-listp rest)
                (<= (+ (len (fn-cbor-encode v)) (len rest)) *fn-cbor-max-input*))
           (equal (fn-cbor-decode (append (fn-cbor-encode v) rest))
                  (fn-cbor-ok v rest)))
  :hints (("Goal"
           :use ((:instance fn-record-cbor-stream-uint-round-trip (n (cdr v)))
                 (:instance fn-record-cbor-stream-bytes-round-trip (xs (cdr v))))
           :in-theory (e/d (fn-record-uint32p)
                           (fn-cbor-decode fn-cbor-encode
                            fn-record-cbor-stream-uint-round-trip
                            fn-record-cbor-stream-bytes-round-trip)))))

(defun fn-stmt-items-fuel-induct (fuel items)
  (if (consp items)
      (fn-stmt-items-fuel-induct (1- fuel) (cdr items))
    (list fuel items)))

(defthm fn-stmt-encode-items-of-append
  (equal (fn-stmt-encode-items (append a b))
         (append (fn-stmt-encode-items a) (fn-stmt-encode-items b)))
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-stmt-decode-items-of-encode-items
  (implies (and (fn-stmt-item-listp items)
                (natp fuel)
                (<= (len items) fuel)
                (<= (len (fn-stmt-encode-items items)) *fn-cbor-max-input*))
           (equal (fn-stmt-decode-items fuel (fn-stmt-encode-items items))
                  (fn-stmt-ok items)))
  :hints (("Goal" :induct (fn-stmt-items-fuel-induct fuel items)
           :in-theory (disable fn-cbor-decode fn-cbor-encode))))

(defthm fn-stmt-encode-items-of-decode-items
  (implies (fn-stmt-okp (fn-stmt-decode-items fuel octets))
           (equal (fn-stmt-encode-items
                   (fn-stmt-value (fn-stmt-decode-items fuel octets)))
                  octets))
  :hints (("Goal" :induct (fn-stmt-decode-items fuel octets)
           :in-theory (disable fn-cbor-decode fn-cbor-encode
                               fn-cbor-result-okp fn-cbor-result-value
                               fn-cbor-result-rest
                               fn-stmt-okp fn-stmt-value fn-stmt-rest
                               fn-stmt-ok fn-stmt-ok2 fn-stmt-error))))

(defthm fn-stmt-decode-ok-implies-octets
  (implies (fn-cbor-result-okp (fn-cbor-decode octets))
           (fn-cbor-octet-listp octets))
  :hints (("Goal" :in-theory (enable fn-cbor-decode))))

(defthm fn-stmt-decode-items-value-is-item-list
  (implies (fn-stmt-okp (fn-stmt-decode-items fuel octets))
           (fn-stmt-item-listp
            (fn-stmt-value (fn-stmt-decode-items fuel octets))))
  :hints (("Goal" :induct (fn-stmt-decode-items fuel octets)
           :in-theory (disable fn-cbor-decode fn-cbor-encode
                               fn-cbor-result-okp fn-cbor-result-value
                               fn-cbor-result-rest
                               fn-stmt-okp fn-stmt-value fn-stmt-rest))))

; -----------------------------------------------------------------------------
; Predecessor lists

(defthm fn-stmt-take-id-items-of-id-items
  (implies (fn-stmt-id-listp ids)
           (equal (fn-stmt-take-id-items (len ids)
                                         (append (fn-stmt-id-items ids) rest))
                  (fn-stmt-ok2 ids rest)))
  :hints (("Goal" :induct (fn-stmt-id-items ids))))

(defthm fn-stmt-take-id-items-reconstruct
  (implies (fn-stmt-okp (fn-stmt-take-id-items n items))
           (and (equal (append (fn-stmt-id-items
                                (fn-stmt-value (fn-stmt-take-id-items n items)))
                               (fn-stmt-rest (fn-stmt-take-id-items n items)))
                       items)
                (equal (len (fn-stmt-value (fn-stmt-take-id-items n items)))
                       (nfix n))
                (fn-stmt-id-listp
                 (fn-stmt-value (fn-stmt-take-id-items n items)))))
  :hints (("Goal" :induct (fn-stmt-take-id-items n items))))

(defthm fn-stmt-encode-items-of-id-items-bound
  (implies (fn-stmt-id-listp ids)
           (<= (len (fn-stmt-encode-items (fn-stmt-id-items ids)))
               (* 35 (len ids))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-stmt-id-items ids)
           :in-theory (disable fn-cbor-encode))))

; -----------------------------------------------------------------------------
; Kinds and header reconstruction

(defthm fn-stmt-kind-of-code-of-kind-code
  (implies (fn-stmt-kindp k)
           (equal (fn-stmt-kind-of-code (fn-stmt-kind-code k)) k)))

(defthm fn-stmt-kind-code-of-kind-of-code
  (implies (fn-stmt-kind-of-code n)
           (and (fn-stmt-kindp (fn-stmt-kind-of-code n))
                (equal (fn-stmt-kind-code (fn-stmt-kind-of-code n)) n))))

(defthm fn-stmt-kind-code-is-uint32
  (implies (fn-stmt-kindp k)
           (fn-record-uint32p (fn-stmt-kind-code k))))

(defthm fn-stmt-header-reconstruct
  (implies (and (true-listp h) (equal (len h) 6))
           (equal (fn-stmt-make-header
                   (fn-stmt-header-creator h) (fn-stmt-header-incarnation h)
                   (fn-stmt-header-sequence h) (fn-stmt-header-preds h)
                   (fn-stmt-header-kind h) (fn-stmt-header-ref h))
                  h)))

(defthm fn-stmt-id-items-length
  (equal (len (fn-stmt-id-items ids)) (len ids)))

(defthm fn-stmt-header-items-length
  (implies (fn-stmt-headerp h)
           (equal (len (fn-stmt-header-items h))
                  (+ 7 (len (fn-stmt-header-preds h))))))

; -----------------------------------------------------------------------------
; Header: items both ways

(defthm fn-stmt-header-of-items-of-header-items
  (implies (fn-stmt-headerp h)
           (equal (fn-stmt-header-of-items
                   (append (fn-stmt-header-items h) rest))
                  (fn-stmt-ok2 h rest)))
  :hints (("Goal"
           :in-theory (disable fn-stmt-take-id-items fn-stmt-id-items
                               fn-stmt-kind-of-code fn-stmt-kind-code
                               fn-stmt-make-header))))

(defthm fn-stmt-header-of-items-of-header-items-exact
  (implies (fn-stmt-headerp h)
           (equal (fn-stmt-header-of-items (fn-stmt-header-items h))
                  (fn-stmt-ok2 h nil)))
  :hints (("Goal"
           :use ((:instance fn-stmt-header-of-items-of-header-items (rest nil)))
           :in-theory (disable fn-stmt-header-of-items fn-stmt-header-items
                               fn-stmt-headerp
                               fn-stmt-header-of-items-of-header-items))))

(defthm fn-stmt-header-of-items-sound
  (implies (fn-stmt-okp (fn-stmt-header-of-items items))
           (and (fn-stmt-headerp (fn-stmt-value (fn-stmt-header-of-items items)))
                (equal (append (fn-stmt-header-items
                                (fn-stmt-value (fn-stmt-header-of-items items)))
                               (fn-stmt-rest (fn-stmt-header-of-items items)))
                       items)))
  :hints (("Goal"
           :in-theory (disable fn-stmt-take-id-items fn-stmt-id-items
                               fn-stmt-kind-of-code fn-stmt-kind-code))))

; -----------------------------------------------------------------------------
; Header bytes

(defthm fn-stmt-header-encoding-bound
  (implies (fn-stmt-headerp h)
           (<= (len (fn-stmt-encode-items (fn-stmt-header-items h))) 655))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-stmt-header-round-trip
  (implies (fn-stmt-headerp h)
           (equal (fn-stmt-header-decode-exact (fn-stmt-header-encode h))
                  (fn-stmt-ok h)))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stmt-header-items h))
                            (fuel *fn-stmt-max-header-items*))
                 (:instance fn-stmt-header-encoding-bound)
                 (:instance fn-stmt-header-items-length))
           :in-theory (disable fn-stmt-header-items fn-stmt-headerp
                               fn-stmt-decode-items fn-stmt-header-of-items
                               fn-stmt-encode-items
                               fn-stmt-decode-items-of-encode-items
                               fn-stmt-header-encoding-bound
                               fn-stmt-header-items-length))))

(defthm fn-stmt-header-accepted-input-is-canonical
  (implies (fn-stmt-okp (fn-stmt-header-decode-exact octets))
           (equal (fn-stmt-header-encode
                   (fn-stmt-value (fn-stmt-header-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items
                            (fuel *fn-stmt-max-header-items*))
                 (:instance fn-stmt-header-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items
                                     *fn-stmt-max-header-items* octets)))))
           :in-theory (disable fn-stmt-decode-items fn-stmt-header-of-items
                               fn-stmt-header-items fn-stmt-encode-items
                               fn-stmt-headerp
                               fn-stmt-encode-items-of-decode-items
                               fn-stmt-header-of-items-sound))))

(defthm fn-stmt-header-encode-injective
  (implies (and (fn-stmt-headerp h1)
                (fn-stmt-headerp h2)
                (equal (fn-stmt-header-encode h1) (fn-stmt-header-encode h2)))
           (equal h1 h2))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-stmt-header-round-trip (h h1))
                 (:instance fn-stmt-header-round-trip (h h2)))
           :in-theory (disable fn-stmt-header-round-trip
                               fn-stmt-header-decode-exact
                               fn-stmt-header-encode fn-stmt-headerp))))

; The content id is, by definition, the tagged digest of the canonical header
; bytes.  Stated so the name says exactly that and nothing more.
(defthm fn-stmt-content-id-unfolds
  (equal (fn-stmt-content-id h)
         (fn-digest (fn-digest-tagged-preimage *fn-stmt-id-tag*
                                               (fn-stmt-header-encode h)))))

; -----------------------------------------------------------------------------
; Whole statement

(defthm fn-stmt-reconstruct
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (fn-stmt-make (fn-stmt-header s) (fn-stmt-payload s)
                                (fn-stmt-signature s))
                  s)))

(defthm fn-stmt-items-length
  (implies (fn-stmt-p s)
           (<= (len (fn-stmt-items s)) 25))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-stmt-header-items fn-stmt-headerp))))

(defthm fn-stmt-encoding-bound
  (implies (fn-stmt-p s)
           (<= (len (fn-stmt-encode-items (fn-stmt-items s))) 12949))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-cbor-encode fn-stmt-header-items
                                      fn-stmt-headerp))))

(defthm fn-stmt-of-items-of-items
  (implies (fn-stmt-p s)
           (equal (fn-stmt-of-items (fn-stmt-items s))
                  (fn-stmt-ok s)))
  :hints (("Goal"
           :in-theory (disable fn-stmt-header-of-items fn-stmt-header-items
                               fn-stmt-headerp fn-stmt-payload-ref))))

(defthm fn-stmt-round-trip
  (implies (fn-stmt-p s)
           (equal (fn-stmt-decode-exact (fn-stmt-encode s))
                  (fn-stmt-ok s)))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stmt-items s))
                            (fuel *fn-stmt-max-items*))
                 (:instance fn-stmt-encoding-bound)
                 (:instance fn-stmt-items-length))
           :in-theory (disable fn-stmt-items fn-stmt-p
                               fn-stmt-decode-items fn-stmt-of-items
                               fn-stmt-encode-items
                               fn-stmt-decode-items-of-encode-items
                               fn-stmt-encoding-bound
                               fn-stmt-items-length))))

(defthm fn-stmt-of-items-sound
  (implies (fn-stmt-okp (fn-stmt-of-items items))
           (and (fn-stmt-p (fn-stmt-value (fn-stmt-of-items items)))
                (equal (fn-stmt-items (fn-stmt-value (fn-stmt-of-items items)))
                       items)))
  :hints (("Goal"
           :use ((:instance fn-stmt-header-of-items-sound))
           :in-theory (disable fn-stmt-header-of-items fn-stmt-header-items
                               fn-stmt-headerp fn-stmt-payload-ref
                               fn-stmt-header-of-items-sound))))

(defthm fn-stmt-accepted-input-is-canonical
  (implies (fn-stmt-okp (fn-stmt-decode-exact octets))
           (equal (fn-stmt-encode (fn-stmt-value (fn-stmt-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items
                            (fuel *fn-stmt-max-items*))
                 (:instance fn-stmt-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items
                                     *fn-stmt-max-items* octets)))))
           :in-theory (disable fn-stmt-decode-items fn-stmt-of-items
                               fn-stmt-items fn-stmt-encode-items fn-stmt-p
                               fn-stmt-encode-items-of-decode-items
                               fn-stmt-of-items-sound))))

; -----------------------------------------------------------------------------
; Signing

(defthm fn-stmt-sign-is-verified
  (implies (and (fn-sig-seed-p sk)
                (fn-digest-octetsp creator)
                (fn-record-uint32p incarnation)
                (fn-record-uint32p sequence)
                (fn-stmt-predsp preds)
                (fn-stmt-kindp kind)
                (fn-stmt-payloadp payload))
           (fn-stmt-verifiedp
            (fn-stmt-sign sk creator incarnation sequence preds kind payload)
            (fn-sig-public-key sk)))
  :hints (("Goal"
           :in-theory (disable fn-digest-tagged fn-digest-tagged-preimage
                               fn-stmt-header-encode fn-stmt-content-id
                               fn-stmt-signing-preimage fn-stmt-payload-ref
                               fn-digest-octetsp fn-stmt-predsp fn-stmt-kindp
                               fn-record-uint32p fn-sig-signature-p))))

; -----------------------------------------------------------------------------
; Receipts

(defthm fn-stmt-receipt-reconstruct
  (implies (and (true-listp r) (equal (len r) 4))
           (equal (fn-stmt-make-receipt
                   (fn-stmt-receipt-subject r) (fn-stmt-receipt-obligation r)
                   (fn-stmt-receipt-policy-id r) (fn-stmt-receipt-evidence r))
                  r)))

(defthm fn-stmt-receipt-items-are-items
  (implies (fn-stmt-receipt-p r)
           (fn-stmt-item-listp (fn-stmt-receipt-items r))))

(defthm fn-stmt-receipt-encoding-bound
  (implies (fn-stmt-receipt-p r)
           (<= (len (fn-stmt-encode-items (fn-stmt-receipt-items r))) 364))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-stmt-receipt-of-items-of-receipt-items
  (implies (fn-stmt-receipt-p r)
           (equal (fn-stmt-receipt-of-items (fn-stmt-receipt-items r))
                  (fn-stmt-ok r))))

(defthm fn-stmt-receipt-round-trip
  (implies (fn-stmt-receipt-p r)
           (equal (fn-stmt-receipt-decode-exact (fn-stmt-receipt-encode r))
                  (fn-stmt-ok r)))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stmt-receipt-items r))
                            (fuel 4))
                 (:instance fn-stmt-receipt-encoding-bound))
           :in-theory (disable fn-stmt-receipt-items fn-stmt-receipt-p
                               fn-stmt-decode-items fn-stmt-receipt-of-items
                               fn-stmt-encode-items
                               fn-stmt-decode-items-of-encode-items
                               fn-stmt-receipt-encoding-bound))))

(defthm fn-stmt-receipt-of-items-sound
  (implies (fn-stmt-okp (fn-stmt-receipt-of-items items))
           (and (fn-stmt-receipt-p
                 (fn-stmt-value (fn-stmt-receipt-of-items items)))
                (equal (fn-stmt-receipt-items
                        (fn-stmt-value (fn-stmt-receipt-of-items items)))
                       items))))

(defthm fn-stmt-receipt-accepted-input-is-canonical
  (implies (fn-stmt-okp (fn-stmt-receipt-decode-exact octets))
           (equal (fn-stmt-receipt-encode
                   (fn-stmt-value (fn-stmt-receipt-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items (fuel 4))
                 (:instance fn-stmt-receipt-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items 4 octets)))))
           :in-theory (disable fn-stmt-decode-items fn-stmt-receipt-of-items
                               fn-stmt-receipt-items fn-stmt-encode-items
                               fn-stmt-receipt-p
                               fn-stmt-encode-items-of-decode-items
                               fn-stmt-receipt-of-items-sound))))

(defthm fn-stmt-receipt-encode-injective
  (implies (and (fn-stmt-receipt-p r1)
                (fn-stmt-receipt-p r2)
                (equal (fn-stmt-receipt-encode r1) (fn-stmt-receipt-encode r2)))
           (equal r1 r2))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-stmt-receipt-round-trip (r r1))
                 (:instance fn-stmt-receipt-round-trip (r r2)))
           :in-theory (disable fn-stmt-receipt-round-trip
                               fn-stmt-receipt-decode-exact
                               fn-stmt-receipt-encode fn-stmt-receipt-p))))

; A receipt's payload bytes fix its policy term: the same bytes never carry two
; terms.  The step from payload bytes to the header's `ref` is a digest and
; therefore A-CRYPTO; see specs/policy.md.
(defthm fn-stmt-receipt-bytes-determine-term
  (implies (and (fn-stmt-receipt-p r1)
                (fn-stmt-receipt-p r2)
                (equal (fn-stmt-receipt-encode r1) (fn-stmt-receipt-encode r2)))
           (equal (fn-stmt-receipt-term r1) (fn-stmt-receipt-term r2)))
  :rule-classes nil
  :hints (("Goal" :use fn-stmt-receipt-encode-injective
           :in-theory (disable fn-stmt-receipt-encode fn-stmt-receipt-p))))
