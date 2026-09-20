; fn: certified properties of the BPv7 primary block codec.
;
; The two directions of the codec are proved here, as
; `books/cbor-invariants.lisp` does for the original profile: every valid block
; decodes back from its own encoding, and every accepted octet sequence
; re-encodes to exactly itself.  The second direction is what makes a
; non-deterministic CBOR spelling, a wrong CRC, a wrong arity for the fragment
; and CRC flags, or a version other than 7 unable to pass.
;
; The identity theorems say which fields a bundle's identity is and is not a
; function of.  RFC 9171 section 4.3.1 makes the identity of a fragment depend
; on its payload length as well, which is not in the primary block; that is
; carried as an argument and stated as such, not quietly dropped.

(in-package "ACL2")

(include-book "bp-primary")

(local (include-book "arithmetic/top" :dir :system))
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-cbor-record-vocabulary fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; Endpoint IDs

(defthm fn-bpp-vchar-listp-implies-octet-listp
  (implies (fn-bpp-vchar-listp xs)
           (fn-cbor-octet-listp xs))
  :hints (("Goal" :induct (fn-bpp-vchar-listp xs))))

(defthm fn-bpp-eid-value-is-shape
  (implies (fn-bpp-eidp e)
           (fn-bpc-shapep :item (fn-bpp-eid-value e))))

(defthm fn-bpp-eid-value-cost
  (implies (fn-bpp-eidp e)
           (<= (fn-bpc-cost :item (fn-bpp-eid-value e)) 11))
  :rule-classes :linear)

; An ipn EID is a three-element true list, and `fn-bpp-value-eid` rebuilds it
; field by field; ACL2 does not open `len` or `true-listp` on a variable, so
; the reconstruction is stated once here.
(local
 (defthm fn-bpp-three-element-list-reconstructs
   (implies (and (true-listp e) (equal (len e) 3))
            (equal (list (car e) (nth 1 e) (nth 2 e)) e))
   :hints (("Goal" :expand ((len e) (len (cdr e)) (len (cddr e))
                            (len (cdddr e))
                            (true-listp e) (true-listp (cdr e))
                            (true-listp (cddr e)) (true-listp (cdddr e)))))))

(local
 (defthm fn-bpp-equal-three-element-list
   (implies (and (true-listp e) (equal (len e) 3))
            (equal (equal (list a b c) e)
                   (and (equal a (car e)) (equal b (nth 1 e))
                        (equal c (nth 2 e)))))
   :hints (("Goal" :use fn-bpp-three-element-list-reconstructs
            :in-theory (disable fn-bpp-three-element-list-reconstructs)))))

(defthm fn-bpp-value-eid-of-eid-value
  (implies (fn-bpp-eidp e)
           (equal (fn-bpp-value-eid (fn-bpp-eid-value e)) e))
  :hints (("Goal" :use fn-bpp-three-element-list-reconstructs)))

(defthm fn-bpp-value-eid-yields-eid
  (implies (fn-bpp-value-eid v)
           (fn-bpp-eidp (fn-bpp-value-eid v))))

; -----------------------------------------------------------------------------
; The block value is in the CBOR domain, within the item budget, and within
; the input preflight.  All three are needed before the round trip can be
; stated about `fn-bpp-decode` itself rather than about an inner function.

(defthm fn-bpp-block-value-is-shape
  (implies (and (fn-bpp-blockp b)
                (fn-cbor-octet-listp crc-octets)
                (<= (len crc-octets) *fn-bpc-max-bytes*))
           (fn-bpc-shapep :item (fn-bpp-block-value b crc-octets)))
  :hints (("Goal" :in-theory (disable fn-bpp-eid-value))))

(defthm fn-bpp-block-value-cost
  (implies (and (fn-bpp-blockp b)
                (fn-cbor-octet-listp crc-octets))
           (<= (fn-bpc-cost :item (fn-bpp-block-value b crc-octets)) 59))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-bpp-eid-value))))

(defthm fn-bpp-zero-crc-is-octets
  (fn-cbor-octet-listp (fn-bpp-zero-crc type)))

(defthm fn-bpp-zero-crc-length
  (<= (len (fn-bpp-zero-crc type)) 4)
  :rule-classes :linear)

(defthm fn-bpp-crc-octets-are-octets
  (implies (and (fn-bpp-crc-typep type) (fn-cbor-octet-listp octets))
           (fn-cbor-octet-listp (fn-bpp-crc-octets type octets))))

(defthm fn-bpp-crc-octets-length
  (implies (fn-bpp-crc-typep type)
           (<= (len (fn-bpp-crc-octets type octets)) 4))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-cbor-u16-bytes fn-cbor-u32-bytes))))

; The computed CRC field, as the preflight and the round trip see it: an octet
; list of at most four octets.  Both follow from `fn-bpp-crc-octets` on the
; zero-filled encoding without opening `fn-bpc-enc`.
(defthm fn-bpp-block-crc-is-octets
  (implies (fn-bpp-blockp b)
           (fn-cbor-octet-listp (fn-bpp-block-crc b)))
  :hints (("Goal" :in-theory (disable fn-bpp-crc-octets fn-bpc-enc
                                      fn-bpp-block-value))))

(defthm fn-bpp-block-crc-length
  (implies (fn-bpp-blockp b)
           (<= (len (fn-bpp-block-crc b)) 4))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-bpp-crc-octets fn-bpc-enc
                                      fn-bpp-block-value))))

(defthm fn-bpp-encoding-fits-the-preflight
  (implies (fn-bpp-blockp b)
           (fn-cbor-at-mostp (fn-bpp-encode b) *fn-bpc-max-input*))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpc-enc-length-bound
                            (flg :item)
                            (x (fn-bpp-block-value b (fn-bpp-block-crc b))))
                 (:instance fn-bpp-block-value-cost
                            (crc-octets (fn-bpp-block-crc b)))
                 (:instance fn-cbor-at-mostp-from-length
                            (xs (fn-bpp-encode b))
                            (bound *fn-bpc-max-input*)))
           :in-theory (disable fn-bpc-enc-length-bound
                               fn-bpp-block-value-cost
                               fn-cbor-at-mostp-from-length
                               fn-bpp-block-value fn-bpp-block-crc
                               fn-bpc-cost fn-bpc-enc fn-bpp-blockp))))

; -----------------------------------------------------------------------------
; Keystone: the section 4.3.1 field layout is a bijection on valid blocks.
;
; This is the lemma that does the work in both directions of the codec.  Its
; hypothesis stack is: the block is in the domain, and the CRC field content
; has the width its CRC type demands.

; The block record is an eleven-element true list; the same reconstruction
; as for ipn EIDs, one level per field.
(local
 (defthm fn-bpp-eleven-element-list-reconstructs
   (implies (and (true-listp b) (equal (len b) 11))
            (equal (list (car b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b)) b))
   :hints (("Goal" :expand ((len b) (len (cdr b)) (len (cdr (cdr b))) (len (cdr (cdr (cdr b)))) (len (cdr (cdr (cdr (cdr b))))) (len (cdr (cdr (cdr (cdr (cdr b)))))) (len (cdr (cdr (cdr (cdr (cdr (cdr b))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))))) (true-listp b) (true-listp (cdr b)) (true-listp (cdr (cdr b))) (true-listp (cdr (cdr (cdr b)))) (true-listp (cdr (cdr (cdr (cdr b))))) (true-listp (cdr (cdr (cdr (cdr (cdr b)))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr b))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))))))))))

(local
 (defthm fn-bpp-equal-eleven-element-list
   (implies (and (true-listp b) (equal (len b) 11))
            (equal (equal (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) b)
                   (and (equal a0 (car b)) (equal a1 (nth 1 b)) (equal a2 (nth 2 b)) (equal a3 (nth 3 b)) (equal a4 (nth 4 b)) (equal a5 (nth 5 b)) (equal a6 (nth 6 b)) (equal a7 (nth 7 b)) (equal a8 (nth 8 b)) (equal a9 (nth 9 b)) (equal a10 (nth 10 b)))))
   :hints (("Goal" :use fn-bpp-eleven-element-list-reconstructs
            :in-theory (disable fn-bpp-eleven-element-list-reconstructs)))))

; The CRC field is not read back by fn-bpp-value-block, so the former
; hypotheses (fn-cbor-octet-listp crc-octets) and the width equation had no
; violating value (probed 2026-09-19: '(0 0 0 0), '(1 2 3) and 'x all round
; trip); they are dropped rather than kept as teeth-less hypotheses.
(defthm fn-bpp-value-block-of-block-value
  (implies (fn-bpp-blockp b)
           (equal (fn-bpp-value-block (fn-bpp-block-value b crc-octets)) b))
  :hints (("Goal" :in-theory (disable fn-bpp-eid-value fn-bpp-value-eid))))

(defthm fn-bpp-value-crc-field-of-block-value
  (implies (and (fn-bpp-blockp b)
                (not (equal (fn-bpp-crc-type b) 0))
                (fn-cbor-octet-listp crc-octets))
           (equal (fn-bpp-value-crc-field (fn-bpp-block-value b crc-octets))
                  crc-octets))
  :hints (("Goal" :in-theory (disable fn-bpp-eid-value))))

(defthm fn-bpp-block-crc-width
  (implies (fn-bpp-blockp b)
           (equal (len (fn-bpp-block-crc b))
                  (fn-bpp-crc-width (fn-bpp-crc-type b))))
  :hints (("Goal" :in-theory (disable fn-bpc-enc fn-bpp-block-value))))

; -----------------------------------------------------------------------------
; Keystone: round trip.  Every valid primary block decodes back from its own
; encoding, CRC and all.

; `fn-bpp-encode` in the form the CBOR round trip is stated in.  Kept as a
; rule rather than opened, so that `fn-bpc-value-round-trip` matches the
; decoder call syntactically instead of both sides unfolding to `fn-bpc-enc`.
(local
 (defthm fn-bpp-encode-unfolds
   (equal (fn-bpp-encode b)
          (fn-bpc-encode (fn-bpp-block-value b (fn-bpp-block-crc b))))
   :hints (("Goal" :in-theory (e/d (fn-bpp-encode fn-bpc-encode)
                                   (fn-bpc-enc fn-bpp-block-value
                                    fn-bpp-block-crc))))))

(local
 (defthm fn-bpp-block-value-fits-the-preflight
   (implies (fn-bpp-blockp b)
            (fn-cbor-at-mostp
             (fn-bpc-enc :item (fn-bpp-block-value b (fn-bpp-block-crc b)))
             *fn-bpc-max-input*))
   :hints (("Goal" :use fn-bpp-encoding-fits-the-preflight
            :in-theory (e/d (fn-bpp-encode)
                            (fn-bpp-encoding-fits-the-preflight
                             fn-bpp-encode-unfolds fn-bpc-enc
                             fn-bpp-block-value fn-bpp-block-crc
                             fn-bpp-blockp))))))

(local
 (defthm fn-bpp-blockp-is-consp
   (implies (fn-bpp-blockp b) (consp b))
   :rule-classes (:rewrite :forward-chaining)))

(defthm fn-bpp-decode-of-encode
  (implies (fn-bpp-blockp b)
           (equal (fn-bpp-decode (fn-bpp-encode b)) (fn-bpp-ok b)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpc-value-round-trip
                            (x (fn-bpp-block-value b (fn-bpp-block-crc b))))
                 (:instance fn-bpp-block-value-is-shape
                            (crc-octets (fn-bpp-block-crc b)))
                 (:instance fn-bpp-block-value-cost
                            (crc-octets (fn-bpp-block-crc b)))
                 fn-bpp-block-value-fits-the-preflight
                 fn-bpp-block-crc-is-octets
                 fn-bpp-block-crc-length
                 fn-bpp-block-crc-width
                 (:instance fn-bpp-value-block-of-block-value
                            (crc-octets (fn-bpp-block-crc b)))
                 (:instance fn-bpp-value-crc-field-of-block-value
                            (crc-octets (fn-bpp-block-crc b))))
           :in-theory (disable fn-bpc-value-round-trip
                               fn-bpp-block-value-is-shape
                               fn-bpp-block-value-cost
                               fn-bpp-block-value-fits-the-preflight
                               fn-bpp-block-crc-is-octets
                               fn-bpp-block-crc-length
                               fn-bpp-block-crc-width
                               fn-bpp-value-block-of-block-value
                               fn-bpp-value-crc-field-of-block-value
                               fn-bpp-block-value fn-bpp-block-crc
                               fn-bpp-encode fn-bpc-cost fn-bpc-encode
                               fn-bpc-enc fn-bpc-decode-exact fn-bpc-decode
                               fn-bpc-shapep fn-bpp-blockp fn-bpp-value-block
                               fn-bpp-value-crc-field fn-bpp-crc-width))))

(defthm fn-bpp-accepted-input-is-canonical-by-construction
  (implies (fn-bpp-result-okp (fn-bpp-decode octets))
           (equal (fn-bpp-encode (fn-bpp-result-block (fn-bpp-decode octets)))
                  octets))
  :hints (("Goal" :in-theory (disable fn-bpc-decode-exact fn-bpc-decode
                                      fn-bpc-enc fn-bpp-encode
                                      fn-bpp-value-block fn-bpp-block-crc
                                      fn-bpp-blockp fn-bpp-value-crc-field))))

(defthm fn-bpp-decode-yields-block
  (implies (fn-bpp-result-okp (fn-bpp-decode octets))
           (fn-bpp-blockp (fn-bpp-result-block (fn-bpp-decode octets))))
  :hints (("Goal" :in-theory (disable fn-bpc-decode-exact fn-bpc-decode
                                      fn-bpc-enc fn-bpp-encode
                                      fn-bpp-value-block fn-bpp-block-crc
                                      fn-bpp-blockp fn-bpp-value-crc-field))))

; A block accepted with a non-zero CRC type carries exactly the CRC that
; section 4.2.2 prescribes over its own zero-filled encoding.
(defthm fn-bpp-accepted-block-has-valid-crc
  (implies (and (fn-bpp-result-okp (fn-bpp-decode octets))
                (not (equal (fn-bpp-crc-type
                             (fn-bpp-result-block (fn-bpp-decode octets)))
                            0)))
           (equal (fn-bpp-value-crc-field
                   (fn-cbor-result-value (fn-bpc-decode-exact octets)))
                  (fn-bpp-block-crc
                   (fn-bpp-result-block (fn-bpp-decode octets)))))
  :hints (("Goal" :in-theory (disable fn-bpc-decode-exact fn-bpc-decode
                                      fn-bpc-enc fn-bpp-encode
                                      fn-bpp-value-block fn-bpp-block-crc
                                      fn-bpp-blockp fn-bpp-value-crc-field))))

; -----------------------------------------------------------------------------
; Keystone: encoding is injective, so identity is determined by the canonical
; encoding.  The identity corollary below is named for what it is.

(defthm fn-bpp-encode-is-injective
  (implies (and (fn-bpp-blockp p) (fn-bpp-blockp q)
                (equal (fn-bpp-encode p) (fn-bpp-encode q)))
           (equal p q))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpp-decode-of-encode (b p))
                 (:instance fn-bpp-decode-of-encode (b q)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-bpp-ok cons-equal)))))

(defthm fn-bpp-identity-determined-by-encoding-corollary
  (implies (and (fn-bpp-blockp p) (fn-bpp-blockp q)
                (equal (fn-bpp-encode p) (fn-bpp-encode q)))
           (and (equal (fn-bpp-adu-key p) (fn-bpp-adu-key q))
                (equal (fn-bpp-bundle-id p n) (fn-bpp-bundle-id q n))))
  :rule-classes nil
  :hints (("Goal" :use fn-bpp-encode-is-injective
           :in-theory (theory 'minimal-theory))))

; -----------------------------------------------------------------------------
; The section 4.2.7 projection, spelled out.  These three are unfoldings of
; `fn-bpp-adu-key` and `fn-bpp-bundle-id`, not proof events: they record which
; fields identity is and is not a function of, so that a later change to the
; record shape breaks them.  The keystone for identity is
; `fn-bpp-encode-is-injective` above.

(defthm fn-bpp-adu-key-ignores-destination-lifetime-and-crc-type-by-definition
  (implies (and (fn-bpp-blockp b) (fn-bpp-eidp d) (fn-bpp-timep l)
                (fn-bpp-crc-typep type))
           (and (equal (fn-bpp-adu-key (fn-bpp-with-destination b d))
                       (fn-bpp-adu-key b))
                (equal (fn-bpp-adu-key (fn-bpp-with-lifetime b l))
                       (fn-bpp-adu-key b))
                (equal (fn-bpp-adu-key (fn-bpp-with-crc-type b type))
                       (fn-bpp-adu-key b))))
  :hints (("Goal" :in-theory (disable fn-bpp-blockp fn-bpp-eidp fn-bpp-timep
                                      fn-bpp-crc-typep))))

(defthm fn-bpp-adu-key-separates-source-and-timestamp-by-definition
  (implies (and (fn-bpp-blockp p) (fn-bpp-blockp q)
                (equal (fn-bpp-adu-key p) (fn-bpp-adu-key q)))
           (and (equal (fn-bpp-source p) (fn-bpp-source q))
                (equal (fn-bpp-creation-time p) (fn-bpp-creation-time q))
                (equal (fn-bpp-sequence p) (fn-bpp-sequence q))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bpp-blockp fn-bpp-eidp fn-bpp-timep
                                      fn-bpp-crc-typep))))

; The fragment case adds the fragment offset and this bundle's payload length.
; The payload length is not in the primary block, so two fragments of one ADU
; that differ only in payload length have the same primary-block fields and
; different bundle identities.
(defthm fn-bpp-bundle-id-of-fragment-uses-payload-length-by-definition
  (implies (and (fn-bpp-blockp b)
                (fn-bpp-fragmentp (fn-bpp-flags b))
                (not (equal m n)))
           (not (equal (fn-bpp-bundle-id b m) (fn-bpp-bundle-id b n))))
  :hints (("Goal" :in-theory (disable fn-bpp-blockp fn-bpp-eidp fn-bpp-timep
                                      fn-bpp-crc-typep))))

(defthm fn-bpp-bundle-id-of-non-fragment-ignores-payload-length-by-definition
  (implies (and (fn-bpp-blockp b)
                (not (fn-bpp-fragmentp (fn-bpp-flags b))))
           (equal (fn-bpp-bundle-id b m) (fn-bpp-bundle-id b n)))
  :hints (("Goal" :in-theory (disable fn-bpp-blockp fn-bpp-eidp fn-bpp-timep
                                      fn-bpp-crc-typep))))

; A bundle whose source node ID is the null endpoint is not uniquely
; identifiable at all (section 4.2.3), and this is the predicate that says so.
(defthm fn-bpp-anonymous-source-is-not-identifiable-by-definition
  (implies (and (fn-bpp-blockp b)
                (equal (fn-bpp-source b) (list :dtn-none)))
           (not (fn-bpp-identifiablep b)))
  :hints (("Goal" :in-theory (disable fn-bpp-blockp fn-bpp-eidp fn-bpp-timep
                                      fn-bpp-crc-typep))))

; -----------------------------------------------------------------------------
; Extension blocks (section 4.4): both directions for each.

; Every block-type-specific datum in this book has a cost far below the item
; budget, and a value of cost at most 59 encodes within the input preflight.
(local
 (defthm fn-bpp-small-value-fits-the-preflight
   (implies (and (fn-bpc-shapep :item x) (<= (fn-bpc-cost :item x) 59))
            (fn-cbor-at-mostp (fn-bpc-enc :item x) *fn-bpc-max-input*))
   :hints (("Goal"
            :use ((:instance fn-bpc-enc-length-bound (flg :item))
                  (:instance fn-cbor-at-mostp-from-length
                             (xs (fn-bpc-enc :item x))
                             (bound *fn-bpc-max-input*)))
            :in-theory (disable fn-bpc-enc-length-bound
                                fn-cbor-at-mostp-from-length
                                fn-bpc-enc fn-bpc-cost fn-bpc-shapep)))))

;; OPEN, not certified: the `fn-bpc-value-round-trip` instance
;; sinks into preprocessing over the opened EID predicates; needs the same
;; closed-theory treatment as `fn-bpp-decode-of-encode` before it can close.
;; (defthm fn-bpp-previous-node-round-trip
;;   (implies (fn-bpp-previous-nodep e)
;;            (equal (fn-bpp-data-previous-node (fn-bpp-previous-node-data e)) e))
;;   :hints (("Goal"
;;            :use ((:instance fn-bpc-value-round-trip (x (fn-bpp-eid-value e))))
;;            :in-theory (disable fn-bpc-value-round-trip fn-bpp-eid-value
;;                                fn-bpc-enc fn-bpc-shapep))))

(defthm fn-bpp-bundle-age-round-trip
  (implies (fn-bpp-bundle-agep ms)
           (equal (fn-bpp-data-bundle-age (fn-bpp-bundle-age-data ms)) ms))
  :hints (("Goal"
           :use ((:instance fn-bpc-value-round-trip (x (cons :uint ms))))
           :in-theory (disable fn-bpc-value-round-trip fn-bpc-enc))))

;; OPEN, not certified: the `fn-bpc-value-round-trip` instance sinks
;; into preprocessing (zero prover time, a minute of other time) on some runs
;; and closes on others; not admitted until that is understood.
;; (defthm fn-bpp-hop-count-round-trip
;;   (implies (fn-bpp-hop-countp x)
;;            (equal (fn-bpp-data-hop-count (fn-bpp-hop-count-data x)) x))
;;   :hints (("Goal"
;;            :use ((:instance fn-bpc-value-round-trip
;;                             (x (cons :array (list (cons :uint (nth 1 x))
;;                                                   (cons :uint (nth 2 x)))))))
;;            :in-theory (disable fn-bpc-value-round-trip fn-bpc-enc))))

(defthm fn-bpp-hop-count-limit-is-bounded
  (implies (fn-bpp-hop-countp x)
           (and (<= 1 (nth 1 x)) (<= (nth 1 x) 255))))
