; Teeth for packet P6: the wide CBOR uint (books/cbor, cbor-invariants), the
; schema-2 record (books/records), and the translation keystone
; (books/records-schema-v1).  Each keystone has a reachable non-degenerate
; witness and one `must-fail' per hypothesis, with a ground case showing the
; conclusion false once the hypothesis is dropped.

(in-package "ACL2")
(include-book "../../books/records-schema-v1")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The wide uint.  Boundary vectors: the last narrow value keeps its head, the
; first wide value takes the eight-octet head, and the u64 maximum.

(assert-event (equal (fn-cbor-encode-uint-wide 4294967295) '(26 255 255 255 255)))
(assert-event (equal (fn-cbor-encode-uint-wide 4294967296) '(27 0 0 0 1 0 0 0 0)))
(assert-event (equal (fn-cbor-encode-uint-wide 18446744073709551615)
                     '(27 255 255 255 255 255 255 255 255)))
(assert-event (equal (fn-cbor-encode-uint-wide 18446744073709551616) nil))
(assert-event (equal (fn-cbor-decode-prechecked-wide '(27 0 0 0 1 0 0 0 0 7) 10)
                     (fn-cbor-ok (cons :uint 4294967296) '(7))))
; An eight-octet head carrying a narrow value is not the shortest form.
(assert-event (equal (fn-cbor-decode-prechecked-wide '(27 0 0 0 0 255 255 255 255) 10)
                     (fn-cbor-error :noncanonical)))
(assert-event (equal (fn-cbor-decode-prechecked-wide '(27 0 0 0 1 0 0 0) 10)
                     (fn-cbor-error :truncated)))
; The narrow decoder refuses what the wide one accepts: the reason
; `fn-cbor-decode-prechecked-wide-extends-narrow' needs its hypothesis.
(assert-event (not (fn-cbor-result-okp
                    (fn-cbor-decode-prechecked '(27 0 0 0 1 0 0 0 0) 10))))
(assert-event (not (equal (fn-cbor-decode-prechecked-wide '(27 0 0 0 1 0 0 0 0) 10)
                          (fn-cbor-decode-prechecked '(27 0 0 0 1 0 0 0 0) 10))))

(must-fail
 (defthm p6-teeth-extends-narrow-without-acceptance
   (equal (fn-cbor-decode-prechecked-wide octets budget)
          (fn-cbor-decode-prechecked octets budget))))

(must-fail
 (defthm p6-teeth-wide-round-trip-without-width
   (implies (and (natp n) (fn-cbor-octet-listp rest))
            (equal (fn-cbor-decode-prechecked-wide
                    (append (fn-cbor-encode-uint-wide n) rest) budget)
                   (fn-cbor-ok (cons :uint n) rest)))))

(must-fail
 (defthm p6-teeth-wide-round-trip-without-octet-rest
   (implies (and (natp n) (<= n *fn-cbor-max-uint64*))
            (equal (fn-cbor-decode-prechecked-wide
                    (append (fn-cbor-encode-uint-wide n) rest) budget)
                   (fn-cbor-ok (cons :uint n) rest)))))

(must-fail
 (defthm p6-teeth-reencode-without-acceptance
   (implies (fn-cbor-octet-listp octets)
            (equal (append (fn-cbor-encode-uint-wide
                            (cdr (fn-cbor-result-value
                                  (fn-cbor-decode-prechecked-wide octets budget))))
                           (fn-cbor-result-rest
                            (fn-cbor-decode-prechecked-wide octets budget)))
                   octets))))

; -----------------------------------------------------------------------------
; The schema-2 record: a record whose fields are all distinct and whose
; sequence, transaction ID, charge and stamp are above 2^32 - 1, round trips
; under schema 2; its u32 twin keeps schema 1.

(defconst *p6-wide-record*
  (fn-record-make 4294967297 4294967298 3 "<w@example.invalid>" '(72 105 13 10)
                  '("fn.letters" "fn.test") "archive-w" "content-w" "evidence-w"
                  1099511627776 18446744073709551615))

(assert-event (fn-record-p *p6-wide-record*))
(assert-event (equal (fn-record-schema-octet *p6-wide-record*) 2))
(assert-event (equal (nth 5 (fn-record-encode-impl *p6-wide-record*)) 2))
(assert-event (equal (fn-record-decode-exact-impl (fn-record-encode-impl *p6-wide-record*))
                     (fn-record-result-ok *p6-wide-record*)))
(assert-event (equal (fn-record-schema-octet
                      (fn-record-make 1 2 3 "<w@example.invalid>" '(72 105 13 10)
                                      '("fn.letters" "fn.test") "archive-w" "content-w"
                                      "evidence-w" 4 5))
                     1))

; -----------------------------------------------------------------------------
; The translation keystone.  Witness: both golden vectors of the old schemas
; are accepted by the frozen decoder, decoded identically by the new one, and
; re-encoded to the same octets.

(assert-event (fn-record-result-okp
               (fn-record-v1-decode-exact *fn-record-schema0-golden-octets*)))
(assert-event (fn-record-result-okp
               (fn-record-v1-decode-exact *fn-record-schema1-golden-octets*)))
(assert-event (equal (fn-record-decode-exact-impl *fn-record-schema1-golden-octets*)
                     (fn-record-v1-decode-exact *fn-record-schema1-golden-octets*)))
(assert-event (equal (fn-record-encode-impl
                      (fn-record-result-record
                       (fn-record-v1-decode-exact *fn-record-schema1-golden-octets*)))
                     *fn-record-schema1-golden-octets*))

; Without the hypothesis: schema-2 octets, which the frozen decoder refuses by
; version and the new one accepts, separate the two decoders; and a refused
; input does not re-encode to itself.
(assert-event (not (fn-record-result-okp
                    (fn-record-v1-decode-exact *fn-record-schema2-golden-octets*))))
(assert-event (not (equal (fn-record-decode-exact-impl *fn-record-schema2-golden-octets*)
                          (fn-record-v1-decode-exact *fn-record-schema2-golden-octets*))))

(must-fail
 (defthm p6-teeth-identically-without-acceptance
   (equal (fn-record-decode-exact-impl octets)
          (fn-record-v1-decode-exact octets))))

(must-fail
 (defthm p6-teeth-translation-without-acceptance
   (equal (fn-record-encode-impl
           (fn-record-result-record (fn-record-v1-decode-exact octets)))
          octets)))
