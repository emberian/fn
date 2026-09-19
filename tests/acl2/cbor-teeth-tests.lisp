; Teeth for the CBOR codec keystones.
;
; The 2026-09-18 review §5: "Codecs are closed both directions: CBOR and the
; schema-0 record prove decode(encode(v)) = v and encode(decode(b)) = b for
; accepted b, with non-minimal heads rejected at the CBOR level."  Both
; directions are keystones with one hypothesis each, and both hypotheses are
; type recognizers, so each negative case below is a malformed value.

(in-package "ACL2")
(include-book "../../books/cbor-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Reachable, non-degenerate witnesses.
;
; Not a single small value: both major types, both argument-width boundaries,
; and a byte string whose length needs a one-octet argument.  A witness that
; only exercised the shortest head would separate the deterministic profile
; from a permissive decoder by nothing at all.

(defconst *cbor-teeth-small-uint* '(:uint . 23))
(defconst *cbor-teeth-wide-uint* '(:uint . 4294967295))
(defconst *cbor-teeth-bytes*
  '(:bytes 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23))

(assert-event (fn-cbor-valuep *cbor-teeth-small-uint*))
(assert-event (fn-cbor-valuep *cbor-teeth-wide-uint*))
(assert-event (fn-cbor-valuep *cbor-teeth-bytes*))

(assert-event (equal (fn-cbor-encode *cbor-teeth-small-uint*) '(23)))
(assert-event (equal (fn-cbor-encode *cbor-teeth-wide-uint*)
                     '(26 255 255 255 255)))
(assert-event
 (equal (fn-cbor-encode *cbor-teeth-bytes*)
        '(88 24 0 1 2 3 4 5 6 7 8 9 10 11
          12 13 14 15 16 17 18 19 20 21 22 23)))

; Both directions close at each witness.
(assert-event (equal (fn-cbor-decode-exact (fn-cbor-encode *cbor-teeth-small-uint*))
                     (fn-cbor-ok *cbor-teeth-small-uint* nil)))
(assert-event (equal (fn-cbor-decode-exact (fn-cbor-encode *cbor-teeth-wide-uint*))
                     (fn-cbor-ok *cbor-teeth-wide-uint* nil)))
(assert-event (equal (fn-cbor-decode-exact (fn-cbor-encode *cbor-teeth-bytes*))
                     (fn-cbor-ok *cbor-teeth-bytes* nil)))

; And a non-minimal head for the same value is refused rather than accepted
; into a second encoding of one value.
(assert-event (equal (fn-cbor-decode-exact '(24 23)) '(:error :noncanonical)))
(assert-event (equal (fn-cbor-decode-exact '(89 0 24)) '(:error :noncanonical)))

; -----------------------------------------------------------------------------
; Teeth for `fn-cbor-value-round-trip'
;   (implies (fn-cbor-valuep value)
;            (equal (fn-cbor-decode-exact (fn-cbor-encode value))
;                   (fn-cbor-ok value nil)))

; The only hypothesis is a type recognizer, so the case is a malformed value:
; a major type outside the profile.  `fn-cbor-decode-exact' can only ever
; return a :uint or a :bytes value, so it cannot return this one.
(defconst *cbor-teeth-foreign* '(:float . 1))
(assert-event (not (fn-cbor-valuep *cbor-teeth-foreign*)))

(local
 (must-fail
  (defthm cbor-teeth-round-trip-without-valuep
    (equal (fn-cbor-decode-exact (fn-cbor-encode *cbor-teeth-foreign*))
           (fn-cbor-ok *cbor-teeth-foreign* nil)))))

; A second malformed value, this time in range but over the profile bound.
(defconst *cbor-teeth-oversize* '(:uint . 4294967296))
(assert-event (not (fn-cbor-valuep *cbor-teeth-oversize*)))

(local
 (must-fail
  (defthm cbor-teeth-round-trip-without-bound
    (equal (fn-cbor-decode-exact (fn-cbor-encode *cbor-teeth-oversize*))
           (fn-cbor-ok *cbor-teeth-oversize* nil)))))

; -----------------------------------------------------------------------------
; Teeth for `fn-cbor-accepted-input-is-canonical'
;   (implies (fn-cbor-result-okp (fn-cbor-decode-exact octets))
;            (equal (fn-cbor-encode (fn-cbor-result-value (fn-cbor-decode-exact octets)))
;                   octets))

; The hypothesis dropped: a non-minimal head is exactly the input the profile
; refuses, and re-encoding what the refused decode "returned" is not the input.
(defconst *cbor-teeth-noncanonical* '(24 23))
(assert-event
 (not (fn-cbor-result-okp (fn-cbor-decode-exact *cbor-teeth-noncanonical*))))

(local
 (must-fail
  (defthm cbor-teeth-canonical-without-accepted-decode
    (equal (fn-cbor-encode
            (fn-cbor-result-value (fn-cbor-decode-exact *cbor-teeth-noncanonical*)))
           *cbor-teeth-noncanonical*))))
