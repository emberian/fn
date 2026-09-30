; fn: executable BLAKE3 for the identity digest seam.
;
; fn-digest remains constrained and attached to fn-blake3-stobj. Signature
; seams remain constrained. Frame integrity now has a concrete, closed
; fn-frame-digest definition in frame-octets, with the same BLAKE3 bytes
; computed before this change. It needs no attachment. The shape lemmas
; below remain public for existing consumers of either boundary.
;
; Defattach adds no axiom: the identity attachment discharges its shape
; constraint only. Computing BLAKE3 proves neither collision resistance nor
; preimage resistance. Those remain A-CRYPTO, separately stated in
; assumptions.lisp and specs/failures.md. Pessimistic generic collision work
; for the 256-bit digest is about 2^128 operations; the second-preimage
; figure is not a substitute for that scope. The identity seam's colliding
; toy attachment still witnesses that its shape constraint proves no such
; security property. SHA-256 remains RFC 8315's Cancel-Lock algorithm.

(in-package "ACL2")
(include-book "crypto-seam")
(include-book "frame-octets")
(include-book "blake3")
(include-book "blake3-stobj")

(local (in-theory (enable fn-cbor-codec-vocabulary
                          fn-cbor-invariants-vocabulary
                          fn-crypto-seam-internals)))

; -----------------------------------------------------------------------------
; The bridge.  `books/blake3.lisp' sits below the codecs and carries its own
; octet-list recognizer so that it depends on no other fn book; the two are
; the same predicate, and that is proved here rather than assumed.

(local
 (defthm fn-blake3-cbor-octet-listp-is-b3-octet-listp
   (equal (fn-cbor-octet-listp xs)
          (fn-b3-octet-listp xs))))

; -----------------------------------------------------------------------------
; The constraints, discharged for the attachment.
;
; These are exactly the `defthm's inside the two `encapsulate's, with
; `fn-blake3' in place of the constrained function.

(defthm fn-blake3-satisfies-fn-digest-shape
  ; crypto-seam's `fn-digest-shape'.
  (fn-digest-octetsp (fn-blake3 m))
  :hints (("Goal" :in-theory (enable fn-digest-octetsp))))

(defthm fn-blake3-satisfies-fn-frame-digest-octet-listp
  ; frame-octets' `fn-frame-digest-octet-listp'.
  (fn-cbor-octet-listp (fn-blake3 octets)))

(defthm fn-blake3-satisfies-fn-frame-digest-length
  ; frame-octets' `fn-frame-digest-length'.  *fn-frame-trailer-octets* is 32.
  (equal (len (fn-blake3 octets)) *fn-frame-trailer-octets*))

; No constraint of either `encapsulate' is stronger than 32 octets.  If a
; later constraint is added that BLAKE3 does not provide, that is a finding
; about the seam to be recorded, never a constraint to weaken.

; The same three, for the executable, through `fn-blake3-stobj-is-blake3'.

(defthm fn-blake3-stobj-satisfies-fn-digest-shape
  (fn-digest-octetsp (fn-blake3-stobj m)))

(defthm fn-blake3-stobj-satisfies-fn-frame-digest-octet-listp
  (fn-cbor-octet-listp (fn-blake3-stobj octets)))

(defthm fn-blake3-stobj-satisfies-fn-frame-digest-length
  (equal (len (fn-blake3-stobj octets)) *fn-frame-trailer-octets*))

; -----------------------------------------------------------------------------
; The attachments.

(defattach fn-digest fn-blake3-stobj)

; -----------------------------------------------------------------------------
; The coercion is the identity on the domain fn actually digests: on an
; octet list, `fn-blake3' is BLAKE3 of exactly those octets.

(defthm fn-b3-fix-octets-is-identity
  (implies (fn-cbor-octet-listp m)
           (equal (fn-b3-fix-octets m) m)))

(defthm fn-blake3-is-blake3-of-the-octets
  (implies (fn-cbor-octet-listp m)
           (equal (fn-blake3 m) (fn-b3-hash *fn-b3-iv* 0 m)))
  :rule-classes nil
  :hints (("Goal" :use fn-blake3-of-octets)))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

(deftheory fn-crypto-attach-internals
  '(fn-b3-fix-octets-is-identity))

(in-theory (disable fn-crypto-attach-internals))
