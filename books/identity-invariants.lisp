; Invariants for content identity and the charge policy.
;
; The hexadecimal projection is proved invertible both ways, which is what
; makes a subject or obligation string a faithful rendering of its digest
; rather than a lossy label: two different digests cannot produce the same
; identity string, so identity collisions are digest collisions and nothing
; else.  That is the only claim; digest collision resistance itself is
; A-CRYPTO and is not proved anywhere in this tree.
;
; The charge theorems are the two properties the accounting depends on: a
; charge is always positive (the retention book's `posp` obligation), and it
; never decreases with payload length, so a larger article can never be
; cheaper than a smaller one.

(in-package "ACL2")
(include-book "identity")
(include-book "frame-invariants")

; This book is about the definitions in `identity`, so it opens them, the
; frame vocabulary and the CBOR list vocabulary locally.
(local (in-theory (enable fn-id-definitions
                          fn-frame-octet-vocabulary
                          fn-frame-fields-vocabulary
                          fn-frame-codec-vocabulary
                          fn-frame-journal-vocabulary
                          fn-frame-invariants-vocabulary
                          fn-cbor-invariants-vocabulary
                          (:d fn-frame-split)
                          (:d fn-frame-u64-bytes))))
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Hexadecimal, both directions

(defthm fn-id-hex-digit-is-a-hex-digit
  (implies (and (natp n) (< n 16))
           (fn-id-hex-digitp (fn-id-hex-digit n)))
  :hints (("Goal" :in-theory (enable fn-id-hex-digit fn-id-hex-digitp))))

(defthm fn-id-hex-value-of-hex-digit
  (implies (and (natp n) (< n 16))
           (equal (fn-id-hex-value (fn-id-hex-digit n)) n))
  :hints (("Goal" :in-theory (enable fn-id-hex-digit fn-id-hex-value))))

(defthm fn-id-hex-digit-of-hex-value
  (implies (fn-id-hex-digitp octet)
           (equal (fn-id-hex-digit (fn-id-hex-value octet)) octet))
  :hints (("Goal" :in-theory (enable fn-id-hex-digit fn-id-hex-value
                                     fn-id-hex-digitp))))

(defthm fn-id-hex-octets-are-hex
  (implies (fn-cbor-octet-listp octets)
           (fn-id-hex-listp (fn-id-hex-octets octets)))
  :hints (("Goal" :in-theory (e/d (fn-id-hex-octets fn-id-hex-listp
                                   fn-cbor-octet-listp fn-cbor-octetp)
                                  (floor mod)))))

(defthm fn-id-hex-octets-are-octets
  (implies (fn-cbor-octet-listp octets)
           (fn-cbor-octet-listp (fn-id-hex-octets octets)))
  :hints (("Goal" :in-theory (e/d (fn-id-hex-octets fn-id-hex-digit
                                   fn-cbor-octet-listp fn-cbor-octetp)
                                  (floor mod)))))

(defthm fn-id-hex-octets-length
  (equal (len (fn-id-hex-octets octets)) (* 2 (len octets)))
  :hints (("Goal" :in-theory (enable fn-id-hex-octets))))

; KEYSTONE: the value direction.  Every digest is recovered from its hex.
(defthm fn-id-unhex-of-hex-octets
  (implies (fn-cbor-octet-listp octets)
           (equal (fn-id-unhex (fn-id-hex-octets octets)) octets))
  :hints (("Goal" :in-theory (e/d (fn-id-unhex fn-id-hex-octets
                                   fn-cbor-octet-listp fn-cbor-octetp)
                                  (floor mod)))))

; KEYSTONE: the byte direction.  An accepted lowercase hex string of even
; length is the only spelling of the octets it denotes.
; A digit's value is a nibble.  Stated once so that the quotient and
; remainder of `16a + b` below are rewritten rather than computed by opening
; `floor` and `mod` on every pair of octets.

(defthm fn-id-hex-value-natp
  (implies (fn-id-hex-digitp octet) (natp (fn-id-hex-value octet)))
  :hints (("Goal" :in-theory (enable fn-id-hex-value fn-id-hex-digitp)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-id-hex-value-bound
  (implies (fn-id-hex-digitp octet) (< (fn-id-hex-value octet) 16))
  :hints (("Goal" :in-theory (enable fn-id-hex-value fn-id-hex-digitp)))
  :rule-classes :linear)

(local
 (defthm fn-id-mod-16
   (implies (and (natp a) (natp b) (< b 16))
            (equal (mod (+ (* 16 a) b) 16) b))))

(local
 (defthm fn-id-floor-16
   (implies (and (natp a) (natp b) (< b 16))
            (equal (floor (+ (* 16 a) b) 16) a))
   :hints (("Goal" :in-theory (disable floor mod)
            :use ((:instance floor-mod-elim (x (+ (* 16 a) b)) (y 16))
                  fn-id-mod-16)))))

(defthm fn-id-hex-octets-of-unhex
  (implies (and (fn-id-hex-listp octets)
                (equal (mod (len octets) 2) 0))
           (equal (fn-id-hex-octets (fn-id-unhex octets)) octets))
  :hints (("Goal" :induct (fn-id-unhex octets)
           :in-theory (e/d (fn-id-unhex fn-id-hex-octets fn-id-hex-listp)
                           (floor mod fn-id-hex-digit fn-id-hex-value
                            fn-id-hex-digitp)))))

; KEYSTONE: distinct digests never collide in the identity string, so an
; identity comparison is a digest comparison.
(defthm fn-id-hex-octets-injective
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
                (equal (fn-id-hex-octets a) (fn-id-hex-octets b)))
           (equal a b))
  :hints (("Goal" :use ((:instance fn-id-unhex-of-hex-octets (octets a))
                        (:instance fn-id-unhex-of-hex-octets (octets b)))
           :in-theory (disable fn-id-unhex-of-hex-octets)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The two identities

(defthm fn-id-subject-shape
  (implies (fn-id-digestp digest)
           (and (fn-cbor-octet-listp (fn-id-subject digest))
                (equal (len (fn-id-subject digest)) *fn-id-subject-octets*)
                (fn-id-subjectp (fn-id-subject digest))))
  :hints (("Goal" :in-theory (enable fn-id-subject fn-id-digestp
                                     fn-id-subjectp fn-id-labelledp))))

(defthm fn-id-obligation-shape
  (implies (fn-id-digestp digest)
           (and (fn-cbor-octet-listp (fn-id-obligation digest))
                (equal (len (fn-id-obligation digest))
                       *fn-id-obligation-octets*)
                (fn-id-obligationp (fn-id-obligation digest))))
  :hints (("Goal" :in-theory (enable fn-id-obligation fn-id-digestp
                                     fn-id-obligationp fn-id-labelledp))))

(defthm fn-id-subject-injective
  (implies (and (fn-id-digestp a) (fn-id-digestp b)
                (equal (fn-id-subject a) (fn-id-subject b)))
           (equal a b))
  :hints (("Goal" :in-theory (enable fn-id-subject fn-id-digestp)
           :use ((:instance fn-id-hex-octets-injective
                            (a a) (b b)))))
  :rule-classes nil)

(defthm fn-id-obligation-injective
  (implies (and (fn-id-digestp a) (fn-id-digestp b)
                (equal (fn-id-obligation a) (fn-id-obligation b)))
           (equal a b))
  :hints (("Goal" :in-theory (enable fn-id-obligation fn-id-digestp)
           :use ((:instance fn-id-hex-octets-injective
                            (a a) (b b)))))
  :rule-classes nil)

; A subject identity can never be mistaken for an obligation identity: the
; labels differ in their first octet and neither is a prefix of the other.
(defthm fn-id-subject-is-not-an-obligation
  (implies (fn-id-digestp digest)
           (not (fn-id-obligationp (fn-id-subject digest))))
  :hints (("Goal" :in-theory (enable fn-id-subject fn-id-digestp
                                     fn-id-obligationp fn-id-labelledp))))

(defthm fn-id-obligation-is-not-a-subject
  (implies (fn-id-digestp digest)
           (not (fn-id-subjectp (fn-id-obligation digest))))
  :hints (("Goal" :in-theory (enable fn-id-obligation fn-id-digestp
                                     fn-id-subjectp fn-id-labelledp))))

; The preimage keeps the Message-ID and the subject apart with one octet that
; neither of them can contain, so no pair of distinct (msgid, subject) inputs
; whose parts are printable produces the same preimage by re-splitting.
(defthm fn-id-obligation-preimage-octets
  (implies (and (fn-cbor-octet-listp msgid) (fn-cbor-octet-listp subject))
           (and (fn-cbor-octet-listp (fn-id-obligation-preimage msgid subject))
                (equal (len (fn-id-obligation-preimage msgid subject))
                       (+ 1 (len msgid) (len subject)))))
  :hints (("Goal" :in-theory (enable fn-id-obligation-preimage))))

; A-CRYPTO: the host-facing pair is the specification pair exactly when the
; host supplied the constrained digest of the right preimage.
(defthm fn-id-subject-is-subject-of-payload
  (implies (equal digest (fn-frame-digest payload))
           (equal (fn-id-subject digest)
                  (fn-id-subject-of-payload payload)))
  :hints (("Goal" :in-theory (enable fn-id-subject-of-payload))))

(defthm fn-id-obligation-is-obligation-of
  (implies (equal digest
                  (fn-frame-digest (fn-id-obligation-preimage msgid subject)))
           (equal (fn-id-obligation digest)
                  (fn-id-obligation-of msgid subject)))
  :hints (("Goal" :in-theory (enable fn-id-obligation-of))))

; -----------------------------------------------------------------------------
; Charge policy

; KEYSTONE: every charge is a positive integer, which is what the retention
; accounting's `posp` obligation needs.
(defthm fn-charge-for-payload-posp
  (posp (fn-charge-for-payload length))
  :hints (("Goal" :in-theory (enable fn-charge-for-payload)))
  :rule-classes (:rewrite :type-prescription))

; KEYSTONE: a longer payload is never charged less than a shorter one.
(defthm fn-charge-for-payload-monotone
  (implies (and (natp m) (natp n) (<= m n))
           (<= (fn-charge-for-payload m) (fn-charge-for-payload n)))
  :hints (("Goal" :in-theory (enable fn-charge-for-payload)))
  :rule-classes :linear)

; The store's own payload cap keeps every charge inside the record's uint32
; field, so the policy cannot produce a charge the record grammar rejects.
(defthm fn-charge-for-payload-fits-uint32
  (implies (and (natp length) (<= length 32768))
           (<= (fn-charge-for-payload length) *fn-cbor-max-uint*))
  :hints (("Goal" :in-theory (enable fn-charge-for-payload)))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; Export theory.
;
; The keystones leave this book enabled: the hex round trips
; (`fn-id-unhex-of-hex-octets', `fn-id-hex-octets-of-unhex'), the two shape
; theorems, the domain separation facts and the charge properties.  The
; digit-level arithmetic and `fn-id-subject-is-subject-of-payload' (an
; accessor equality) are proof vocabulary.

(deftheory fn-id-invariants-vocabulary
  '(    fn-id-hex-digit-is-a-hex-digit fn-id-hex-value-of-hex-digit
    fn-id-hex-digit-of-hex-value fn-id-hex-value-natp
    fn-id-hex-value-bound fn-id-subject-is-subject-of-payload))

(in-theory (disable fn-id-hex-digit-is-a-hex-digit fn-id-hex-value-of-hex-digit
             fn-id-hex-digit-of-hex-value fn-id-hex-value-natp
             fn-id-hex-value-bound fn-id-subject-is-subject-of-payload))
