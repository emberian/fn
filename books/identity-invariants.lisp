; Invariants for content identity and the charge policy.
;
; Three claims carry the v1 profile.
;
;   * Domain separation.  `fn-id-subject-and-obligation-preimages-differ` has
;     no hypotheses: for EVERY payload and EVERY (msgid, subject) pair the two
;     preimages are different octet strings, because the label octets differ.
;     Two kinds of identity therefore cannot share a preimage by construction,
;     which is what ENC-003 asks for.
;
;   * Length prefixing.  Each variable field of a preimage is preceded by its
;     own length as four big-endian octets, and that length is read back out
;     of the preimage below.  A field boundary is a decoded number, not a
;     separator octet that the field might itself contain.
;
;   * The hexadecimal projection is invertible both ways, which is what makes
;     `fn-id-text` a faithful rendering of a canonical identity rather than a
;     lossy label: two different identities cannot produce the same string, so
;     identity collisions are digest collisions and nothing else.  That is the
;     only claim; digest collision resistance itself is A-CRYPTO and is not
;     proved anywhere in this tree.
;
; The charge theorems are the two properties the accounting depends on: a
; charge is always positive (the retention book's `posp` obligation), and it
; never decreases with payload length, so a larger article can never be
; cheaper than a smaller one.

(in-package "ACL2")
(include-book "identity")
(include-book "frame-invariants")
(include-book "cbor-invariants")
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

; KEYSTONE: the value direction.  Every identity is recovered from its text.
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

; KEYSTONE: distinct identities never collide in the text, so a comparison at
; a string boundary is an octet comparison.
(defthm fn-id-hex-octets-injective
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
                (equal (fn-id-hex-octets a) (fn-id-hex-octets b)))
           (equal a b))
  :hints (("Goal" :use ((:instance fn-id-unhex-of-hex-octets (octets a))
                        (:instance fn-id-unhex-of-hex-octets (octets b)))
           :in-theory (disable fn-id-unhex-of-hex-octets)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The string boundary, in both directions

(defthm fn-id-from-text-of-text
  (implies (fn-cbor-octet-listp identity)
           (equal (fn-id-from-text (fn-id-text identity)) identity))
  :hints (("Goal" :in-theory (enable fn-id-text fn-id-from-text))))

(defthm fn-id-text-of-from-text
  (implies (and (fn-id-hex-listp octets)
                (equal (mod (len octets) 2) 0))
           (equal (fn-id-text (fn-id-from-text octets)) octets))
  :hints (("Goal" :in-theory (enable fn-id-text fn-id-from-text))))

(defthm fn-id-text-is-hex-octets
  (implies (fn-cbor-octet-listp identity)
           (and (fn-cbor-octet-listp (fn-id-text identity))
                (fn-id-hex-listp (fn-id-text identity))
                (equal (len (fn-id-text identity)) (* 2 (len identity)))))
  :hints (("Goal" :in-theory (enable fn-id-text))))

(defthm fn-id-text-injective
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
                (equal (fn-id-text a) (fn-id-text b)))
           (equal a b))
  :hints (("Goal" :in-theory (enable fn-id-text)
           :use ((:instance fn-id-hex-octets-injective (a a) (b b)))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Domain separation: the whole point of the v1 profile

; KEYSTONE.  No hypotheses: for every payload and every (msgid, subject) pair
; the two preimages differ, at the fourth octet, because the domain labels
; "fn/subject/v1" and "fn/obligation/v1" differ there.  A subject digest can
; therefore never be an obligation digest by construction; only a SHA-256
; collision could make the two identities meet.
(defthm fn-id-subject-and-obligation-preimages-differ
  (not (equal (fn-id-subject-preimage payload)
              (fn-id-obligation-preimage msgid subject)))
  :hints (("Goal" :in-theory (enable fn-id-subject-preimage
                                     fn-id-subject-prefix
                                     fn-id-obligation-preimage))))

; -----------------------------------------------------------------------------
; Length prefixing: a field boundary is a decoded number

(local
 (defthm fn-id-u32-from-append
   (equal (fn-cbor-u32-from (append (fn-cbor-u32-bytes n) tail))
          (fn-cbor-u32-from (fn-cbor-u32-bytes n)))
   :hints (("Goal" :in-theory (enable fn-cbor-u32-from fn-cbor-u32-bytes)))))

(local
 (defthm fn-id-nthcdr-len-append
   (equal (nthcdr (+ (len a) (nfix k)) (append a b))
          (nthcdr (nfix k) b))
   :hints (("Goal" :induct (append a b)
            :in-theory (enable append len nthcdr)))))

; The payload length is read back out of the subject preimage: 13 label
; octets and the separator, then the four length octets.
(defthm fn-id-subject-preimage-length-is-recoverable
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (equal (fn-cbor-u32-from
                   (nthcdr 14 (append (fn-id-subject-prefix n) payload)))
                  n))
  :hints (("Goal" :in-theory (e/d (fn-id-subject-prefix)
                                  (fn-cbor-u32-bytes fn-cbor-u32-from)))))

; The Message-ID length is read back out of the obligation preimage: 16 label
; octets and the separator, then the four length octets.
(defthm fn-id-obligation-preimage-msgid-length-is-recoverable
  (implies (and (fn-cbor-octet-listp msgid)
                (<= (len msgid) *fn-cbor-max-uint*))
           (equal (fn-cbor-u32-from
                   (nthcdr 17 (fn-id-obligation-preimage msgid subject)))
                  (len msgid)))
  :hints (("Goal" :in-theory (e/d (fn-id-obligation-preimage)
                                  (fn-cbor-u32-bytes fn-cbor-u32-from)))))

; And so is the subject length, past the Message-ID the first prefix measured.
(defthm fn-id-obligation-preimage-subject-length-is-recoverable
  (implies (and (fn-cbor-octet-listp subject)
                (<= (len subject) *fn-cbor-max-uint*))
           (equal (fn-cbor-u32-from
                   (nthcdr (+ 21 (len msgid))
                           (fn-id-obligation-preimage msgid subject)))
                  (len subject)))
  :hints (("Goal" :in-theory (e/d (fn-id-obligation-preimage)
                                  (fn-cbor-u32-bytes fn-cbor-u32-from))
           :use ((:instance fn-id-nthcdr-len-append
                            (a msgid) (k 0)
                            (b (append (fn-cbor-u32-bytes (len subject))
                                       subject)))))))

(defthm fn-id-subject-preimage-octets
  (implies (and (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-cbor-max-uint*))
           (and (fn-cbor-octet-listp (fn-id-subject-preimage payload))
                (equal (len (fn-id-subject-preimage payload))
                       (+ 18 (len payload)))))
  :hints (("Goal" :in-theory (enable fn-id-subject-preimage
                                     fn-id-subject-prefix
                                     fn-cbor-octet-listp))))

(defthm fn-id-obligation-preimage-octets
  (implies (and (fn-cbor-octet-listp msgid)
                (<= (len msgid) *fn-cbor-max-uint*)
                (fn-cbor-octet-listp subject)
                (<= (len subject) *fn-cbor-max-uint*))
           (and (fn-cbor-octet-listp (fn-id-obligation-preimage msgid subject))
                (equal (len (fn-id-obligation-preimage msgid subject))
                       (+ 25 (len msgid) (len subject)))))
  :hints (("Goal" :in-theory (enable fn-id-obligation-preimage
                                     fn-cbor-octet-listp))))

; -----------------------------------------------------------------------------
; The two identities

(defthm fn-id-subject-shape
  (implies (fn-id-digestp digest)
           (and (fn-cbor-octet-listp (fn-id-subject digest))
                (equal (len (fn-id-subject digest)) *fn-id-subject-octets*)
                (fn-id-subjectp (fn-id-subject digest))))
  :hints (("Goal" :in-theory (enable fn-id-subject fn-id-render fn-id-digestp
                                     fn-id-subjectp fn-id-labelledp
                                     fn-cbor-octet-listp fn-cbor-octetp))))

(defthm fn-id-obligation-shape
  (implies (fn-id-digestp digest)
           (and (fn-cbor-octet-listp (fn-id-obligation digest))
                (equal (len (fn-id-obligation digest))
                       *fn-id-obligation-octets*)
                (fn-id-obligationp (fn-id-obligation digest))))
  :hints (("Goal" :in-theory (enable fn-id-obligation fn-id-render
                                     fn-id-digestp fn-id-obligationp
                                     fn-id-labelledp fn-cbor-octet-listp
                                     fn-cbor-octetp))))

(defthm fn-id-subject-injective
  (implies (and (fn-id-digestp a) (fn-id-digestp b)
                (equal (fn-id-subject a) (fn-id-subject b)))
           (equal a b))
  :hints (("Goal" :in-theory (enable fn-id-subject fn-id-render fn-id-digestp)))
  :rule-classes nil)

(defthm fn-id-obligation-injective
  (implies (and (fn-id-digestp a) (fn-id-digestp b)
                (equal (fn-id-obligation a) (fn-id-obligation b)))
           (equal a b))
  :hints (("Goal" :in-theory (enable fn-id-obligation fn-id-render
                                     fn-id-digestp)))
  :rule-classes nil)

; A subject identity can never be mistaken for an obligation identity: the
; labels differ and neither is a prefix of the other.
(defthm fn-id-subject-is-not-an-obligation
  (implies (fn-id-digestp digest)
           (not (fn-id-obligationp (fn-id-subject digest))))
  :hints (("Goal" :in-theory (enable fn-id-subject fn-id-render fn-id-digestp
                                     fn-id-obligationp fn-id-labelledp))))

(defthm fn-id-obligation-is-not-a-subject
  (implies (fn-id-digestp digest)
           (not (fn-id-subjectp (fn-id-obligation digest))))
  :hints (("Goal" :in-theory (enable fn-id-obligation fn-id-render
                                     fn-id-digestp fn-id-subjectp
                                     fn-id-labelledp))))

; A-CRYPTO: the host-facing pair is the specification pair exactly when the
; host supplied the constrained digest of the right preimage.
(defthm fn-id-subject-is-subject-of-payload
  (implies (equal digest (fn-frame-digest (fn-id-subject-preimage payload)))
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
