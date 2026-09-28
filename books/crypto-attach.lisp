; fn: the realiser of the two digest seams: BLAKE3.
;
; `books/crypto-seam.lisp' constrains `fn-digest' and `books/frame-octets.lisp'
; constrains `fn-frame-digest'.  A constrained function has no executable
; counterpart, so without an attachment every term mentioning either one is
; un-evaluable: the served path could not digest anything, and the host would
; compute identities in Python or host Lisp, the twin AGENTS.md's one-owner
; rule forbids.  This book attaches BLAKE3 to both seams (ember, 2026-09-28:
; BLAKE3 wherever fn chooses the algorithm; SHA-256 only where an RFC puts it
; on the wire, which is RFC 8315's Cancel-Lock hash, books/control-authority.lisp
; and books/cancel-lock.lisp).  The realiser is `fn-blake3-stobj'
; (books/blake3-stobj.lisp, the octets copied once into a buffer and hashed
; in place), attached under `fn-blake3-stobj-is-blake3', the theorem that it
; equals `fn-blake3' (books/blake3.lisp), the list definition, on every
; object.  Every statement below is about `fn-blake3'; the executable is the
; buffer twin.  Until 2026-09-28 the realiser was SHA-256 (`fn-sha256-stobj'):
; the change is store format 10 (every stored digest changes; lane
; format-bump-10 owns the format number and the reader).
;
; WHAT THE ATTACHMENT CHANGES IN THE LOGIC: nothing.  `defattach' introduces
; no axiom.  It obliges ACL2 to prove that the attached function satisfies
; EVERY constraint the `encapsulate' states -- here, the shape theorems
; re-proved just below for `fn-blake3' -- and in exchange makes ground terms
; over the constrained function evaluate.  Every theorem that was true of the
; seam before is the same theorem now, with the same hypotheses.
;
; WHAT REMAINS ASSUMED: collision resistance and preimage resistance, which
; are A-CRYPTO (specs/failures.md, books/assumptions.lisp), now of BLAKE3:
; about 2^-128 per chosen pair (the birthday bound over a 256-bit output) is
; the figure to quote, not the 2^-256 second-preimage one.  They were never
; consequences of the seam and are not consequences of the attachment.  The
; seam's own local witness is the constant zero digest, under which every
; preimage collides, and `tests/acl2/crypto-seam-tests.lisp' still attaches a
; colliding toy realiser to make that visible.  A later `defattach' for the
; same function replaces an earlier one, so a test book re-attaching a toy
; realiser after including this one gets the toy.
;
; SCOPE.  Signature verification is NOT touched.  `fn-sig-sign',
; `fn-sig-verify' and `fn-sig-public-key' (crypto-seam) and
; `fn-anchor-sig-verify' (books/anchor.lisp) stay constrained.

(in-package "ACL2")
(include-book "crypto-seam")
(include-book "frame-octets")
(include-book "blake3")
(include-book "blake3-stobj")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-digest-octetsp))))

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
(defattach fn-frame-digest fn-blake3-stobj)

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
