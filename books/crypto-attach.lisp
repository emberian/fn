; fn: the realiser of the two digest seams.
;
; `books/crypto-seam.lisp' constrains `fn-digest' and `books/frame-octets.lisp'
; constrains `fn-frame-digest'.  A constrained function has no executable
; counterpart, so before this book every term mentioning either one was
; un-evaluable: the served path could not digest anything, the AUTHINFO
; credential had to hold its secret in the clear (board note OB-AUTH-DIGEST),
; and the host computed the content identity in Python and in host Lisp, which
; is the twin AGENTS.md's one-owner rule forbids.  This book attaches
; `fn-sha256' (books/sha256.lisp) to both seams.
;
; WHAT THE ATTACHMENT CHANGES IN THE LOGIC: nothing.  `defattach' introduces
; no axiom.  It obliges ACL2 to prove that the attached function satisfies
; EVERY constraint the `encapsulate' states -- here, the two shape theorems
; re-proved just below for `fn-sha256' -- and in exchange makes ground terms
; over the constrained function evaluate.  Every theorem that was true of the
; seam before is the same theorem now, with the same hypotheses.
;
; WHAT REMAINS ASSUMED: collision resistance and preimage resistance, which
; are A-CRYPTO (specs/failures.md, books/assumptions.lisp).  They were never
; consequences of the seam and are not consequences of the attachment.  The
; seam's own local witness is the constant zero digest, under which every
; preimage collides, and `tests/acl2/crypto-seam-tests.lisp' still attaches a
; colliding toy realiser to make that visible.  A later `defattach' for the
; same function replaces an earlier one, so a test book re-attaching a toy
; realiser after including this one gets the toy, which is what those books
; intend and what keeps their collision witnesses reachable.
;
; SCOPE.  Signature verification is NOT touched.  `fn-sig-sign',
; `fn-sig-verify' and `fn-sig-public-key' (crypto-seam) and
; `fn-anchor-sig-verify' (books/anchor.lisp) stay constrained: Ed25519 in
; logic is a different packet, and this book must not be read as having made
; a signature executable.  `fn-anchor-leaf-digest' is also left constrained;
; attaching it is a one-line follow-on once its cluster's owner wants it.

(in-package "ACL2")
(include-book "crypto-seam")
(include-book "frame-octets")
(include-book "sha256")

(local (in-theory (enable fn-cbor-codec-vocabulary
                          fn-cbor-invariants-vocabulary
                          fn-crypto-seam-internals)))

; -----------------------------------------------------------------------------
; The bridge.  `books/sha256.lisp' sits below the codecs and carries its own
; octet-list recognizer so that it depends on no other fn book; the two are
; the same predicate, and that is proved here rather than assumed.

(local
 (defthm fn-sha256-cbor-octet-listp-is-sha256-octet-listp
   (equal (fn-cbor-octet-listp xs)
          (fn-sha256-octet-listp xs))))

; -----------------------------------------------------------------------------
; The constraints, discharged for the attachment.
;
; These are exactly the `defthm's inside the two `encapsulate's, with
; `fn-sha256' in place of the constrained function.  `defattach' re-generates
; them as proof obligations; proving them here as named events is what makes
; the discharge citable rather than something that happened inside an event.

(defthm fn-sha256-satisfies-fn-digest-shape
  ; crypto-seam's `fn-digest-shape'.
  (fn-digest-octetsp (fn-sha256 m))
  :hints (("Goal" :in-theory (enable fn-digest-octetsp))))

(defthm fn-sha256-satisfies-fn-frame-digest-octet-listp
  ; frame-octets' `fn-frame-digest-octet-listp'.
  (fn-cbor-octet-listp (fn-sha256 octets)))

(defthm fn-sha256-satisfies-fn-frame-digest-length
  ; frame-octets' `fn-frame-digest-length'.  *fn-frame-trailer-octets* is 32.
  (equal (len (fn-sha256 octets)) *fn-frame-trailer-octets*))

; No constraint of either `encapsulate' is stronger than 32 octets: the seams
; ask for shape and for nothing else, which is why the discharge is three
; lines and not a research programme.  If a later constraint is added that
; SHA-256 does not provide, that is a finding about the seam to be recorded,
; never a constraint to weaken.

; -----------------------------------------------------------------------------
; The attachments.

(defattach fn-digest fn-sha256)
(defattach fn-frame-digest fn-sha256)

; -----------------------------------------------------------------------------
; The coercion is the identity on the domain fn actually digests.
;
; `fn-sha256' is total because `fn-digest' is constrained over ANY object, so
; it fixes its argument to octets first.  Every preimage fn digests is an
; octet list -- the tagged preimages of crypto-seam, the protected prefix of a
; frame, the subject and obligation preimages of books/identity.lisp -- and on
; those the fixer does nothing.  Without this theorem, "fn-digest is SHA-256"
; would be a claim about a coerced argument rather than about the octets the
; caller passed.

(defthm fn-sha256-fix-octets-is-identity
  (implies (fn-cbor-octet-listp m)
           (equal (fn-sha256-fix-octets m) m)))

(defthm fn-sha256-is-sha256-of-the-octets
  (implies (fn-cbor-octet-listp m)
           (equal (fn-sha256 m) (fn-sha256-of-octets m)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; What leaves this book is the three constraint discharges -- the shape facts
; every caller of a digest already had from the seam -- and the two identity
; facts that say the coercion is invisible on octet lists.

; The bridge equality is `local': exported, it would rewrite every
; fn-cbor-octet-listp goal in the tree into sha256's vocabulary.
