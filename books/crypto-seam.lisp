; fn: the cryptographic seam.
;
; This book introduces the digest and the signature scheme that every identity,
; statement and policy definition depends on.  Both are ACL2 constrained
; functions (`encapsulate` with a local witness).  The only facts ACL2 knows
; about them are the shape constraints below and one correctness property: a
; signature produced by the seam's signer over message m under seed sk verifies
; under the public key of sk.  Nothing here says that a digest is collision
; resistant, that a signature is unforgeable, or that any deployed primitive
; realises the seam.  Those are A-CRYPTO (specs/failures.md) and are NOT
; proved; see specs/identity.md.
;
; Shape (the deployed profile is a D09 proposal, planning/decision-packet-d09-d11.md):
;   digest       : any object -> 32 octets            (blake3 / SHA-256 shaped)
;   seed         : 32 octets                          (ed25519 seed; ML-DSA-65 derives from it)
;   public key   : 1..4096 octets                     (ed25519 32; hybrid 32 + 1952)
;   signature    : 0..4096 octets                     (ed25519 64; hybrid 64 + 3309)
;
; Mirrors: ~/dev/breadstuffs/blocklace/src/pq.rs (seed-derived hybrid key,
; BLOCK_PQ_CTX domain separation), signer.rs (`HybridBlockSigner`), and the
; Lean seam shapes `SigChecker` (Dregg2/Authority/BiscuitGraph.lean:55) and
; `SigScheme.verify` (Dregg2/Crypto/CapabilityChain.lean:65), where the
; verifier is an opaque oracle that laws only READ.
;
; Domain separation: every preimage that is digested or signed starts with a
; length-prefixed tag "fn-<purpose>-v1"; `fn-digest-tagged-preimage` is proved
; to separate the tag from the message unambiguously.

(in-package "ACL2")
(include-book "records-invariants")


;; Convergence: the codecs cluster withdraws its proof vocabulary on export;
;; re-open it locally (agreed on the deputy board, codecs ANSWER to substrate).
(local (in-theory (enable fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary fn-record-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; Shapes

(defconst *fn-digest-octets* 32)
(defconst *fn-sig-seed-octets* 32)
(defconst *fn-sig-max-public-key-octets* 4096)
(defconst *fn-sig-max-signature-octets* 4096)
(defconst *fn-digest-max-tag-octets* 64)

(defun fn-digest-octetsp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (equal (len x) *fn-digest-octets*)))

(defun fn-sig-seed-p (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (equal (len x) *fn-sig-seed-octets*)))

(defun fn-sig-public-key-p (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (consp x)
       (<= (len x) *fn-sig-max-public-key-octets*)))

(defun fn-sig-signature-p (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (<= (len x) *fn-sig-max-signature-octets*)))

(defun fn-digest-tagp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (consp x)
       (<= (len x) *fn-digest-max-tag-octets*)))

(defthm fn-digest-octetsp-implies-octet-listp
  (implies (fn-digest-octetsp x)
           (and (fn-cbor-octet-listp x)
                (true-listp x)
                (equal (len x) 32))))

; -----------------------------------------------------------------------------
; The digest.  Constraint: shape only.  The local witness is a constant, which
; makes the point visible: the constraints are satisfied by a realiser under
; which every preimage collides.  Equal digests therefore imply nothing about
; the preimages in this logic.

(encapsulate
  (((fn-digest *) => *))
  (local (defun fn-digest (m)
           (declare (ignore m))
           (make-list 32 :initial-element 0)))
  (defthm fn-digest-shape
    (fn-digest-octetsp (fn-digest m))))

(defthm fn-digest-is-octet-list
  (and (fn-cbor-octet-listp (fn-digest m))
       (true-listp (fn-digest m))
       (equal (len (fn-digest m)) 32))
  :hints (("Goal" :use fn-digest-shape
           :in-theory (disable fn-digest-shape))))

; -----------------------------------------------------------------------------
; The signature scheme.  Three constrained functions and one correctness
; property.  The local witness publishes the seed as the public key and uses
; the seed as the signature, so under the witness anyone can sign for anyone:
; unforgeability is exactly what this seam does not carry.

(encapsulate
  (((fn-sig-public-key *) => *)
   ((fn-sig-sign * *) => *)
   ((fn-sig-verify * * *) => *))
  (local (defun fn-sig-public-key (sk)
           (if (fn-sig-seed-p sk) sk (make-list 32 :initial-element 0))))
  (local (defun fn-sig-sign (sk m)
           (declare (ignore m))
           (if (fn-sig-seed-p sk) sk nil)))
  (local (defun fn-sig-verify (pk m sig)
           (declare (ignore m))
           (equal pk sig)))
  (defthm fn-sig-public-key-shape
    (fn-sig-public-key-p (fn-sig-public-key sk)))
  (defthm fn-sig-signature-shape
    (fn-sig-signature-p (fn-sig-sign sk m)))
  (defthm fn-sig-verify-is-boolean
    (booleanp (fn-sig-verify pk m sig)))
  (defthm fn-sig-verify-of-sign
    (implies (and (fn-sig-seed-p sk)
                  (fn-cbor-octet-listp m))
             (fn-sig-verify (fn-sig-public-key sk) m (fn-sig-sign sk m)))))

(defthm fn-sig-public-key-is-octet-list
  (and (fn-cbor-octet-listp (fn-sig-public-key sk))
       (true-listp (fn-sig-public-key sk))
       (consp (fn-sig-public-key sk))
       (<= (len (fn-sig-public-key sk)) *fn-sig-max-public-key-octets*))
  :hints (("Goal" :use fn-sig-public-key-shape
           :in-theory (disable fn-sig-public-key-shape))))

(defthm fn-sig-signature-is-octet-list
  (and (fn-cbor-octet-listp (fn-sig-sign sk m))
       (true-listp (fn-sig-sign sk m))
       (<= (len (fn-sig-sign sk m)) *fn-sig-max-signature-octets*))
  :hints (("Goal" :use fn-sig-signature-shape
           :in-theory (disable fn-sig-signature-shape))))

; -----------------------------------------------------------------------------
; Domain-separated preimages.  A tagged preimage is the CBOR byte string of the
; tag followed by the raw message.  The tag item is self-delimiting, so the tag
; and the message are recoverable from the preimage: two different (tag,
; message) pairs never produce the same preimage.  That is the whole content of
; domain separation at the preimage level; whether two different preimages can
; share a digest is A-CRYPTO.

(defun fn-digest-tagged-preimage (tag m)
  (declare (xargs :guard (and (fn-digest-tagp tag)
                              (fn-cbor-octet-listp m))))
  (append (fn-cbor-encode (cons :bytes tag)) m))

(defun fn-digest-tagged (tag m)
  (declare (xargs :guard (and (fn-digest-tagp tag)
                              (fn-cbor-octet-listp m))))
  (fn-digest (fn-digest-tagged-preimage tag m)))

(defthm fn-digest-tagged-shape
  (fn-digest-octetsp (fn-digest-tagged tag m)))

(defthm fn-digest-tagged-is-octet-list
  (and (fn-cbor-octet-listp (fn-digest-tagged tag m))
       (true-listp (fn-digest-tagged tag m))
       (equal (len (fn-digest-tagged tag m)) 32)))

(defthm fn-digest-tagged-preimage-is-octet-list
  (implies (and (fn-digest-tagp tag)
                (fn-cbor-octet-listp m))
           (fn-cbor-octet-listp (fn-digest-tagged-preimage tag m)))
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-digest-tagged-preimage-length
  (implies (fn-digest-tagp tag)
           (equal (len (fn-digest-tagged-preimage tag m))
                  (+ (len (fn-cbor-encode (cons :bytes tag))) (len m)))))

; The tag item decodes off the front of the preimage and leaves exactly the
; message.  Bounded by the one-item decoder's input cap; every preimage in fn
; is far below it.
(defthm fn-digest-tagged-preimage-separates
  (implies (and (fn-digest-tagp tag)
                (fn-cbor-octet-listp m)
                (<= (+ 3 (len tag) (len m)) *fn-cbor-max-input*))
           (equal (fn-cbor-decode (fn-digest-tagged-preimage tag m))
                  (fn-cbor-ok (cons :bytes tag) m)))
  :hints (("Goal"
           :use ((:instance fn-record-cbor-stream-bytes-round-trip
                            (xs tag) (rest m)))
           :in-theory (disable fn-cbor-decode fn-cbor-encode
                               fn-record-cbor-stream-bytes-round-trip))))

(defthm fn-digest-tagged-preimage-injective
  (implies (and (fn-digest-tagp tag1) (fn-cbor-octet-listp m1)
                (fn-digest-tagp tag2) (fn-cbor-octet-listp m2)
                (<= (+ 3 (len tag1) (len m1)) *fn-cbor-max-input*)
                (<= (+ 3 (len tag2) (len m2)) *fn-cbor-max-input*)
                (equal (fn-digest-tagged-preimage tag1 m1)
                       (fn-digest-tagged-preimage tag2 m2)))
           (and (equal tag1 tag2)
                (equal m1 m2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-digest-tagged-preimage-separates
                            (tag tag1) (m m1))
                 (:instance fn-digest-tagged-preimage-separates
                            (tag tag2) (m m2)))
           :in-theory (disable fn-digest-tagged-preimage-separates
                               fn-digest-tagged-preimage
                               fn-cbor-decode fn-cbor-encode))))

; -----------------------------------------------------------------------------
; Hex rendering of digests for hosts, logs and Message-ID-like handles.  It is a
; display helper, not an identity: identity is the octet list.

(defun fn-digest-hex-char (n)
  (declare (xargs :guard (and (natp n) (< n 16))))
  (code-char (if (< n 10) (+ 48 n) (+ 87 n))))

(local (defthm fn-digest-hex-floor-bound
         (implies (and (natp x) (<= x 255))
                  (and (natp (floor x 16)) (< (floor x 16) 16)))
         :hints (("Goal" :in-theory (disable floor)))))

(local (defthm fn-digest-hex-mod-bound
         (implies (natp x)
                  (and (natp (mod x 16)) (< (mod x 16) 16)))
         :hints (("Goal" :in-theory (disable mod)))))

(defun fn-digest-hex-chars (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :guard-hints (("Goal" :in-theory (disable floor mod)))))
  (if (consp octets)
      (cons (fn-digest-hex-char (floor (car octets) 16))
            (cons (fn-digest-hex-char (mod (car octets) 16))
                  (fn-digest-hex-chars (cdr octets))))
    nil))

(defthm fn-digest-hex-chars-are-characters
  (character-listp (fn-digest-hex-chars octets)))

(defun fn-digest-hex (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (coerce (fn-digest-hex-chars octets) 'string))

(defthm fn-digest-hex-chars-length
  (equal (len (fn-digest-hex-chars octets)) (* 2 (len octets))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; The seam exports its constrained functions' shape theorems and the
; preimage separation laws.  The shape recognizers, the tagged preimage and the
; hex helpers are proof vocabulary and are withdrawn.
;
; Only the `:definition' rune is withdrawn, so type prescriptions and
; executable counterparts still decide ground terms.  A book inside this
; cluster that must open one of these enables `fn-crypto-seam-internals' locally.

(deftheory fn-crypto-seam-internals
  '(
    (:d fn-digest-octetsp)
    (:d fn-sig-seed-p)
    (:d fn-sig-public-key-p)
    (:d fn-sig-signature-p)
    (:d fn-digest-tagp)
    (:d fn-digest-tagged-preimage)
    (:d fn-digest-tagged)
    (:d fn-digest-hex-char)
    (:d fn-digest-hex)))

(in-theory (disable fn-crypto-seam-internals))
