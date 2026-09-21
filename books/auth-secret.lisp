; fn: the AUTHINFO stored-credential scheme (RFC 4643 section 2.3).
;
; Before this book the AUTHINFO credential held its secret IN THE CLEAR and
; the comparison was `equal' on the octets, for a reason recorded in
; books/nntp-auth.lisp and on the deputy board as OB-AUTH-DIGEST: fn's only
; digest was a constrained function with no attachment, so a digest on the
; served path would have made `fn-served-step' non-executable, and deriving
; it in Python is refused by the one-owner rule.  `books/crypto-attach.lisp'
; removed that wall.  This book is the scheme; `books/nntp-auth.lisp' calls
; `fn-authsec-checkp' where it used to call `equal'.
;
; THE SCHEME, exactly (specs/nntp.md, "The stored AUTHINFO credential"):
;
;   salt      : exactly 16 octets, per credential, chosen at enrolment
;   preimage  : salt || secret                (the salt's length is fixed, so
;                                              the boundary is unambiguous;
;                                              see -preimage-injective below)
;   stored    : (:fn-authsec-v1 salt (fn-digest-tagged "fn-authinfo-v1"
;                                                      preimage))
;   check     : the supplied octets pass iff re-deriving the digest under the
;               stored salt yields the stored digest
;
; The tag is the crypto seam's domain separation: an AUTHINFO digest and a
; content identity digest never share a preimage, whatever their messages
; (books/crypto-seam.lisp, `fn-digest-tagged-preimage-injective').
;
; WHAT IS PROVED AND WHAT IS NOT.  The enrolled secret checks; the verifier
; is a structured value rather than an octet list; its digest has fixed length;
; and the preimage encoding recovers (salt, secret).  These are shape/encoding
; facts, not confidentiality or password-guessing resistance.  The concrete
; scheme uses one fast tagged SHA-256 computation per guess, with no tunable
; work factor.  A salt does not make a low-entropy password hard to guess.
; No theorem here proves distinct secrets have distinct digests; the seam's
; local constant-digest witness makes every secret pass.  The test book's
; concrete rejection witness is evidence for those inputs, not a universal
; rejection or secrecy theorem.  See specs/nntp.md for the hardening boundary.
;
; This book also does not make AUTHINFO USER/PASS safe on an unprotected
; connection: the secret still crosses the wire in the clear, which is why
; RFC 4643 section 2.3.2 asks for a protected channel and why
; `fn-auth-config-protected-onlyp' answers 483 until STARTTLS has run.  What
; changes is what an operator's configuration file, and a stolen copy of it,
; contains.

(in-package "ACL2")
(include-book "crypto-attach")

(local (in-theory (enable fn-cbor-codec-vocabulary
                          fn-cbor-invariants-vocabulary
                          fn-crypto-seam-internals)))

; -----------------------------------------------------------------------------
; Shapes

(defconst *fn-authsec-salt-octets* 16)
(defconst *fn-authsec-tag* (fn-record-string-octets "fn-authinfo-v1"))

(defun fn-authsec-saltp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (equal (len x) *fn-authsec-salt-octets*)))

; A total coercion, so every function below has `:guard t' and the served
; path never needs a guard obligation re-established at a call site.
(defun fn-authsec-octets (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (if (fn-cbor-octetp (car x)) (car x) 0)
            (fn-authsec-octets (cdr x)))
    nil))

(defthm fn-authsec-octets-is-octet-list
  (and (fn-cbor-octet-listp (fn-authsec-octets x))
       (true-listp (fn-authsec-octets x))))

(defthm fn-authsec-octets-is-identity-on-octets
  (implies (fn-cbor-octet-listp x)
           (equal (fn-authsec-octets x) x)))

(defthm fn-authsec-len-of-octets
  (equal (len (fn-authsec-octets x)) (len x)))

; -----------------------------------------------------------------------------
; The preimage and the digest

(defun fn-authsec-preimage (salt secret)
  ; salt || secret, both read as octets.
  (declare (xargs :guard t))
  (append (fn-authsec-octets salt) (fn-authsec-octets secret)))

(defthm fn-authsec-preimage-is-octet-list
  (fn-cbor-octet-listp (fn-authsec-preimage salt secret)))

(defthm fn-authsec-len-of-preimage
  (equal (len (fn-authsec-preimage salt secret))
         (+ (len salt) (len secret))))

; The salt's length is fixed, so the preimage is not the ambiguous
; concatenation the tagged-preimage laws warn about: (salt, secret) is
; recoverable from it.  Without this, a short salt and a long secret could
; produce the same preimage as a long salt and a short one, and one
; credential's digest would authenticate another's secret.
(local
 (defun fn-authsec-two-list-induction (a b)
   (declare (xargs :guard t))
   (if (and (consp a) (consp b))
       (fn-authsec-two-list-induction (cdr a) (cdr b))
     (list a b))))

(local
 (defthm fn-authsec-append-equal-with-equal-lengths
   (implies (and (true-listp a) (true-listp b)
                 (equal (len a) (len b))
                 (equal (append a x) (append b y)))
            (and (equal a b) (equal x y)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-authsec-two-list-induction a b)))))

(defthm fn-authsec-preimage-injective
  (implies (and (fn-authsec-saltp s1) (fn-cbor-octet-listp p1)
                (fn-authsec-saltp s2) (fn-cbor-octet-listp p2)
                (equal (fn-authsec-preimage s1 p1)
                       (fn-authsec-preimage s2 p2)))
           (and (equal s1 s2) (equal p1 p2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-authsec-append-equal-with-equal-lengths
                            (a s1) (b s2) (x p1) (y p2))))))

(defun fn-authsec-digest (salt secret)
  ; The stored digest: the crypto seam's tagged digest of salt || secret.
  (declare (xargs :guard t))
  (fn-digest-tagged *fn-authsec-tag* (fn-authsec-preimage salt secret)))

(defthm fn-authsec-digest-shape
  (and (fn-cbor-octet-listp (fn-authsec-digest salt secret))
       (true-listp (fn-authsec-digest salt secret))
       (equal (len (fn-authsec-digest salt secret)) 32)))

; -----------------------------------------------------------------------------
; The stored verifier

(defun fn-authsec-enrol (salt secret)
  ; What the configuration stores for a credential.  The secret is an input
  ; to this function and appears in no field of its result.
  (declare (xargs :guard t))
  (list :fn-authsec-v1 (fn-authsec-octets salt) (fn-authsec-digest salt secret)))

(defun fn-authsec-verifierp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 3)
       (equal (car x) :fn-authsec-v1)
       (fn-authsec-saltp (car (cdr x)))
       (fn-cbor-octet-listp (car (cdr (cdr x))))
       (equal (len (car (cdr (cdr x)))) 32)))

(defun fn-authsec-ver-salt (x)
  (declare (xargs :guard t))
  (if (and (consp x) (consp (cdr x))) (car (cdr x)) nil))

(defun fn-authsec-ver-digest (x)
  (declare (xargs :guard t))
  (if (and (consp x) (consp (cdr x)) (consp (cdr (cdr x))))
      (car (cdr (cdr x)))
    nil))

(defthm fn-authsec-verifierp-of-enrol
  (implies (fn-authsec-saltp salt)
           (fn-authsec-verifierp (fn-authsec-enrol salt secret))))

; `local': an enabled equality between two one-argument applications is
; proof vocabulary, not an export (docs/proof-style.md section 2).
(local
 (defthm fn-authsec-ver-salt-of-enrol
   (equal (fn-authsec-ver-salt (fn-authsec-enrol salt secret))
          (fn-authsec-octets salt))))

(defthm fn-authsec-ver-digest-of-enrol
  (equal (fn-authsec-ver-digest (fn-authsec-enrol salt secret))
         (fn-authsec-digest salt secret)))

; The verifier reassembled from the two fields the operator's file stores.
; `fn principal set-password' writes what `fn-authsec-enrol' produced and
; the owner reads the two fields back at start-up; this is the ONLY place
; the stored shape is rebuilt, so the host never writes the tag or the
; layout and `fn-authsec-enrol' and this function cannot drift
; (fn-authsec-enrol-is-a-verifier-of-its-fields).
(defun fn-authsec-verifier (salt digest)
  (declare (xargs :guard t))
  (list :fn-authsec-v1 (fn-authsec-octets salt) (fn-authsec-octets digest)))

(defthm fn-authsec-enrol-is-a-verifier-of-its-fields
  (equal (fn-authsec-enrol salt secret)
         (fn-authsec-verifier salt (fn-authsec-digest salt secret)))
  :hints (("Goal" :in-theory (e/d (fn-authsec-enrol fn-authsec-verifier)
                                  (fn-authsec-digest fn-authsec-octets))))
  :rule-classes nil)

(defthm fn-authsec-verifierp-of-fn-authsec-verifier
  (implies (and (fn-authsec-saltp salt)
                (fn-cbor-octet-listp digest)
                (equal (len digest) 32))
           (fn-authsec-verifierp (fn-authsec-verifier salt digest)))
  :hints (("Goal" :in-theory (e/d (fn-authsec-verifierp fn-authsec-verifier
                                   fn-authsec-saltp)
                                  nil))))

(defun fn-authsec-checkp (ver supplied)
  ; The whole of the AUTHINFO password comparison.  A function of the stored
  ; verifier and the supplied octets; it reads no secret, because the
  ; verifier holds none.
  (declare (xargs :guard t))
  (and (fn-authsec-verifierp ver)
       (equal (fn-authsec-digest (fn-authsec-ver-salt ver) supplied)
              (fn-authsec-ver-digest ver))
       t))

(defthm fn-authsec-checkp-is-boolean
  (booleanp (fn-authsec-checkp ver supplied)))

; -----------------------------------------------------------------------------
; Keystones

; K1.  The enrolled secret authenticates.  Without it the scheme could reject
; everyone and satisfy every other theorem here.
; The secret needs no hypothesis: `fn-authsec-octets' is total and enrolment
; and checking coerce identically, so the round trip holds for any object the
; wire could hand us.  A `fn-cbor-octet-listp' hypothesis here proved
; unnecessary and was deleted rather than carried.
(defthm fn-authsec-enrolled-secret-checks
  (implies (fn-authsec-saltp salt)
           (fn-authsec-checkp (fn-authsec-enrol salt secret) secret)))

; K2.  The stored verifier is not a secret.  `fn-auth-credp' recognized the
; stored secret as an octet list (a printable token); a verifier is never an
; octet list, so the configuration slot cannot hold a cleartext secret and a
; book that reads the old slot as one fails to certify rather than silently
; comparing a record with a password.
(defthm fn-authsec-verifier-is-not-octets
  (implies (fn-authsec-verifierp v)
           (not (fn-cbor-octet-listp v))))

; K3.  The stored digest is 32 octets whatever the secret is: a stolen
; configuration reveals neither the secret nor its length.  Stated as the
; agreement of two enrolments under one salt, which is the form that says
; "the secret is not visible through the stored value's shape".
(defthm fn-authsec-stored-shape-is-independent-of-the-secret
  (equal (len (fn-authsec-ver-digest (fn-authsec-enrol salt s1)))
         (len (fn-authsec-ver-digest (fn-authsec-enrol salt s2)))))

; K4.  The check is a function of (salt, supplied) and the stored digest, and
; of nothing else in the verifier: two verifiers agreeing on those two fields
; accept exactly the same octets.  This is what "the host cannot slip a
; second credential past the comparison" means at this layer.
(defthm fn-authsec-checkp-depends-only-on-salt-and-digest
  (implies (and (fn-authsec-verifierp v1)
                (fn-authsec-verifierp v2)
                (equal (fn-authsec-ver-salt v1) (fn-authsec-ver-salt v2))
                (equal (fn-authsec-ver-digest v1) (fn-authsec-ver-digest v2)))
           (equal (fn-authsec-checkp v1 supplied)
                  (fn-authsec-checkp v2 supplied)))
  :rule-classes nil)

; NOT A THEOREM, deliberately: that a secret other than the enrolled one
; fails.  It is second-preimage resistance of the attached digest, A-CRYPTO,
; and under the seam's local witness (a constant digest) it is false.
; tests/acl2/auth-secret-tests.lisp exhibits rejection on concrete octets
; under the real attachment; that is a witness, not a proof.

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

(deftheory fn-authsec-internals
  '((:d fn-authsec-saltp) (:d fn-authsec-octets)
    (:d fn-authsec-preimage) (:d fn-authsec-digest) (:d fn-authsec-enrol)
    (:d fn-authsec-verifierp) (:d fn-authsec-verifier) (:d fn-authsec-ver-salt)
    (:d fn-authsec-ver-digest) (:d fn-authsec-checkp)))

(in-theory (disable fn-authsec-internals))
