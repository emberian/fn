; fn: teeth for books/auth-secret.lisp, the AUTHINFO stored-credential scheme.
;
; Everything here runs under the REAL attachment (books/crypto-attach.lisp
; attaches fn-sha256 to fn-digest), so these are digests of actual SHA-256,
; not of a toy realiser.  Read the rejection witnesses accordingly: they are
; evidence on concrete octets, and rejection in general is A-CRYPTO.

(in-package "ACL2")
(include-book "../../books/auth-secret")

(defconst *fn-authsec-t-salt*
  '(17 34 51 68 85 102 119 136 153 170 187 204 221 238 255 0))
(defconst *fn-authsec-t-salt2*
  '(18 34 51 68 85 102 119 136 153 170 187 204 221 238 255 0))
(defconst *fn-authsec-t-secret* (fn-record-string-octets "correct-horse"))
(defconst *fn-authsec-t-other* (fn-record-string-octets "correct-horsf"))
; A macro, not a `defconst': ACL2 refuses to call an ATTACHMENT while
; computing a constant (see :DOC ignored-attachment), so the enrolment has to
; happen inside each `assert-event', where top-level evaluation applies.
; That restriction is itself the point -- a `defconst' over `fn-digest' would
; bake an attachment-dependent value into the logical world.
(defmacro fn-authsec-t-ver ()
  '(fn-authsec-enrol *fn-authsec-t-salt* *fn-authsec-t-secret*))

; -----------------------------------------------------------------------------
; The keystone is reachable and non-degenerate.

(assert-event (fn-authsec-verifierp (fn-authsec-t-ver)))
(assert-event (fn-authsec-checkp (fn-authsec-t-ver) *fn-authsec-t-secret*))

; The check is not the constant T: a one-octet change to the secret fails.
; (A witness.  "Every other secret fails" is second-preimage resistance,
; A-CRYPTO, and is not claimed.)
(assert-event (not (fn-authsec-checkp (fn-authsec-t-ver) *fn-authsec-t-other*)))
(assert-event (not (fn-authsec-checkp (fn-authsec-t-ver) nil)))

; The salt separates: the same secret under a different salt is a different
; verifier and does not check against this one's digest.
(assert-event
 (not (equal (fn-authsec-ver-digest (fn-authsec-t-ver))
             (fn-authsec-ver-digest
              (fn-authsec-enrol *fn-authsec-t-salt2* *fn-authsec-t-secret*)))))

; -----------------------------------------------------------------------------
; Teeth: one violating value per hypothesis of
; `fn-authsec-enrolled-secret-checks'.  Its only hypothesis is the salt's
; shape; the secret hypothesis proved unnecessary and was deleted.

; A 15-octet salt: enrolment still produces a list, but it is not a verifier,
; and the check refuses rather than accepting whatever it is handed.
(defconst *fn-authsec-t-short-salt*
  '(17 34 51 68 85 102 119 136 153 170 187 204 221 238 255))
(assert-event (not (fn-authsec-saltp *fn-authsec-t-short-salt*)))
(assert-event
 (not (fn-authsec-verifierp
       (fn-authsec-enrol *fn-authsec-t-short-salt* *fn-authsec-t-secret*))))
(assert-event
 (not (fn-authsec-checkp
       (fn-authsec-enrol *fn-authsec-t-short-salt* *fn-authsec-t-secret*)
       *fn-authsec-t-secret*)))

; A non-verifier in the slot refuses; the check never defaults to accepting.
(assert-event (not (fn-authsec-checkp nil nil)))
(assert-event (not (fn-authsec-checkp *fn-authsec-t-secret* *fn-authsec-t-secret*)))

; -----------------------------------------------------------------------------
; What the configuration no longer holds.

; The stored verifier is not an octet list, so the slot cannot hold a
; cleartext secret: K2, on a concrete value.
(assert-event (not (fn-cbor-octet-listp (fn-authsec-t-ver))))

; The stored digest is not the secret, and is 32 octets whatever the secret's
; length: K3, on a long secret and a short one.
(assert-event (not (equal (fn-authsec-ver-digest (fn-authsec-t-ver))
                          *fn-authsec-t-secret*)))
(assert-event
 (equal (len (fn-authsec-ver-digest
              (fn-authsec-enrol *fn-authsec-t-salt* (fn-record-string-octets "x"))))
        32))
(assert-event
 (equal (len (fn-authsec-ver-digest
              (fn-authsec-enrol *fn-authsec-t-salt*
                                (fn-record-string-octets
                                 "a-very-much-longer-passphrase-than-the-other-one"))))
        32))

; -----------------------------------------------------------------------------
; Domain separation.  An AUTHINFO digest is the seam's TAGGED digest, so it is
; never the digest of a bare preimage that happens to be the same octets.

(assert-event
 (not (equal (fn-authsec-digest *fn-authsec-t-salt* *fn-authsec-t-secret*)
             (fn-digest (fn-authsec-preimage *fn-authsec-t-salt*
                                             *fn-authsec-t-secret*)))))
(assert-event
 (not (equal (fn-authsec-digest *fn-authsec-t-salt* *fn-authsec-t-secret*)
             (fn-digest-tagged (fn-record-string-octets "fn-subject-v1")
                               (fn-authsec-preimage *fn-authsec-t-salt*
                                                    *fn-authsec-t-secret*)))))

; -----------------------------------------------------------------------------
; The preimage boundary is unambiguous, which is what
; `fn-authsec-preimage-injective' says: with a fixed 16-octet salt, moving an
; octet across the boundary cannot be hidden.  Without the fixed length it
; could be, and this pair shows the concatenation that would collide.
(assert-event
 (equal (append '(1 2) '(3)) (append '(1) '(2 3))))
(assert-event
 (not (equal (fn-authsec-preimage *fn-authsec-t-salt* *fn-authsec-t-secret*)
             (fn-authsec-preimage *fn-authsec-t-salt2* *fn-authsec-t-secret*))))
