;; fn: the subject identity of the octet buffer, through the digest seam
;; (lane blake3-digest, 2026-09-28; replaces the deleted SHA-256 buffer book's
;; `fn-shb-subject-id', which named SHA-256 directly).  Prefix `fn-sidb-'.
;;
;; The served POST's payload sits in the octet buffer `fn-octets'
;; (books/octets-stobj.lisp).  Its subject identity (books/identity.lisp
;; `fn-id-subject-of-payload') is `fn-id-subject' of the frame digest of the
;; subject preimage: the fixed head for the payload's length, then the
;; payload.  Here the digest is `fn-frame-digest-buffer' of that head and the
;; buffer (books/frame-digest-buffer.lisp): the constrained function, not a
;; named algorithm, so the identity is stated against the assumption it rests
;; on (A-CRYPTO) and the algorithm is the attachment's (BLAKE3,
;; `fn-blake3-of-prefixed-buffer-any', by books/frame-digest-buffer.lisp's
;; `defattach').
;;
;; KEYSTONE `fn-sidb-subject-id-is-id-subject-of-payload': the buffer identity
;; is `fn-id-subject-of-payload' of the buffer's octets, with no hypothesis
;; beyond the length bound the preimage's head needs.

(in-package "ACL2")
(include-book "frame-digest-buffer")
(include-book "identity")

(local
 (defthm fn-sidb-true-listp-of-subject-prefix
   (true-listp (fn-id-subject-prefix n))
   :hints (("Goal" :in-theory (enable fn-id-subject-prefix fn-cbor-u32-bytes)))))

(local
 (defthm fn-sidb-digestp-of-frame-digest
   (fn-id-digestp (fn-frame-digest x))
   :hints (("Goal" :in-theory (enable fn-id-digestp)))))

(defun fn-sidb-subject-id (fn-octets)
  ; `fn-id-subject-of-payload' with the payload in the buffer.
  (declare (xargs :stobjs fn-octets
                  :guard (<= (fn-octets-len fn-octets) *fn-cbor-max-uint*)))
  (fn-id-subject
   (fn-frame-digest-buffer (fn-id-subject-prefix (fn-octets-len fn-octets))
                           fn-octets)))

(defthm fn-sidb-subject-id-is-id-subject-of-payload
  ; KEYSTONE: the buffer identity is the specification's identity of the
  ; buffer's octets.
  (equal (fn-sidb-subject-id fn-octets)
         (fn-id-subject-of-payload fn-octets))
  :hints (("Goal" :in-theory (enable fn-id-subject-of-payload fn-id-subject-preimage))))

;; The entry the served POST calls (host/native/io.lisp fnn-subject-id-buffer
;; through fnn-core): the identity when the buffer's length is in the CBOR uint
;; domain, else NIL.  Guard T and guard-verified, so the host's call runs the
;; compiled code (qual-e747dbcc A4: an unverified caller of a stobj updater is
;; invariant risk).
(defun fn-sidb-subject-id-bounded (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (<= (fn-octets-len fn-octets) *fn-cbor-max-uint*)
      (fn-sidb-subject-id fn-octets)
    nil))

(defthm fn-sidb-subject-id-bounded-unfolds
  (equal (fn-sidb-subject-id-bounded fn-octets)
         (if (<= (len fn-octets) *fn-cbor-max-uint*)
             (fn-id-subject-of-payload fn-octets)
           nil))
  :hints (("Goal" :in-theory '(fn-sidb-subject-id-bounded fn-oct-len-is-len
                               fn-sidb-subject-id-is-id-subject-of-payload))))

(in-theory (disable fn-sidb-subject-id))
