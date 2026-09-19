; Witnesses and teeth for books/crypto-seam.lisp.
;
; The seam's functions are constrained, so nothing about them executes until
; a realiser is attached.  This book attaches TOY realisers with `defattach`
; (ACL2 proves the seam's constraints hold of them; nothing is assumed):
;   fn-toy-mix-digest     a 256-bit polynomial fold; not cryptographic
;   fn-toy-length-digest  the input length, zero padded: every equal-length
;                         pair collides (minidregg `lengthScheme`)
;   fn-toy-*-sign         public key = seed, signature = mix(pk || m):
;                         anyone holding a PUBLIC key can sign under it.
; That both digests satisfy the seam is the point: the seam does not carry
; collision resistance or unforgeability (A-CRYPTO).  Test books that need
; execution include this book and inherit the final (mix) attachment.

(in-package "ACL2")
(include-book "../../books/crypto-seam")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Toy realisers

(defconst *fn-toy-modulus* (- (expt 2 256) 189))

(defun fn-toy-fold (octets acc)
  (declare (xargs :guard (and (fn-cbor-octet-listp octets) (natp acc))))
  (if (consp octets)
      (fn-toy-fold (cdr octets)
                   (mod (+ (* acc 263) (car octets) 1) *fn-toy-modulus*))
    acc))

(defun fn-toy-nat-octets (n k)
  (declare (xargs :guard (and (natp n) (natp k))))
  (if (zp k)
      nil
    (append (fn-toy-nat-octets (floor n 256) (1- k))
            (list (mod n 256)))))

(defthm fn-toy-nat-octets-shape
  (implies (natp n)
           (and (fn-cbor-octet-listp (fn-toy-nat-octets n k))
                (equal (len (fn-toy-nat-octets n k)) (nfix k))))
  :hints (("Goal" :induct (fn-toy-nat-octets n k))))

(defun fn-toy-mix-digest (m)
  (declare (xargs :guard t))
  (fn-toy-nat-octets (fn-toy-fold (if (fn-cbor-octet-listp m) m nil) 7) 32))

(defun fn-toy-length-digest (m)
  (declare (xargs :guard t))
  (fn-toy-nat-octets (len m) 32))

(defthm fn-toy-fold-is-natural
  (implies (natp acc) (natp (fn-toy-fold octets acc))))

(defthm fn-toy-mix-digest-shape
  (fn-digest-octetsp (fn-toy-mix-digest m)))

(defthm fn-toy-length-digest-shape
  (fn-digest-octetsp (fn-toy-length-digest m)))

(defun fn-toy-public-key (sk)
  (declare (xargs :guard t))
  (if (fn-sig-seed-p sk) sk (make-list 32 :initial-element 0)))

(defun fn-toy-sign (sk m)
  (declare (xargs :guard t))
  (fn-toy-mix-digest (append (fn-toy-public-key sk)
                             (if (fn-cbor-octet-listp m) m nil))))

(defun fn-toy-verify (pk m sig)
  (declare (xargs :guard t))
  (equal sig
         (fn-toy-mix-digest (append (if (fn-cbor-octet-listp pk) pk nil)
                                    (if (fn-cbor-octet-listp m) m nil)))))

(defthm fn-toy-public-key-shape
  (fn-sig-public-key-p (fn-toy-public-key sk)))

(defthm fn-toy-sign-shape
  (fn-sig-signature-p (fn-toy-sign sk m))
  :hints (("Goal" :in-theory (disable fn-toy-mix-digest-shape)
           :use ((:instance fn-toy-mix-digest-shape
                            (m (append (fn-toy-public-key sk)
                                       (if (fn-cbor-octet-listp m) m nil))))))))

(defthm fn-toy-verify-is-boolean
  (booleanp (fn-toy-verify pk m sig)))

(defthm fn-toy-verify-of-sign
  (implies (and (fn-sig-seed-p sk) (fn-cbor-octet-listp m))
           (fn-toy-verify (fn-toy-public-key sk) m (fn-toy-sign sk m))))

(defattach (fn-sig-public-key fn-toy-public-key)
           (fn-sig-sign fn-toy-sign)
           (fn-sig-verify fn-toy-verify))

; -----------------------------------------------------------------------------
; The seam does not carry collision resistance: a colliding realiser
; satisfies it.  (minidregg `lengthScheme_not_binding`)

(defattach fn-digest fn-toy-length-digest)

(assert-event (equal (fn-digest '(1 2 3)) (fn-digest '(4 5 6))))
(assert-event (not (equal '(1 2 3) '(4 5 6))))
(assert-event (fn-digest-octetsp (fn-digest '(1 2 3))))

; Digest injectivity is not a theorem of the seam.
(must-fail
 (thm (implies (equal (fn-digest a) (fn-digest b))
               (equal a b))))

; -----------------------------------------------------------------------------
; Domain separation lives below the digest: tagged preimages separate.

(defattach fn-digest fn-toy-mix-digest)

(defconst *fn-toy-tag-a* (fn-record-string-octets "fn-a-v1"))
(defconst *fn-toy-tag-b* (fn-record-string-octets "fn-b-v1"))

(assert-event (equal (fn-cbor-decode
                      (fn-digest-tagged-preimage *fn-toy-tag-a* '(9 8 7)))
                     (fn-cbor-ok (cons :bytes *fn-toy-tag-a*) '(9 8 7))))

; Raw concatenation is ambiguous; the tagged preimage is not.
(assert-event (equal (append '(97 98) '(99)) (append '(97) '(98 99))))
(assert-event (not (equal (fn-digest-tagged-preimage '(97 98) '(99))
                          (fn-digest-tagged-preimage '(97) '(98 99)))))
(assert-event (not (equal (fn-digest-tagged *fn-toy-tag-a* '(1))
                          (fn-digest-tagged *fn-toy-tag-b* '(1)))))

; Teeth for fn-digest-tagged-preimage-injective: without the tag shape
; hypothesis an empty tag and a non-octet tag both encode to nothing useful.
(assert-event (equal (ec-call (fn-digest-tagged-preimage '(300) '(1)))
                     (ec-call (fn-digest-tagged-preimage '(301) '(1)))))
(assert-event (not (fn-digest-tagp '(300))))

; -----------------------------------------------------------------------------
; Signatures under the toy: the satisfiable pole and one tooth per input.

(defconst *fn-toy-seed-a* (make-list 32 :initial-element 1))
(defconst *fn-toy-seed-b* (make-list 32 :initial-element 2))

(assert-event (fn-sig-seed-p *fn-toy-seed-a*))
(assert-event (fn-sig-verify (fn-sig-public-key *fn-toy-seed-a*)
                             '(10 20 30)
                             (fn-sig-sign *fn-toy-seed-a* '(10 20 30))))
; wrong key
(assert-event (not (fn-sig-verify (fn-sig-public-key *fn-toy-seed-b*)
                                  '(10 20 30)
                                  (fn-sig-sign *fn-toy-seed-a* '(10 20 30)))))
; wrong message
(assert-event (not (fn-sig-verify (fn-sig-public-key *fn-toy-seed-a*)
                                  '(10 20 31)
                                  (fn-sig-sign *fn-toy-seed-a* '(10 20 30)))))
; tampered signature
(assert-event (not (fn-sig-verify (fn-sig-public-key *fn-toy-seed-a*)
                                  '(10 20 30)
                                  (let ((sig (fn-sig-sign *fn-toy-seed-a*
                                                          '(10 20 30))))
                                    (cons (mod (1+ (car sig)) 256) (cdr sig))))))
; no signature at all
(assert-event (not (fn-sig-verify (fn-sig-public-key *fn-toy-seed-a*)
                                  '(10 20 30) nil)))
; The toy is forgeable by design: holding the public key suffices.
(assert-event (fn-sig-verify (fn-sig-public-key *fn-toy-seed-a*)
                             '(10 20 30)
                             (fn-toy-mix-digest
                              (append (fn-sig-public-key *fn-toy-seed-a*)
                                      '(10 20 30)))))

; Unforgeability is not a theorem of the seam.
(must-fail
 (thm (implies (fn-sig-verify pk m sig)
               (equal sig (fn-sig-sign sk m)))))

; -----------------------------------------------------------------------------
; Hex rendering

(assert-event (equal (fn-digest-hex '(0 255 16 171)) "00ff10ab"))
(assert-event (equal (length (fn-digest-hex (fn-digest '(1)))) 64))
