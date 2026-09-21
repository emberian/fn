; Teeth for the one frame integrity trailer.
;
; `books/frame-trailer.lisp' includes `books/crypto-attach', so every term
; here EVALUATES: `fn-frame-digest' is realised by `fn-sha256' and a ground
; trailer is a concrete 32 octets.  That is what makes this book possible at
; all -- `tests/acl2/frame-tests.lisp' records, at its last tooth, that a
; separating witness for the specification decoder "cannot have one:
; `fn-frame-digest' is constrained (A-CRYPTO), so no ground term evaluates
; it".  Under the attachment it does.
;
; The first section is the one that licenses deleting three host copies of
; SHA-256: the octets ACL2 computes are the octets `hashlib.sha256` and
; `fnn-sha256' computed, so no byte on disk changes.  Cross-checked outside
; ACL2 at authoring time with CPython 3.13 `hashlib.sha256`, recorded in
; planning/lanes/HANDOFF-w11-one-owner.md.
;
; NOT tested here, because it is not true and no test can make it so:
; anything about collision or preimage resistance.  A-CRYPTO
; (books/assumptions.lisp) is unchanged by the attachment, and every witness
; below is a statement about specific octets.

(in-package "ACL2")
(include-book "../../books/frame-trailer")

; -----------------------------------------------------------------------------
; 1. The trailer is SHA-256, on octets the host used to hash for itself.
;
; Two FIPS 180-4 vectors first, so a reader can check the function is the
; hash it is claimed to be without trusting the frame layout, and then the
; frame case: the protected prefix of the one-record store frame, and the
; trailer over it.

(assert-event
 (equal (fn-frame-trailer nil)
        ; SHA-256 of the empty message.
        '(227 176 196 66 152 252 28 20 154 251 244 200 153 111 185 36
          39 174 65 228 100 155 147 76 164 149 153 27 120 82 184 85)))

(assert-event
 (equal (fn-frame-trailer '(97 98 99))
        ; SHA-256 of "abc".
        '(186 120 22 191 143 1 207 234 65 65 64 222 93 174 34 35
          176 3 97 163 150 23 122 156 180 16 255 97 242 0 21 173)))

; The store frame's protected prefix, spelled out: FNST, version 1, kind 1,
; a four-octet big-endian length of 3, and the record.  This is the byte
; string `tools/frame_bridge.py' used to hand to `hashlib.sha256'.
(defconst *fn-frame-trailer-t-prefix* '(70 78 83 84 1 1 0 0 0 3 1 2 3))

(assert-event
 (equal (fn-frame-store-protected '(1 2 3)) *fn-frame-trailer-t-prefix*))

; And the trailer over it.  Deleting `FrameSession.seal''s `hashlib.sha256',
; `fnn-seal''s `fnn-sha256' and `Acl2Owner.feed_frames''s `hashlib.sha256'
; changes this byte string not at all; that is the whole content of the
; migration, and it is checked here rather than asserted in prose.
(assert-event
 (equal (fn-frame-trailer *fn-frame-trailer-t-prefix*)
        '(183 162 160 5 37 20 123 28 147 194 61 218 190 130 161 178
          246 131 69 54 36 252 244 95 20 124 177 90 71 84 36 157)))

; -----------------------------------------------------------------------------
; 2. The boundary guard.
;
; A host that sends something that is not an octet list is refused rather
; than handed the digest of a coerced value.  `fn-sha256' fixes its argument,
; so without this test the wrapper's `:bad' arm would be untested and a host
; bug would come back as a plausible 32 octets.

(assert-event (equal (fn-frame-trailer 7) :bad))
(assert-event (equal (fn-frame-trailer '(1 2 256)) :bad))
(assert-event (equal (fn-frame-trailer '(1 2 . 3)) :bad))

; Not degenerate: one octet less and the same call answers a digest.
(assert-event (fn-frame-digestp (fn-frame-trailer '(1 2 255))))

; -----------------------------------------------------------------------------
; 3. Witnesses for the keystones.
;
; `fn-frame-protected-plus-trailer-is-seal' and
; `fn-frame-decode-of-host-framing' on a reachable non-degenerate value: a
; three-octet store record, which is what `tools/run_store.py' writes for a
; one-transaction store.

(assert-event
 (fn-frame-inputp *fn-frame-magic-store* *fn-frame-version*
                  *fn-frame-store-kind* '(1 2 3) *fn-frame-max-store-payload*))

(assert-event
 (equal (append (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                                    *fn-frame-store-kind* '(1 2 3))
                (fn-frame-trailer
                 (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                                     *fn-frame-store-kind* '(1 2 3))))
        (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                       *fn-frame-store-kind* '(1 2 3))))

; And the byte string it is, so the witness separates by more than "both
; sides are the same term".
(assert-event
 (equal (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                       *fn-frame-store-kind* '(1 2 3))
        (append *fn-frame-trailer-t-prefix*
                '(183 162 160 5 37 20 123 28 147 194 61 218 190 130 161 178
                  246 131 69 54 36 252 244 95 20 124 177 90 71 84 36 157))))

; The decode direction, with the trailer re-derived over the frame's own
; protected prefix -- which is exactly what `FrameSession.digest_of',
; `fnn-digest-of' and `Acl2Owner.feed_replay_frame' now do.
(assert-event
 (equal (fn-frame-decode
         (append (fn-frame-store-protected '(1 2 3))
                 (fn-frame-trailer (fn-frame-store-protected '(1 2 3))))
         (fn-frame-trailer
          (fn-frame-protected-prefix
           (append (fn-frame-store-protected '(1 2 3))
                   (fn-frame-trailer (fn-frame-store-protected '(1 2 3))))))
         *fn-frame-max-store-payload*)
        (fn-frame-ok *fn-frame-magic-store* *fn-frame-version*
                     *fn-frame-store-kind* '(1 2 3))))

(assert-event
 (equal (fn-frame-store-decode
         (append (fn-frame-store-protected '(1 2 3))
                 (fn-frame-trailer (fn-frame-store-protected '(1 2 3))))
         (fn-frame-trailer
          (fn-frame-protected-prefix
           (append (fn-frame-store-protected '(1 2 3))
                   (fn-frame-trailer (fn-frame-store-protected '(1 2 3)))))))
        (fn-frame-ok *fn-frame-magic-store* *fn-frame-version*
                     *fn-frame-store-kind* '(1 2 3))))

; -----------------------------------------------------------------------------
; 4. One violating value per hypothesis.
;
; `fn-frame-protected-plus-trailer-is-seal' has one hypothesis,
; `fn-frame-inputp'.  It is the caller's domain predicate and it is stronger
; than this keystone strictly needs -- only its octet-shape clauses are
; load-bearing here; the `(<= (len payload) max-payload)' clause is what
; `fn-frame-decode-of-host-framing' needs -- so the two witnesses below drop
; a DIFFERENT clause each, and each one is a value at which the conclusion
; is false.

; (a) Shape: a magic whose third element is not an octet.  The header is
; then not an octet list, the trailer wrapper refuses it, and the host's
; concatenation is not the sealed frame.  This is the clause keystone 1
; needs.
(assert-event (not (fn-frame-magicp '(70 78 300 84))))
(assert-event
 (not (fn-frame-inputp '(70 78 300 84) *fn-frame-version*
                       *fn-frame-store-kind* '(1 2 3)
                       *fn-frame-max-store-payload*)))
(assert-event
 (with-guard-checking :none
  (equal (fn-frame-trailer
          (fn-frame-protected '(70 78 300 84) *fn-frame-version*
                              *fn-frame-store-kind* '(1 2 3)))
         :bad)))
(assert-event
 (with-guard-checking :none
  (not (equal (append (fn-frame-protected '(70 78 300 84) *fn-frame-version*
                                          *fn-frame-store-kind* '(1 2 3))
                      (fn-frame-trailer
                       (fn-frame-protected '(70 78 300 84) *fn-frame-version*
                                           *fn-frame-store-kind* '(1 2 3))))
              (fn-frame-seal '(70 78 300 84) *fn-frame-version*
                             *fn-frame-store-kind* '(1 2 3))))))

; (b) Bound: a payload longer than the `max-payload' the decoder is given.
; The seal is built, but the decoder refuses it, so
; `fn-frame-decode-of-host-framing''s conclusion is false.  This is the
; clause keystone 2 needs and keystone 1 does not.
(assert-event
 (not (fn-frame-inputp *fn-frame-magic-store* *fn-frame-version*
                       *fn-frame-store-kind* '(1 2 3) 2)))
(assert-event
 (with-guard-checking :none
  (not (equal (fn-frame-decode
               (append (fn-frame-protected
                        *fn-frame-magic-store* *fn-frame-version*
                        *fn-frame-store-kind* '(1 2 3))
                       (fn-frame-trailer
                        (fn-frame-protected
                         *fn-frame-magic-store* *fn-frame-version*
                         *fn-frame-store-kind* '(1 2 3))))
               (fn-frame-trailer
                (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                                    *fn-frame-store-kind* '(1 2 3)))
               2)
              (fn-frame-ok *fn-frame-magic-store* *fn-frame-version*
                           *fn-frame-store-kind* '(1 2 3))))))
; And it is the bound that refuses and not the shape: at 3 it is accepted.
(assert-event
 (fn-frame-result-okp
  (fn-frame-decode
   (append (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                               *fn-frame-store-kind* '(1 2 3))
           (fn-frame-trailer
            (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                                *fn-frame-store-kind* '(1 2 3))))
   (fn-frame-trailer
    (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                        *fn-frame-store-kind* '(1 2 3)))
   3)))

; (c) The store instances: a record that is not an octet list, and a record
; over the store payload bound.  `fn-frame-store-protected' answers `:bad'
; for both, so the host has no prefix to seal and the conclusion fails.
(assert-event (not (fn-cbor-octet-listp '(1 2 256))))
(assert-event (equal (fn-frame-store-protected '(1 2 256)) :bad))
(assert-event
 (with-guard-checking :none
  (not (equal (append (fn-frame-store-protected '(1 2 256))
                      (fn-frame-trailer (fn-frame-store-protected '(1 2 256))))
              (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                             *fn-frame-store-kind* '(1 2 256))))))

; -----------------------------------------------------------------------------
; 5. The trailer covers the whole prefix, not part of it.
;
; A frame whose payload differs in one octet has a different trailer, so a
; decoder given the first frame's trailer refuses the second.  This is an
; integrity statement about these two concrete byte strings and NOT a
; collision-resistance claim: it says these two disagree, not that no two
; agree.

(assert-event
 (not (equal (fn-frame-trailer (fn-frame-store-protected '(1 2 3)))
             (fn-frame-trailer (fn-frame-store-protected '(1 2 4))))))

(assert-event
 (not (fn-frame-result-okp
       (fn-frame-store-decode
        (append (fn-frame-store-protected '(1 2 4))
                (fn-frame-trailer (fn-frame-store-protected '(1 2 4))))
        (fn-frame-trailer (fn-frame-store-protected '(1 2 3)))))))
