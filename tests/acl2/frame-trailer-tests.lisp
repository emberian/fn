; Teeth for the one frame integrity trailer.
;
; `books/frame-trailer.lisp' includes `books/crypto-attach', so every term
; here EVALUATES: `fn-frame-digest' is realised by `fn-blake3' (BLAKE3, store
; format 10; SHA-256 before) and a ground
; trailer is a concrete 32 octets.  That is what makes this book possible at
; all -- `tests/acl2/frame-tests.lisp' records, at its last tooth, that a
; separating witness for the specification decoder "cannot have one:
; `fn-frame-digest' is constrained (A-CRYPTO), so no ground term evaluates
; it".  Under the attachment it does.
;
; The first section pins the trailer's octets: the BLAKE3 values below are
; tools/blake3_ref.py's pure-Python BLAKE3 (a third implementation), and the
; first two are the BLAKE3 repository's own published values for "" and
; "abc".  (Until store format 10 this section pinned SHA-256, the octets the
; deleted host copies computed: planning/lanes/HANDOFF-w11-one-owner.md.)
;
; NOT tested here, because it is not true and no test can make it so:
; anything about collision or preimage resistance.  A-CRYPTO
; (books/assumptions.lisp) is unchanged by the attachment, and every witness
; below is a statement about specific octets.

(in-package "ACL2")
(include-book "../../books/frame-trailer")

; -----------------------------------------------------------------------------
; 1. The trailer is BLAKE3, on octets the host used to hash for itself.
;
; Two BLAKE3 vectors first, so a reader can check the function is the
; hash it is claimed to be without trusting the frame layout, and then the
; frame case: the protected prefix of the one-record store frame, and the
; trailer over it.

(assert-event
 (equal (fn-frame-trailer nil)
        ; BLAKE3 of the empty message.
        '(175 19 73 185 245 249 161 166 160 64 77 234 54 220 201 73
          155 203 37 201 173 193 18 183 204 154 147 202 228 31 50 98)))

(assert-event
 (equal (fn-frame-trailer '(97 98 99))
        ; BLAKE3 of "abc".
        '(100 55 179 172 56 70 81 51 255 182 59 117 39 58 141 181
          72 197 88 70 93 121 219 3 253 53 156 108 213 189 157 133)))

; The store frame's protected prefix, spelled out: FNST, version 1, kind 1,
; a four-octet big-endian length of 3, and the record.  This is the byte
; string `tools/frame_bridge.py' used to hand to `hashlib.sha256'.
(defconst *fn-frame-trailer-t-prefix* '(70 78 83 84 1 1 0 0 0 3 1 2 3))

(assert-event
 (equal (fn-frame-store-protected '(1 2 3)) *fn-frame-trailer-t-prefix*))

; And the trailer over it (BLAKE3 of the prefix; the host copies of the
; digest were deleted when the trailer moved into ACL2, and every host asks
; `fn-frame-trailer' for these octets).
(assert-event
 (equal (fn-frame-trailer *fn-frame-trailer-t-prefix*)
        '(205 109 140 213 55 4 42 226 118 170 158 232 33 189 42 208
          177 165 152 88 92 252 16 186 129 188 95 134 108 90 94 37)))

; -----------------------------------------------------------------------------
; 2. The boundary guard.
;
; A host that sends something that is not an octet list is refused rather
; than handed the digest of a coerced value.  `fn-blake3' fixes its argument,
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
                '(205 109 140 213 55 4 42 226 118 170 158 232 33 189 42 208
                  177 165 152 88 92 252 16 186 129 188 95 134 108 90 94 37))))

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
;; Anchor: the store's own magic is one.
(assert-event (fn-frame-magicp *fn-frame-magic-store*))
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
