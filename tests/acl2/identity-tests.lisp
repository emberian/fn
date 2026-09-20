; Golden vectors and teeth for content identity and the charge policy.
;
; The vectors are the v1 profile of `specs/encoding.md` evaluated on the
; payload "hello world\n" and the Message-ID <a@example.invalid>.  They were
; computed from the specified preimages, not from any host code: a host that
; disagrees with these octets is wrong, and the pre-v1 `"sha256:"`/`"archive:"`
; derivation disagrees with all of them, which is exactly why a store written
; under it is refused at open by `fn-store-experiment-5`.

(in-package "ACL2")
(include-book "../../books/identity-invariants")

; "<a@example.invalid>"
(defconst *fn-id-test-msgid*
  '(60 97 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62))

; "hello world\n"
(defconst *fn-id-test-payload*
  '(104 101 108 108 111 32 119 111 114 108 100 10))

; SHA-256 of the subject-v1 preimage, supplied by the host.
; 02af9c8c081529a5711c6dd798876c40aa331bd1c07ba7b6fbe261143db58a27
(defconst *fn-id-test-subject-digest*
  '(2 175 156 140 8 21 41 165 113 28 109 215 152 135 108 64 170 51 27
    209 192 123 167 182 251 226 97 20 61 181 138 39))

; SHA-256 of the obligation-v1 preimage, supplied by the host.
; cb713c96d6692d192d8e13448497907925de0d1bbe053d1ececca989b0da3f61
(defconst *fn-id-test-obligation-digest*
  '(203 113 60 150 214 105 45 25 45 142 19 68 132 151 144 121 37 222 13
    27 190 5 61 30 206 204 169 137 176 218 63 97))

; -----------------------------------------------------------------------------
; The preimages, exactly as `specs/encoding.md` writes them

; "fn/subject/v1" || 0x00 || uint32-be(12) || "hello world\n"
(assert-event
 (equal (fn-id-subject-preimage *fn-id-test-payload*)
        '(102 110 47 115 117 98 106 101 99 116 47 118 49 0 0 0 0 12 104 101
          108 108 111 32 119 111 114 108 100 10)))

; The subject identity: label, separator, version 1, algorithm 1, digest.
(assert-event
 (equal (fn-id-subject *fn-id-test-subject-digest*)
        '(102 110 47 115 117 98 106 101 99 116 47 118 49 0 1 1 2 175 156 140 8
          21 41 165 113 28 109 215 152 135 108 64 170 51 27 209 192 123 167
          182 251 226 97 20 61 181 138 39)))

; "fn/obligation/v1" || 0x00 || uint32-be(19) || msgid
;                    || uint32-be(48) || subject
(assert-event
 (equal (fn-id-obligation-preimage
         *fn-id-test-msgid* (fn-id-subject *fn-id-test-subject-digest*))
        '(102 110 47 111 98 108 105 103 97 116 105 111 110 47 118 49 0 0 0 0
          19 60 97 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100
          62 0 0 0 48 102 110 47 115 117 98 106 101 99 116 47 118 49 0 1 1 2
          175 156 140 8 21 41 165 113 28 109 215 152 135 108 64 170 51 27 209
          192 123 167 182 251 226 97 20 61 181 138 39)))

(assert-event
 (equal (fn-id-obligation *fn-id-test-obligation-digest*)
        '(102 110 47 111 98 108 105 103 97 116 105 111 110 47 118 49 0 1 1 203
          113 60 150 214 105 45 25 45 142 19 68 132 151 144 121 37 222 13 27
          190 5 61 30 206 204 169 137 176 218 63 97)))

(assert-event
 (equal (len (fn-id-subject *fn-id-test-subject-digest*)) 48))
(assert-event
 (equal (len (fn-id-obligation *fn-id-test-obligation-digest*)) 51))

; The subject prefix is the preimage with the payload removed, which is what
; lets the host hash a 32 KiB article without sending it across the bridge.
(assert-event
 (equal (append (fn-id-subject-prefix (len *fn-id-test-payload*))
                *fn-id-test-payload*)
        (fn-id-subject-preimage *fn-id-test-payload*)))

; -----------------------------------------------------------------------------
; Domain separation, on a witness

; The labels part company at the fourth octet, 115 ("s") against 111 ("o").
(assert-event (equal (nth 3 (fn-id-subject-preimage *fn-id-test-payload*)) 115))
(assert-event
 (equal (nth 3 (fn-id-obligation-preimage *fn-id-test-msgid* nil)) 111))
(assert-event
 (not (equal (fn-id-subject-preimage *fn-id-test-payload*)
             (fn-id-obligation-preimage
              *fn-id-test-msgid*
              (fn-id-subject *fn-id-test-subject-digest*)))))

; An obligation preimage cannot be re-split: the field lengths are decoded,
; not found.  A Message-ID that ends where the length says it does is the
; only reading.
(assert-event
 (not (equal (fn-id-obligation-preimage '(97 98) '(99))
             (fn-id-obligation-preimage '(97) '(98 99)))))

; -----------------------------------------------------------------------------
; The string boundary

(assert-event
 (equal (fn-id-from-text (fn-id-text (fn-id-subject *fn-id-test-subject-digest*)))
        (fn-id-subject *fn-id-test-subject-digest*)))
(assert-event
 (equal (len (fn-id-text (fn-id-subject *fn-id-test-subject-digest*))) 96))
(assert-event
 (equal (len (fn-id-text (fn-id-obligation *fn-id-test-obligation-digest*))) 102))

; -----------------------------------------------------------------------------
; Hexadecimal, both directions, on a witness that uses both halves of the
; alphabet and both nibble positions

(assert-event (equal (fn-id-hex-octets '(0 15 16 171 255))
                     '(48 48 48 102 49 48 97 98 102 102)))
(assert-event (equal (fn-id-unhex '(48 48 48 102 49 48 97 98 102 102))
                     '(0 15 16 171 255)))
(assert-event
 (equal (fn-id-unhex (fn-id-hex-octets *fn-id-test-subject-digest*))
        *fn-id-test-subject-digest*))

; Uppercase hexadecimal is not an accepted spelling, so an identity string
; has exactly one form.
(assert-event (not (fn-id-hex-listp '(48 70))))
(assert-event (fn-id-hex-listp '(48 102)))

; -----------------------------------------------------------------------------
; Teeth: the recognizers separate by more than their weakest clause

(assert-event (fn-id-subjectp (fn-id-subject *fn-id-test-subject-digest*)))
(assert-event
 (not (fn-id-obligationp (fn-id-subject *fn-id-test-subject-digest*))))
(assert-event
 (fn-id-obligationp (fn-id-obligation *fn-id-test-obligation-digest*)))
(assert-event
 (not (fn-id-subjectp (fn-id-obligation *fn-id-test-obligation-digest*))))

; The right label with the wrong digest width is refused.
(assert-event
 (not (fn-id-subjectp (append *fn-id-subject-label* '(0 1 1 0 0)))))

; The right label and width with the wrong algorithm octet is refused, so a
; future suite cannot be read as this one.
(assert-event
 (not (fn-id-subjectp
       (append *fn-id-subject-label*
               (cons 0 (cons 1 (cons 2 *fn-id-test-subject-digest*)))))))

; And the wrong version octet is refused for the same reason.
(assert-event
 (not (fn-id-subjectp
       (append *fn-id-subject-label*
               (cons 0 (cons 2 (cons 1 *fn-id-test-subject-digest*)))))))

; Two digests that differ in one octet give different subjects.
(assert-event
 (not (equal (fn-id-subject *fn-id-test-subject-digest*)
             (fn-id-subject (cons 170 (cdr *fn-id-test-subject-digest*))))))

; -----------------------------------------------------------------------------
; Charge policy

(assert-event (equal (fn-charge-for-payload 0) 1))
(assert-event (equal (fn-charge-for-payload 1) 2))
(assert-event (equal (fn-charge-for-payload 4095) 2))
(assert-event (equal (fn-charge-for-payload 4096) 2))
(assert-event (equal (fn-charge-for-payload 4097) 3))
(assert-event (equal (fn-charge-for-payload 32768) 9))

; The policy is not the constant function: a larger payload does cost more.
(assert-event (< (fn-charge-for-payload 0) (fn-charge-for-payload 32768)))

; Monotonicity needs its ordering hypothesis, and here is the pair that shows
; it: 32768 and 0 are both naturals, and dropping `(<= m n)` would claim the
; charge for the larger payload is not above the charge for the smaller.
(assert-event (natp 32768))
(assert-event (natp 0))
(assert-event (not (<= (fn-charge-for-payload 32768)
                       (fn-charge-for-payload 0))))

; The hexadecimal projection needs its even-length hypothesis, and `(48)`, a
; lone ASCII "0", is the witness: it is a hex list, it is odd, and unhexing
; then rehexing it does not return it.
(assert-event (fn-id-hex-listp '(48)))
(assert-event (not (equal (len '(48)) (* 2 (floor (len '(48)) 2)))))
(assert-event
 (with-guard-checking :none
  (not (equal (fn-id-hex-octets (fn-id-unhex '(48))) '(48)))))
