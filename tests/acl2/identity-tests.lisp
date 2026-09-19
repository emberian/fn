; Golden vectors and teeth for content identity and the charge policy.
;
; The subject and obligation vectors were computed from the derivation in
; `tools/run_store.py` as it stood before `metadata()` became a bridge call,
; for the payload "hello world\n" and the Message-ID <a@example.invalid>.
; Asserting them here makes the migration a checked conformance: every lab
; store and fixture that already holds one of these strings still matches.

(in-package "ACL2")
(include-book "../../books/identity-invariants")
(include-book "std/testing/must-fail" :dir :system)

; SHA-256 of "hello world\n", supplied by the host.
(defconst *fn-id-test-payload-digest*
  '(169 72 144 79 47 15 71 155 143 129 151 105 75 48 24 75
    13 46 209 193 205 42 30 192 251 133 210 153 161 146 164 71))

; "<a@example.invalid>"
(defconst *fn-id-test-msgid*
  '(60 97 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62))

; SHA-256 of the obligation preimage for that pair.
(defconst *fn-id-test-obligation-digest*
  '(113 159 173 217 166 148 43 5 247 33 125 242 129 210 66 254
    245 105 205 93 179 14 23 32 101 251 227 66 34 247 96 116))

; -----------------------------------------------------------------------------
; The exact bytes the store already holds

; "sha256:a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447"
(assert-event
 (equal (fn-id-subject *fn-id-test-payload-digest*)
        '(115 104 97 50 53 54 58 97 57 52 56 57 48 52 102 50 102 48 102 52 55
          57 98 56 102 56 49 57 55 54 57 52 98 51 48 49 56 52 98 48 100 50 101
          100 49 99 49 99 100 50 97 49 101 99 48 102 98 56 53 100 50 57 57 97
          49 57 50 97 52 52 55)))

; msgid || 0x00 || subject, exactly as the Python preimage was assembled.
(assert-event
 (equal (fn-id-obligation-preimage
         *fn-id-test-msgid* (fn-id-subject *fn-id-test-payload-digest*))
        '(60 97 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62
          0 115 104 97 50 53 54 58 97 57 52 56 57 48 52 102 50 102 48 102 52
          55 57 98 56 102 56 49 57 55 54 57 52 98 51 48 49 56 52 98 48 100 50
          101 100 49 99 49 99 100 50 97 49 101 99 48 102 98 56 53 100 50 57 57
          97 49 57 50 97 52 52 55)))

; "archive:719fadd9a6942b05f7217df281d242fef569cd5db30e172065fbe34222f76074"
(assert-event
 (equal (fn-id-obligation *fn-id-test-obligation-digest*)
        '(97 114 99 104 105 118 101 58 55 49 57 102 97 100 100 57 97 54 57 52
          50 98 48 53 102 55 50 49 55 100 102 50 56 49 100 50 52 50 102 101
          102 53 54 57 99 100 53 100 98 51 48 101 49 55 50 48 54 53 102 98 101
          51 52 50 50 50 102 55 54 48 55 52)))

(assert-event (equal (len (fn-id-subject *fn-id-test-payload-digest*)) 71))
(assert-event
 (equal (len (fn-id-obligation *fn-id-test-obligation-digest*)) 72))

; -----------------------------------------------------------------------------
; Hexadecimal, both directions, on a witness that uses both halves of the
; alphabet and both nibble positions

(assert-event (equal (fn-id-hex-octets '(0 15 16 171 255))
                     '(48 48 48 102 49 48 97 98 102 102)))
(assert-event (equal (fn-id-unhex '(48 48 48 102 49 48 97 98 102 102))
                     '(0 15 16 171 255)))
(assert-event
 (equal (fn-id-unhex (fn-id-hex-octets *fn-id-test-payload-digest*))
        *fn-id-test-payload-digest*))

; Uppercase hexadecimal is not an accepted spelling, so an identity string
; has exactly one form.
(assert-event (not (fn-id-hex-listp '(48 70))))
(assert-event (fn-id-hex-listp '(48 102)))

; -----------------------------------------------------------------------------
; Teeth: the recognizers separate by more than their weakest clause

; A subject-shaped string is not an obligation and the reverse, because the
; labels differ rather than because either is malformed.
(assert-event (fn-id-subjectp (fn-id-subject *fn-id-test-payload-digest*)))
(assert-event
 (not (fn-id-obligationp (fn-id-subject *fn-id-test-payload-digest*))))
(assert-event
 (fn-id-obligationp (fn-id-obligation *fn-id-test-obligation-digest*)))
(assert-event
 (not (fn-id-subjectp (fn-id-obligation *fn-id-test-obligation-digest*))))

; The right label with the wrong digest width is refused.
(assert-event (not (fn-id-subjectp '(115 104 97 50 53 54 58 48 48))))

; The right length with an octet outside the hexadecimal alphabet is refused,
; so the recognizer is checking the alphabet and not only the length.
(assert-event
 (not (fn-id-subjectp
       (append '(115 104 97 50 53 54 58 122)
               (cdr (fn-id-hex-octets *fn-id-test-payload-digest*))))))

; Two digests that differ in one octet give different subjects.
(assert-event
 (not (equal (fn-id-subject *fn-id-test-payload-digest*)
             (fn-id-subject (cons 170 (cdr *fn-id-test-payload-digest*))))))

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

; Monotonicity is not provable without the ordering hypothesis.
(must-fail
 (defthm fn-charge-for-payload-monotone-without-order
   (implies (and (natp m) (natp n))
            (<= (fn-charge-for-payload m) (fn-charge-for-payload n)))))

; The hexadecimal projection is not invertible without the even-length
; hypothesis: a lone hex digit has no octet.
(must-fail
 (defthm fn-id-hex-octets-of-unhex-without-even-length
   (implies (fn-id-hex-listp octets)
            (equal (fn-id-hex-octets (fn-id-unhex octets)) octets))))
