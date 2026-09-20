; fn: the FIPS 180-4 test vectors for books/sha256.lisp.
;
; What this book is evidence FOR and what it is not.  `books/sha256.lisp'
; proves that `fn-sha256' always yields 32 octets; it does not and cannot
; prove that those octets are the ones FIPS 180-4 specifies, because "the
; standard" is a document, not an ACL2 term.  The bridge from the definition
; to the standard is EVALUATION against the published vectors, and that is
; what this book is: each `assert-event' below runs `fn-sha256' and compares
; its 32 octets with the digest printed in the standard (FIPS 180-4 and the
; NIST CSRC "SHA-256 Examples" note).  A failure here is a defect in the
; definition; a pass here is agreement on these inputs, which is evidence,
; not a proof of agreement on all inputs.
;
; Nothing here bears on collision resistance (A-CRYPTO, specs/failures.md).

(in-package "ACL2")
(include-book "../../books/sha256")

; -----------------------------------------------------------------------------
; A local string reader, so this book depends on nothing but sha256.

(defun fn-sha256-t-octets (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars)) (fn-sha256-t-octets (cdr chars)))
    nil))

(defmacro fn-sha256-t-string (s)
  `(fn-sha256-t-octets (coerce ,s 'list)))

(defun fn-sha256-t-repeat (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n) nil (cons x (fn-sha256-t-repeat (- n 1) x)))))

; -----------------------------------------------------------------------------
; The vectors.  Each expected value is the digest as the standard prints it,
; transcribed to octets.

; empty: message of 0 octets, digest e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
(assert-event
 (equal (fn-sha256 nil)
        '(227 176 196 66 152 252 28 20 154 251 244 200 153 111 185 36 39 174 65 228 100 155 147 76 164 149 153 27 120 82 184 85)))

; abc: message of 3 octets, digest ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
(assert-event
 (equal (fn-sha256 (fn-sha256-t-string "abc"))
        '(186 120 22 191 143 1 207 234 65 65 64 222 93 174 34 35 176 3 97 163 150 23 122 156 180 16 255 97 242 0 21 173)))

; fips-56: message of 56 octets, digest 248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
(assert-event
 (equal (fn-sha256 (fn-sha256-t-string "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
        '(36 141 106 97 210 6 56 184 229 192 38 147 12 62 96 57 163 60 228 89 100 255 33 103 246 236 237 212 25 219 6 193)))

; fips-112: message of 112 octets, digest cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1
(assert-event
 (equal (fn-sha256 (fn-sha256-t-string "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"))
        '(207 91 22 167 120 175 131 128 3 108 229 158 123 4 146 55 11 36 155 17 232 240 122 81 175 172 69 3 122 254 233 209)))

; 1000 repetitions of 'a' (0x61): a multi-block message, digest 41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3
(assert-event
 (equal (fn-sha256 (fn-sha256-t-repeat 1000 97))
        '(65 237 236 228 45 99 232 217 191 81 90 155 166 147 46 28 32 203 201 245 165 209 52 100 90 219 93 177 185 115 126 163)))

; The padding boundaries (FIPS 180-4 section 5.1.1): 55 octets is the last
; length whose padding fits in one block, 56 forces a second block, and 64 is
; a whole block with a full extra block of padding.  A padding bug that the
; short vectors miss shows up here.
(assert-event
 (equal (fn-sha256 (fn-sha256-t-repeat 55 97))
        '(159 67 144 248 211 12 45 217 46 201 240 149 182 94 43 154 233 176 169 37 165 37 142 36 28 159 30 145 15 115 67 24)))
(assert-event
 (equal (fn-sha256 (fn-sha256-t-repeat 56 97))
        '(179 84 57 164 172 111 9 72 182 214 249 227 198 175 15 95 89 12 226 15 27 222 112 144 239 121 112 104 110 198 115 138)))
(assert-event
 (equal (fn-sha256 (fn-sha256-t-repeat 63 97))
        '(125 62 116 160 93 125 177 91 206 74 217 236 6 88 234 152 227 240 110 238 207 22 180 198 255 242 218 69 125 220 47 52)))
(assert-event
 (equal (fn-sha256 (fn-sha256-t-repeat 64 97))
        '(255 224 84 254 122 224 203 109 198 92 58 249 182 29 82 9 244 57 133 29 180 61 11 165 153 115 55 223 21 70 104 235)))
(assert-event
 (equal (fn-sha256 (fn-sha256-t-repeat 65 97))
        '(99 83 97 196 139 185 234 177 65 152 231 110 168 171 127 26 65 104 93 106 214 42 169 20 109 48 29 79 23 235 10 224)))
(assert-event
 (equal (fn-sha256 (fn-sha256-t-repeat 119 97))
        '(49 235 165 28 49 58 92 8 34 106 223 24 212 163 89 207 223 216 210 232 22 177 63 74 249 82 247 234 101 132 220 251)))
(assert-event
 (equal (fn-sha256 (fn-sha256-t-repeat 120 97))
        '(47 61 51 84 50 199 11 88 10 240 232 225 179 103 74 124 2 13 104 58 165 247 58 170 237 253 197 90 249 4 194 28)))

; FIPS 180-4 / NIST CSRC long vector: one million repetitions of 'a' (0x61),
; digest cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0.
; Measured on hbox 2026-09-20: 0.40 s realtime, 104 MB allocated, which is
; why it is in the book rather than in a note about a vector we skipped.
(assert-event
 (equal (fn-sha256 (fn-sha256-t-repeat 1000000 97))
        '(205 199 110 92 153 20 251 146 129 161 199 226 132 215 62 103 241 128 154 72 164 151 32 14 4 109 57 204 199 17 44 208)))

; -----------------------------------------------------------------------------
; Teeth.
;
; `fn-sha256-shape' has no hypotheses, so there is no must-fail case to make
; for it; what it needs instead is a witness that the realiser is not
; degenerate, because the seam's LOCAL witness is the constant zero digest and
; the point of this book is that the attached realiser is not that.

; Not constant: two messages, two digests.  (The toy realiser attached in
; tests/acl2/crypto-seam-tests.lisp collides here on purpose; this one does
; not.)
(assert-event (not (equal (fn-sha256 '(1 2 3)) (fn-sha256 '(4 5 6)))))

; Not the zero digest, which is exactly the seam's local witness.
(assert-event (not (equal (fn-sha256 nil) (fn-sha256-t-repeat 32 0))))

; Avalanche: one bit of the message changes the digest.  (Evidence about this
; pair only; it is not a proof of any diffusion property.)
(assert-event (not (equal (fn-sha256 '(0)) (fn-sha256 '(1)))))

; Length extension is visible at the preimage, which is why every fn preimage
; is length-prefixed or tagged (books/crypto-seam.lisp): raw concatenation is
; ambiguous and SHA-256 hashes the concatenation, not the pair.
(assert-event (equal (append '(97 98) '(99)) (append '(97) '(98 99))))
(assert-event (equal (fn-sha256 (append '(97 98) '(99)))
                     (fn-sha256 (append '(97) '(98 99)))))

; The coercion is total and the shape holds off the octet domain: a non-list,
; and a list of non-octets, both still digest to 32 octets.
(assert-event (equal (len (fn-sha256 7)) 32))
(assert-event (fn-sha256-octet-listp (fn-sha256 '(:a "b" 300))))
; and the coercion is the identity on octets, so the non-octet case above is
; the digest of the coerced octets and of nothing else.
(assert-event (equal (fn-sha256 '(300 -1)) (fn-sha256 '(44 255))))
