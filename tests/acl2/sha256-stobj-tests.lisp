; fn: teeth for books/sha256-stobj.lisp.
;
; What this book is evidence FOR.  `fn-sha256-stobj-is-sha256' is a theorem
; with no hypothesis, so there is no must-fail case to make for it; what it
; needs is the same witness books/sha256's tests give the list model: the
; FIPS 180-4 vectors, now evaluated through the stobj computation and through
; the string entry, and the non-degeneracy checks.  A pass here is agreement
; with the standard on these inputs by evaluation, which is evidence and not
; a proof; the proof is the correspondence in the book, and it says the two
; computations agree on EVERY input, vectors or not.
;
; Nothing here bears on collision resistance (A-CRYPTO, specs/failures.md).

(in-package "ACL2")
(include-book "../../books/sha256-stobj")
(include-book "../../books/records-shape")
(include-book "std/testing/must-fail" :dir :system)
(include-book "sha256-tests")

; -----------------------------------------------------------------------------
; Every entry the host may call is guard-verified.

(assert-event
 (equal (list (symbol-class 'fn-sha256-stobj (w state))
              (symbol-class 'fn-sha256-of-string (w state))
              (symbol-class 'fn-shs-string-octets (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The vectors, through both entries.  Expected values as in sha256-tests.

; empty
(assert-event
 (equal (fn-sha256-stobj nil)
        '(227 176 196 66 152 252 28 20 154 251 244 200 153 111 185 36 39 174 65 228 100 155 147 76 164 149 153 27 120 82 184 85)))
(assert-event
 (equal (fn-sha256-of-string "")
        '(227 176 196 66 152 252 28 20 154 251 244 200 153 111 185 36 39 174 65 228 100 155 147 76 164 149 153 27 120 82 184 85)))

; abc
(assert-event
 (equal (fn-sha256-stobj (fn-sha256-t-string "abc"))
        '(186 120 22 191 143 1 207 234 65 65 64 222 93 174 34 35 176 3 97 163 150 23 122 156 180 16 255 97 242 0 21 173)))
(assert-event
 (equal (fn-sha256-of-string "abc")
        '(186 120 22 191 143 1 207 234 65 65 64 222 93 174 34 35 176 3 97 163 150 23 122 156 180 16 255 97 242 0 21 173)))

; fips-56: the 56-octet message, which forces a second block of padding
(assert-event
 (equal (fn-sha256-stobj (fn-sha256-t-string "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
        '(36 141 106 97 210 6 56 184 229 192 38 147 12 62 96 57 163 60 228 89 100 255 33 103 246 236 237 212 25 219 6 193)))
(assert-event
 (equal (fn-sha256-of-string "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
        '(36 141 106 97 210 6 56 184 229 192 38 147 12 62 96 57 163 60 228 89 100 255 33 103 246 236 237 212 25 219 6 193)))

; fips-112
(assert-event
 (equal (fn-sha256-of-string "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")
        '(207 91 22 167 120 175 131 128 3 108 229 158 123 4 146 55 11 36 155 17 232 240 122 81 175 172 69 3 122 254 233 209)))

; one million repetitions of 'a', through both entries
(assert-event
 (equal (fn-sha256-stobj (fn-sha256-t-repeat 1000000 97))
        '(205 199 110 92 153 20 251 146 129 161 199 226 132 215 62 103 241 128 154 72 164 151 32 14 4 109 57 204 199 17 44 208)))
(assert-event
 (equal (fn-sha256-of-string (coerce (make-list 1000000 :initial-element #\a) 'string))
        '(205 199 110 92 153 20 251 146 129 161 199 226 132 215 62 103 241 128 154 72 164 151 32 14 4 109 57 204 199 17 44 208)))

; The padding boundaries (section 5.1.1), against the list model by
; evaluation: 55 is the last length whose padding fits one block, 56 and 64
; force a second, 119 and 120 straddle the third.
(assert-event
 (let ((m (fn-sha256-t-repeat 55 97))) (equal (fn-sha256-stobj m) (fn-sha256 m))))
(assert-event
 (let ((m (fn-sha256-t-repeat 56 97))) (equal (fn-sha256-stobj m) (fn-sha256 m))))
(assert-event
 (let ((m (fn-sha256-t-repeat 63 97))) (equal (fn-sha256-stobj m) (fn-sha256 m))))
(assert-event
 (let ((m (fn-sha256-t-repeat 64 97))) (equal (fn-sha256-stobj m) (fn-sha256 m))))
(assert-event
 (let ((m (fn-sha256-t-repeat 65 97))) (equal (fn-sha256-stobj m) (fn-sha256 m))))
(assert-event
 (let ((m (fn-sha256-t-repeat 119 97))) (equal (fn-sha256-stobj m) (fn-sha256 m))))
(assert-event
 (let ((m (fn-sha256-t-repeat 120 97))) (equal (fn-sha256-stobj m) (fn-sha256 m))))

; -----------------------------------------------------------------------------
; Non-degeneracy, as sha256-tests has it for the list model.

(assert-event (not (equal (fn-sha256-stobj '(1 2 3)) (fn-sha256-stobj '(4 5 6)))))
(assert-event (not (equal (fn-sha256-stobj nil) (fn-sha256-t-repeat 32 0))))
(assert-event (not (equal (fn-sha256-stobj '(0)) (fn-sha256-stobj '(1)))))
(assert-event (not (equal (fn-sha256-of-string "a") (fn-sha256-of-string "b"))))

; The coercion is total and the shape holds off the octet domain, and the
; coerced input digests as the coerced octets: the stobj entry agrees with
; the list model there too, as the keystone says it does everywhere.
(assert-event (equal (len (fn-sha256-stobj 7)) 32))
(assert-event (equal (fn-sha256-stobj '(300 -1)) (fn-sha256-stobj '(44 255))))
(assert-event (equal (fn-sha256-stobj '(:a "b" 300)) (fn-sha256 '(:a "b" 300))))

; The string entry reads character codes, all 256 of them, not ASCII.
(assert-event
 (equal (fn-sha256-of-string (coerce (list (code-char 255) (code-char 0) (code-char 128)) 'string))
        (fn-sha256-stobj '(255 0 128))))

; -----------------------------------------------------------------------------
; The string octets are records-shape's: one notion of "the octets of a
; string" in the tree.

(local
 (defthm shs-t-char-octets-are-record-aux
   (equal (fn-shs-char-octets cs) (fn-record-string-octets-aux cs))
   :hints (("Goal" :in-theory (enable fn-shs-char-octets)))))

(defthm shs-t-string-octets-are-record-string-octets
  (implies (stringp s)
           (equal (fn-shs-string-octets s) (fn-record-string-octets s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-shs-string-octets))))

; -----------------------------------------------------------------------------
; Teeth.
;
; `fn-sha256-stobj-is-sha256' has no hypothesis.  `fn-sha256-stobj-is-sha256-
; of-octets' carries `fn-sha256-octet-listp' only because it is the instance
; of sha256's own `fn-sha256-is-of-octets-on-octets', which has it; the two
; sides agree on every object (the coercion checks above), so the hypothesis
; is proof-support there, not a boundary of the statement.
;
; `fn-sha256-of-string-is-sha256-of-octets' needs `stringp': on a list the
; entry reads `length' and `char' of a non-string, which are the length of
; the list and the code of nil, while `fn-shs-string-octets' of a non-string
; is nil.  Without the hypothesis the statement is false, and here is the
; separating witness, evaluated in the logic where the guard does not apply.

(must-fail
 (defthm shs-t-string-without-stringp
   (equal (fn-sha256-of-string s)
          (fn-sha256-of-octets (fn-shs-string-octets s)))))

(defthm shs-t-string-separates-on-a-list
  (not (equal (fn-sha256-of-string '(97))
              (fn-sha256-of-octets (fn-shs-string-octets '(97)))))
  :rule-classes nil)

; The correspondence, cited as the keystone is, on a witness that is not a
; vector: a message whose octets are not all below 128 and whose length is
; not a multiple of anything convenient.
(assert-event
 (let ((m '(0 255 128 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 200 201 202 203 204 205 206 207 208 209 210 211 212 213 214 215 216 217 218 219 220 221 222 223 224 225 226 227 228 229 230 231 232 233 234 235 236 237 238 239 240)))
   (and (equal (fn-sha256-stobj m) (fn-sha256 m))
        (equal (fn-sha256-stobj m) (fn-sha256-of-octets m)))))
