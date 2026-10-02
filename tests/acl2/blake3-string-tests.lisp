;; fn: the string-indexed BLAKE3 (books/blake3-string.lisp) and the Message-ID
;; tag built on it (books/msgid-tag-exec.lisp) against the official BLAKE3
;; vectors.
;;
;; What this book is evidence FOR and what it is not.  `fn-b3s-root-is-hash'
;; proves the string reader equal to `fn-b3-hash', and `fn-mlh-tag-x-is-tag'
;; proves the tag equal to its list model; neither can prove that the octets
;; are the ones BLAKE3 specifies.  The bridge is EVALUATION of the functions
;; the host calls against the published vectors: test_vectors.json at tag
;; 1.8.7, the expected octets COPIED from tests/acl2/blake3-tests.lisp (its
;; header carries the provenance and the file's SHA-256), never recomputed
;; here with `fn-blake3'.  The input of length n is the string whose
;; character i is (code-char (mod i 251)), so every length from 129 on carries
;; the high-bit characters 128..250; the key is "whats the Elvish word for
;; friend".  All 35 lengths, in the hash mode (the IV words of *fn-b3-iv*,
;; flags 0) and the keyed mode (the key's words by `fn-mlh-key-word', flags
;; *fn-b3-keyed-hash*): every chunk and block edge up to 8 chunks, 16 and 31
;; chunks, and 100 chunks.  The root's eight words are compared as 32
;; octets, each word least significant octet first, by this book's own
;; `fn-b3st-le-octets' (not the book's `fn-b3-words-octets').
;;
;; Also: two further keys against `fn-blake3-keyed' (books/blake3.lisp, itself
;; checked against all 35 keyed vectors by tests/acl2/blake3-tests.lisp); the
;; tag against the right-hand side of `fn-mlh-tag-x-is-tag' on Message-IDs
;; with high-bit characters and lengths 63, 64 and 65 under three keys; the
;; tag pinned to the official keyed vectors (the first eight octets read
;; little-endian, reduced to 60 bits, floored at 1); and labelled MUTATION
;; witnesses: the mode flag, a chunk counter and the ROOT flag each moved,
;; with the unmoved call asserted equal to the vector beside it.
;;
;; A failure here is a defect; a pass is agreement on these inputs, which is
;; evidence, not a proof of agreement on all inputs.  Nothing here bears on
;; collision resistance (A-CRYPTO, specs/failures.md).

(in-package "ACL2")
(include-book "../../books/msgid-tag-exec")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; Inputs, keys and the octet reading of words.

(defun fn-b3st-chars-below (i acc)
  ; Characters (mod j 251) for j below I, consed onto ACC in order.
  (declare (xargs :guard (and (natp i) (character-listp acc))))
  (if (zp i)
      acc
    (fn-b3st-chars-below (- i 1) (cons (code-char (mod (- i 1) 251)) acc))))

(defthm fn-b3st-character-listp-of-chars-below
  (implies (character-listp acc)
           (character-listp (fn-b3st-chars-below i acc))))

(defun fn-b3st-string (n)
  ; The vector input of length N as a string.
  (declare (xargs :guard (natp n)))
  (coerce (fn-b3st-chars-below n nil) 'string))

(defun fn-b3st-octets-below (i acc)
  ; The same input as an octet list (for `fn-blake3-keyed').
  (declare (xargs :guard (and (natp i) (true-listp acc))))
  (if (zp i)
      acc
    (fn-b3st-octets-below (- i 1) (cons (mod (- i 1) 251) acc))))

(defconst *fn-b3st-key*
  ; "whats the Elvish word for friend" (test_vectors.json's key).
  '(119 104 97 116 115 32 116 104 101 32 69 108 118 105 115 104 32 119 111 114 100 32 102 111 114 32 102 114 105 101 110 100))

(defconst *fn-b3st-key2*
  ; The octets 0..31.
  '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31))

(defconst *fn-b3st-key3*
  ; (7 + 151 i) mod 256: high-bit octets throughout, no order.
  '(7 158 53 204 99 250 145 40 191 86 237 132 27 178 73 224 119 14 165 60 211 106 1 152 47 198 93 244 139 34 185 80))

(defun fn-b3st-le-word (w)
  ; Four octets of the 32-bit word W, least significant first.
  (declare (xargs :guard t))
  (let ((w (nfix w)))
    (list (mod w 256) (mod (floor w 256) 256)
          (mod (floor w 65536) 256) (mod (floor w 16777216) 256))))

(defun fn-b3st-le-octets (ws)
  (declare (xargs :guard (true-listp ws)))
  (if (endp ws)
      nil
    (append (fn-b3st-le-word (car ws)) (fn-b3st-le-octets (cdr ws)))))

(defun fn-b3st-le-nat (k octets)
  ; The first K octets as a little-endian natural.
  (declare (xargs :guard (and (natp k) (true-listp octets))))
  (if (or (zp k) (endp octets))
      0
    (+ (nfix (car octets)) (* 256 (fn-b3st-le-nat (- k 1) (cdr octets))))))

(defmacro fn-b3st-list8 (form)
  `(mv-let (o0 o1 o2 o3 o4 o5 o6 o7) ,form (list o0 o1 o2 o3 o4 o5 o6 o7)))

; -----------------------------------------------------------------------------
; The host-called entries, read as octets.

(defun fn-b3st-plain (s)
  ; The hash mode: the IV as the key words, flags 0 (`fn-blake3').
  (declare (xargs :guard (stringp s)))
  (fn-b3st-le-octets
   (fn-b3st-list8
    (fn-b3s-root (nth 0 *fn-b3-iv*) (nth 1 *fn-b3-iv*) (nth 2 *fn-b3-iv*) (nth 3 *fn-b3-iv*)
                 (nth 4 *fn-b3-iv*) (nth 5 *fn-b3-iv*) (nth 6 *fn-b3-iv*) (nth 7 *fn-b3-iv*)
                 0 s))))

(defun fn-b3st-keyed (key s)
  ; keyed_hash: the key's eight words as the tag reads them, flags
  ; *fn-b3-keyed-hash* (`fn-blake3-keyed', `fn-mlh-tag-x').
  (declare (xargs :guard (stringp s)))
  (fn-b3st-le-octets
   (fn-b3st-list8
    (fn-b3s-root (fn-mlh-key-word 0 key) (fn-mlh-key-word 1 key)
                 (fn-mlh-key-word 2 key) (fn-mlh-key-word 3 key)
                 (fn-mlh-key-word 4 key) (fn-mlh-key-word 5 key)
                 (fn-mlh-key-word 6 key) (fn-mlh-key-word 7 key)
                 *fn-b3-keyed-hash* s))))

(defun fn-b3st-tag (key s)
  (declare (xargs :guard (stringp s)))
  (fn-mlh-tag-x s (fn-mlh-key-word 0 key) (fn-mlh-key-word 1 key)
                (fn-mlh-key-word 2 key) (fn-mlh-key-word 3 key)
                (fn-mlh-key-word 4 key) (fn-mlh-key-word 5 key)
                (fn-mlh-key-word 6 key) (fn-mlh-key-word 7 key)))

(defun fn-b3st-tag-spec (key s)
  ; The right-hand side of `fn-mlh-tag-x-is-tag'.
  (declare (xargs :guard (stringp s)))
  (max 1 (mod (fn-mpxt-word 8 (fn-ns-mac key (fn-record-string-octets s)))
              1152921504606846976)))

(defun fn-b3st-tag-of-vector (octets)
  ; The tag the specification gives for a keyed digest: its first eight
  ; octets little-endian, reduced to 60 bits, floored at 1.
  (declare (xargs :guard (true-listp octets)))
  (max 1 (mod (fn-b3st-le-nat 8 octets) 1152921504606846976)))

; =============================================================================
; 1. The official vectors through `fn-b3s-root', both modes, all 35 lengths.

; input_len 0
(assert-event
 (let ((s (fn-b3st-string 0)))
   (and (equal (length s) 0)
        (equal (fn-b3st-plain s)
               '(175 19 73 185 245 249 161 166 160 64 77 234 54 220 201 73 155 203 37 201 173 193 18 183 204 154 147 202 228 31 50 98))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(146 178 183 86 4 237 60 118 31 157 111 98 57 44 138 146 39 173 14 163 240 149 115 231 131 241 73 138 78 214 13 38)))))

; input_len 1
(assert-event
 (let ((s (fn-b3st-string 1)))
   (and (equal (length s) 1)
        (equal (fn-b3st-plain s)
               '(45 58 222 223 241 27 97 241 76 136 110 53 175 160 54 115 109 205 135 167 77 39 181 193 81 2 37 208 245 146 226 19))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(109 120 120 223 255 47 72 86 53 211 144 19 39 138 225 79 20 84 184 192 163 162 211 75 193 171 56 34 138 128 201 91)))))

; input_len 2
(assert-event
 (let ((s (fn-b3st-string 2)))
   (and (equal (length s) 2)
        (equal (fn-b3st-plain s)
               '(123 112 21 187 146 207 11 49 128 55 112 42 108 221 129 222 228 18 36 247 52 104 76 44 18 44 214 53 156 177 238 99))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(83 146 221 174 14 10 105 213 244 1 96 70 44 189 155 216 137 55 80 130 255 34 74 201 199 88 128 43 122 111 210 10)))))

; input_len 3
(assert-event
 (let ((s (fn-b3st-string 3)))
   (and (equal (length s) 3)
        (equal (fn-b3st-plain s)
               '(225 190 77 122 138 181 86 10 164 25 158 234 51 152 73 186 142 41 61 85 202 10 129 0 103 38 209 132 81 158 100 127))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(57 230 123 118 181 160 7 212 146 25 105 119 159 230 102 218 103 181 33 59 9 96 132 171 103 71 66 240 213 236 98 185)))))

; input_len 4
(assert-event
 (let ((s (fn-b3st-string 4)))
   (and (equal (length s) 4)
        (equal (fn-b3st-plain s)
               '(243 15 90 178 143 224 71 144 64 55 247 123 109 164 254 161 226 114 65 197 209 50 99 141 139 237 206 157 64 73 79 50))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(118 113 221 229 144 201 93 90 201 97 102 81 255 90 160 162 123 238 89 19 163 72 224 83 184 170 145 8 145 127 224 112)))))

; input_len 5
(assert-event
 (let ((s (fn-b3st-string 5)))
   (and (equal (length s) 5)
        (equal (fn-b3st-plain s)
               '(180 11 68 223 217 126 122 132 169 150 169 26 248 184 81 136 198 108 18 105 64 186 122 173 46 122 230 179 133 64 42 162))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(115 172 105 238 207 40 104 148 216 16 32 24 166 252 114 159 75 31 66 71 211 112 63 105 189 198 165 254 62 12 132 97)))))

; input_len 6
(assert-event
 (let ((s (fn-b3st-string 6)))
   (and (equal (length s) 6)
        (equal (fn-b3st-plain s)
               '(6 196 232 255 182 135 47 173 150 249 170 202 94 238 21 83 235 98 174 208 173 113 152 206 244 46 135 246 166 22 200 68))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(130 211 25 157 0 19 3 86 130 204 127 42 57 157 76 33 37 68 55 106 131 154 168 99 160 244 201 18 32 202 122 109)))))

; input_len 7
(assert-event
 (let ((s (fn-b3st-string 7)))
   (and (equal (length s) 7)
        (equal (fn-b3st-plain s)
               '(63 135 112 243 135 250 173 8 250 169 216 65 78 159 68 154 198 142 111 240 65 127 103 63 96 42 100 106 137 20 25 254))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(175 10 126 195 130 174 220 12 253 98 110 73 231 98 139 199 163 83 164 203 16 136 85 84 26 86 81 191 100 251 178 138)))))

; input_len 8
(assert-event
 (let ((s (fn-b3st-string 8)))
   (and (equal (length s) 8)
        (equal (fn-b3st-plain s)
               '(35 81 32 125 4 252 22 173 228 60 202 176 134 0 147 156 124 31 167 10 92 10 172 167 96 99 208 76 50 40 234 235))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(190 47 84 149 198 28 186 27 179 72 163 73 72 192 4 4 94 59 212 218 232 240 254 130 191 68 208 218 36 90 6 0)))))

; input_len 63
(assert-event
 (let ((s (fn-b3st-string 63)))
   (and (equal (length s) 63)
        (equal (fn-b3st-plain s)
               '(233 188 55 165 148 218 173 131 190 148 112 223 127 123 55 152 41 124 61 131 76 232 11 168 93 110 32 118 39 183 219 123))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(187 30 181 212 175 167 147 193 235 221 159 176 141 239 108 54 209 0 150 152 106 224 207 225 72 205 16 17 112 206 55 174)))))

; input_len 64
(assert-event
 (let ((s (fn-b3st-string 64)))
   (and (equal (length s) 64)
        (equal (fn-b3st-plain s)
               '(78 237 113 65 234 74 92 212 183 136 96 107 210 63 70 226 18 175 156 172 235 172 220 125 31 76 109 199 242 81 27 152))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(186 140 237 54 243 39 112 13 33 63 18 11 26 32 122 59 140 4 51 5 40 88 111 65 77 9 242 247 217 204 183 230)))))

; input_len 65
(assert-event
 (let ((s (fn-b3st-string 65)))
   (and (equal (length s) 65)
        (equal (fn-b3st-plain s)
               '(222 30 95 160 190 112 223 109 43 232 255 253 14 153 206 170 142 182 232 201 58 99 242 216 209 195 14 203 107 38 61 238))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(192 164 237 239 162 210 172 203 146 119 195 113 172 18 252 219 181 41 136 168 110 220 84 240 113 110 21 145 180 50 110 114)))))

; input_len 127
(assert-event
 (let ((s (fn-b3st-string 127)))
   (and (equal (length s) 127)
        (equal (fn-b3st-plain s)
               '(216 18 147 253 168 99 240 8 192 158 146 252 56 42 129 245 160 180 161 37 28 186 22 52 1 106 15 134 166 189 100 13))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(198 66 0 174 125 250 243 85 119 172 90 149 33 196 120 99 251 113 81 74 59 202 209 136 25 33 139 129 141 232 88 24)))))

; input_len 128
(assert-event
 (let ((s (fn-b3st-string 128)))
   (and (equal (length s) 128)
        (equal (fn-b3st-plain s)
               '(241 126 87 5 100 178 101 120 195 59 183 244 70 67 245 57 98 75 5 223 26 118 200 31 48 172 213 72 196 75 69 239))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(176 79 225 85 119 69 114 103 255 59 111 60 148 125 147 190 88 30 126 58 75 1 134 121 18 94 175 134 246 166 40 236)))))

; input_len 129
(assert-event
 (let ((s (fn-b3st-string 129)))
   (and (equal (length s) 129)
        (equal (fn-b3st-plain s)
               '(104 58 170 233 243 197 186 55 234 175 7 42 237 15 158 48 186 192 134 81 55 186 230 139 31 222 76 162 174 189 203 18))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(212 166 77 174 108 220 203 172 30 82 135 245 79 23 197 249 133 16 84 87 193 162 236 24 120 235 212 181 126 32 211 143)))))

; input_len 1023
(assert-event
 (let ((s (fn-b3st-string 1023)))
   (and (equal (length s) 1023)
        (equal (fn-b3st-plain s)
               '(16 16 137 112 238 218 62 185 50 186 172 20 40 199 162 22 59 14 146 76 154 158 37 179 91 186 114 178 143 112 189 17))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(201 81 236 223 3 40 141 15 204 150 238 52 19 86 61 138 109 53 137 84 127 44 47 179 109 151 134 71 15 27 157 110)))))

; input_len 1024
(assert-event
 (let ((s (fn-b3st-string 1024)))
   (and (equal (length s) 1024)
        (equal (fn-b3st-plain s)
               '(66 33 71 57 240 149 164 6 243 252 131 222 184 137 116 74 192 13 248 49 193 13 170 85 24 155 93 18 28 133 90 247))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(117 196 111 111 61 158 180 245 94 202 174 228 128 219 115 46 108 33 5 84 111 30 103 80 3 104 124 49 113 156 123 164)))))

; input_len 1025
(assert-event
 (let ((s (fn-b3st-string 1025)))
   (and (equal (length s) 1025)
        (equal (fn-b3st-plain s)
               '(208 2 120 174 71 235 39 179 79 174 207 103 180 254 38 63 130 213 65 41 22 193 255 217 124 140 183 251 129 75 132 68))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(53 125 197 93 224 199 227 130 201 0 253 110 50 10 204 4 20 107 224 29 182 168 206 114 16 183 24 155 214 100 234 105)))))

; input_len 2048
(assert-event
 (let ((s (fn-b3st-string 2048)))
   (and (equal (length s) 2048)
        (equal (fn-b3st-plain s)
               '(231 118 182 2 140 124 210 42 77 11 161 130 168 191 98 32 93 46 245 118 70 126 131 142 214 242 82 155 133 251 162 74))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(135 156 241 250 46 160 231 145 38 203 16 99 97 122 5 182 173 157 11 105 109 13 117 124 240 83 67 159 96 169 157 209)))))

; input_len 2049
(assert-event
 (let ((s (fn-b3st-string 2049)))
   (and (equal (length s) 2049)
        (equal (fn-b3st-plain s)
               '(95 77 114 244 13 122 95 130 177 92 162 178 228 75 29 227 194 239 134 196 38 201 92 26 240 182 135 149 34 86 48 48))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(159 41 112 9 2 247 200 110 81 77 220 77 241 227 4 159 37 139 36 114 182 221 82 103 246 27 241 57 131 183 141 213)))))

; input_len 3072
(assert-event
 (let ((s (fn-b3st-string 3072)))
   (and (equal (length s) 3072)
        (equal (fn-b3st-plain s)
               '(185 140 176 255 54 35 190 3 50 107 55 61 230 185 9 82 24 81 62 100 241 238 46 221 37 37 199 173 30 92 255 210))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(4 74 14 123 23 42 49 45 192 42 76 154 129 140 3 111 250 39 118 54 141 127 82 130 104 210 230 181 223 25 23 112)))))

; input_len 3073
(assert-event
 (let ((s (fn-b3st-string 3073)))
   (and (equal (length s) 3073)
        (equal (fn-b3st-plain s)
               '(113 36 180 149 1 1 47 129 204 127 17 202 6 158 201 34 108 236 184 162 200 80 207 230 68 227 39 210 45 62 28 211))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(104 222 222 155 239 0 186 137 228 63 49 166 130 95 76 244 51 56 159 237 174 117 192 78 233 240 207 22 164 39 201 90)))))

; input_len 4096
(assert-event
 (let ((s (fn-b3st-string 4096)))
   (and (equal (length s) 4096)
        (equal (fn-b3st-plain s)
               '(1 80 148 1 63 87 165 39 123 89 216 71 92 5 1 4 44 11 100 46 83 27 10 28 143 88 210 22 50 41 233 105))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(190 252 102 10 234 47 23 24 136 76 216 222 185 144 40 17 211 50 244 252 74 56 207 124 115 0 213 151 160 129 191 192)))))

; input_len 4097
(assert-event
 (let ((s (fn-b3st-string 4097)))
   (and (equal (length s) 4097)
        (equal (fn-b3st-plain s)
               '(155 64 82 179 143 28 95 200 177 249 255 122 199 178 124 210 66 72 123 61 137 13 21 201 106 28 37 184 170 15 185 149))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(0 223 148 12 211 107 185 250 124 187 195 85 103 68 224 219 200 25 20 1 175 231 5 32 186 41 46 227 202 128 171 188)))))

; input_len 5120
(assert-event
 (let ((s (fn-b3st-string 5120)))
   (and (equal (length s) 5120)
        (equal (fn-b3st-plain s)
               '(156 173 193 95 237 139 93 133 69 98 178 106 149 54 217 112 124 173 237 169 177 67 151 143 49 154 179 66 48 83 88 51))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(44 73 62 72 233 185 191 49 224 85 58 34 178 53 3 192 163 56 143 3 92 236 230 142 180 56 210 47 161 148 62 32)))))

; input_len 5121
(assert-event
 (let ((s (fn-b3st-string 5121)))
   (and (equal (length s) 5121)
        (equal (fn-b3st-plain s)
               '(98 139 210 203 32 4 105 74 218 171 123 189 119 138 37 223 37 196 123 157 65 85 165 95 143 189 121 242 254 21 76 255))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(108 207 28 52 117 62 122 4 77 184 7 152 236 208 120 42 143 118 243 53 99 172 202 221 191 187 46 14 164 178 208 36)))))

; input_len 6144
(assert-event
 (let ((s (fn-b3st-string 6144)))
   (and (equal (length s) 6144)
        (equal (fn-b3st-plain s)
               '(62 46 91 116 224 72 243 173 214 210 31 170 179 248 58 164 77 59 34 120 175 184 59 128 179 195 81 100 235 236 162 5))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(61 107 109 33 40 29 10 222 91 43 1 106 228 3 76 93 236 16 202 126 71 95 144 247 110 172 113 56 233 188 143 29)))))

; input_len 6145
(assert-event
 (let ((s (fn-b3st-string 6145)))
   (and (equal (length s) 6145)
        (equal (fn-b3st-plain s)
               '(241 50 58 134 49 68 108 197 5 54 169 247 5 238 92 182 25 66 77 70 136 127 60 55 108 105 91 112 224 240 80 127))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(154 195 1 233 227 158 69 227 37 10 126 59 61 247 1 170 15 182 136 159 189 128 238 236 242 141 188 99 0 251 197 57)))))

; input_len 7168
(assert-event
 (let ((s (fn-b3st-string 7168)))
   (and (equal (length s) 7168)
        (equal (fn-b3st-plain s)
               '(97 218 149 126 194 73 154 149 214 184 2 62 43 14 96 78 199 246 181 14 128 169 103 139 137 210 98 142 153 173 167 122))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(180 40 53 228 14 157 74 127 66 173 140 192 79 133 169 99 167 110 24 25 131 119 237 132 173 221 234 236 172 198 243 252)))))

; input_len 7169
(assert-event
 (let ((s (fn-b3st-string 7169)))
   (and (equal (length s) 7169)
        (equal (fn-b3st-plain s)
               '(160 3 252 122 81 117 74 155 60 127 174 3 103 171 61 120 45 204 242 136 85 160 61 67 95 140 254 116 96 94 120 23))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(237 155 26 146 44 4 111 219 61 66 58 227 78 20 59 5 202 27 242 139 113 4 50 133 123 247 56 188 237 191 165 17)))))

; input_len 8192
(assert-event
 (let ((s (fn-b3st-string 8192)))
   (and (equal (length s) 8192)
        (equal (fn-b3st-plain s)
               '(170 231 146 72 76 142 254 79 25 226 202 125 55 29 140 70 127 251 16 116 141 138 90 26 229 121 148 143 113 138 42 99))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(220 150 55 200 132 90 119 11 76 191 118 184 218 236 14 235 247 220 46 172 17 73 133 23 240 141 68 200 252 0 213 138)))))

; input_len 8193
(assert-event
 (let ((s (fn-b3st-string 8193)))
   (and (equal (length s) 8193)
        (equal (fn-b3st-plain s)
               '(186 182 192 156 184 206 140 244 89 38 19 152 210 231 174 243 87 0 191 72 129 22 206 185 74 54 208 245 241 183 188 59))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(149 74 42 117 66 12 141 101 71 227 186 91 152 217 99 230 250 100 145 173 220 140 2 49 137 204 81 152 33 180 161 245)))))

; input_len 16384
(assert-event
 (let ((s (fn-b3st-string 16384)))
   (and (equal (length s) 16384)
        (equal (fn-b3st-plain s)
               '(248 117 214 100 109 226 137 133 100 111 52 238 19 190 154 87 111 213 21 247 107 91 10 38 187 50 71 53 4 29 221 228))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(158 159 196 235 124 240 129 234 124 71 209 128 119 144 237 33 27 254 197 106 162 91 183 3 119 132 193 60 75 112 123 13)))))

; input_len 31744
(assert-event
 (let ((s (fn-b3st-string 31744)))
   (and (equal (length s) 31744)
        (equal (fn-b3st-plain s)
               '(98 182 150 14 26 68 188 193 235 26 97 26 141 98 53 182 180 183 143 50 231 171 196 251 76 108 220 206 148 137 92 71))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(239 165 59 56 154 182 124 89 61 186 98 77 137 141 15 115 83 171 153 228 172 157 66 48 46 230 76 191 153 57 164 25)))))

; input_len 102400
(assert-event
 (let ((s (fn-b3st-string 102400)))
   (and (equal (length s) 102400)
        (equal (fn-b3st-plain s)
               '(188 62 61 65 161 20 107 6 154 191 250 211 192 212 72 96 207 102 67 144 175 206 77 150 97 247 144 46 121 67 224 133))
        (equal (fn-b3st-keyed *fn-b3st-key* s)
               '(28 53 209 165 129 16 131 253 113 25 245 213 209 186 2 123 77 1 192 198 196 159 182 255 44 247 83 147 234 93 180 167)))))

; =============================================================================
; 2. Further keys against `fn-blake3-keyed' (books/blake3.lisp; its keyed
; mode is checked against all 35 official keyed vectors by
; tests/acl2/blake3-tests.lisp).  Same inputs, as a string and as octets.

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key2* (fn-b3st-string 0))
        (fn-blake3-keyed *fn-b3st-key2* (fn-b3st-octets-below 0 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key2* (fn-b3st-string 1))
        (fn-blake3-keyed *fn-b3st-key2* (fn-b3st-octets-below 1 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key2* (fn-b3st-string 63))
        (fn-blake3-keyed *fn-b3st-key2* (fn-b3st-octets-below 63 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key2* (fn-b3st-string 64))
        (fn-blake3-keyed *fn-b3st-key2* (fn-b3st-octets-below 64 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key2* (fn-b3st-string 65))
        (fn-blake3-keyed *fn-b3st-key2* (fn-b3st-octets-below 65 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key2* (fn-b3st-string 1024))
        (fn-blake3-keyed *fn-b3st-key2* (fn-b3st-octets-below 1024 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key2* (fn-b3st-string 1025))
        (fn-blake3-keyed *fn-b3st-key2* (fn-b3st-octets-below 1025 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key2* (fn-b3st-string 2049))
        (fn-blake3-keyed *fn-b3st-key2* (fn-b3st-octets-below 2049 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key2* (fn-b3st-string 4097))
        (fn-blake3-keyed *fn-b3st-key2* (fn-b3st-octets-below 4097 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key3* (fn-b3st-string 0))
        (fn-blake3-keyed *fn-b3st-key3* (fn-b3st-octets-below 0 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key3* (fn-b3st-string 1))
        (fn-blake3-keyed *fn-b3st-key3* (fn-b3st-octets-below 1 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key3* (fn-b3st-string 63))
        (fn-blake3-keyed *fn-b3st-key3* (fn-b3st-octets-below 63 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key3* (fn-b3st-string 64))
        (fn-blake3-keyed *fn-b3st-key3* (fn-b3st-octets-below 64 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key3* (fn-b3st-string 65))
        (fn-blake3-keyed *fn-b3st-key3* (fn-b3st-octets-below 65 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key3* (fn-b3st-string 1024))
        (fn-blake3-keyed *fn-b3st-key3* (fn-b3st-octets-below 1024 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key3* (fn-b3st-string 1025))
        (fn-blake3-keyed *fn-b3st-key3* (fn-b3st-octets-below 1025 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key3* (fn-b3st-string 2049))
        (fn-blake3-keyed *fn-b3st-key3* (fn-b3st-octets-below 2049 nil))))

(assert-event
 (equal (fn-b3st-keyed *fn-b3st-key3* (fn-b3st-string 4097))
        (fn-blake3-keyed *fn-b3st-key3* (fn-b3st-octets-below 4097 nil))))

; The keys are different keys: the outputs differ (a key reader that ignored
; its key would pass the comparisons above only if `fn-blake3-keyed' did too).
(assert-event
 (let ((s (fn-b3st-string 65)))
   (and (not (equal (fn-b3st-keyed *fn-b3st-key2* s) (fn-b3st-keyed *fn-b3st-key3* s)))
        (not (equal (fn-b3st-keyed *fn-b3st-key2* s) (fn-b3st-keyed *fn-b3st-key* s)))
        (not (equal (fn-b3st-keyed *fn-b3st-key3* s) (fn-b3st-keyed *fn-b3st-key* s))))))

; =============================================================================
; 3. The Message-ID tag.

(defun fn-b3st-mixed-below (i acc)
  ; Characters alternating ASCII letters and high-bit 128..250.
  (declare (xargs :guard (and (natp i) (character-listp acc))))
  (if (zp i)
      acc
    (fn-b3st-mixed-below (- i 1)
                         (cons (if (evenp (- i 1))
                                   (code-char (+ 97 (mod (- i 1) 26)))
                                 (code-char (+ 128 (mod (* 37 (- i 1)) 123))))
                               acc))))

(defthm fn-b3st-character-listp-of-mixed-below
  (implies (character-listp acc)
           (character-listp (fn-b3st-mixed-below i acc))))

(defun fn-b3st-msgid (n)
  ; "<" ++ N-4 mixed characters ++ "@h>": a Message-ID of length N (N >= 4).
  (declare (xargs :guard (natp n)))
  (coerce (cons #\< (fn-b3st-mixed-below (nfix (- n 4)) (list #\@ #\h #\>))) 'string))

(defconst *fn-b3st-msgids*
  (list "<a@b>"
        "<20261001.123456.42@fn.fg-goose.online>"
        (coerce (list #\< (code-char 200) (code-char 233) (code-char 250) (code-char 128)
                      #\@ #\x #\. (code-char 255) #\>)
                'string)
        (fn-b3st-msgid 63)
        (fn-b3st-msgid 64)
        (fn-b3st-msgid 65)
        (fn-b3st-msgid 129)))

(assert-event
 (and (equal (length (nth 3 *fn-b3st-msgids*)) 63)
      (equal (length (nth 4 *fn-b3st-msgids*)) 64)
      (equal (length (nth 5 *fn-b3st-msgids*)) 65)
      (equal (char-code (char (nth 5 *fn-b3st-msgids*) 2)) (+ 128 37))))

(defun fn-b3st-tags-agree (key ids)
  ; Each tag equals the specified tag, and is a positive natural below 2^60.
  (declare (xargs :guard (string-listp ids)))
  (if (endp ids)
      t
    (and (equal (fn-b3st-tag key (car ids)) (fn-b3st-tag-spec key (car ids)))
         (posp (fn-b3st-tag key (car ids)))
         (< (fn-b3st-tag key (car ids)) 1152921504606846976)
         (fn-b3st-tags-agree key (cdr ids)))))


(assert-event (fn-b3st-tags-agree *fn-b3st-key* *fn-b3st-msgids*))

(assert-event (fn-b3st-tags-agree *fn-b3st-key2* *fn-b3st-msgids*))

(assert-event (fn-b3st-tags-agree *fn-b3st-key3* *fn-b3st-msgids*))


; The tag pinned to the official keyed vectors, by the specification's own
; reading of the digest (not through `fn-ns-mac' or `fn-mpxt-word').

(assert-event
 (equal (fn-b3st-tag *fn-b3st-key* (fn-b3st-string 1))
        (fn-b3st-tag-of-vector '(109 120 120 223 255 47 72 86 53 211 144 19 39 138 225 79 20 84 184 192 163 162 211 75 193 171 56 34 138 128 201 91))))

(assert-event
 (equal (fn-b3st-tag *fn-b3st-key* (fn-b3st-string 63))
        (fn-b3st-tag-of-vector '(187 30 181 212 175 167 147 193 235 221 159 176 141 239 108 54 209 0 150 152 106 224 207 225 72 205 16 17 112 206 55 174))))

(assert-event
 (equal (fn-b3st-tag *fn-b3st-key* (fn-b3st-string 64))
        (fn-b3st-tag-of-vector '(186 140 237 54 243 39 112 13 33 63 18 11 26 32 122 59 140 4 51 5 40 88 111 65 77 9 242 247 217 204 183 230))))

(assert-event
 (equal (fn-b3st-tag *fn-b3st-key* (fn-b3st-string 65))
        (fn-b3st-tag-of-vector '(192 164 237 239 162 210 172 203 146 119 195 113 172 18 252 219 181 41 136 168 110 220 84 240 113 110 21 145 180 50 110 114))))

(assert-event
 (equal (fn-b3st-tag *fn-b3st-key* (fn-b3st-string 129))
        (fn-b3st-tag-of-vector '(212 166 77 174 108 220 203 172 30 82 135 245 79 23 197 249 133 16 84 87 193 162 236 24 120 235 212 181 126 32 211 143))))

(assert-event
 (equal (fn-b3st-tag *fn-b3st-key* (fn-b3st-string 1025))
        (fn-b3st-tag-of-vector '(53 125 197 93 224 199 227 130 201 0 253 110 50 10 204 4 20 107 224 29 182 168 206 114 16 183 24 155 214 100 234 105))))


; Different Message-IDs, different keys: different tags here.
(assert-event
 (and (not (equal (fn-b3st-tag *fn-b3st-key* (nth 4 *fn-b3st-msgids*))
                  (fn-b3st-tag *fn-b3st-key* (nth 5 *fn-b3st-msgids*))))
      (not (equal (fn-b3st-tag *fn-b3st-key* (nth 0 *fn-b3st-msgids*))
                  (fn-b3st-tag *fn-b3st-key2* (nth 0 *fn-b3st-msgids*))))))

; =============================================================================
; 4. Mutation witnesses.  Each pairs the lower-level call with its arguments
; as `fn-b3s-root' passes them (asserted EQUAL to the vector) with one
; argument moved (asserted NOT equal), so the inequality is that argument's.

(defun fn-b3st-chunk-octets (q e counter flags rootfl s)
  ; The IV as the chaining value, the chunk [Q, E).
  (declare (xargs :guard (and (natp q) (natp e) (natp counter) (natp flags) (natp rootfl)
                              (<= q e) (stringp s) (<= e (length s)))))
  (fn-b3st-le-octets
   (fn-b3st-list8
    (fn-b3s-chunk (nth 0 *fn-b3-iv*) (nth 1 *fn-b3-iv*) (nth 2 *fn-b3-iv*) (nth 3 *fn-b3-iv*)
                  (nth 4 *fn-b3-iv*) (nth 5 *fn-b3-iv*) (nth 6 *fn-b3-iv*) (nth 7 *fn-b3-iv*)
                  q e counter flags t rootfl s))))

(defun fn-b3st-block-octets (e counter blen fl s)
  ; The IV as the chaining value, the block at 0.
  (declare (xargs :guard (and (natp e) (stringp s) (<= e (length s)))))
  (fn-b3st-le-octets
   (fn-b3st-list8
    (fn-b3s-block (nth 0 *fn-b3-iv*) (nth 1 *fn-b3-iv*) (nth 2 *fn-b3-iv*) (nth 3 *fn-b3-iv*)
                  (nth 4 *fn-b3-iv*) (nth 5 *fn-b3-iv*) (nth 6 *fn-b3-iv*) (nth 7 *fn-b3-iv*)
                  0 e counter blen fl s))))

(defun fn-b3st-top-octets (flags lcounter rcounter topfl s)
  ; `fn-b3s-root''s step above 1024 octets with the IV as the key, its two
  ; subtrees' counters and the top compression's flags as arguments: the
  ; root passes LCOUNTER 0, RCOUNTER the left subtree's chunk count, TOPFL
  ; FLAGS | PARENT | ROOT.
  (declare (xargs :guard (and (natp flags) (natp lcounter) (natp rcounter) (natp topfl)
                              (stringp s) (< 1024 (length s)))))
  (let* ((n (length s))
         (ll (* 1024 (fn-b3-left-chunks 1 n))))
    (mv-let (l0 l1 l2 l3 l4 l5 l6 l7)
      (fn-b3s-node (nth 0 *fn-b3-iv*) (nth 1 *fn-b3-iv*) (nth 2 *fn-b3-iv*) (nth 3 *fn-b3-iv*)
                   (nth 4 *fn-b3-iv*) (nth 5 *fn-b3-iv*) (nth 6 *fn-b3-iv*) (nth 7 *fn-b3-iv*)
                   0 ll lcounter flags s)
      (mv-let (r0 r1 r2 r3 r4 r5 r6 r7)
        (fn-b3s-node (nth 0 *fn-b3-iv*) (nth 1 *fn-b3-iv*) (nth 2 *fn-b3-iv*) (nth 3 *fn-b3-iv*)
                     (nth 4 *fn-b3-iv*) (nth 5 *fn-b3-iv*) (nth 6 *fn-b3-iv*) (nth 7 *fn-b3-iv*)
                     ll n rcounter flags s)
        (fn-b3st-le-octets
         (fn-b3st-list8
          (fn-b3-compress-core (nth 0 *fn-b3-iv*) (nth 1 *fn-b3-iv*) (nth 2 *fn-b3-iv*) (nth 3 *fn-b3-iv*)
                               (nth 4 *fn-b3-iv*) (nth 5 *fn-b3-iv*) (nth 6 *fn-b3-iv*) (nth 7 *fn-b3-iv*)
                               l0 l1 l2 l3 l4 l5 l6 l7 r0 r1 r2 r3 r4 r5 r6 r7
                               0 64 topfl)))))))


(defconst *fn-b3st-v64-plain* '(78 237 113 65 234 74 92 212 183 136 96 107 210 63 70 226 18 175 156 172 235 172 220 125 31 76 109 199 242 81 27 152))
(defconst *fn-b3st-v65-plain* '(222 30 95 160 190 112 223 109 43 232 255 253 14 153 206 170 142 182 232 201 58 99 242 216 209 195 14 203 107 38 61 238))
(defconst *fn-b3st-v65-keyed* '(192 164 237 239 162 210 172 203 146 119 195 113 172 18 252 219 181 41 136 168 110 220 84 240 113 110 21 145 180 50 110 114))
(defconst *fn-b3st-v1024-plain* '(66 33 71 57 240 149 164 6 243 252 131 222 184 137 116 74 192 13 248 49 193 13 170 85 24 155 93 18 28 133 90 247))
(defconst *fn-b3st-v2049-plain* '(95 77 114 244 13 122 95 130 177 92 162 178 228 75 29 227 194 239 134 196 38 201 92 26 240 182 135 149 34 86 48 48))

; MUTATION (mode flag): the vector key's words with flags 0, and the IV with
; flags KEYED_HASH, each leave its vector.
(assert-event
 (let ((s (fn-b3st-string 65)))
   (and (equal (fn-b3st-keyed *fn-b3st-key* s) *fn-b3st-v65-keyed*)
        (not (equal (fn-b3st-le-octets
                     (fn-b3st-list8
                      (fn-b3s-root (fn-mlh-key-word 0 *fn-b3st-key*) (fn-mlh-key-word 1 *fn-b3st-key*)
                                   (fn-mlh-key-word 2 *fn-b3st-key*) (fn-mlh-key-word 3 *fn-b3st-key*)
                                   (fn-mlh-key-word 4 *fn-b3st-key*) (fn-mlh-key-word 5 *fn-b3st-key*)
                                   (fn-mlh-key-word 6 *fn-b3st-key*) (fn-mlh-key-word 7 *fn-b3st-key*)
                                   0 s)))
                    *fn-b3st-v65-keyed*)))))

(assert-event
 (let ((s (fn-b3st-string 65)))
   (and (equal (fn-b3st-chunk-octets 0 65 0 0 *fn-b3-root* s) *fn-b3st-v65-plain*)
        (not (equal (fn-b3st-chunk-octets 0 65 0 *fn-b3-keyed-hash* *fn-b3-root* s)
                    *fn-b3st-v65-plain*)))))

; MUTATION (chunk counter): the one-chunk root compressed with counter 1.
(assert-event
 (let ((s (fn-b3st-string 65)))
   (and (equal (fn-b3st-chunk-octets 0 65 0 0 *fn-b3-root* s) *fn-b3st-v65-plain*)
        (not (equal (fn-b3st-chunk-octets 0 65 1 0 *fn-b3-root* s) *fn-b3st-v65-plain*)))))

(assert-event
 (let ((s (fn-b3st-string 1024)))
   (and (equal (fn-b3st-chunk-octets 0 1024 0 0 *fn-b3-root* s) *fn-b3st-v1024-plain*)
        (not (equal (fn-b3st-chunk-octets 0 1024 1 0 *fn-b3-root* s) *fn-b3st-v1024-plain*)))))

; MUTATION (ROOT flag): the one-chunk message finished without ROOT.
(assert-event
 (let ((s (fn-b3st-string 65)))
   (and (equal (fn-b3st-chunk-octets 0 65 0 0 *fn-b3-root* s) *fn-b3st-v65-plain*)
        (not (equal (fn-b3st-chunk-octets 0 65 0 0 0 s) *fn-b3st-v65-plain*)))))

; At the block: a one-block message is one compression with CHUNK_START |
; CHUNK_END | ROOT.
(assert-event
 (let ((s (fn-b3st-string 64))
       (fl (logior *fn-b3-chunk-start* *fn-b3-chunk-end* *fn-b3-root*)))
   (and (equal (fn-b3st-block-octets 64 0 64 fl s) *fn-b3st-v64-plain*)
        ; MUTATION (chunk counter)
        (not (equal (fn-b3st-block-octets 64 1 64 fl s) *fn-b3st-v64-plain*))
        ; MUTATION (ROOT flag)
        (not (equal (fn-b3st-block-octets 64 0 64 (logior *fn-b3-chunk-start* *fn-b3-chunk-end*) s)
                    *fn-b3st-v64-plain*))
        ; MUTATION (mode flag)
        (not (equal (fn-b3st-block-octets 64 0 64 (logior fl *fn-b3-keyed-hash*) s)
                    *fn-b3st-v64-plain*)))))

; In the tree (2049 octets: two chunks on the left, one on the right).
(assert-event
 (let ((s (fn-b3st-string 2049))
       (top (logior *fn-b3-parent* *fn-b3-root*)))
   (and (equal (fn-b3-left-chunks 1 2049) 2)
        (equal (fn-b3st-top-octets 0 0 2 top s) *fn-b3st-v2049-plain*)
        ; MUTATION (chunk counter): the right subtree counted from 0
        (not (equal (fn-b3st-top-octets 0 0 0 top s) *fn-b3st-v2049-plain*))
        ; MUTATION (chunk counter): the left subtree counted from 1
        (not (equal (fn-b3st-top-octets 0 1 2 top s) *fn-b3st-v2049-plain*))
        ; MUTATION (ROOT flag): the top parent without ROOT
        (not (equal (fn-b3st-top-octets 0 0 2 *fn-b3-parent* s) *fn-b3st-v2049-plain*))
        ; MUTATION (mode flag): KEYED_HASH through every node, IV as key
        (not (equal (fn-b3st-top-octets *fn-b3-keyed-hash* 0 2 (logior top *fn-b3-keyed-hash*) s)
                    *fn-b3st-v2049-plain*)))))
