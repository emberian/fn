;; fn: the executable twin of books/blake3.lisp against the official BLAKE3
;; vectors (books/blake3-stobj.lisp).  `fn-blake3-stobj-is-blake3' and the
;; buffer and range keystones already prove the twin equal to the definition;
;; these evaluations are the other direction of evidence: that the functions
;; the seams attach to compute the published digests, through each reader
;; (a list copied into a buffer; a list prefix before a buffer, split at
;; several points; a window inside a buffer with octets on both sides).

(in-package "ACL2")
(include-book "../../books/blake3-stobj")

(defun fn-b3st-input-from (i n)
  (declare (xargs :guard (and (natp i) (natp n)) :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (mod i 251) (fn-b3st-input-from (+ i 1) n))
    nil))

(defun fn-b3st-split (k m)
  ; The first K octets as the list prefix, the rest in the buffer.
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (d fn-octets)
      (let ((fn-octets (fn-octets-from-list (nthcdr k m) fn-octets)))
        (mv (fn-blake3-of-prefixed-buffer (take k m) fn-octets) fn-octets))
      d)))

(defun fn-b3st-window (m)
  ; M between 7 octets of 255 before and 5 after, read as a window.
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (d fn-octets)
      (let ((fn-octets (fn-octets-from-list
                        (append (make-list 7 :initial-element 255) m
                                (make-list 5 :initial-element 255))
                        fn-octets)))
        (mv (fn-blake3-of-prefixed-range nil 7 (len m) fn-octets) fn-octets))
      d)))

(defun fn-b3st-all-agree (n expected)
  (declare (xargs :verify-guards nil))
  (let ((m (fn-b3st-input-from 0 n)))
    ; The prefix is read by `nth' (fn's prefixes are frame and preimage
    ; heads, tens of octets), so a long prefix costs its length squared:
    ; the half and whole splits run up to two chunks and one block edge.
    (and (equal (fn-blake3-stobj m) expected)
         (equal (fn-b3st-split 0 m) expected)
         (equal (fn-b3st-split (min n 13) m) expected)
         (or (< 2049 n)
             (and (equal (fn-b3st-split (floor n 2) m) expected)
                  (equal (fn-b3st-split n m) expected)))
         (equal (fn-b3st-window m) expected))))

(assert-event (fn-b3st-all-agree 0 '(175 19 73 185 245 249 161 166 160 64 77 234 54 220 201 73 155 203 37 201 173 193 18 183 204 154 147 202 228 31 50 98)))
(assert-event (fn-b3st-all-agree 1 '(45 58 222 223 241 27 97 241 76 136 110 53 175 160 54 115 109 205 135 167 77 39 181 193 81 2 37 208 245 146 226 19)))
(assert-event (fn-b3st-all-agree 2 '(123 112 21 187 146 207 11 49 128 55 112 42 108 221 129 222 228 18 36 247 52 104 76 44 18 44 214 53 156 177 238 99)))
(assert-event (fn-b3st-all-agree 3 '(225 190 77 122 138 181 86 10 164 25 158 234 51 152 73 186 142 41 61 85 202 10 129 0 103 38 209 132 81 158 100 127)))
(assert-event (fn-b3st-all-agree 4 '(243 15 90 178 143 224 71 144 64 55 247 123 109 164 254 161 226 114 65 197 209 50 99 141 139 237 206 157 64 73 79 50)))
(assert-event (fn-b3st-all-agree 5 '(180 11 68 223 217 126 122 132 169 150 169 26 248 184 81 136 198 108 18 105 64 186 122 173 46 122 230 179 133 64 42 162)))
(assert-event (fn-b3st-all-agree 6 '(6 196 232 255 182 135 47 173 150 249 170 202 94 238 21 83 235 98 174 208 173 113 152 206 244 46 135 246 166 22 200 68)))
(assert-event (fn-b3st-all-agree 7 '(63 135 112 243 135 250 173 8 250 169 216 65 78 159 68 154 198 142 111 240 65 127 103 63 96 42 100 106 137 20 25 254)))
(assert-event (fn-b3st-all-agree 8 '(35 81 32 125 4 252 22 173 228 60 202 176 134 0 147 156 124 31 167 10 92 10 172 167 96 99 208 76 50 40 234 235)))
(assert-event (fn-b3st-all-agree 63 '(233 188 55 165 148 218 173 131 190 148 112 223 127 123 55 152 41 124 61 131 76 232 11 168 93 110 32 118 39 183 219 123)))
(assert-event (fn-b3st-all-agree 64 '(78 237 113 65 234 74 92 212 183 136 96 107 210 63 70 226 18 175 156 172 235 172 220 125 31 76 109 199 242 81 27 152)))
(assert-event (fn-b3st-all-agree 65 '(222 30 95 160 190 112 223 109 43 232 255 253 14 153 206 170 142 182 232 201 58 99 242 216 209 195 14 203 107 38 61 238)))
(assert-event (fn-b3st-all-agree 127 '(216 18 147 253 168 99 240 8 192 158 146 252 56 42 129 245 160 180 161 37 28 186 22 52 1 106 15 134 166 189 100 13)))
(assert-event (fn-b3st-all-agree 128 '(241 126 87 5 100 178 101 120 195 59 183 244 70 67 245 57 98 75 5 223 26 118 200 31 48 172 213 72 196 75 69 239)))
(assert-event (fn-b3st-all-agree 129 '(104 58 170 233 243 197 186 55 234 175 7 42 237 15 158 48 186 192 134 81 55 186 230 139 31 222 76 162 174 189 203 18)))
(assert-event (fn-b3st-all-agree 1023 '(16 16 137 112 238 218 62 185 50 186 172 20 40 199 162 22 59 14 146 76 154 158 37 179 91 186 114 178 143 112 189 17)))
(assert-event (fn-b3st-all-agree 1024 '(66 33 71 57 240 149 164 6 243 252 131 222 184 137 116 74 192 13 248 49 193 13 170 85 24 155 93 18 28 133 90 247)))
(assert-event (fn-b3st-all-agree 1025 '(208 2 120 174 71 235 39 179 79 174 207 103 180 254 38 63 130 213 65 41 22 193 255 217 124 140 183 251 129 75 132 68)))
(assert-event (fn-b3st-all-agree 2048 '(231 118 182 2 140 124 210 42 77 11 161 130 168 191 98 32 93 46 245 118 70 126 131 142 214 242 82 155 133 251 162 74)))
(assert-event (fn-b3st-all-agree 2049 '(95 77 114 244 13 122 95 130 177 92 162 178 228 75 29 227 194 239 134 196 38 201 92 26 240 182 135 149 34 86 48 48)))
(assert-event (fn-b3st-all-agree 3072 '(185 140 176 255 54 35 190 3 50 107 55 61 230 185 9 82 24 81 62 100 241 238 46 221 37 37 199 173 30 92 255 210)))
(assert-event (fn-b3st-all-agree 3073 '(113 36 180 149 1 1 47 129 204 127 17 202 6 158 201 34 108 236 184 162 200 80 207 230 68 227 39 210 45 62 28 211)))
(assert-event (fn-b3st-all-agree 4096 '(1 80 148 1 63 87 165 39 123 89 216 71 92 5 1 4 44 11 100 46 83 27 10 28 143 88 210 22 50 41 233 105)))
(assert-event (fn-b3st-all-agree 4097 '(155 64 82 179 143 28 95 200 177 249 255 122 199 178 124 210 66 72 123 61 137 13 21 201 106 28 37 184 170 15 185 149)))
(assert-event (fn-b3st-all-agree 5120 '(156 173 193 95 237 139 93 133 69 98 178 106 149 54 217 112 124 173 237 169 177 67 151 143 49 154 179 66 48 83 88 51)))
(assert-event (fn-b3st-all-agree 5121 '(98 139 210 203 32 4 105 74 218 171 123 189 119 138 37 223 37 196 123 157 65 85 165 95 143 189 121 242 254 21 76 255)))
(assert-event (fn-b3st-all-agree 6144 '(62 46 91 116 224 72 243 173 214 210 31 170 179 248 58 164 77 59 34 120 175 184 59 128 179 195 81 100 235 236 162 5)))
(assert-event (fn-b3st-all-agree 6145 '(241 50 58 134 49 68 108 197 5 54 169 247 5 238 92 182 25 66 77 70 136 127 60 55 108 105 91 112 224 240 80 127)))
(assert-event (fn-b3st-all-agree 7168 '(97 218 149 126 194 73 154 149 214 184 2 62 43 14 96 78 199 246 181 14 128 169 103 139 137 210 98 142 153 173 167 122)))
(assert-event (fn-b3st-all-agree 7169 '(160 3 252 122 81 117 74 155 60 127 174 3 103 171 61 120 45 204 242 136 85 160 61 67 95 140 254 116 96 94 120 23)))
(assert-event (fn-b3st-all-agree 8192 '(170 231 146 72 76 142 254 79 25 226 202 125 55 29 140 70 127 251 16 116 141 138 90 26 229 121 148 143 113 138 42 99)))
(assert-event (fn-b3st-all-agree 8193 '(186 182 192 156 184 206 140 244 89 38 19 152 210 231 174 243 87 0 191 72 129 22 206 185 74 54 208 245 241 183 188 59)))
(assert-event (fn-b3st-all-agree 16384 '(248 117 214 100 109 226 137 133 100 111 52 238 19 190 154 87 111 213 21 247 107 91 10 38 187 50 71 53 4 29 221 228)))
(assert-event (fn-b3st-all-agree 31744 '(98 182 150 14 26 68 188 193 235 26 97 26 141 98 53 182 180 183 143 50 231 171 196 251 76 108 220 206 148 137 92 71)))
(assert-event (fn-b3st-all-agree 102400 '(188 62 61 65 161 20 107 6 154 191 250 211 192 212 72 96 207 102 67 144 175 206 77 150 97 247 144 46 121 67 224 133)))

;; An improper list and non-octet elements read as `fn-b3-fix-octets' reads them.
(assert-event (equal (fn-blake3-stobj '(1 2 . 3)) (fn-blake3 '(1 2))))
(assert-event (equal (fn-blake3-stobj '(257 -1 a)) (fn-blake3 '(1 255 0))))
(assert-event (equal (fn-blake3-stobj "not a list") (fn-blake3 nil)))
