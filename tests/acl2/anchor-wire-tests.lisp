; Executable tests for the ACL2-owned deployed RoughTime v1 grammar.
; The two packets are exact transcriptions of tests/vectors/roughtime-int08h-2026-09-19.json
; and tests/vectors/roughtime-int08h-2026-09-19-later2.json.  They exercise both the one-nonce shape
; the current anchor machine can accept and a well-formed batched shape that
; the current machine must report as uncertain after parsing.

(in-package "ACL2")
(include-book "../../books/anchor-wire")

(defconst *fn-anchor-wire-test-key*
 '(   1 110 110 2 132 210 76 55 198 228 215 216 213 180 225 211 193 148 156 234 165 69
   191 135 86 22 201 220 224 201 190 193))
(defconst *fn-anchor-wire-test-nonce*
 '(   149 179 179 248 80 223 100 39 92 132 72 216 112 168 89 251 30 78 105 10 198 180 78
   22 216 60 18 215 138 163 162 193))
(defconst *fn-anchor-wire-test-response*
 '(   6 0 0 0 64 0 0 0 96 0 0 0 96 0 0 0 196 0 0 0 92 1 0 0 83 73 71 0 78 79 78 67 80 65
   84 72 83 82 69 80 67 69 82 84 73 78 68 88 167 176 13 248 220 115 89 127 133 217
   185 95 250 61 214 214 111 99 179 138 247 227 191 171 231 159 119 111 19 222 210 42
   155 123 234 58 32 17 33 7 21 40 82 150 147 224 224 224 134 229 216 172 42 96 11
   145 67 174 202 140 193 102 5 3 149 179 179 248 80 223 100 39 92 132 72 216 112 168
   89 251 30 78 105 10 198 180 78 22 216 60 18 215 138 163 162 193 3 0 0 0 4 0 0 0 12
   0 0 0 82 65 68 73 77 73 68 80 82 79 79 84 64 75 76 0 225 226 191 57 215 91 6 0 254
   82 135 71 189 187 83 171 13 4 181 230 42 123 242 229 198 219 113 137 206 39 198 24
   190 15 16 30 59 254 239 50 233 1 28 45 176 61 76 83 102 108 2 83 35 251 121 82 28
   28 160 248 150 151 44 149 212 120 181 252 16 170 228 126 2 0 0 0 64 0 0 0 83 73 71
   0 68 69 76 69 87 225 33 224 241 80 220 225 1 150 133 87 82 115 28 33 135 244 117
   247 106 201 154 207 152 226 221 225 39 169 161 114 23 19 115 137 134 116 246 138
   52 156 54 11 61 7 92 144 175 88 216 182 45 47 9 144 97 138 145 112 8 93 207 15 3 0
   0 0 32 0 0 0 40 0 0 0 80 85 66 75 77 73 78 84 77 65 88 84 112 225 147 18 154 229
   157 97 162 171 106 245 153 162 69 214 84 231 236 149 66 50 74 243 234 59 223 111
   207 214 35 185 0 0 0 0 0 0 0 0 255 255 255 255 255 255 255 255 0 0 0 0))

(defconst *fn-anchor-wire-test-batched-nonce*
 '(   11 175 253 86 208 37 167 201 14 115 106 210 224 144 177 90 231 131 80 25 121 183
   202 148 162 138 93 37 218 36 73 223))
(defconst *fn-anchor-wire-test-batched-response*
 '(   6 0 0 0 64 0 0 0 96 0 0 0 160 0 0 0 4 1 0 0 156 1 0 0 83 73 71 0 78 79 78 67 80 65
   84 72 83 82 69 80 67 69 82 84 73 78 68 88 102 37 255 166 34 9 51 226 43 249 99 243
   225 83 11 193 13 46 206 26 6 185 143 205 249 247 229 133 143 247 157 131 142 93
   207 36 2 61 90 85 109 14 225 59 255 194 61 31 79 51 237 32 248 101 120 217 82 219
   195 118 97 31 113 2 11 175 253 86 208 37 167 201 14 115 106 210 224 144 177 90 231
   131 80 25 121 183 202 148 162 138 93 37 218 36 73 223 86 96 32 160 85 240 22 252
   118 202 56 28 112 161 66 176 37 237 130 105 102 226 28 235 133 244 29 126 129 146
   246 5 82 8 75 58 42 164 145 33 49 17 10 30 163 14 77 169 118 230 56 14 251 136 196
   222 79 235 96 241 205 116 62 106 3 0 0 0 4 0 0 0 12 0 0 0 82 65 68 73 77 73 68 80
   82 79 79 84 64 75 76 0 184 225 178 66 215 91 6 0 202 123 23 89 123 14 99 76 104
   173 191 21 119 218 96 186 146 111 30 82 82 121 169 87 141 43 251 9 148 169 21 180
   48 23 20 58 73 174 237 191 194 31 53 182 153 112 8 186 248 146 186 111 254 108 3
   95 231 148 211 23 250 185 137 25 2 0 0 0 64 0 0 0 83 73 71 0 68 69 76 69 26 52 55
   70 147 69 140 89 35 188 104 105 47 147 191 21 77 78 156 204 114 81 28 135 180 181
   33 244 44 171 224 74 122 134 82 187 218 9 0 119 236 16 43 5 193 200 138 189 152
   239 160 24 207 152 72 247 208 144 12 162 161 34 212 8 3 0 0 0 32 0 0 0 40 0 0 0 80
   85 66 75 77 73 78 84 77 65 88 84 69 91 77 196 154 28 126 73 217 71 237 214 130 224
   58 250 108 10 34 238 158 128 135 101 114 157 254 227 170 194 121 207 0 0 0 0 0 0 0
   0 255 255 255 255 255 255 255 255 1 0 0 0))

(defconst *fn-anchor-wire-test-result*
  (fn-anchor-wire-parse-response *fn-anchor-wire-test-response*
                                 *fn-anchor-wire-test-nonce*
                                 *fn-anchor-wire-test-key*))
(defconst *fn-anchor-wire-test-parsed*
  (fn-anchor-wire-result-value *fn-anchor-wire-test-result*))
(defconst *fn-anchor-wire-test-anchor*
  (fn-anchor-wire-parsed-anchor *fn-anchor-wire-test-parsed*))

; Reachable, non-degenerate witness for the public success theorem.
(assert-event (fn-anchor-wire-result-okp *fn-anchor-wire-test-result*))
(assert-event (fn-anchor-p *fn-anchor-wire-test-anchor*))
(assert-event
 (equal (fn-anchor-midpoint *fn-anchor-wire-test-anchor*) 1789829805236961))
(assert-event
 (equal (fn-anchor-radius *fn-anchor-wire-test-anchor*) 5000000))
(assert-event
 (equal (fn-anchor-delegation-signed-octets *fn-anchor-wire-test-anchor*)
        (append *fn-anchor-delegation-context*
                '(                 3 0 0 0 32 0 0 0 40 0 0 0 80 85 66 75 77 73 78 84 77 65 88 84 112
                 225 147 18 154 229 157 97 162 171 106 245 153 162 69 214 84 231 236
                 149 66 50 74 243 234 59 223 111 207 214 35 185 0 0 0 0 0 0 0 0 255
                 255 255 255 255 255 255 255))))
(assert-event
 (equal (fn-anchor-signed-octets *fn-anchor-wire-test-anchor*)
        (append *fn-anchor-response-context*
                '(                 3 0 0 0 4 0 0 0 12 0 0 0 82 65 68 73 77 73 68 80 82 79 79 84 64 75
                 76 0 225 226 191 57 215 91 6 0 254 82 135 71 189 187 83 171 13 4 181
                 230 42 123 242 229 198 219 113 137 206 39 198 24 190 15 16 30 59 254
                 239 50 233 1 28 45 176 61 76 83 102 108 2 83 35 251 121 82 28 28 160
                 248 150 151 44 149 212 120 181 252 16 170 228 126))))
(assert-event (fn-anchor-wire-single-leafp
               *fn-anchor-wire-test-parsed*))

; A real batched response parses, retains its one-node path and index, and is
; not mislabeled as the one-nonce shape accepted by the current model.
(defconst *fn-anchor-wire-test-batched-result*
  (fn-anchor-wire-parse-response *fn-anchor-wire-test-batched-response*
                                 *fn-anchor-wire-test-batched-nonce*
                                 *fn-anchor-wire-test-key*))
(defconst *fn-anchor-wire-test-batched-parsed*
  (fn-anchor-wire-result-value *fn-anchor-wire-test-batched-result*))
(assert-event (fn-anchor-wire-result-okp *fn-anchor-wire-test-batched-result*))
(assert-event
 (equal (len (fn-anchor-wire-parsed-path
              *fn-anchor-wire-test-batched-parsed*)) 64))
(assert-event
 (equal (fn-anchor-wire-parsed-index
         *fn-anchor-wire-test-batched-parsed*) 1))
(assert-event
 (not (fn-anchor-wire-single-leafp
       *fn-anchor-wire-test-batched-parsed*)))

(defun fn-anchor-wire-test-set (n value xs)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
    (if (zp (nfix n))
        (cons value (cdr xs))
      (cons (car xs)
            (fn-anchor-wire-test-set (1- (nfix n)) value (cdr xs))))))

(defun fn-anchor-wire-test-zeroes (n)
  (declare (xargs :guard t))
  (if (zp (nfix n))
      nil
    (cons 0 (fn-anchor-wire-test-zeroes (1- (nfix n))))))

; The request nonce is a binding input, not decorative packet data.
(assert-event
 (equal (fn-anchor-wire-result-reason
         (fn-anchor-wire-parse-response
          *fn-anchor-wire-test-response*
          (cons 0 (cdr *fn-anchor-wire-test-nonce*))
          *fn-anchor-wire-test-key*))
        :top-field))

; Repeating the first top-level tag at the second tag position violates strict
; numeric tag order and therefore also demonstrates duplicate rejection.
(defconst *fn-anchor-wire-test-duplicate-tag*
  (fn-anchor-wire-test-set
   31 0
   (fn-anchor-wire-test-set
    30 71
    (fn-anchor-wire-test-set
     29 73
     (fn-anchor-wire-test-set
      28 83 *fn-anchor-wire-test-response*)))))
(assert-event
 (equal (fn-anchor-wire-result-reason
         (fn-anchor-wire-parse-response
          *fn-anchor-wire-test-duplicate-tag*
          *fn-anchor-wire-test-nonce*
          *fn-anchor-wire-test-key*))
        :tag-order))

; The first cumulative end cannot pass the second end.
(defconst *fn-anchor-wire-test-decreasing-offset*
  (fn-anchor-wire-test-set 4 255 *fn-anchor-wire-test-response*))
(assert-event
 (equal (fn-anchor-wire-result-reason
         (fn-anchor-wire-parse-response
          *fn-anchor-wire-test-decreasing-offset*
          *fn-anchor-wire-test-nonce*
          *fn-anchor-wire-test-key*))
        :decreasing-offset))

; Truncation and the hard packet bound both fail before any crypto observation.
(assert-event
 (not (fn-anchor-wire-result-okp
       (fn-anchor-wire-parse-response
        (take (1- (len *fn-anchor-wire-test-response*))
              *fn-anchor-wire-test-response*)
        *fn-anchor-wire-test-nonce* *fn-anchor-wire-test-key*))))
(assert-event
 (equal (fn-anchor-wire-result-reason
         (fn-anchor-wire-parse-response
          (append *fn-anchor-wire-test-response*
                  (fn-anchor-wire-test-zeroes 4097))
          *fn-anchor-wire-test-nonce* *fn-anchor-wire-test-key*))
        :message-length))
