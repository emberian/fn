; fn: published vectors for books/hmac-sha256.lisp.
;
; Evidence, not proof (as tests/acl2/sha256-tests.lisp says of SHA-256): each
; `assert-event' evaluates the function the host calls -- the `:exec' half of
; its `mbe', the key-block midstate -- and compares the octets with the value
; the standard prints.  The `:logic' half is the RFC text and the guard proof
; is their equality, so a pass here is agreement of both on these inputs.
;
;   RFC 4231 section 4.2, 4.3, 4.7  HMAC-SHA-256 test cases 1, 2 and 6 (case
;                                   6 is the 131-octet key the RFC hashes
;                                   first: the long-key branch)
;   RFC 7914 section 11             PBKDF2-HMAC-SHA-256, P "passwd", S
;                                   "salt", c 1; P "Password", S "NaCl",
;                                   c 80000 (first 32 octets of each dkLen 64:
;                                   PBKDF2's first block is Hi)
;
; The RFC 7677 exchange (SaltedPassword under 4096 iterations and every
; message) is tests/acl2/scram-tests.lisp.

(in-package "ACL2")
(include-book "../../books/hmac-sha256")

(defun fn-hmac-t-octets (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars)) (fn-hmac-t-octets (cdr chars)))
    nil))

(defmacro fn-hmac-t-string (s)
  `(fn-hmac-t-octets (coerce ,s 'list)))

; RFC 4231 test case 1: key 0x0b x 20, data "Hi There",
; HMAC-SHA-256 b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7
(assert-event
 (equal (fn-hmac-sha256 (make-list 20 :initial-element 11)
                        (fn-hmac-t-string "Hi There"))
        '(176 52 76 97 216 219 56 83 92 168 175 206 175 11 241 43 136 29 194 0
          201 131 61 167 38 233 55 108 46 50 207 247)))

; RFC 4231 test case 2: key "Jefe", data "what do ya want for nothing?",
; HMAC-SHA-256 5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843
(assert-event
 (equal (fn-hmac-sha256 (fn-hmac-t-string "Jefe")
                        (fn-hmac-t-string "what do ya want for nothing?"))
        '(91 220 193 70 191 96 117 78 106 4 36 38 8 149 117 199 90 0 63 8 157
          39 57 131 157 236 88 185 100 236 56 67)))

; RFC 4231 test case 6: key 0xaa x 131 (longer than the block: hashed first),
; data "Test Using Larger Than Block-Size Key - Hash Key First",
; HMAC-SHA-256 60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54
(assert-event
 (equal (fn-hmac-sha256
         (make-list 131 :initial-element 170)
         (fn-hmac-t-string
          "Test Using Larger Than Block-Size Key - Hash Key First"))
        '(96 228 49 89 30 224 182 127 13 138 38 170 203 245 183 127 142 11 198
          33 55 40 197 20 5 70 4 15 14 227 127 84)))

; The midstate form agrees with the RFC text on case 6's key as well (the
; theorem says so for every key; this is the evaluated instance).
(assert-event
 (equal (fn-hmac-from-states (fn-hmac-states (make-list 131 :initial-element 170))
                             (fn-hmac-t-string "abc"))
        (fn-hmac-sha256 (make-list 131 :initial-element 170)
                        (fn-hmac-t-string "abc"))))

; RFC 7914 section 11: PBKDF2-HMAC-SHA256 (P="passwd", S="salt", c=1,
; dkLen=64) = 55 ac 04 6e 56 e3 08 9f ec 16 91 c2 25 44 b6 05 f9 41 85 21 6d
; de 04 65 e6 8b 9d 57 c2 0d ac bc 49 ...; the first block is Hi.
(assert-event
 (equal (fn-pbkdf2-sha256 (fn-hmac-t-string "passwd") (fn-hmac-t-string "salt") 1)
        '(85 172 4 110 86 227 8 159 236 22 145 194 37 68 182 5 249 65 133 33
          109 222 4 101 230 139 157 87 194 13 172 188)))

; RFC 7914 section 11: (P="Password", S="NaCl", c=80000, dkLen=64) = 4d dc d8
; f6 0b 98 be 21 83 0c ee 5e f2 27 01 f9 64 1a 44 18 d0 4c 04 14 ae ff 08 87
; 6b 34 ab 56 a1 ...
(assert-event
 (equal (fn-pbkdf2-sha256 (fn-hmac-t-string "Password") (fn-hmac-t-string "NaCl")
                          80000)
        '(77 220 216 246 11 152 190 33 131 12 238 94 242 39 1 249 100 26 68 24
          208 76 4 20 174 255 8 135 107 52 171 86)))

; The iteration count is read: counts 1 and 2 differ (a chain that stopped
; after U1 would satisfy the c=1 vector and fail this one), and a count
; below one is one.
(assert-event
 (not (equal (fn-pbkdf2-sha256 (fn-hmac-t-string "passwd") (fn-hmac-t-string "salt") 1)
             (fn-pbkdf2-sha256 (fn-hmac-t-string "passwd") (fn-hmac-t-string "salt") 2))))

(assert-event
 (equal (fn-pbkdf2-sha256 (fn-hmac-t-string "passwd") (fn-hmac-t-string "salt") 0)
        (fn-pbkdf2-sha256 (fn-hmac-t-string "passwd") (fn-hmac-t-string "salt") 1)))
