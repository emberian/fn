; fn: teeth for books/sha256-buffer.lisp.
;
; What this book is evidence FOR.  `fn-sha256-of-prefixed-buffer-is-sha256'
; has no hypothesis, so there is no must-fail case to make for it; what it
; needs is what sha256-stobj's tests give the other two readers: the FIPS
; 180-4 vectors evaluated through the buffer reader on a live local buffer
; (the split between the list prefix and the buffer varied), the padding
; boundaries and a 3,000-octet buffer (past the array's first 1024 cells)
; against the list model, and non-degeneracy.
; `fn-shb-subject-id-is-id-subject-of-sha256-preimage' has no hypothesis
; either; its witness is the identity itself: on live buffers the buffer
; identity equals `fn-id-subject-of-payload' of the same octets under the
; image's attachment (books/crypto-attach.lisp binds `fn-frame-digest' to
; `fn-sha256-stobj') and equals the theorem's own right-hand side.  A pass
; here is agreement by evaluation; the proof is the correspondence in the
; book, and it says the two computations agree on EVERY prefix and value.
;
; Nothing here bears on collision resistance (A-CRYPTO, specs/failures.md).

(in-package "ACL2")
(include-book "../../books/sha256-buffer")
(include-book "../../books/crypto-attach")

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it may reach is guard-verified.

(assert-event
 (equal (list (symbol-class 'fn-shb-byte (w state))
              (symbol-class 'fn-shb-load-word (w state))
              (symbol-class 'fn-shb-load-block (w state))
              (symbol-class 'fn-shb-compress (w state))
              (symbol-class 'fn-shb-blocks (w state))
              (symbol-class 'fn-shb-digest (w state))
              (symbol-class 'fn-sha256-of-prefixed-buffer (w state))
              (symbol-class 'fn-shb-subject-id (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The executable path on a live local buffer, the way the host runs it: the
; buffer filled, then read in place by the digest.

(defun shbt-repeat (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n) nil (cons x (shbt-repeat (- n 1) x)))))

(defthm shbt-octet-listp-of-repeat
  (implies (fn-cbor-octetp x)
           (fn-cbor-octet-listp (shbt-repeat n x))))

(defun shbt-digest-run (prefix xs fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (true-listp prefix) (fn-cbor-octet-listp xs))))
  (let ((fn-octets (fn-octets-from-list xs fn-octets)))
    (mv (fn-sha256-of-prefixed-buffer prefix fn-octets) fn-octets)))

(defun shbt-digest (prefix xs)
  ; SHA-256 of (append PREFIX XS) with XS in a fresh local buffer.
  (declare (xargs :guard (and (true-listp prefix) (fn-cbor-octet-listp xs))))
  (with-local-stobj fn-octets
    (mv-let (digest fn-octets) (shbt-digest-run prefix xs fn-octets)
      digest)))

(defun shbt-subject-run (xs fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-cbor-octet-listp xs)
                              (<= (len xs) *fn-cbor-max-uint*))))
  (let ((fn-octets (fn-octets-from-list xs fn-octets)))
    (mv (fn-shb-subject-id fn-octets) fn-octets)))

(defun shbt-subject (xs)
  ; The subject identity of XS held in a fresh local buffer.
  (declare (xargs :guard (and (fn-cbor-octet-listp xs)
                              (<= (len xs) *fn-cbor-max-uint*))))
  (with-local-stobj fn-octets
    (mv-let (id fn-octets) (shbt-subject-run xs fn-octets)
      id)))

; -----------------------------------------------------------------------------
; The vectors, with the split between the prefix and the buffer varied.
; Expected values as in sha256-tests.

(defconst *shbt-empty*
  '(227 176 196 66 152 252 28 20 154 251 244 200 153 111 185 36 39 174 65 228 100 155 147 76 164 149 153 27 120 82 184 85))
(defconst *shbt-abc*
  '(186 120 22 191 143 1 207 234 65 65 64 222 93 174 34 35 176 3 97 163 150 23 122 156 180 16 255 97 242 0 21 173))
(defconst *shbt-m56* (fn-shs-string-octets "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
(defconst *shbt-m56-digest*
  '(36 141 106 97 210 6 56 184 229 192 38 147 12 62 96 57 163 60 228 89 100 255 33 103 246 236 237 212 25 219 6 193))
(defconst *shbt-m112*
  (fn-shs-string-octets "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"))
(defconst *shbt-m112-digest*
  '(207 91 22 167 120 175 131 128 3 108 229 158 123 4 146 55 11 36 155 17 232 240 122 81 175 172 69 3 122 254 233 209))

(assert-event (and (fn-cbor-octet-listp *shbt-m56*) (equal (len *shbt-m56*) 56)
                   (fn-cbor-octet-listp *shbt-m112*) (equal (len *shbt-m112*) 112)))

; empty
(assert-event (equal (shbt-digest nil nil) *shbt-empty*))

; abc: all of it in the prefix, split, all of it in the buffer
(assert-event (equal (shbt-digest '(97 98 99) nil) *shbt-abc*))
(assert-event (equal (shbt-digest '(97) '(98 99)) *shbt-abc*))
(assert-event (equal (shbt-digest nil '(97 98 99)) *shbt-abc*))

; fips-56 (a second block of padding), split at 0, at 18 (the subject
; prefix's length) and at 56
(assert-event (equal (shbt-digest nil *shbt-m56*) *shbt-m56-digest*))
(assert-event (equal (shbt-digest (take 18 *shbt-m56*) (nthcdr 18 *shbt-m56*)) *shbt-m56-digest*))
(assert-event (equal (shbt-digest *shbt-m56* nil) *shbt-m56-digest*))

; fips-112
(assert-event (equal (shbt-digest (take 18 *shbt-m112*) (nthcdr 18 *shbt-m112*)) *shbt-m112-digest*))
(assert-event (equal (shbt-digest nil *shbt-m112*) *shbt-m112-digest*))

; -----------------------------------------------------------------------------
; The padding boundaries (section 5.1.1) and the resize, against the list
; model by evaluation: 55 is the last length whose padding fits one block, 56
; and 64 the first of the next, 119/120 across the second; 3,000 octets in
; the buffer is past its first 1024 cells (the array doubles twice).

(defun shbt-agrees-p (prefix xs)
  (declare (xargs :guard (and (true-listp prefix) (fn-cbor-octet-listp xs))))
  (equal (shbt-digest prefix xs) (fn-sha256-stobj (append prefix xs))))

(assert-event
 (and (shbt-agrees-p (shbt-repeat 18 0) (shbt-repeat 37 97))    ; 55
      (shbt-agrees-p (shbt-repeat 18 0) (shbt-repeat 38 97))    ; 56
      (shbt-agrees-p (shbt-repeat 18 0) (shbt-repeat 45 97))    ; 63
      (shbt-agrees-p (shbt-repeat 18 0) (shbt-repeat 46 97))    ; 64
      (shbt-agrees-p (shbt-repeat 18 0) (shbt-repeat 47 97))    ; 65
      (shbt-agrees-p (shbt-repeat 18 0) (shbt-repeat 101 97))   ; 119
      (shbt-agrees-p (shbt-repeat 18 0) (shbt-repeat 102 97))   ; 120
      (shbt-agrees-p (shbt-repeat 55 1) nil)                    ; the prefix alone
      (shbt-agrees-p (shbt-repeat 64 1) (shbt-repeat 1 2))
      (shbt-agrees-p (shbt-repeat 18 97) (shbt-repeat 982 97))  ; 1000
      (shbt-agrees-p nil (shbt-repeat 3000 7))                  ; the resize
      (shbt-agrees-p (shbt-repeat 18 0) (shbt-repeat 2982 255))))

; -----------------------------------------------------------------------------
; Non-degeneracy: the split does not matter, the octets do.

(assert-event (equal (shbt-digest '(1) '(2)) (shbt-digest nil '(1 2))))
(assert-event (equal (shbt-digest '(1) '(2)) (shbt-digest '(1 2) nil)))
(assert-event (not (equal (shbt-digest '(1) '(2)) (shbt-digest '(2) '(1)))))
(assert-event (not (equal (shbt-digest '(1) '(2)) (shbt-digest '(1) '(3)))))
(assert-event (not (equal (shbt-digest nil (shbt-repeat 3000 7))
                          (shbt-digest nil (append (shbt-repeat 2999 7) '(8))))))
(assert-event (not (equal (shbt-digest nil nil) (shbt-repeat 32 0))))

; -----------------------------------------------------------------------------
; The subject identity over the buffer: the host's identity (the list entry
; through the attachment) and the theorem's right-hand side, on a 160-octet
; article, the empty payload and a 3,000-octet payload; a changed octet and
; the bare digest's identity differ from it.

(defconst *shbt-article*
  (fn-shs-string-octets
   "From: rep@example.invalid
Newsgroups: fn.test
Subject: rep 7
Date: Thu, 24 Sep 2026 12:00:00 +0000
Message-ID: <t17-000007@example.invalid>

0123456789abcdefghijklmnopqrstuvwxyz
"))

(assert-event (and (fn-cbor-octet-listp *shbt-article*) (< 100 (len *shbt-article*))))

(defun shbt-subject-agrees-p (xs)
  ; Evaluated in the logic (the theorem's right-hand side is a term over the
  ; specification, not a host entry); the entries it calls are guard-verified.
  (declare (xargs :guard (and (fn-cbor-octet-listp xs)
                              (<= (len xs) *fn-cbor-max-uint*))
                  :verify-guards nil))
  (let ((id (shbt-subject xs)))
    (and (equal id (fn-id-subject-of-payload xs))
         (equal id (fn-id-subject (fn-sha256 (fn-id-subject-preimage xs))))
         (fn-id-subjectp id))))

(assert-event (shbt-subject-agrees-p *shbt-article*))
(assert-event (shbt-subject-agrees-p nil))
(assert-event (shbt-subject-agrees-p (shbt-repeat 3000 7)))
(assert-event (not (equal (shbt-subject *shbt-article*)
                          (shbt-subject (append (take 100 *shbt-article*)
                                                (cons 88 (nthcdr 101 *shbt-article*)))))))
(assert-event (not (equal (shbt-subject *shbt-article*)
                          (fn-id-subject (fn-sha256 *shbt-article*)))))
