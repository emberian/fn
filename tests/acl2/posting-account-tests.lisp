; Teeth for the posting-account value (P2 primitive, PRF-206 (c);
; books/posting-account.lisp).  The executed HMAC-SHA256 against RFC 4231's
; published vectors, the value's shape, and the claim this book does NOT make.
(in-package "ACL2")
(include-book "../../books/posting-account")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-pat-codes (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (consp cs) (cons (char-code (car cs)) (fn-pat-codes (cdr cs))) nil))

; RFC 4231 section 4.3, test case 2: key "Jefe".
(assert-event
 (equal (fn-pa-account-value (fn-pat-codes (coerce "Jefe" 'list))
                             (fn-pat-codes (coerce "what do ya want for nothing?"
                                                   'list)))
        (fn-pat-codes
         (coerce "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
                 'list))))
; RFC 4231 section 4.2, test case 1: key 0x0b x 20, data "Hi There".
(assert-event
 (equal (fn-pa-account-value (make-list 20 :initial-element 11)
                             (fn-pat-codes (coerce "Hi There" 'list)))
        (fn-pat-codes
         (coerce "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
                 'list))))
; RFC 4231 section 4.7, test case 6: a 131-octet key (hashed first).
(assert-event
 (equal (fn-pa-account-value
         (make-list 131 :initial-element 170)
         (fn-pat-codes
          (coerce "Test Using Larger Than Block-Size Key - Hash Key First" 'list)))
        (fn-pat-codes
         (coerce "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
                 'list))))

; A 32-octet node key and two logins: 64 hex digits, no login octet run.
(defconst *pat-key* (make-list 32 :initial-element 7))
(assert-event
 (let ((v (fn-pa-account-value *pat-key* (fn-pat-codes (coerce "alice" 'list)))))
   (and (equal (len v) 64) (fn-pa-hex-octetsp v)
        (not (equal v (fn-pa-account-value
                       *pat-key* (fn-pat-codes (coerce "bob" 'list))))))))
; The key matters: another key gives another value for the same login.
(assert-event
 (not (equal (fn-pa-account-value *pat-key* (fn-pat-codes (coerce "alice" 'list)))
             (fn-pa-account-value (make-list 32 :initial-element 8)
                                  (fn-pat-codes (coerce "alice" 'list))))))

; fn-pa-account-value-depends-only-on-the-mac: its hypothesis is needed
; (two logins, same key, different values).
(must-fail
 (defthm fn-pat-value-without-equal-macs
   (equal (fn-pa-account-value key login1) (fn-pa-account-value key login2))))
; NOT CLAIMED: login injectivity is HMAC-SHA256's collision resistance, a
; cryptographic assumption; it is not a theorem about the executed function.
(must-fail
 (defthm fn-pat-value-determines-the-login
   (implies (equal (fn-pa-account-value key login1)
                    (fn-pa-account-value key login2))
            (equal login1 login2))))
