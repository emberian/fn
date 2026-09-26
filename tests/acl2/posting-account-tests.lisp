; Teeth for the posting-account value (PKT-597; books/posting-account.lisp).
; The value is the lowercase hex of the node secret's posting-account MAC
; (books/node-secret.lisp fn-ns-posting-account-mac; the HMAC itself is
; checked against RFC 4231 in tests/acl2/node-secret-tests.lisp).  Its
; shape, what it depends on, and the claim this book does NOT make.
(in-package "ACL2")
(include-book "../../books/posting-account")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-pat-codes (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (consp cs) (cons (char-code (car cs)) (fn-pat-codes (cdr cs))) nil))

(defconst *pat-secret* (make-list 32 :initial-element 7))
(defconst *pat-alice* (fn-pat-codes (coerce "alice" 'list)))
(defconst *pat-bob* (fn-pat-codes (coerce "bob" 'list)))

; The value renders the MAC: 64 lowercase hex digits of the 32 MAC octets.
(assert-event
 (let ((v (fn-pa-account-value *pat-secret* *pat-alice*)))
   (and (equal (len v) 64) (fn-pa-hex-octetsp v)
        (equal v (fn-pa-hex (fn-ns-posting-account-mac *pat-secret* *pat-alice*))))))
; Two logins, two values; the same login under another secret, another value.
(assert-event
 (not (equal (fn-pa-account-value *pat-secret* *pat-alice*)
             (fn-pa-account-value *pat-secret* *pat-bob*))))
(assert-event
 (not (equal (fn-pa-account-value *pat-secret* *pat-alice*)
             (fn-pa-account-value (make-list 32 :initial-element 8) *pat-alice*))))
; Domain separation: the value is not the hex of the Cancel-Lock MAC of the
; same octets under the same secret.
(assert-event
 (not (equal (fn-pa-account-value *pat-secret* *pat-alice*)
             (fn-pa-hex (fn-ns-cancel-lock-mac *pat-secret* *pat-alice*)))))

; fn-pa-account-value-depends-only-on-the-mac: its hypothesis is needed
; (two logins, one secret, two values: the witness above).
(must-fail
 (defthm fn-pat-value-without-equal-macs
   (equal (fn-pa-account-value secret login1) (fn-pa-account-value secret login2))))
; NOT CLAIMED: one value, one login.  That is HMAC-SHA256's collision
; resistance, a cryptographic assumption about the real function; for n
; logins under one secret a shared value has probability at most
; n(n-1)/2^257.
(must-fail
 (defthm fn-pat-value-determines-the-login
   (implies (equal (fn-pa-account-value secret login1)
                   (fn-pa-account-value secret login2))
            (equal login1 login2))))
