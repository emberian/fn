; Teeth for books/node-secret.lisp (SEC-006, PRF-210): HMAC-SHA256 against
; RFC 4231, and the label separation fn-ns-input-separates-labels with a
; witness and one removal per hypothesis.
(in-package "ACL2")
(include-book "../../books/node-secret")
(include-book "std/testing/must-fail" :dir :system)

(defun nst-codes (cs)
  (if (consp cs) (cons (char-code (car cs)) (nst-codes (cdr cs))) nil))
(defun nst-octets (s) (nst-codes (coerce s 'list)))
(defun nst-hex (octets)
  (if (consp octets)
      (let ((d "0123456789abcdef"))
        (concatenate 'string (string (char d (floor (car octets) 16)))
                     (string (char d (mod (car octets) 16)))
                     (nst-hex (cdr octets))))
    ""))

; RFC 4231 test cases 2 and 6 (a key over the block length is hashed first).
(assert-event
 (equal (nst-hex (fn-ns-hmac-sha256 (nst-octets "Jefe")
                                    (nst-octets "what do ya want for nothing?")))
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"))
(assert-event
 (equal (nst-hex (fn-ns-hmac-sha256
                  (make-list 131 :initial-element 170)
                  (nst-octets "Test Using Larger Than Block-Size Key - Hash Key First")))
        "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"))

; The labels are the ones the header names.
(assert-event (equal *fn-ns-cancel-lock-label* (nst-octets "fn cancel-lock v1")))
(assert-event (equal *fn-ns-posting-account-label* (nst-octets "fn posting-account v1")))
(assert-event (equal (fn-ns-secret-width) 32))

; fn-ns-input-separates-labels.  Witness: the two labels the node uses, and
; the messages of one login under both uses.
(defconst *nst-s* (make-list 32 :initial-element 7))
(assert-event
 (and (fn-ns-labelp *fn-ns-cancel-lock-label*)
      (fn-ns-labelp *fn-ns-posting-account-label*)
      (not (equal *fn-ns-cancel-lock-label* *fn-ns-posting-account-label*))
      (not (equal (fn-ns-input *fn-ns-cancel-lock-label* (nst-octets "<a@b>alice"))
                  (fn-ns-input *fn-ns-posting-account-label* (nst-octets "alice"))))
      (not (equal (fn-ns-cancel-lock-mac *nst-s* (nst-octets "alice"))
                  (fn-ns-posting-account-mac *nst-s* (nst-octets "alice"))))))

; Removal of `distinct labels': one label, one message: the inputs coincide.
(defconst *nst-l* (nst-octets "ab"))
(assert-event (fn-ns-labelp *nst-l*))
(assert-event (equal (fn-ns-input *nst-l* '(5)) (fn-ns-input *nst-l* '(5))))
(must-fail
 (assert-event (not (equal (fn-ns-input *nst-l* '(5)) (fn-ns-input *nst-l* '(5))))))

; Removal of `l2 is a label' (it contains the separator): "a" with message
; (98 0 5) and "a\0b" with message (5) are the same input.
(defconst *nst-l1* '(97))
(defconst *nst-l2* '(97 0 98))
(assert-event (and (fn-ns-labelp *nst-l1*) (not (fn-ns-labelp *nst-l2*))
                   (not (equal *nst-l1* *nst-l2*))))
(assert-event (equal (fn-ns-input *nst-l1* '(98 0 5)) (fn-ns-input *nst-l2* '(5))))
(must-fail
 (assert-event (not (equal (fn-ns-input *nst-l1* '(98 0 5))
                           (fn-ns-input *nst-l2* '(5))))))
; ... and symmetrically for l1.
(assert-event (equal (fn-ns-input *nst-l2* '(5)) (fn-ns-input *nst-l1* '(98 0 5))))

; Removal of `an octet list' (a dotted label drops its tail in the input):
; (97 . 3) and (97) are distinct, carry no NUL, and give the same input.
(defconst *nst-dotted* (cons 97 3))
(assert-event (and (not (fn-ns-labelp *nst-dotted*)) (fn-ns-labelp '(97))
                   (not (equal *nst-dotted* '(97)))))
(assert-event (equal (fn-ns-input *nst-dotted* '(5)) (fn-ns-input '(97) '(5))))
(must-fail
 (assert-event (not (equal (fn-ns-input *nst-dotted* '(5)) (fn-ns-input '(97) '(5))))))
