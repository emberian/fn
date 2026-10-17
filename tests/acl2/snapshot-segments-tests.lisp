; fn: witnesses and teeth for the snapshot container
; (books/snapshot-segments.lisp; lane snapshot-open).  Attachments evaluate
; in assert-event and defun bodies: the digest is fn-blake3's.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/crypto-attach")

(defconst *t-w* '(8 1))
(defconst *t-s1* '((5 6 7) (1 2 3 4 5)))
(defconst *t-s2* '((5 6 7 8 9) (1 2 3 4 5 6)))
(defconst *t-meta* '(9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9
                     9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9))

(defconst *t-states* (list *t-s1* *t-s2*))

