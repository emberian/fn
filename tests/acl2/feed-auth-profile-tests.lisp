; Executable witnesses for the bounded outbound AUTHINFO profile codec.
(in-package "ACL2")
(include-book "../../books/feed-auth-profile")

(defconst *fap-good*
  '(70 78 65 85 84 72 49 10 110 111 100 101 10
    115 101 99 114 101 116 10))
(assert-event
 (equal (fn-fap-decode *fap-good*)
        '(:ok (110 111 100 101) (115 101 99 114 101 116))))
(assert-event (equal (car (fn-fap-decode (butlast *fap-good* 1))) :bad))
(assert-event
 (equal (car (fn-fap-decode
              '(70 78 65 85 84 72 49 10 110 0 100 101 10 112 10))) :bad))
(assert-event
 (equal (car (fn-fap-decode
              (append *fap-good* (make-list 1024 :initial-element 65)))) :bad))
