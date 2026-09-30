(in-package "ACL2")
(include-book "../../books/connection-operation-cost")

; Literal keystone positive and hypothesis-removal witnesses.
(assert-event
 (let ((x '(0 127 255)) (y '(0 127 255)))
  (and (fn-cop-octets-match x y 3) (equal x y))))
(assert-event
 (let ((x '(0 127 255)) (y '(0 127 254)))
  (and (not (fn-cop-octets-match x y 3)) (not (equal x y)))))
(assert-event (not (fn-cop-octets-match '(0 1 2) '(0 1 2) 2)))
(assert-event (not (fn-cop-octets-match '(256) '(256) 1)))
(assert-event (not (fn-cop-octets-match '(1 . 2) '(1 . 2) 2)))
(assert-event
 (mv-let (word left) (fn-cop-octets-left '(1 2 3) 7)
  (and (natp 7) (eq word :counted) (natp left) (<= left 7) (equal left 4))))
(assert-event
 (with-guard-checking :none
 (let ((fuel -1))
  (and (not (natp fuel))
       (not (natp (mv-nth 1 (mv-list 2 (fn-cop-octets-left nil fuel)))))))))
(assert-event
 (mv-let (word body) (fn-cop-body-demand 100 3 4 20 2 1000)
  (and (eq word :derived) (natp body) (<= body 1000)
       (equal body (+ 100 (* 3 4) (* 20 2))) (equal body 152))))
(assert-event
 (mv-let (word body) (fn-cop-body-demand 100 3 4 20 2 151)
  (and (not (eq word :derived)) (not (natp body))
       (not (equal body (+ 100 (* 3 4) (* 20 2)))))))
(assert-event (equal (mv-list 2 (fn-cop-body-demand 0 1000 1000 0 0 1000)) '(:unavailable nil)))

; Synthetic descriptor exercises evaluator, not genuine installation authority.
(defconst *fn-cop-test-installation*
 '(:connection-operation-installation 9 :association :full-source-fixture 1000
   (40 0 0 0 1) 100 3 20 20))
(assert-event
 (equal (mv-list 5 (fn-cop-evaluate *fn-cop-test-installation* :exposure :inet '(127 0 0 1) '(65 66) 0))
        '(:derived (40 0 0 0 1) 8 138 20)))
(assert-event
 (equal (mv-list 5 (fn-cop-evaluate *fn-cop-test-installation* :reader nil nil nil 1))
        '(:derived (40 0 0 0 1) 16 140 20)))
(assert-event (eq (mv-nth 0 (mv-list 5 (fn-cop-evaluate nil :reader nil nil nil 0))) :unsupported-runtime))
(assert-event (eq (mv-nth 0 (mv-list 5 (fn-cop-evaluate *fn-cop-test-installation* :exposure :inet '(127 0) nil 0))) :refused))
(assert-event (eq (mv-nth 0 (mv-list 5 (fn-cop-evaluate *fn-cop-test-installation* :reader nil nil '(1) 0))) :refused))
(assert-event (eq (mv-nth 0 (mv-list 5 (fn-cop-evaluate *fn-cop-test-installation* :peer nil nil (make-list 21 :initial-element 0) 0))) :refused))
(assert-event
 (fn-cop-issuer-domainp (fn-prl-build '(1000 1000 5 5 99) '(40 0 0 0 1) 1 nil '(100 0 0 0 0)) '(40 0 0 0 1) 1000))
(assert-event
 (not (fn-cop-issuer-domainp (fn-prl-build '(1000 1000 5 5 99) '(900 0 0 0 1) 1 nil '(100 0 0 0 0)) '(40 0 0 0 1) 1000)))
(assert-event
 (not (fn-cop-issuer-domainp (fn-prl-build '(1000 1000 5 5 99) '(40 0 0 0 1) 1 nil '(100 0 0 0 0)) '(40 0 0 0 1 0) 1000)))
