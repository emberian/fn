; Executable examples for the total cursor/refinement theorem.
(in-package "ACL2")
(include-book "../../books/bp-fragment-fast")

(assert-event
 (equal (fn-bpf-fragment-fast '(10 20 30 40 50 60 70 80) '(3 5))
        '(:ok ((:fn-bp-fragment 0 (10 20 30) 8)
               (:fn-bp-fragment 3 (40 50) 8)
               (:fn-bp-fragment 5 (60 70 80) 8)))))
(assert-event
 (equal (fn-bpf-fragment-fast '(10 20 30) '(3))
        '(:invalid :bounds)))
(assert-event
 (equal (fn-bpf-fragment-fast '(10 20 30) '(2 1))
        '(:invalid :bounds)))
(assert-event
 (equal (fn-bpf-fragment-fast '(10 20 30) nil)
        (fn-bpf-fragment '(10 20 30) nil)))
