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

; The fast reassembler returns all four reference outcomes, including the
; least conflict and the first contiguous gap.  The nonzero-offset fragment
; arrives first in the complete-cover case.
(defconst *bpf-fast-cover*
  '((:fn-bp-fragment 3 (40 50 60) 6)
    (:fn-bp-fragment 0 (10 20 30) 6)))
(assert-event
 (equal (fn-bpf-reassemble-fast *bpf-fast-cover* 6)
        '(:ok (10 20 30 40 50 60))))
(assert-event
 (equal (fn-bpf-reassemble-fast
         '((:fn-bp-fragment 0 (10 20 30 40) 6)
           (:fn-bp-fragment 2 (30 99 50 60) 6)) 6)
        '(:conflict 3)))
(assert-event
 (equal (fn-bpf-reassemble-fast
         '((:fn-bp-fragment 0 (10 20) 6)
           (:fn-bp-fragment 4 (50 60) 6)) 6)
        '(:missing 2 4)))
(assert-event
 (equal (fn-bpf-reassemble-fast *bpf-fast-cover* 0)
        '(:invalid :bounds)))
(assert-event
 (equal (fn-bpf-reassemble-fast
         '((:fn-bp-fragment 4 (50 60 70) 6)) 6)
        '(:invalid :bounds)))
(assert-event
 (equal (fn-bpf-reassemble-fast
         '((:fn-bp-fragment 0 (10 20 30 40) 6)
           (:fn-bp-fragment 2 (30 99) 6)) 6)
        '(:conflict 3)))
