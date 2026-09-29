(in-package "ACL2")
(include-book "../../books/snapshot-capture-lease")
; Literal positive acquisition witness; positive ticket/count, no vacuity.
(assert-event
 (and (natp 8) (natp 4)
      (equal (car (fn-osl-acquire 8 4 nil nil nil)) :accepted)
      (and (not nil) (not nil) (not nil))
      (equal (fn-osl-acquire 8 4 nil nil nil) '(:accepted :captured (8 4) 9))))
(assert-event (equal (fn-osl-acquire 8 4 '(7 4) nil nil)
                      '(:refused :maintenance-busy (7 4) 8)))
(assert-event (equal (fn-osl-acquire 8 4 nil 0 nil)
                      '(:refused :maintenance-busy nil 8)))
(assert-event (equal (fn-osl-acquire 8 4 nil nil :recorded)
                      '(:refused :maintenance-busy nil 8)))
; Literal complete matching release witness.
(assert-event
 (and (fn-osl-leasep '(8 4)) (natp 8)
      (equal 8 (car '(8 4))) (equal 4 (cadr '(8 4)))
      (equal (fn-osl-release '(8 4) 8 4) '(:released nil))))
; Hypothesis-removal: retain shape/count, fail ticket equality and release.
(assert-event
 (and (fn-osl-leasep '(8 4)) (natp 7)
      (not (equal 7 (car '(8 4)))) (equal 4 (cadr '(8 4)))
      (not (equal (car (fn-osl-release '(8 4) 7 4)) :released))
      (equal (cadr (fn-osl-release '(8 4) 7 4)) '(8 4))))
; Hypothesis-removal: retain shape/ticket, fail shared-slot equality.
(assert-event
 (and (fn-osl-leasep '(8 4)) (natp 8) (equal 8 (car '(8 4)))
      (not (equal 5 (cadr '(8 4))))
      (not (equal (car (fn-osl-release '(8 4) 8 5)) :released))
      (equal (cadr (fn-osl-release '(8 4) 8 5)) '(8 4))))
; Malformed state is separate from a reachable stale callback.
(assert-event (equal (fn-osl-acquire -1 4 nil nil nil)
                      '(:refused :capture-state nil -1)))
(assert-event (equal (fn-osl-release '(8 broken) 8 'broken)
                      '(:refused (8 broken))))
