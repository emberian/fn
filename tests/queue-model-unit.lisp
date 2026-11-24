(in-package "ACL2")
(include-book "../books/queue-model")
; Principal FIFOs append without changing another principal's order.
(assert-event
 (equal (fn2-ref-enqueue 7 2 '((0 3 4) (2 5))) '((0 3 4) (2 5 7))))
; Queued-anywhere is idempotent even when a different principal is supplied.
(assert-event
 (equal (fn2-ref-enqueue 4 2 '((0 3 4) (2 5))) '((0 3 4) (2 5))))
(assert-event (equal (fn2-ref-enqueue 7 2 nil) '((2 7))))
(assert-event (equal (fn2-ref-enqueue *fn2-none* 2 '((0 3))) '((0 3))))
