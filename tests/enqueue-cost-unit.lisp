; Static enqueue-effect bounds are inferred from actual callback declarations,
; independently of the three-dimensional I/O/work report and trace capacity.
(in-package "ACL2")
(include-book "../books/assembly-attach")
(assert-event
 (and (equal (fn2-arms-call-enqueues '(fn2-identity-decide) (w state)) 1)
      (equal (fn2-arms-call-enqueues '(fn2-identity-decide fn2-successor-release) (w state)) 2)
      (equal (fn2-arms-call-enqueues '(fn2-txn-offer fn2-txn-offer fn2-txn-offer) (w state)) 3)
      (equal (fn2-arms-loop-enqueues '((left 3 0 0 0 3 1))) 3)
      (not (fn2-arms-call-enqueues '(missing-enqueue-operation) (w state)))
      (not (fn2-arms-loop-enqueues '((left 3 0 0 0 3))))
      (not (fn2-arms-loop-enqueues '((left 3 0 0 0 3 nil))))
      (equal (fn2-arms-enqueue-max '(0 1 3 2)) 3)
      (equal (fn2-arms-enqueue-max '(0 nil 2)) :unbounded)
      (fn2-cost-problem 'enqueue-cost-probe '(:enqueues -1 :doc "invalid"))
      (not (fn2-cost-problem 'enqueue-cost-probe '(:enqueues 1 :doc "bounded")))))
; A real emitted lookup arm carries the maximum of its offer/decision paths,
; rather than counting mutually exclusive branches as sequential calls.
(assert-event
 (equal (fn2-decl-get :enqueues (fn2-operation-row 'fn2-txn-run-lookup (w state))) 1))
