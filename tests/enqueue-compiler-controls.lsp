; Source-only controls loaded after the exact machine-arms24 world.
; No extra book dependency and no actual query-consumer claim.
(in-package "ACL2")
(defcost fn2-enqueue-compiler-one :enqueues 1 :doc "One declared bounded enqueue.")
(defcost fn2-enqueue-compiler-two :enqueues 2 :doc "Two declared bounded enqueues.")
(assert-event
 (and (equal (fn2-arms-call-enqueues '(fn2-enqueue-compiler-one) (w state)) 1)
      (equal (fn2-arms-call-enqueues '(fn2-enqueue-compiler-one fn2-enqueue-compiler-two) (w state)) 3)
      (equal (fn2-arms-call-enqueues '(fn2-enqueue-compiler-two fn2-enqueue-compiler-two) (w state)) 4)
      (not (fn2-arms-call-enqueues '(fn2-enqueue-compiler-missing) (w state)))))
(assert-event
 (and (equal (fn2-arms-loop-enqueues '((left 3 0 0 0 3 2))) 6)
      (not (fn2-arms-loop-enqueues '((left 3 0 0 0 3))))
      (not (fn2-arms-loop-enqueues '((left 3 0 0 0 3 nil))))
      (equal (fn2-arms-enqueue-max '(0 1 3 2)) 3)
      (equal (fn2-arms-enqueue-max '(0 nil 2)) :unbounded)))
(assert-event
 (and (fn2-cost-problem 'enqueue-cost-probe '(:enqueues -1 :doc "invalid"))
      (not (fn2-cost-problem 'enqueue-cost-probe '(:enqueues 2 :doc "bounded")))))
