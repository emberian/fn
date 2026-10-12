(in-package "ACL2")
(include-book "../../books/cold-read-reservation")
(include-book "std/testing/assert-bang" :dir :system)

; The explicit cold pool's budget, which the served run's launch funds as one
; of its pools (books/heap-command.lisp fn-mo-serve-pools; its teeth are
; tests/acl2/heap-command-tests.lisp's).
(assert-event
 (and (eq (symbol-class 'fn-crv-pool-budget (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-crv-native-baseline (w state)) :common-lisp-compliant)))

(defconst *crvt-policy* '(67108864 2 16 10000 10000))
; Two workers' stacks and runtime and the cold-wait queue, beside the pool's heap.
(assert! (equal (fn-crv-native-baseline *crvt-policy* nil)
                (+ (* 2 (fn-crv-native-per-worker nil)) (fn-cwq-queue-octets))))
(assert! (equal (fn-crv-pool-budget *crvt-policy* nil)
                (list (+ 67108864 (fn-crv-native-baseline *crvt-policy* nil)) 0 16 2 10000)))
(assert! (fn-crv-policy-p *crvt-policy*))
(assert! (not (fn-crv-policy-p nil)))
(assert! (not (fn-crv-policy-p '(1 2 3 4))))
