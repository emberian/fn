(in-package "ACL2")
(include-book "../../books/string-line-cursor-cost")
; Literal unconditional bridge/bound positives, exact reaching branch,
; quoted byte branches, early termination and malformed total inputs.
(assert-event
 (let* ((cur (fn-sl-make "abc" 0 :text)) (bytes 1))
   (and (= (fn-sl-step-conses cur bytes) 10)
        (<= (fn-sl-step-conses cur bytes) (fn-sl-step-cons-cells cur bytes))
        (<= (fn-sl-step-conses cur bytes) (+ (* 8 (nfix bytes)) 2)))))
(assert-event
 (let* ((cur (fn-sl-make "" 0 :cr)) (bytes 1))
   (and (= (fn-sl-step-conses cur bytes) 9)
        (<= (fn-sl-step-conses cur bytes) (fn-sl-step-cons-cells cur bytes))
        (<= (fn-sl-step-conses cur bytes) (+ (* 8 (nfix bytes)) 2)))))
(assert-event
 (and (= (fn-sl-step-conses nil 128) 2)
      (<= (fn-sl-step-conses nil 128) (fn-sl-step-cons-cells nil 128))
      (<= (fn-sl-step-conses nil 128) (+ (* 8 128) 2))))
(assert-event
 (let ((cur '(42 -3 :text)) (bytes 0) (acc '(a . b)))
   (and (<= (fn-sl-loop-conses cur bytes acc)
            (fn-sl-loop-cons-cells cur bytes (len acc)))
        (<= (fn-sl-step-conses cur bytes) (fn-sl-step-cons-cells cur bytes))
        (<= (fn-sl-step-conses cur bytes) (+ (* 8 (nfix bytes)) 2)))))
; MUTATION: dropping the accumulator/reverse copy from an active text step
; understates its allocation. No artificial hypothesis-removal claim:
; both boundary theorems above are unconditional.
(assert-event
 (let ((cur (fn-sl-make "abc" 0 :text)))
   (and (= (fn-sl-step-conses cur 1) 10)
        (not (<= (fn-sl-step-conses cur 1) 8)))))
