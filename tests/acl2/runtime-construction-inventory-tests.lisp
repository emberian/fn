(in-package "ACL2")
(include-book "../../books/runtime-construction-inventory")

(assert-event (equal (fn-runtime-construction-inventory '(16 32 672) 80 64 4096)
                     '(:inventory-observed 720 80 64 1664)))
(assert-event (equal (fn-runtime-construction-inventory nil 0 0 1)
                     '(:inventory-observed 0 0 0 0)))
(assert-event (equal (fn-runtime-construction-inventory '(10 -1) 0 0 100)
                     '(:inventory-unavailable)))
(assert-event (equal (fn-runtime-construction-inventory '(10 . 1) 0 0 100)
                     '(:inventory-unavailable)))
(assert-event (equal (fn-runtime-construction-inventory '(60 50) 0 0 100)
                     '(:inventory-unavailable)))
(assert-event (equal (fn-runtime-construction-inventory '(40) 11 0 100)
                     '(:inventory-unavailable)))
(assert-event (equal (fn-runtime-construction-inventory '(40) 0 21 100)
                     '(:inventory-unavailable)))
(assert-event (equal (fn-runtime-construction-inventory '(40) 10 0 100)
                     '(:inventory-observed 40 10 0 100)))

; Complete antecedent and conclusion of the literal host-subject theorem.
(assert-event
 (let ((answer (fn-runtime-construction-inventory '(16 32 672) 80 64 4096)))
   (and (equal (car answer) :inventory-observed)
        (natp (nth 1 answer)) (natp (nth 4 answer))
        (equal (nth 4 answer) (+ (* 2 (+ (nth 1 answer) 80)) 64))
        (<= (nth 4 answer) 4096))))

; Removing the sole success premise falsifies the complete conclusion;
; there are no retained hypotheses. This is malformed input, not corruption
; of an already installed inventory or a simulated runtime success.
(assert-event
 (let ((answer (fn-runtime-construction-inventory '(16 -1) 0 0 4096)))
   (and (not (equal (car answer) :inventory-observed))
        (not (and (natp (nth 1 answer)) (natp (nth 4 answer))
                  (equal (nth 4 answer) (+ (* 2 (+ (nth 1 answer) 0)) 0))
                  (<= (nth 4 answer) 4096))))))
