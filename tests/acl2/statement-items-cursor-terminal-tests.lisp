(in-package "ACL2")
(include-book "../../books/statement-items-cursor-terminal")
(include-book "../../books/statement-items-cursor-spans")
; Real terminal completion tolerates extra scheduling ticks.
(assert-event
 (let* ((c (fn-sic-begin 2 '(66 9 10 1) 4 2))
        (p (fn-sic-completion-cost c)) (q (+ 3 p)) (d (fn-sic-run q c)))
  (and (natp q) (natp 2) (natp 4) (natp 2)
       (equal (fn-sic-at 0 d) :done) (equal d (fn-sic-run p c))
       (true-listp (car (fn-stmt-value (fn-sic-result d))))
       (equal (len (car (fn-stmt-value (fn-sic-result d)))) 4))))
; Terminal premise removal retains natural quantum and all profile hypotheses.
(assert-event
 (let* ((c (fn-sic-begin 2 '(66 9 10 1) 4 2)) (q 1) (d (fn-sic-run q c)))
  (and (natp q) (natp 2) (natp 4) (natp 2)
       (not (equal (fn-sic-at 0 d) :done))
       (not (equal d (fn-sic-run (fn-sic-completion-cost c) c))))))
; Corrupted descriptor with extra fields fails the now-carried fixed4 shape.
(assert-event
 (and (not (fn-sic-span-itemp '(:bytes 0 1 (1) :extra) '(1)))
      (fn-sic-span-itemp '(:bytes 0 1 (1)) '(1))))
