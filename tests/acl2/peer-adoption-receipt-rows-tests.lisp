(in-package "ACL2")
(include-book "../../books/peer-adoption-receipt-rows")

; Positive complete antecedent/conclusion for preservation, nonempty rows.
(assert-event
 (let ((rows '(("p" "path-identity" "p" 0)
               ("p" "transport-nntp" "127.0.0.1" 119))))
   (and (fn-par-receipt-freep rows)
        (equal (fn-par-without-receipts rows) rows))))

; Positive mutation: all three internal receipt slots disappear, while
; ordinary rows retain their exact values and order.
(assert-event
 (let ((rows '(("p" "internal-invite-source" "subject" 3)
               ("p" "path-identity" "p" 0)
               ("p" "internal-invite-store" "store" 7)
               ("p" "internal-invite-key-generation" "" 2))))
   (and (not (fn-par-receipt-freep rows))
        (fn-par-receipt-freep (fn-par-without-receipts rows))
        (equal (fn-par-without-receipts rows)
               '(("p" "path-identity" "p" 0)))
        (equal (fn-par-without-receipts (fn-par-without-receipts rows))
               (fn-par-without-receipts rows)))))

; Hypothesis-removal witness: preservation fails on receipt-bearing rows.
(assert-event
 (let ((rows '(("p" "path-identity" "p" 0)
               ("p" "internal-invite-source" "subject" 3))))
   (and (not (fn-par-receipt-freep rows))
        (not (equal (fn-par-without-receipts rows) rows)))))
