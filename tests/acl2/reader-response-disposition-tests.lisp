; The core-produced step alone decides parser progress versus response custody.
(in-package "ACL2")
(include-book "../../books/reader-response-disposition")
(assert-event
 (equal (fn-rrd-step-disposition (fn-splan-step-make nil nil nil nil 3 nil nil))
        :parser-progress))
(assert-event
 (equal (fn-rrd-step-disposition (fn-splan-step-make nil t nil nil 0 nil nil))
        :response))
(assert-event
 (equal (fn-rrd-step-disposition
         (fn-splan-step-make '((:reply (50 50 52 13 10))) nil nil nil 17 nil nil))
        :response))
(assert-event
 (equal (fn-rrd-step-disposition (fn-splan-step-make nil nil nil nil 0 '((49)) nil))
        :response))
; Corrupted-state witness, not an omitted domain hypothesis.
(assert-event (eq (fn-rrd-step-disposition '(:served-step nil nil nil nil -1 nil nil))
                  :unavailable-step))
