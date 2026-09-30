(in-package "ACL2")
(include-book "../../books/operator-report-reader-domain")

; All widths and the exact maximum scalar satisfy the literal antecedent
; and both bounds. This domain is the actual decoder's result, not a host
; supplied report/profile width certificate.
(assert-event
 (let ((next (fn-wildmat-utf8-next '(127))))
   (and (fn-wildmat-result-okp next)
        (natp (fn-wildmat-result-value next))
        (<= (fn-wildmat-result-value next) 1114111)
        (equal (fn-wildmat-result-value next) 127))))
(assert-event
 (let ((next (fn-wildmat-utf8-next '(223 191))))
   (and (fn-wildmat-result-okp next)
        (natp (fn-wildmat-result-value next))
        (<= (fn-wildmat-result-value next) 1114111)
        (equal (fn-wildmat-result-value next) 2047))))
(assert-event
 (let ((next (fn-wildmat-utf8-next '(239 191 191))))
   (and (fn-wildmat-result-okp next)
        (natp (fn-wildmat-result-value next))
        (<= (fn-wildmat-result-value next) 1114111)
        (equal (fn-wildmat-result-value next) 65535))))
(assert-event
 (let ((next (fn-wildmat-utf8-next '(244 143 191 191))))
   (and (fn-wildmat-result-okp next)
        (natp (fn-wildmat-result-value next))
        (<= (fn-wildmat-result-value next) 1114111)
        (equal (fn-wildmat-result-value next) 1114111))))

(defthm fn-oru-next-success-hypothesis-removal-witness
 (let* ((next (fn-wildmat-utf8-next '(255)))
        (value (fn-wildmat-result-value next)))
   (and (not (fn-wildmat-result-okp next))
        (not (and (natp value) (<= value 1114111)))))
 :rule-classes nil)
