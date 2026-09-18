; Result-shape and rejection-boundary assertions for parser invariants.
(in-package "ACL2")
(include-book "../../books/wildmat-parser-invariants")

(assert-event
 (fn-wildmat-parsedp
  (fn-wildmat-result-value (fn-wildmat-parse '(42)))))

(assert-event
 (fn-wildmat-parsedp
  (fn-wildmat-result-value
   (fn-wildmat-parse '(97 42 44 33 98 63 44 99)))))

(assert-event (equal (fn-wildmat-parse nil) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(33 97)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(97 44 44 98)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(97 44)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(194)) '(:error :malformed-utf8)))
