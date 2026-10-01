(in-package "ACL2")
(include-book "../../books/admission-semantic-census-source-guard")
(defthm fn-owner-census-source-begin-complete-positive
 (and (natp 2)
      (fn-osrc-guardp (fn-osrc-begin '(a b) 2 7 '(11 2)))
      (equal (fn-osrc-at 1 (fn-osrc-begin '(a b) 2 7 '(11 2))) '(a b))
      (equal (fn-osrc-at 9 (fn-osrc-begin '(a b) 2 7 '(11 2))) 7)
      (equal (fn-osrc-at 10 (fn-osrc-begin '(a b) 2 7 '(11 2))) '(11 2))))
; Logical invalid-guard mutation, not a reachable admitted constructor call.
(defthm fn-owner-census-source-begin-negative-count-mutation
 (and (not (natp -1))
      (not (fn-osrc-guardp (fn-osrc-begin '(a b) -1 7 '(11 2))))
      (equal (fn-osrc-at 1 (fn-osrc-begin '(a b) -1 7 '(11 2))) '(a b))
      (equal (fn-osrc-at 9 (fn-osrc-begin '(a b) -1 7 '(11 2))) 7)
      (equal (fn-osrc-at 10 (fn-osrc-begin '(a b) -1 7 '(11 2))) '(11 2))))
