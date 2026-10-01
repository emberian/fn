(in-package "ACL2")
(include-book "../../books/operation-diagnostics")
(defun fn-od-test-report (budget)
 ; Logical fixture only, including deliberately corrupted negative budget.
 (declare (xargs :guard (natp budget) :verify-guards nil))
 (fn-od-report :observed :waiting :reserved :writing 19 0 7 23 :request-budget
  100 2 13 17 19 23 29 nil budget))
(assert-event
 (let ((budget 1000))
  (mv-let (word bytes) (fn-od-test-report budget)
   (and (natp budget) (eq word :rendered)
        (consp bytes) (<= (len bytes) budget)))))
 ; Corrupted-state removal witness is checked in logic, not by executing a
; negative budget through the guard-verified production entry.
(defthm fn-od-negative-budget-removal-witness
 (let ((budget -1))
  (and (not (natp budget))
       (equal (mv-nth 0 (fn-od-report :observed :waiting :reserved :writing
         19 0 7 23 :request-budget 100 2 13 17 19 23 29 nil budget))
              :response-budget-unavailable)
       (not (<= (len (mv-nth 1 (fn-od-report :observed :waiting :reserved :writing
         19 0 7 23 :request-budget 100 2 13 17 19 23 29 nil budget))) budget))))
 :hints (("Goal" :in-theory (enable fn-od-report)))
 :rule-classes nil)
(assert-event
 (mv-let (word bytes) (fn-od-test-report 1000)
  (let ((n (len bytes)))
   (mv-let (fit same) (fn-od-test-report n)
    (mv-let (short none) (fn-od-test-report (1- n))
     (and (eq word :rendered) (eq fit :rendered) (equal same bytes)
          (eq short :response-budget-unavailable) (null none)))))))
