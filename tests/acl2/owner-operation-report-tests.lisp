(in-package "ACL2")
(include-book "../../books/owner-operation-report")

(defun fn-oor-test-report (current reason epoch fault budget)
 (declare (xargs :guard (natp budget)))
 (mv-let (word bytes) (fn-oor-report current reason epoch fault budget)
  (list word bytes)))

; Reachable retained row, all scalar fields are present and the entire report
; fits exactly. This uses the actual renderer, not a hand-built expected prefix.
(defconst *fn-oor-test-row*
 '((:admission-grant 731 19 3 4 23 :article) (13 17 19 23 29)
   :reserved :borrowed-graph nil))
(assert-event (fn-apr-livep (car *fn-oor-test-row*) *fn-oor-test-row*))
(assert-event
 (let* ((result (cadr (fn-oor-test-report *fn-oor-test-row* :writer-current 19 nil 4096)))
        (budget (len result)))
  (and (consp result)
       (equal (car (fn-oor-test-report *fn-oor-test-row* :writer-current 19 nil budget)) :rendered)
       (equal (cadr (fn-oor-test-report *fn-oor-test-row* :writer-current 19 nil budget)) result)
       (<= (len result) 4096))))
; Insufficient budget refuses the whole report rather than truncating fields.
(assert-event
 (let ((budget (1- (len (cadr (fn-oor-test-report *fn-oor-test-row* :writer-current 19 nil 4096))))))
  (and (equal (car (fn-oor-test-report *fn-oor-test-row* :writer-current 19 nil budget)) :response-budget-unavailable)
       (equal (cadr (fn-oor-test-report *fn-oor-test-row* :writer-current 19 nil budget)) nil))))
(assert-event (equal (cadr (fn-oor-test-report *fn-oor-test-row* :waiting 19 nil 0)) nil))
(assert-event
 (equal (cadr (fn-oor-test-report *fn-oor-test-row* :writer-current 19 nil 4096))
        (cadr (fn-oor-test-report (update-nth 3 '(:private arbitrary payload graph) *fn-oor-test-row*)
                                :writer-current 19 nil 4096))))
; Corrupted-state witness: no token/charge details leak from an invalid row.
(assert-event
 (equal (cadr (fn-oor-test-report '(:invalid (999 999 999 999 999) :reserved) :runtime-operation-unavailable 19 nil 4096))
        (cadr (fn-oor-test-report nil :runtime-operation-unavailable 19 nil 4096))))
