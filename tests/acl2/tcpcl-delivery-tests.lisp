; A real fn-tcl-complete END acknowledgement held across a BPA decision.
(in-package "ACL2")
(include-book "../../books/tcpcl-delivery-invariants")
(include-book "tcpcl-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *t-delivery-events* (fn-tcl-result-events *t-b3*))
(defconst *t-delivery-held*
  (list (cadr (nth 0 *t-delivery-events*))
        (cadr (nth 1 *t-delivery-events*))))

(assert-event (fn-tcl-held-final-ackp *t-delivery-held* 0))
(assert-event (equal (nth 2 *t-delivery-events*)
                     '(:bundle-received 0 (10 20 30 40 50))))
(assert-event
 (equal (fn-tcl-delivery-plan-status
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:accepted nil)))
        :accepted))
(assert-event
 (equal (fn-tcl-delivery-plan-messages
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:accepted nil)))
        *t-delivery-held*))
(assert-event
 (equal (fn-tcl-delivery-plan-messages
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:refused :capacity)))
        (list (fn-tcl-make-xfer-ack 2 0 3)
              (fn-tcl-make-xfer-refuse *fn-tcl-refuse-no-resources* 0))))
(assert-event
 (equal (fn-tcl-delivery-plan-messages
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:refused :identity-conflict)))
        (list (fn-tcl-make-xfer-ack 2 0 3)
              (fn-tcl-make-xfer-refuse *fn-tcl-refuse-not-acceptable* 0))))
(assert-event
 (null (fn-tcl-delivery-plan-messages
        (fn-tcl-delivery-plan *t-delivery-held* 0 '(:uncertain :persistence)))))
(assert-event
 (equal (fn-tcl-delivery-plan-status
         (fn-tcl-delivery-plan nil 0 '(:refused :capacity)))
        :fault))
(assert-event
 (equal (fn-tcl-delivery-plan-status
         (fn-tcl-delivery-plan *t-delivery-held* 18 '(:refused :capacity)))
        :fault))
(assert-event
 (equal (fn-tcl-delivery-plan-status
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:accepted 99)))
        :fault))
(assert-event
 (not (fn-tcl-output-has-final-ackp
       (fn-tcl-delivery-plan-messages
        (fn-tcl-delivery-plan *t-delivery-held* 0 '(:refused :capacity)))
       0)))
(must-fail
 (assert-event
  (equal (fn-tcl-delivery-plan-status
          (fn-tcl-delivery-plan nil 0 '(:refused :capacity)))
         :refused)))
