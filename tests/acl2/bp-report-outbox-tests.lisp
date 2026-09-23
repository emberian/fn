(in-package "ACL2")
(include-book "../../books/bp-report-outbox")
(include-book "bp-node-report-step-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun bpro-outbox ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-report-outbox-next (fn-bpnf-answer-state (bprst-settled)) nil))
(assert-event (equal (car (bpro-outbox)) :report-outbox))
(assert-event (equal (second (bpro-outbox)) 0))
(assert-event (equal (third (bpro-outbox)) *bpah-peer*))
(assert-event
 (equal (fourth (bpro-outbox))
        (fn-bpn-nth 6 (fourth (bprst-effect)))))
(assert-event
 (null (fn-bpn-report-outbox-next
        (fn-bpnf-answer-state (bprst-settled)) 0)))
(assert-event (null (fn-bpn-report-outbox-view *bprst-held*)))
(must-fail (assert-event (fn-bpn-report-outbox-view *bprst-held*)))
