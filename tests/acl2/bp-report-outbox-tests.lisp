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
 (equal (fn-bpn-report-outbox-peer-matchp (bpro-outbox) *bpah-peer*) t))
(assert-event
 (null (fn-bpn-report-outbox-peer-matchp (bpro-outbox) '(:dtn-none))))
(assert-event
 (equal (fourth (bpro-outbox))
        (fn-bpn-nth 6 (fourth (bprst-effect)))))
(assert-event
 (null (fn-bpn-report-outbox-next
        (fn-bpnf-answer-state (bprst-settled)) 0)))
(assert-event (null (fn-bpn-report-outbox-view *bprst-held*)))
(defun bpro-two-tombstones ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((old (car (fn-bpnf-held-list
                    (fn-bpnf-answer-state (bprst-settled)))))
         (new (update-nth 14
                          (update-nth 3 1 (fn-bpn-nth 14 old))
                          (update-nth 3 1 old))))
    (fn-bpnf-state-with-arrival
     (fn-bpnf-base *bprst-state*) (list new old)
     nil nil nil nil nil 4 0 2)))
(assert-event
 (equal (second (fn-bpn-report-outbox-next (bpro-two-tombstones) nil)) 0))
(assert-event
 (equal (second (fn-bpn-report-outbox-next (bpro-two-tombstones) 0)) 1))
(must-fail (assert-event (fn-bpn-report-outbox-view *bprst-held*)))
