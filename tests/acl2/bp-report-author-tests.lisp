(in-package "ACL2")
(include-book "../../books/bp-report-author")
(include-book "bp-report-outbox-tests")
(include-book "bp-node-machine-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun bpra-proposal ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-report-author-step
   (fn-bpnf-answer-state (bprst-settled))
   (list :queue-report 0 9 *bpnm-route* *bpnm-obs*)))
(assert-event (equal (car (car (fn-bpnf-answer-effects (bpra-proposal))))
                     :persist))
(assert-event
 (let* ((effect (car (fn-bpnf-answer-effects (bpra-proposal))))
        (job (third (third effect)))
        (bundle (fn-bpn-job-bundle job)))
   (and (fn-bpn-lifecycle-recordp (third effect))
        (equal (fn-bpp-flags (fn-bpb-bundle-primary bundle))
               *fn-bpp-flag-administrative*)
        (equal (fn-bpb-payload bundle) (fourth (bpro-outbox)))
        (equal (fn-bpp-report-to (fn-bpb-bundle-primary bundle))
               '(:dtn-none)))))
(assert-event
 (equal (fn-bpnf-held-list (fn-bpnf-answer-state (bpra-proposal)))
        (fn-bpnf-held-list (fn-bpnf-answer-state (bprst-settled)))))
(assert-event
 (equal (fn-bpnf-answer-effects
         (fn-bpn-report-author-step
          *bprst-state* (list :queue-report 0 9 *bpnm-route* *bpnm-obs*)))
        nil))
(must-fail
 (assert-event
  (equal (car (car (fn-bpnf-answer-effects (bpra-proposal))))
         :bundle-queue-accepted)))
