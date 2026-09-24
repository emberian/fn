(in-package "ACL2")
(include-book "../../books/bp-fnbs-deletion-publication")
(include-book "bp-node-report-step-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun bpdp-operation ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-delete-publication-authorize
   (bprst-issued) (second (bprst-effect)) (third (bprst-effect))
   (fourth (bprst-effect)) t t))
(assert-event (fn-bpnf-delete-publication-operationp (bpdp-operation)))
(assert-event
 (equal (fn-bpnf-delete-publication-frame (bpdp-operation))
        (fn-bpnf-delete-frame (fourth (bprst-effect)))))
(assert-event
 (equal (car (fn-bpnf-delete-publication-authorize
              (bprst-issued) (second (bprst-effect))
              (third (bprst-effect)) (fourth (bprst-effect)) nil t))
        :fault))
(assert-event
 (equal (car (fn-bpnf-delete-publication-authorize
              (bprst-issued) (second (bprst-effect))
              (1+ (third (bprst-effect)))
              (fourth (bprst-effect)) t t))
        :fault))
(assert-event
 (equal (car (fn-bpnf-delete-publication-authorize
              (bprst-issued) (second (bprst-effect))
              (third (bprst-effect))
              (fn-bpn-report-delete-record 4 0 0 '(1)
                                           :lifetime-expired)
              t t))
        :fault))
(must-fail
 (assert-event
  (fn-bpnf-delete-publication-operationp
   (fn-bpnf-delete-publication-authorize
    (bprst-issued) (second (bprst-effect))
    (third (bprst-effect))
    (fourth (bprst-effect)) nil t))))
