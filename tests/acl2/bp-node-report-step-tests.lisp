(in-package "ACL2")
(include-book "../../books/bp-node-report-step")
(include-book "bp-report-deletion-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bprst-held* (update-nth 3 0 *bprd-request-held*))
(defconst *bprst-state*
  (fn-bpnf-state-with-arrival
   (fn-bpnf-base *bpah-state*) (list *bprst-held*)
   nil nil nil nil nil 4 0 1))
(defun bprst-proposal ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-report-step
   *bprst-state* (list :expire-held *bprd-later* t)))
(defun bprst-effect ()
  (declare (xargs :guard t :verify-guards nil)) (car (fn-bpnf-answer-effects (bprst-proposal))))
(defun bprst-issued ()
  (declare (xargs :guard t :verify-guards nil)) (fn-bpnf-answer-state (bprst-proposal)))

(assert-event (equal (car (bprst-effect)) :persist-delete))
(assert-event (equal (fn-bpn-nth 14 (car (fn-bpnf-held-list (bprst-issued))))
                     nil))
(assert-event
 (not (member-equal :report-due (fn-bpnf-answer-effects (bprst-proposal)))))
(defun bprst-settled ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-report-step
   (bprst-issued)
   (list :persist-result (second (bprst-effect))
         (third (bprst-effect)) :durable)))
(assert-event
 (equal (fn-bpn-nth 6 (fourth (bprst-effect)))
        (third (second (fn-bpnf-answer-effects (bprst-settled))))))
(assert-event
 (equal (fn-bpn-nth 14
         (car (fn-bpnf-held-list
               (fn-bpnf-answer-state (bprst-settled)))))
        (fourth (bprst-effect))))
(assert-event
 (equal (car (second (fn-bpnf-answer-effects (bprst-settled))))
        :report-due))
(assert-event
 (equal (fn-bpnf-answer-effects
         (fn-bpn-report-step
          (bprst-issued)
          (list :persist-result (second (bprst-effect))
                (1+ (third (bprst-effect))) :durable)))
        nil))
(defun bprst-refused ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-report-step
   (bprst-issued)
   (list :persist-result (second (bprst-effect))
         (third (bprst-effect)) :refused)))
(assert-event
 (null (fn-bpn-nth 14
        (car (fn-bpnf-held-list
              (fn-bpnf-answer-state (bprst-refused)))))))
(assert-event
 (equal (fn-bpn-nth 5
         (fn-bpnf-issued
          (fn-bpnf-answer-state
           (fn-bpn-report-step
            (bprst-issued)
            (list :persist-result (second (bprst-effect))
                  (third (bprst-effect)) :uncertain)))))
        :uncertain))
(must-fail
 (assert-event
  (equal (fn-bpn-nth 14
          (car (fn-bpnf-held-list (bprst-issued))))
         :lifetime-expired)))
