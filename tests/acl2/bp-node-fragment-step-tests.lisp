(in-package "ACL2")
(include-book "../../books/bp-node-fragment-step")
(include-book "bp-node-fragment-plan-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bpnfs-proposal ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-fragment-step *bpnff-state* '(:family 0)))
(defun bpnfs-pending ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-answer-state (bpnfs-proposal)))
(assert-event
 (equal (car (car (fn-bpnf-answer-effects (bpnfs-proposal))))
        :persist-family))
(assert-event
 (equal (fn-bpnf-held-list (bpnfs-pending))
        (fn-bpnf-held-list *bpnff-state*)))
(assert-event
 (equal (fn-bpnf-next-arrival (bpnfs-pending))
        (1+ (fn-bpnf-next-arrival *bpnff-state*))))
(defun bpnfs-durable ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-fragment-step (bpnfs-pending)
                         '(:persist-result 3 0 :durable)))
(assert-event
 (and (equal (car (car (fn-bpnf-answer-effects (bpnfs-durable))))
             :family-ready)
      (equal (len (fn-bpnf-held-list
                   (fn-bpnf-answer-state (bpnfs-durable)))) 5)
      (not (member-equal *bpnff-p3*
                         (fn-bpnf-held-list
                          (fn-bpnf-answer-state (bpnfs-durable)))))
      (not (member-equal *bpnff-p0*
                         (fn-bpnf-held-list
                          (fn-bpnf-answer-state (bpnfs-durable)))))))
(defun bpnfs-uncertain ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-answer-state
   (fn-bpnf-fragment-step (bpnfs-pending)
                          '(:persist-result 3 0 :uncertain))))
(assert-event
 (equal (fn-bpnf-fragment-step
         (bpnfs-uncertain) '(:persist-result 3 0 :durable))
        (fn-bpnf-answer (bpnfs-uncertain) nil)))
(assert-event
 (equal (fn-bpnf-fragment-step
         (bpnfs-uncertain) '(:family 2))
        (fn-bpnf-answer (bpnfs-uncertain) nil)))
(must-fail
 (assert-event
  (equal (fn-bpnf-held-list
          (fn-bpnf-answer-state (bpnfs-durable)))
         (fn-bpnf-held-list *bpnff-state*))))
