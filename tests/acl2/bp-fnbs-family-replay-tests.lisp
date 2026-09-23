(in-package "ACL2")
(include-book "../../books/bp-fnbs-family-replay")
(include-book "bp-node-fragment-plan-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnfr-p0-arrival-one*
  (fn-bpnfft-held '(112) 1 *bpnff-b0* '(:dispatch-pending) nil))
(defconst *bpnfr-replay-initial*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*)
                 (list *bpnfr-p0-arrival-one* *bpnff-p3*)
                 nil nil nil nil nil 3 0))
(defconst *bpnfr-replay-plan*
  (fn-bpnf-family-plan *bpnfr-replay-initial* *bpnff-p3*))
(defconst *bpnfr-replay-family-record*
  (fn-bpnf-family-record 3 2 0 2 (nth 2 *bpnfr-replay-plan*)))
(defun bpnfr-replay-rows ()
  (declare (xargs :guard t :verify-guards nil))
  (list
   (list (fn-bpnf-stored-record-name 3 0)
         (fn-bpnf-stored-record-frame
          (fn-bpnf-stored-record 3 0 *bpnff-p3*)))
   (list (fn-bpnf-stored-record-name 3 1)
         (fn-bpnf-stored-record-frame
          (fn-bpnf-stored-record 3 1 *bpnfr-p0-arrival-one*)))
   (list (fn-bpnf-stored-record-name 3 2)
         (fn-bpnf-family-frame *bpnfr-replay-family-record*))))
(defun bpnfr-replay-answer ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-family-replay-rows
   (bpnfr-replay-rows) (fn-bpnf-base *bpnff-state*)))
(assert-event (equal (car *bpnfr-replay-plan*) :ready))
(assert-event (equal (car (bpnfr-replay-answer)) :ready))
(assert-event (equal (nth 4 (bpnfr-replay-answer)) 3))
(assert-event (equal (len (nth 1 (bpnfr-replay-answer))) 1))
(assert-event
 (equal (fn-bpnf-held-wire (car (nth 1 (bpnfr-replay-answer))))
        (nth 2 *bpnfr-replay-plan*)))
(assert-event
 (equal (car (fn-bpnf-family-replay-rows
              (list (nth 2 (bpnfr-replay-rows)))
              (fn-bpnf-base *bpnff-state*))) :fault))
(assert-event
 (equal (car (fn-bpnf-family-replay-rows
              (list (nth 1 (bpnfr-replay-rows))
                    (nth 0 (bpnfr-replay-rows))
                    (nth 2 (bpnfr-replay-rows)))
              (fn-bpnf-base *bpnff-state*))) :fault))
(must-fail
 (assert-event
  (equal (car (fn-bpnf-family-replay-rows
               (list (nth 2 (bpnfr-replay-rows)))
               (fn-bpnf-base *bpnff-state*))) :ready)))
