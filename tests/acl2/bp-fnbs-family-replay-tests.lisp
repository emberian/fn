(in-package "ACL2")
(include-book "../../books/bp-fnbs-family-replay")
(include-book "bp-node-fragment-plan-tests")
(include-book "bp-report-deletion-tests")
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
  (fn-bpnf-family-record-at
   3 2 0 2 (nth 2 *bpnfr-replay-plan*)
   (fn-clock-observation 1 2343 0 t)))
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
         (fn-bpnf-family-publication-frame *bpnfr-replay-family-record*))))
(defun bpnfr-replay-answer ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-family-replay-rows
   (bpnfr-replay-rows) (fn-bpnf-base *bpnff-state*)))
(assert-event (equal (car *bpnfr-replay-plan*) :ready))
(assert-event (equal (car (bpnfr-replay-answer)) :ready))
(defconst *bpnfr-legacy-family-record*
  (fn-bpnf-family-record 3 2 0 2 (nth 2 *bpnfr-replay-plan*)))
(defun bpnfr-legacy-replay-answer ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-family-replay-rows
   (list (nth 0 (bpnfr-replay-rows))
         (nth 1 (bpnfr-replay-rows))
         (list (fn-bpnf-stored-record-name 3 2)
               (fn-bpnf-family-frame *bpnfr-legacy-family-record*)))
   (fn-bpnf-base *bpnff-state*)))
(assert-event
 (equal (bpnfr-legacy-replay-answer)
        '(:fault :kind-eighteen-row)))
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

; One ordered kind-5 then kind-10 history keeps the subject as a tombstone.
; Reversing the order or changing the subject identity faults at recovery.
(defconst *bpnfr-delete-held*
  (update-nth 3 0 *bprd-request-held*))
(defconst *bpnfr-delete-record*
  (fn-bpn-report-delete-record
   4 1 0 (fn-bpp-primary-identity
           (fn-bpb-bundle-primary
            (fn-bpnf-held-bundle *bpnfr-delete-held*)))
   :lifetime-expired))
(defun bpnfr-delete-rows ()
  (declare (xargs :guard t :verify-guards nil))
  (list
   (list (fn-bpnf-stored-record-name 4 0)
         (fn-bpnf-stored-record-frame
          (fn-bpnf-stored-record 4 0 *bpnfr-delete-held*)))
   (list (fn-bpnf-stored-record-name 4 1)
         (fn-bpnf-delete-frame *bpnfr-delete-record*))))
(defun bpnfr-delete-answer ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-family-replay-rows
   (bpnfr-delete-rows) (fn-bpnf-base *bpah-state*)))
(assert-event (equal (car (bpnfr-delete-answer)) :ready))
(assert-event
 (equal (fn-bpn-nth 14 (car (nth 1 (bpnfr-delete-answer))))
        *bpnfr-delete-record*))
(assert-event
 (equal (car (fn-bpnf-family-replay-rows
              (reverse (bpnfr-delete-rows))
              (fn-bpnf-base *bpah-state*))) :fault))
(assert-event
 (equal (car (fn-bpnf-family-replay-rows
              (list (car (bpnfr-delete-rows))
                    (list (fn-bpnf-stored-record-name 4 1)
                          (fn-bpnf-delete-frame
                           (fn-bpn-report-delete-record
                            4 1 0 '(1) :lifetime-expired))))
              (fn-bpnf-base *bpah-state*))) :fault))
