(in-package "ACL2")
(include-book "../../books/bp-node-fragment-step")
(include-book "../../books/bp-app-handoff-time")
(include-book "../../books/bp-node-receive-boundary")
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

; Pre-repair logical-state counterexample.  The nonzero fragment has exceeded
; its own Bundle Age lifetime at the later observation.  The newly received
; offset-zero fragment has a fresh local anchor.  The family selector still
; includes the expired nonzero bytes.  This state is NOT reachable through
; today's actual wire boundary: fn-bpn-receive refuses all fragments first.
(defconst *bpnfs-age-zero* (fn-bpb-bundle-age-block 2 0 0 0))
(defconst *bpnfs-aged-b3*
  (fn-bpb-make-bundle (fn-bpb-bundle-primary *bpnff-b3*)
                      (list *bpnfs-age-zero*)
                      (fn-bpb-bundle-payload *bpnff-b3*)))
(defconst *bpnfs-fresh-b0*
  (fn-bpb-make-bundle (fn-bpb-bundle-primary *bpnff-b0*)
                      (list *bpnfs-age-zero*)
                      (fn-bpb-bundle-payload *bpnff-b0*)))
(defconst *bpnfs-age-arrival* (fn-clock-observation 0 0 0 nil))
(defconst *bpnfs-age-later* (fn-clock-observation 60000001 0 0 nil))
(defconst *bpnfs-aged-p3*
  (update-nth 9
              (fn-bpnf-received-anchor *bpnfs-aged-b3*
                                       *bpnfs-age-arrival*)
              (fn-bpnfft-held '(112) 0 *bpnfs-aged-b3*
                               '(:dispatch-pending) nil)))
(defconst *bpnfs-fresh-p0*
  (update-nth 9
              (fn-bpnf-received-anchor *bpnfs-fresh-b0*
                                       *bpnfs-age-later*)
              (fn-bpnfft-held '(112) 1 *bpnfs-fresh-b0*
                               '(:dispatch-pending) nil)))
(defconst *bpnfs-expiry-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*)
                 (list *bpnfs-fresh-p0* *bpnfs-aged-p3*)
                 nil nil nil nil nil 3 0))
(assert-event (fn-bpnf-heldp *bpnfs-aged-p3*))
(assert-event (fn-bpnf-heldp *bpnfs-fresh-p0*))
(assert-event
 (equal (fn-bpnf-receive-wire-event
         *bpnff-config* (fn-bpb-encode *bpnfs-aged-b3*)
         *bpnfs-age-arrival* (fn-bpn-nth 4 *bpnfs-aged-p3*))
        '(:refused :fragment-not-reassembled)))
(assert-event
 (equal (fn-bpnf-receive-wire-event
         *bpnff-config* (fn-bpb-encode *bpnfs-fresh-b0*)
         *bpnfs-age-later* (fn-bpn-nth 4 *bpnfs-fresh-p0*))
        '(:refused :fragment-not-reassembled)))
(must-fail
 (assert-event
  (fn-bpnf-receive-wire-readyp
   (fn-bpnf-receive-wire-event
    *bpnff-config* (fn-bpb-encode *bpnfs-aged-b3*)
    *bpnfs-age-arrival* (fn-bpn-nth 4 *bpnfs-aged-p3*)))))
(assert-event (equal (fn-bpah-held-expiry *bpnfs-aged-p3* *bpnfs-age-later*)
                     :expired))
(assert-event (equal (fn-bpah-held-expiry *bpnfs-fresh-p0* *bpnfs-age-later*)
                     :live))
(assert-event (equal (car (fn-bpnf-family-next *bpnfs-expiry-state*)) :ready))
(assert-event (equal (car (car (fn-bpnf-answer-effects
                         (fn-bpnf-fragment-step
                          *bpnfs-expiry-state* '(:family 0)))))
                     :persist-family))
