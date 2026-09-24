(in-package "ACL2")
(include-book "../../books/bp-app-handoff-time")
(include-book "bp-app-handoff-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpaht-arrival* (fn-clock-observation 1000 0 0 nil))
(defconst *bpaht-live* (fn-clock-observation 1001 0 0 nil))
(defconst *bpaht-expired* (fn-clock-observation 3601002 0 0 nil))
(defconst *bpaht-anchored-held*
  (update-nth 9 (fn-bpnf-received-anchor *bpah-bundle* *bpaht-arrival*)
              *bpah-held*))
(defconst *bpaht-state*
  (fn-bpnf-state (fn-bpnf-base *bpah-state*)
                 (list *bpaht-anchored-held*)
                 (fn-bpnf-outcomes *bpah-state*)
                 (fn-bpnf-handoffs *bpah-state*)
                 (fn-bpnf-correlation *bpah-state*)
                 (fn-bpnf-issued *bpah-state*)
                 (fn-bpnf-waits *bpah-state*)
                 (fn-bpnf-epoch *bpah-state*)
                 (fn-bpnf-next-op *bpah-state*)))

(assert-event (equal (car (fn-bpah-pending-decision-at
                           *bpaht-state* *bpah-local* *bpaht-live*))
                     :ready))
(assert-event (null (fn-bpah-pending-decision-at
                     *bpaht-state* *bpah-local* *bpaht-expired*)))
(assert-event (equal (car (fn-bpah-pending-decision-at
                           *bpah-state* *bpah-local* *bpaht-live*))
                     :uncertain))
(must-fail
 (assert-event
  (equal (car (fn-bpah-pending-decision-at
               *bpah-state* *bpah-local* *bpaht-live*)) :ready)))
(must-fail
 (assert-event
  (equal (car (fn-bpah-pending-decision-at
               *bpaht-state* *bpah-local* *bpaht-expired*)) :ready)))
