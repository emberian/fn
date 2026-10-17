; Successful served-path restart from a rotation that owes a queued job.
(in-package "ACL2")
(include-book "bp-node-rotation-due-tests")

(defun bprr-open-keeps-owed-work-p (answer st plan)
  (and (equal (car (car (fn-bpnf-answer-effects answer))) :restart-ready)
       (equal (fn-bpn-machine-state-jobs (fn-bpnf-base (fn-bpnf-answer-state answer)))
              (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
       (equal (fn-bpn-machine-state-next-token (fn-bpnf-base (fn-bpnf-answer-state answer)))
              (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
       (equal (fn-bpn-host-lifecycle-recovery-agrees-p
               (fn-bpn-lifecycle-recovery-from nil nil (fn-bpnr-plan-start-token plan))
               (fn-bpnf-base (fn-bpnf-answer-state answer))) t)))

;; PREMISE-EXCESS-D: the clock-domain premise's host establishment.
(defconst *bprr-boot*
  '(48 49 50 51 52 53 54 55 45 56 57 97 98 45 99 100 101 102 45
    48 49 50 51 45 52 53 54 55 56 57 97 98 99 100 101 102))

(defun bprr-pending-store-st ()
  (update-nth 6 (fn-bpnf-operation 0 0 :store nil :pending) (bprd-trace-fresh)))
