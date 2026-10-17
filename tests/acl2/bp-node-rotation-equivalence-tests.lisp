; Machine equality teeth: a real queued job and a later received row.
(in-package "ACL2")
(include-book "bp-node-rotation-recovery-tests")
(include-book "bp-node-machine-authorization-tests")
(defun bprr-owed-record ()
  (third (car (fn-bpn-answer-effects
               (fn-bpn-step (fn-bpnf-base (fn-bpnr-open-fresh (bprd-owed-q)))
                            *bpcx-enqueue*)))))
(defun bprr-overlong-q ()
  (update-nth 1
    (nth 1 (fn-bpn-replay-records *bpna-s0* *bpna-overlong-records*))
    (bprd-owed-q)))
(defun bprr-overlong-ck ()
  (fn-bpnr-checkpoint-of-event *bpcx-n16-event* 1 (bprr-overlong-q)))
(defun bprr-empty-jobs-q ()
  (update-nth 1 (fn-bpn-state-with (bprd-owed-fb) nil nil nil nil 1)
              (bprd-owed-q)))
;; The same implementation mutant also violates whole-machine equivalence
;; against the actual pre-rotation lifecycle history; the conclusion stays
;; equality, and only the implementation called on the checkpoint changes.
(assert-event
 (equal
  (fn-bpnf-base (fn-bpnf-answer-state
    (bprr-open (bprd-traced-q) (bprr-traced-plan)
               '(8 1048576 65538 1048576) '(:same (7 7 7 7)))))
  (fn-bpnf-base (fn-bpnf-answer-state
    (fn-bpnj-step (bprd-trace-fresh) (bprd-trace-reopen-event))))))
(must-fail-checked
 (assert-event
  (equal
   (fn-bpnf-base (fn-bpnf-answer-state
     (bprr-mutant-open-without-seed (bprd-traced-q) (bprr-traced-plan)
                                  '(8 1048576 65538 1048576) '(:same (7 7 7 7)))))
   (fn-bpnf-base (fn-bpnf-answer-state
     (fn-bpnj-step (bprd-trace-fresh) (bprd-trace-reopen-event)))))))
