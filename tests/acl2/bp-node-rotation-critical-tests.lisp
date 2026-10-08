; Critical packages for the pre-existing recovery-event theorems.
(in-package "ACL2")
(include-book "bp-node-rotation-recovery-tests")

;; These statements contain redundant conjuncts (ready replay already implies
;; a proper row list).  The admission tooth below removes the WHOLE antecedent
;; and is not evidence of independent necessity of each source conjunct.
;; The positive witness evaluates every conjunct and the complete conclusion.
(defun bprc-new ()
  (fn-bpnr-checkpoint-octets
   (fn-bpn-nth 4 (car (fn-bpnf-answer-effects (bprd-trace-rotate))))
   (bprd-budget (bprd-traced-q))))

(defteeth fn-bpnr-recover-from-checkpoint-equals-full-recover
  :claim (let* ((full (fn-bpnr-recover-auto-event st base-records sequence-ready
                                           rows0 plan0))
         (e (fn-bpn-nth 1 full))
         (rck (fn-bpnr-rotation-checkpoint ck1 e))
         (reopen (fn-bpnr-recover-auto-event
                  st base-records sequence-ready suffix
                  (fn-bpnr-selection-plan
                   t (fn-bpnr-checkpoint-octets rck budget) budget))))
    (((admission (and (true-listp rows0)
                  (not (equal (car plan0) :damaged))
                  (equal (car (fn-bpnr-replay-from
                               (fn-bpnr-plan-checkpoint plan0) rows0
                               (fn-bpnf-base st)))
                         :ready)
                  (equal ck1 (fn-bpnr-checkpoint-of-replay
                              generation
                              (fn-bpnr-replay-from
                               (fn-bpnr-plan-checkpoint plan0) rows0
                               (fn-bpnf-base st))
                              covered jobs next-token))
                  (fn-bpnr-checkpointp ck1)
                  (fn-bpnr-checkpoint-octets rck budget)
                  (fn-bpnr-rows-start-after suffix (cons e 0)))))
(and (implies (null suffix)
                           (equal reopen
                                  (list :recover-fnbs (1+ e) base-records
                                        sequence-ready
                                        (update-nth 3 (cons e 0)
                                                    (fn-bpn-nth 4 full))
                                        0)))
                  (implies (consp suffix)
                           (equal reopen
                                  (update-nth 5 (len suffix)
                                              (fn-bpnr-recover-auto-event
                                               st base-records sequence-ready
                                               (append rows0 suffix)
                                               plan0)))))))
  :subject fn-bpnr-recover-auto-event
  :witness ((st (bprd-trace-fresh)) (base-records (bprd-trace-records))
            (sequence-ready :ready) (rows0 (bprd-trace-rows)) (plan0 '(:none))
            (generation 1) (covered 1)
            (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-traced-q))))
            (next-token 3) (ck1 (bprd-traced-ck))
            (budget (bprd-budget (bprd-traced-q))) (suffix (list (bpcx-n16-row-b))))
  :breaks ((admission ((budget 2) (suffix nil))))
  :mutations ((loses-the-replayed-held-row
               (:conclusion (null (fn-bpn-nth 1 (fn-bpn-nth 4 reopen))))
               ((suffix nil))
               :fault "the reopen discards the held row carried by the traced checkpoint")))

(defteeth fn-bpnr-rotation-crash-recovers-old-or-new
  :claim (let ((e (fn-bpn-nth 1 (fn-bpnr-recover-auto-event
                          st base-records sequence-ready rows0 plan0))))
    (((admission (and (true-listp rows0)
                  (equal plan0 (fn-bpnr-selection-plan (and old t) old budget))
                  (not (equal (car plan0) :damaged))
                  (equal (car (fn-bpnr-replay-from
                               (fn-bpnr-plan-checkpoint plan0) rows0
                               (fn-bpnf-base st)))
                         :ready)
                  (equal ck1 (fn-bpnr-checkpoint-of-replay
                              generation
                              (fn-bpnr-replay-from
                               (fn-bpnr-plan-checkpoint plan0) rows0
                               (fn-bpnf-base st))
                              covered jobs next-token))
                  (fn-bpnr-checkpointp ck1)
                  (equal new (fn-bpnr-checkpoint-octets
                              (fn-bpnr-rotation-checkpoint ck1 e) budget))
                  new)))
(let* ((visible (fn-bpnr-crash-visible phase old new choice))
                    (plan (fn-bpnr-selection-plan (and visible t) visible
                                                  budget)))
               (and (or (equal visible old) (equal visible new))
                    (implies (not (fn-bpnr-replace-issuedp phase))
                             (equal visible old))
                    (implies (equal visible old) (equal plan plan0))
                    (implies (equal visible new)
                             (equal (fn-bpnr-recover-auto-event
                                     st base-records sequence-ready nil plan)
                                    (list :recover-fnbs (1+ e) base-records
                                          sequence-ready
                                          (update-nth
                                           3 (cons e 0)
                                           (fn-bpn-nth
                                            4 (fn-bpnr-recover-auto-event
                                               st base-records sequence-ready
                                               rows0 plan0)))
                                          0)))))))
  :subject fn-bpnr-recover-auto-event
  :witness ((st (bprd-trace-fresh)) (base-records (bprd-trace-records))
            (sequence-ready :ready) (rows0 (bprd-trace-rows)) (plan0 '(:none))
            (generation 1) (covered 1)
            (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-traced-q))))
            (next-token 3) (ck1 (bprd-traced-ck))
            (budget (bprd-budget (bprd-traced-q))) (old nil) (new (bprc-new))
            (phase :marker-attempted) (choice :new))
  :breaks ((admission ((new '(1)))))
  :mutations ((selects-new-before-rename
               (:conclusion (equal (fn-bpnr-crash-visible phase old new choice) new))
               ((phase :marker-staged))
               :fault "the publication implementation exposes the new authority before rename")))

;; Publication implementation mutant: expose NEW whenever the crash choice
;; says :new, omitting the phase test that prevents visibility before rename.
(defun bprc-mutant-crash-visible-before-rename (phase old new choice)
  (declare (ignore phase))
  (if (equal choice :new) new old))
(assert-event
 (and (consp (bprc-new))
      (equal (fn-bpnr-crash-visible :marker-staged nil (bprc-new) :new) nil)
      (equal (bprc-mutant-crash-visible-before-rename
              :marker-staged nil (bprc-new) :new) (bprc-new))))
(must-fail-checked
 (assert-event
  (equal (bprc-mutant-crash-visible-before-rename
          :marker-staged nil (bprc-new) :new) nil)))
