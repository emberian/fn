; Reachable source-only zero/header trajectory and separately labelled mutations.
(in-package "ACL2")
(include-book "../../books/history-image-front-refinement")
(include-book "../../books/history-image-effect-boundary")

(local (defun hpif-test-buffer-copy (fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (list (fn-hpb-prefix-aux 0 2048 fn-hpb) (fn-hpb-used fn-hpb)
       (fn-hpb-epoch fn-hpb) (fn-hpb-lease fn-hpb))))
(local (defun hpif-test-digest-frames (n pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons (pgs-dc-framesi (1- n) pgs-digest-state)
                     (hpif-test-digest-frames (1- n) pgs-digest-state)))))
(local (defun hpif-test-digest-copy (pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
 (list (pgs-dc-mode pgs-digest-state) (pgs-dc-sel pgs-digest-state)
       (pgs-dc-base pgs-digest-state) (pgs-dc-total pgs-digest-state)
       (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state)
       (pgs-dc-pos pgs-digest-state) (pgs-dc-counter pgs-digest-state)
       (pgs-dc-power pgs-digest-state) (pgs-dc-depth pgs-digest-state)
       (pgs-dc-cv pgs-digest-state) (pgs-dc-output pgs-digest-state)
       (pgs-dc-capture pgs-digest-state) (pgs-dc-lease pgs-digest-state)
       (pgs-dc-answer pgs-digest-state) (hpif-test-digest-frames 64 pgs-digest-state))))

(local (defun hpif-test-to-point (fuel phase used c observation ledger
                                 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
                 :verify-guards nil :measure (nfix fuel)
                 :hints (("Goal" :in-theory (disable fn-hpi-tick fn-hie-observation fn-omk-at)))))
 (if (or (zp fuel) (and (equal (fn-omk-at 0 c) phase) (equal (fn-hpb-used fn-hpb) used)))
  (mv (list (if (zp fuel) :fuel :reached) c ledger) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
  (mv-let (status effect c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
   (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
   (if (member-eq status '(:funded :continue :write :written))
    (hpif-test-to-point (1- fuel) phase used c
      (if (eq status :write) (fn-hie-observation c effect (fn-omk-at 3 c) ledger 16384 :ok nil) nil)
      ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (mv (list :unexpected status c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))

(local (defun hpif-test-case (phase kind mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance
                   (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
   (mv-let (point fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpif-test-to-point 5000 phase (if (eq kind :continue) 3 2048) initial nil ledger
                       fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let* ((c (nth 1 point)) (ledger (nth 2 point))
           (baseline (and (eq admitted :admitted) (eq (car point) :reached)
                          (fn-hpif-invariantp c fn-hpb) (fn-hpi-grant-matchesp c ledger)))
           (fn-hpb (if (eq mode :invariant) (update-fn-hpb-wi 0 17 fn-hpb) fn-hpb))
           (c (if (eq mode :status) (fn-hpi-set 22 nil c) c))
           (inv (fn-hpif-invariantp c fn-hpb))
           (used (fn-hpb-used fn-hpb)) (epoch (fn-hpb-epoch fn-hpb)) (lease (fn-hpb-lease fn-hpb))
           (old0 (hpif-test-buffer-copy fn-hpq0)) (old1 (hpif-test-buffer-copy fn-hpq1))
           (old2 (hpif-test-buffer-copy fn-hpq2)) (old3 (hpif-test-buffer-copy fn-hpq3))
           (old4 (hpif-test-buffer-copy fn-hpb)) (digest (hpif-test-digest-copy pgs-digest-state))
           (model (take 2048 (fn-hpif-page-model c))))
     (mv-let (issued expected-effect expected-c)
      (fn-hpi-await-page (fn-hpif-page-region c) (if (eq phase :zero) nil 0)
                        (fn-hpif-page-physical c) 4 (fn-hpif-page-resume c) c)
      (declare (ignore issued))
      (mv-let (status effect next nextledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
       (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
       (let* ((actual-status (eq status kind))
              (frame (and (equal nextledger ledger) (equal (hpif-test-buffer-copy fn-hpq0) old0)
                          (equal (hpif-test-buffer-copy fn-hpq1) old1)
                          (equal (hpif-test-buffer-copy fn-hpq2) old2)
                          (equal (hpif-test-buffer-copy fn-hpq3) old3)
                          (equal (hpif-test-digest-copy pgs-digest-state) digest)))
              (conclusion
               (if (eq kind :continue)
                (and (fn-hpif-invariantp next fn-hpb) (null effect) (equal next c) frame
                     (equal (fn-hpb-used fn-hpb) (+ 1 used))
                     (equal (fn-hpb-epoch fn-hpb) epoch) (equal (fn-hpb-lease fn-hpb) lease))
                (and (equal used 2048) (equal (fn-hpb-prefix fn-hpb) model)
                     (eq status :write) (equal effect expected-effect) (equal next expected-c)
                     frame (equal (hpif-test-buffer-copy fn-hpb) old4)))))
        (mv (and baseline
                 (equal (list (if inv t nil) (if actual-status t nil) (if conclusion t nil))
                  (case mode (:positive '(t t t)) (:invariant '(nil t nil)) (:status '(t nil nil)))))
            fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))))))

(local (defun hpif-test-local (phase kind mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpif-test-case phase kind mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))
; Reachable full literal positive.
(assert-event (hpif-test-local :zero :continue :positive))
; Explicit corruption/removal: retain other premise, negate complete conclusion.
(assert-event (hpif-test-local :zero :continue :invariant))
; Explicit corruption/removal: retain other premise, negate complete conclusion.
(assert-event (hpif-test-local :zero :continue :status))
; Reachable full literal positive.
(assert-event (hpif-test-local :zero :write :positive))
; Explicit corruption/removal: retain other premise, negate complete conclusion.
(assert-event (hpif-test-local :zero :write :invariant))
; Explicit corruption/removal: retain other premise, negate complete conclusion.
(assert-event (hpif-test-local :zero :write :status))
; Reachable full literal positive.
(assert-event (hpif-test-local :header :continue :positive))
; Explicit corruption/removal: retain other premise, negate complete conclusion.
(assert-event (hpif-test-local :header :continue :invariant))
; Explicit corruption/removal: retain other premise, negate complete conclusion.
(assert-event (hpif-test-local :header :continue :status))
; Reachable full literal positive.
(assert-event (hpif-test-local :header :write :positive))
; Explicit corruption/removal: retain other premise, negate complete conclusion.
(assert-event (hpif-test-local :header :write :invariant))
; Explicit corruption/removal: retain other premise, negate complete conclusion.
(assert-event (hpif-test-local :header :write :status))
