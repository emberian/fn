; Actual small decoded source trajectory. Mutations are separately labelled.
; Source-only exact canonical column carry; no INITIAL/physical/native claim.
(in-package "ACL2")
(include-book "../../books/history-image-body-refinement")
(include-book "../../books/history-image-effect-boundary")

(local (defun hpicol-test-buffer-copy (fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (list (fn-hpb-prefix-aux 0 2048 fn-hpb) (fn-hpb-used fn-hpb)
       (fn-hpb-epoch fn-hpb) (fn-hpb-lease fn-hpb))))
(local (defun hpicol-test-digest-frames (n pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons (pgs-dc-framesi (1- n) pgs-digest-state)
                     (hpicol-test-digest-frames (1- n) pgs-digest-state)))))
(local (defun hpicol-test-digest-copy (pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
 (list (pgs-dc-mode pgs-digest-state) (pgs-dc-sel pgs-digest-state)
       (pgs-dc-base pgs-digest-state) (pgs-dc-total pgs-digest-state)
       (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state)
       (pgs-dc-pos pgs-digest-state) (pgs-dc-counter pgs-digest-state)
       (pgs-dc-power pgs-digest-state) (pgs-dc-depth pgs-digest-state)
       (pgs-dc-cv pgs-digest-state) (pgs-dc-output pgs-digest-state)
       (pgs-dc-capture pgs-digest-state) (pgs-dc-lease pgs-digest-state)
       (pgs-dc-answer pgs-digest-state) (hpicol-test-digest-frames 64 pgs-digest-state))))


(local (defun hpicol-test-restore-words (i words fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil :measure (len words)))
 (if (atom words) fn-hpb
  (let ((fn-hpb (update-fn-hpb-wi i (car words) fn-hpb)))
   (hpicol-test-restore-words (+ 1 i) (cdr words) fn-hpb)))))
(local (defun hpicol-test-restore (saved fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let* ((fn-hpb (fn-hpb-begin (nth 2 saved) (nth 3 saved) fn-hpb))
        (fn-hpb (hpicol-test-restore-words 0 (car saved) fn-hpb)))
  (update-fn-hpb-used (nth 1 saved) fn-hpb))))

(local (defun hpicol-test-to-point (fuel column c observation ledger
                       fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
  :verify-guards nil :measure (nfix fuel)
  :hints (("Goal" :in-theory (disable fn-hpi-tick fn-hpi-offer fn-hie-observation fn-omk-at)))))
 (if (or (zp fuel) (and (equal (fn-omk-at 0 c) :body)
                        (equal (fn-hrcur-field 0 (fn-omk-at 14 c)) :columns)
                        (equal (fn-hrcur-field 9 (fn-omk-at 14 c)) column)))
  (mv (list (if (zp fuel) :fuel :reached) c ledger) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
  (mv-let (status effect c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
   (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
   (cond
    ((eq status :need-row)
     (mv-let (offered c) (fn-hpi-offer c 0 '(:decoded (:span 3 0 1 3)) (fn-omk-at 1 effect) (fn-hp-mkey "ABC" 17))
      (if (not (eq offered :started))
       (mv (list :offer-refused offered c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
       (hpicol-test-to-point (1- fuel) column c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
    ((member-eq status '(:funded :continue :write :written :need-byte))
     (hpicol-test-to-point (1- fuel) column c
      (cond ((eq status :write) (fn-hie-observation c effect (fn-omk-at 3 c) ledger 16384 :ok nil))
            ((eq status :need-byte) (list :supply (fn-omk-at 1 effect) (nth (fn-omk-at 1 effect) '(0 65 66 67))))
            (t nil)) ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
    (t (mv (list :unexpected status c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))

(local (defun hpicol-test-case (column mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
   (mv-let (point fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpicol-test-to-point 6000 column initial nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let* ((c (nth 1 point)) (ledger (nth 2 point))
           (baseline (and (eq admitted :admitted) (eq (car point) :reached)
              (fn-hpicol-writer-ready-p nil "ABC" 17 c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (fn-hpi-grant-matchesp c ledger)))
           ; Corrupt only frozen salt or retained receipt after establishing baseline.
           (c (case mode (:invariant (fn-hpi-set 12 18 c)) (:status (fn-hpi-set 22 nil c)) (otherwise c)))
           (ready (fn-hpicol-writer-ready-p nil "ABC" 17 c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))
           (body (fn-omk-at 14 c))
           (old0 (hpicol-test-buffer-copy fn-hpq0)) (old1 (hpicol-test-buffer-copy fn-hpq1))
           (old2 (hpicol-test-buffer-copy fn-hpq2)) (old3 (hpicol-test-buffer-copy fn-hpq3))
           (old4 (hpicol-test-buffer-copy fn-hpb)) (old-digest (hpicol-test-digest-copy pgs-digest-state)))
     ; Test-only independent execution of the actual inner implementation. Restore
     ; every backing word and metadata before calling the actual outer subject.
     (mv-let (inner-status inner-summary expected-body fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
      (fn-hpcx-tick body fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
      (declare (ignore inner-status inner-summary))
      (let* ((fn-hpq0 (hpicol-test-restore old0 fn-hpq0)) (fn-hpq1 (hpicol-test-restore old1 fn-hpq1))
             (fn-hpq2 (hpicol-test-restore old2 fn-hpq2)) (fn-hpq3 (hpicol-test-restore old3 fn-hpq3))
             (fn-hpb (hpicol-test-restore old4 fn-hpb)))
       (mv-let (status effect next next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (let* ((advancing (if (member-eq status '(:continue :row-done)) t nil))
               (done (eq status :row-done))
               (conclusion
                (and (fn-hpicol-four-invariantp (if done (list "ABC") nil) "ABC" 17
                       (fn-omk-at 14 next) (fn-omk-at 15 next) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
                     (equal (fn-omk-at 0 next) :body) (equal (fn-omk-at 12 next) 17)
                     (equal next (fn-hpi-set 14 expected-body c)) (equal next-ledger ledger)
                     (equal (hpicol-test-buffer-copy fn-hpb) old4) (equal (hpicol-test-digest-copy pgs-digest-state) old-digest)
                     (equal effect (if done (list :row-emitted (fn-hrcur-field 6 body) (len (fn-scc-encode "ABC"))) nil))
                     (equal (fn-hrcur-field 10 (fn-omk-at 14 next)) (fn-hrcur-field 10 body))
                     (equal (fn-hrcur-field 11 (fn-omk-at 14 next)) (fn-hrcur-field 11 body))
                     (implies (eq status :continue)
                      (and (equal (fn-hrcur-field 2 (fn-omk-at 14 next)) 0)
                           (equal (fn-hrcur-field 3 (fn-omk-at 14 next)) 0)
                           (equal (fn-hrcur-field 9 (fn-omk-at 14 next)) (+ 1 column))))
                     (implies done (and (equal (fn-hrcur-field 2 (fn-omk-at 14 next)) 1)
                                       (equal (fn-hrcur-field 3 (fn-omk-at 14 next)) (fn-hp-pes-len (list "ABC"))))))))
         (mv (and baseline (equal (list (if ready t nil) advancing (if conclusion t nil))
                (case mode (:positive '(t t t)) (:invariant '(nil t nil)) (:status '(t nil nil)))))
             fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))))))
(local (defun hpicol-test-local (column mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpicol-test-case column mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))
; Reachable full literal positive (decoded source).
(assert-event (hpicol-test-local 0 :positive))
; Labelled corruption/removal; retain other premise and fail full conclusion.
(assert-event (hpicol-test-local 0 :invariant))
; Labelled corruption/removal; retain other premise and fail full conclusion.
(assert-event (hpicol-test-local 0 :status))
; Reachable full literal positive (decoded source).
(assert-event (hpicol-test-local 1 :positive))
; Labelled corruption/removal; retain other premise and fail full conclusion.
(assert-event (hpicol-test-local 1 :invariant))
; Labelled corruption/removal; retain other premise and fail full conclusion.
(assert-event (hpicol-test-local 1 :status))
; Reachable full literal positive (decoded source).
(assert-event (hpicol-test-local 2 :positive))
; Labelled corruption/removal; retain other premise and fail full conclusion.
(assert-event (hpicol-test-local 2 :invariant))
; Labelled corruption/removal; retain other premise and fail full conclusion.
(assert-event (hpicol-test-local 2 :status))
; Reachable full literal positive (decoded source).
(assert-event (hpicol-test-local 3 :positive))
; Labelled corruption/removal; retain other premise and fail full conclusion.
(assert-event (hpicol-test-local 3 :invariant))
; Labelled corruption/removal; retain other premise and fail full conclusion.
(assert-event (hpicol-test-local 3 :status))
