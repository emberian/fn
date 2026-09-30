; Actual decoded-source trajectory through all five canonical padding regions.
; Every test evaluates complete literal hypotheses and conclusions. No native claim.
(in-package "ACL2")
(include-book "../../books/history-image-padding-refinement")
(include-book "../../books/history-image-effect-boundary")
(local (defun hpiz-test-buffer-copy (fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (list (fn-hpb-prefix-aux 0 2048 fn-hpb) (fn-hpb-used fn-hpb)
       (fn-hpb-epoch fn-hpb) (fn-hpb-lease fn-hpb))))
(local (defun hpiz-test-digest-frames (n pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons (pgs-dc-framesi (1- n) pgs-digest-state)
                     (hpiz-test-digest-frames (1- n) pgs-digest-state)))))
(local (defun hpiz-test-digest-copy (pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
 (list (pgs-dc-mode pgs-digest-state) (pgs-dc-sel pgs-digest-state)
       (pgs-dc-base pgs-digest-state) (pgs-dc-total pgs-digest-state)
       (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state)
       (pgs-dc-pos pgs-digest-state) (pgs-dc-counter pgs-digest-state)
       (pgs-dc-power pgs-digest-state) (pgs-dc-depth pgs-digest-state)
       (pgs-dc-cv pgs-digest-state) (pgs-dc-output pgs-digest-state)
       (pgs-dc-capture pgs-digest-state) (pgs-dc-lease pgs-digest-state)
       (pgs-dc-answer pgs-digest-state) (hpiz-test-digest-frames 64 pgs-digest-state))))

(local (defun hpiz-test-selected-copy (region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (case region (0 (hpiz-test-buffer-copy fn-hpq0)) (1 (hpiz-test-buffer-copy fn-hpq1))
              (2 (hpiz-test-buffer-copy fn-hpq2)) (3 (hpiz-test-buffer-copy fn-hpq3))
              (otherwise (hpiz-test-buffer-copy fn-hpb)))))
(local (defun hpiz-test-selected-invariant (region c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (let ((raw (nth region (fn-hp-regs '("ABC") (fn-omk-at 12 c))))
       (page (nfix (fn-omk-at region (fn-omk-at 15 c)))) (cap (fn-hpi-region-cap region c)))
  (case region (0 (fn-hpiz-region-invariantp raw page cap fn-hpq0))
               (1 (fn-hpiz-region-invariantp raw page cap fn-hpq1))
               (2 (fn-hpiz-region-invariantp raw page cap fn-hpq2))
               (3 (fn-hpiz-region-invariantp raw page cap fn-hpq3))
               (otherwise (fn-hpiz-region-invariantp raw page cap fn-hpb))))))

(local (defun hpiz-test-to-point (fuel region used c observation ledger
                       fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
  :verify-guards nil :measure (nfix fuel)
  :hints (("Goal" :in-theory (disable fn-hpi-tick fn-hpi-offer fn-hie-observation fn-omk-at)))))
 (if (or (zp fuel) (and (equal (fn-omk-at 0 c) :pad) (equal (fn-omk-at 18 c) region)
                        (equal (fn-hpi-region-used region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) used)))
  (mv (list (if (zp fuel) :fuel :reached) c ledger) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
  (mv-let (status effect c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
   (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
   (cond
    ((eq status :need-row)
     (mv-let (offered c) (fn-hpi-offer c 0 '(:decoded (:span 3 0 1 3)) (fn-omk-at 1 effect) (fn-hp-mkey "ABC" 17))
      (if (not (eq offered :started))
       (mv (list :offer-refused offered c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
       (hpiz-test-to-point (1- fuel) region used c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
    ((member-eq status '(:funded :continue :write :written :need-byte :row-done))
     (hpiz-test-to-point (1- fuel) region used c
      (cond ((eq status :write) (fn-hie-observation c effect (fn-omk-at 3 c) ledger 16384 :ok nil))
            ((eq status :need-byte) (list :supply (fn-omk-at 1 effect) (nth (fn-omk-at 1 effect) '(0 65 66 67))))
            (t nil)) ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
    (t (mv (list :unexpected status c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))

(local (defun hpiz-test-case (region used mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
   (mv-let (point fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpiz-test-to-point 18000 region used initial nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let* ((c (nth 1 point)) (ledger (nth 2 point))
           (baseline (and (eq admitted :admitted) (eq (car point) :reached)
              (fn-hpiz-writer-ready-p '("ABC") c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
              (fn-hpi-grant-matchesp c ledger)))
           ; Labelled selected-word corruption, after the actual reachable baseline.
           (fn-hpq0 (if (and (eq mode :invariant) (equal region 0)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq0)) fn-hpq0) fn-hpq0))
           (fn-hpq1 (if (and (eq mode :invariant) (equal region 1)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq1)) fn-hpq1) fn-hpq1))
           (fn-hpq2 (if (and (eq mode :invariant) (equal region 2)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq2)) fn-hpq2) fn-hpq2))
           (fn-hpq3 (if (and (eq mode :invariant) (equal region 3)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq3)) fn-hpq3) fn-hpq3))
           (fn-hpb (if (and (eq mode :invariant) (equal region 4)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpb)) fn-hpb) fn-hpb))
           (c (if (eq mode :status) (fn-hpi-set 22 nil c) c))
           (ready (fn-hpiz-writer-ready-p '("ABC") c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
           (old (hpiz-test-selected-copy region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
           (old-prefix (take used (car old)))
           (old0 (hpiz-test-buffer-copy fn-hpq0)) (old1 (hpiz-test-buffer-copy fn-hpq1))
           (old2 (hpiz-test-buffer-copy fn-hpq2)) (old3 (hpiz-test-buffer-copy fn-hpq3))
           (old4 (hpiz-test-buffer-copy fn-hpb)) (old-digest (hpiz-test-digest-copy pgs-digest-state)))
     (mv-let (await-status await-effect await-c) (fn-hpi-await-region region :pad c)
      (declare (ignore await-status))
      (mv-let (status effect next next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
       (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
       (let* ((new (hpiz-test-selected-copy region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
              (new-prefix (take (nth 1 new) (car new)))
              (status-hyp (eq status (if (equal used 2048) :write :continue)))
              (frames
               (and (implies (or (equal used 2048) (not (equal region 0))) (equal (hpiz-test-buffer-copy fn-hpq0) old0))
                    (implies (or (equal used 2048) (not (equal region 1))) (equal (hpiz-test-buffer-copy fn-hpq1) old1))
                    (implies (or (equal used 2048) (not (equal region 2))) (equal (hpiz-test-buffer-copy fn-hpq2) old2))
                    (implies (or (equal used 2048) (not (equal region 3))) (equal (hpiz-test-buffer-copy fn-hpq3) old3))
                    (implies (or (equal used 2048) (not (equal region 4))) (equal (hpiz-test-buffer-copy fn-hpb) old4))
                    (equal next-ledger ledger) (equal (hpiz-test-digest-copy pgs-digest-state) old-digest)))
              (conclusion
               (and frames
                (if (equal used 2048)
                 (and (equal (nth 1 old) 2048) (equal (len old-prefix) 2048)
                      (equal old-prefix (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at region (fn-omk-at 15 c))))
                        (fn-hp-wpad (nth region (fn-hp-regs '("ABC") (fn-omk-at 12 c)))))))
                      (equal status :write) (equal effect await-effect) (equal next await-c))
                 (and (hpiz-test-selected-invariant region c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                      (equal new-prefix (append old-prefix '(0))) (equal (nth 1 new) (+ 1 (nth 1 old)))
                      (equal (nth 2 new) (nth 2 old)) (equal (nth 3 new) (nth 3 old))
                      (equal effect nil) (equal next c))))))
        (mv (and baseline (equal (list (if ready t nil) status-hyp (if conclusion t nil))
                 (case mode (:positive '(t t t)) (:invariant '(nil t nil)) (:status '(t nil nil)))))
            fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))))))
(local (defun hpiz-test-local (region used mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpiz-test-case region used mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 0 1 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 0 1 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 0 1 :status))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 1 1 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 1 1 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 1 1 :status))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 2 1 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 2 1 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 2 1 :status))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 3 1 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 3 1 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 3 1 :status))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 4 1 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 4 1 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 4 1 :status))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 0 2048 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 0 2048 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 0 2048 :status))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 1 2048 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 1 2048 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 1 2048 :status))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 2 2048 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 2 2048 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 2 2048 :status))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 3 2048 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 3 2048 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 3 2048 :status))
; Reachable complete literal positive through actual decoded source and prior page ACKs.
(assert-event (hpiz-test-local 4 2048 :positive))
; Labelled selected-word corruption: fail ready, retain actual status, fail full conclusion.
(assert-event (hpiz-test-local 4 2048 :invariant))
; Labelled receipt removal: retain ready, fail actual status and full conclusion.
(assert-event (hpiz-test-local 4 2048 :status))
