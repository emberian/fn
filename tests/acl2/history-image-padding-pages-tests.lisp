; Actual decoded-source trajectory through all five canonical padding regions.
; Every test evaluates complete literal hypotheses and conclusions. No native claim.
(in-package "ACL2")
(include-book "../../books/history-image-padding-pages")
(include-book "../../books/history-image-effect-boundary")
(local (defun hpizp-test-buffer-copy (fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (list (fn-hpb-prefix-aux 0 2048 fn-hpb) (fn-hpb-used fn-hpb)
       (fn-hpb-epoch fn-hpb) (fn-hpb-lease fn-hpb))))
(local (defun hpizp-test-digest-frames (n pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons (pgs-dc-framesi (1- n) pgs-digest-state)
                     (hpizp-test-digest-frames (1- n) pgs-digest-state)))))
(local (defun hpizp-test-digest-copy (pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
 (list (pgs-dc-mode pgs-digest-state) (pgs-dc-sel pgs-digest-state)
       (pgs-dc-base pgs-digest-state) (pgs-dc-total pgs-digest-state)
       (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state)
       (pgs-dc-pos pgs-digest-state) (pgs-dc-counter pgs-digest-state)
       (pgs-dc-power pgs-digest-state) (pgs-dc-depth pgs-digest-state)
       (pgs-dc-cv pgs-digest-state) (pgs-dc-output pgs-digest-state)
       (pgs-dc-capture pgs-digest-state) (pgs-dc-lease pgs-digest-state)
       (pgs-dc-answer pgs-digest-state) (hpizp-test-digest-frames 64 pgs-digest-state))))

(local (defun hpizp-test-selected-copy (region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (case region (0 (hpizp-test-buffer-copy fn-hpq0)) (1 (hpizp-test-buffer-copy fn-hpq1))
              (2 (hpizp-test-buffer-copy fn-hpq2)) (3 (hpizp-test-buffer-copy fn-hpq3))
              (otherwise (hpizp-test-buffer-copy fn-hpb)))))
(local (defun hpizp-test-selected-invariant (region c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (let ((raw (nth region (fn-hp-regs '("ABC") (fn-omk-at 12 c))))
       (page (nfix (fn-omk-at region (fn-omk-at 15 c)))) (cap (fn-hpi-region-cap region c)))
  (case region (0 (fn-hpiz-region-invariantp raw page cap fn-hpq0))
               (1 (fn-hpiz-region-invariantp raw page cap fn-hpq1))
               (2 (fn-hpiz-region-invariantp raw page cap fn-hpq2))
               (3 (fn-hpiz-region-invariantp raw page cap fn-hpq3))
               (otherwise (fn-hpiz-region-invariantp raw page cap fn-hpb))))))

(local (defun hpizp-test-to-point (fuel region used c observation ledger
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
       (hpizp-test-to-point (1- fuel) region used c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
    ((member-eq status '(:funded :continue :write :written :need-byte :row-done))
     (hpizp-test-to-point (1- fuel) region used c
      (cond ((eq status :write) (fn-hie-observation c effect (fn-omk-at 3 c) ledger 16384 :ok nil))
            ((eq status :need-byte) (list :supply (fn-omk-at 1 effect) (nth (fn-omk-at 1 effect) '(0 65 66 67))))
            (t nil)) ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
    (t (mv (list :unexpected status c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))


(local (defun hpizp-test-case (region mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
   (mv-let (point fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpizp-test-to-point 18000 region 2048 initial nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let ((c (nth 1 point)) (ledger (nth 2 point)))
     (mv-let (issued effect c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (let* ((baseline (and (eq admitted :admitted) (eq (car point) :reached) (eq issued :write)
                           (fn-hpizp-ack-contextp c) (fn-hpi-grant-matchesp c ledger)
                           (fn-hpizp-five-invariantp '("ABC") (fn-omk-at 12 c) (fn-omk-at 15 c)
                            (fn-omk-at 9 c) (fn-omk-at 10 c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
             (observation (fn-hie-observation c effect (fn-omk-at 3 c) ledger 16384 (if (eq mode :status) :uncertain :ok) nil))
             (other (mod (+ 1 region) 5))
             ; Labelled corruption of an untouched region, never source data.
             (fn-hpq0 (if (and (eq mode :canonical) (equal other 0)) (let ((fn-hpq0 (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq0)) fn-hpq0))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpq0)) fn-hpq0)) fn-hpq0))
             (fn-hpq1 (if (and (eq mode :canonical) (equal other 1)) (let ((fn-hpq1 (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq1)) fn-hpq1))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpq1)) fn-hpq1)) fn-hpq1))
             (fn-hpq2 (if (and (eq mode :canonical) (equal other 2)) (let ((fn-hpq2 (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq2)) fn-hpq2))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpq2)) fn-hpq2)) fn-hpq2))
             (fn-hpq3 (if (and (eq mode :canonical) (equal other 3)) (let ((fn-hpq3 (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq3)) fn-hpq3))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpq3)) fn-hpq3)) fn-hpq3))
             (fn-hpb (if (and (eq mode :canonical) (equal other 4)) (let ((fn-hpb (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpb)) fn-hpb))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpb)) fn-hpb)) fn-hpb))
             ; Corrupted pending counter/empty buffer at cap: not a reachable issuance.
             (c (if (eq mode :full) (fn-hpi-set 15 (fn-hpi-set region (fn-hpi-region-cap region c) (fn-omk-at 15 c)) c) c))
             (fn-hpq0 (if (and (eq mode :full) (equal region 0)) (update-fn-hpb-used 0 fn-hpq0) fn-hpq0))
             (fn-hpq1 (if (and (eq mode :full) (equal region 1)) (update-fn-hpb-used 0 fn-hpq1) fn-hpq1))
             (fn-hpq2 (if (and (eq mode :full) (equal region 2)) (update-fn-hpb-used 0 fn-hpq2) fn-hpq2))
             (fn-hpq3 (if (and (eq mode :full) (equal region 3)) (update-fn-hpb-used 0 fn-hpq3) fn-hpq3))
             (fn-hpb (if (and (eq mode :full) (equal region 4)) (update-fn-hpb-used 0 fn-hpb) fn-hpb))
             (c (if (eq mode :context) (fn-hpi-set 17 (list region :header) c) c))
             (context (fn-hpizp-ack-contextp c))
             (canonical (fn-hpizp-five-invariantp '("ABC") (fn-omk-at 12 c) (fn-omk-at 15 c)
                          (fn-omk-at 9 c) (fn-omk-at 10 c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
             (old0 (hpizp-test-buffer-copy fn-hpq0)) (old1 (hpizp-test-buffer-copy fn-hpq1))
             (old2 (hpizp-test-buffer-copy fn-hpq2)) (old3 (hpizp-test-buffer-copy fn-hpq3))
             (old4 (hpizp-test-buffer-copy fn-hpb)) (old-digest (hpizp-test-digest-copy pgs-digest-state))
             (full (equal (fn-hpi-region-used region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 2048)))
       (mv-let (status effect next next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (let* ((written (eq status :written))
               (frames (and (equal effect nil) (equal next-ledger ledger)
                            (equal (hpizp-test-digest-copy pgs-digest-state) old-digest)))
               (main (and frames (fn-hpizp-five-invariantp '("ABC") (fn-omk-at 12 next) (fn-omk-at 15 next)
                         (fn-omk-at 9 next) (fn-omk-at 10 next) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                          (equal (fn-omk-at 0 next) :pad) (equal (fn-omk-at 18 next) (fn-omk-at 18 c))
                          (equal (fn-omk-at 14 next) (fn-omk-at 14 c))))
               (structural
                (and frames (equal (fn-hpi-written-status (fn-omk-at 5 c) observation) :written)
                     (equal (fn-omk-at 0 next) :pad)
                     (equal (fn-omk-at 9 next) (fn-omk-at 9 c)) (equal (fn-omk-at 10 next) (fn-omk-at 10 c))
                     (equal (fn-omk-at 12 next) (fn-omk-at 12 c)) (equal (fn-omk-at 14 next) (fn-omk-at 14 c))
                     (equal (fn-omk-at 18 next) (fn-omk-at 18 c))
                     (equal (fn-omk-at 15 next) (fn-hpi-set region (+ 1 (nfix (fn-omk-at region (fn-omk-at 15 c)))) (fn-omk-at 15 c)))
                     (equal (fn-omk-at 16 next) (fn-hpi-set region (+ 1 (nfix (fn-omk-at region (fn-omk-at 16 c)))) (fn-omk-at 16 c)))
                     (equal (fn-omk-at 5 next) nil) (equal (fn-omk-at 17 next) nil)
                     (equal (hpizp-test-buffer-copy fn-hpq0) (if (equal region 0) (list (car old0) 0 (fn-omk-at 1 c) (fn-omk-at 2 c)) old0))
                     (equal (hpizp-test-buffer-copy fn-hpq1) (if (equal region 1) (list (car old1) 0 (fn-omk-at 1 c) (fn-omk-at 2 c)) old1))
                     (equal (hpizp-test-buffer-copy fn-hpq2) (if (equal region 2) (list (car old2) 0 (fn-omk-at 1 c) (fn-omk-at 2 c)) old2))
                     (equal (hpizp-test-buffer-copy fn-hpq3) (if (equal region 3) (list (car old3) 0 (fn-omk-at 1 c) (fn-omk-at 2 c)) old3))
                     (equal (hpizp-test-buffer-copy fn-hpb) (if (equal region 4) (list (car old4) 0 (fn-omk-at 1 c) (fn-omk-at 2 c)) old4)))))
         (mv (and baseline (equal (list (if context t nil) (if canonical t nil) full written (if main t nil) (if structural t nil))
               (case mode (:positive '(t t t t t t)) (:context '(nil t t t nil nil))
                          (:canonical '(t nil t t nil t)) (:full '(t t nil t nil t)) (:status '(t t t nil nil nil)))))
             fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))))))
(local (defun hpizp-test-local (region mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpizp-test-case region mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))
; Actual decoded-source complete positive through pending full-page issuance and exact ACK.
(assert-event (hpizp-test-local 0 :positive))
; Labelled resume corruption: retain canonical/full/written, fail context and full conclusions.
(assert-event (hpizp-test-local 0 :context))
; Labelled untouched-region corruption: retain context/full/written, fail canonical/main, structural still holds.
(assert-event (hpizp-test-local 0 :canonical))
; Labelled pending counter/empty-buffer corruption at cap (not reachable issuance): retain context/canonical/written, fail full/main; structural holds.
(assert-event (hpizp-test-local 0 :full))
; Actual uncertain outcome: retain context/canonical/full, fail written and complete conclusions.
(assert-event (hpizp-test-local 0 :status))
; Actual decoded-source complete positive through pending full-page issuance and exact ACK.
(assert-event (hpizp-test-local 1 :positive))
; Labelled resume corruption: retain canonical/full/written, fail context and full conclusions.
(assert-event (hpizp-test-local 1 :context))
; Labelled untouched-region corruption: retain context/full/written, fail canonical/main, structural still holds.
(assert-event (hpizp-test-local 1 :canonical))
; Labelled pending counter/empty-buffer corruption at cap (not reachable issuance): retain context/canonical/written, fail full/main; structural holds.
(assert-event (hpizp-test-local 1 :full))
; Actual uncertain outcome: retain context/canonical/full, fail written and complete conclusions.
(assert-event (hpizp-test-local 1 :status))
; Actual decoded-source complete positive through pending full-page issuance and exact ACK.
(assert-event (hpizp-test-local 2 :positive))
; Labelled resume corruption: retain canonical/full/written, fail context and full conclusions.
(assert-event (hpizp-test-local 2 :context))
; Labelled untouched-region corruption: retain context/full/written, fail canonical/main, structural still holds.
(assert-event (hpizp-test-local 2 :canonical))
; Labelled pending counter/empty-buffer corruption at cap (not reachable issuance): retain context/canonical/written, fail full/main; structural holds.
(assert-event (hpizp-test-local 2 :full))
; Actual uncertain outcome: retain context/canonical/full, fail written and complete conclusions.
(assert-event (hpizp-test-local 2 :status))
; Actual decoded-source complete positive through pending full-page issuance and exact ACK.
(assert-event (hpizp-test-local 3 :positive))
; Labelled resume corruption: retain canonical/full/written, fail context and full conclusions.
(assert-event (hpizp-test-local 3 :context))
; Labelled untouched-region corruption: retain context/full/written, fail canonical/main, structural still holds.
(assert-event (hpizp-test-local 3 :canonical))
; Labelled pending counter/empty-buffer corruption at cap (not reachable issuance): retain context/canonical/written, fail full/main; structural holds.
(assert-event (hpizp-test-local 3 :full))
; Actual uncertain outcome: retain context/canonical/full, fail written and complete conclusions.
(assert-event (hpizp-test-local 3 :status))
; Actual decoded-source complete positive through pending full-page issuance and exact ACK.
(assert-event (hpizp-test-local 4 :positive))
; Labelled resume corruption: retain canonical/full/written, fail context and full conclusions.
(assert-event (hpizp-test-local 4 :context))
; Labelled untouched-region corruption: retain context/full/written, fail canonical/main, structural still holds.
(assert-event (hpizp-test-local 4 :canonical))
; Labelled pending counter/empty-buffer corruption at cap (not reachable issuance): retain context/canonical/written, fail full/main; structural holds.
(assert-event (hpizp-test-local 4 :full))
; Actual uncertain outcome: retain context/canonical/full, fail written and complete conclusions.
(assert-event (hpizp-test-local 4 :status))
