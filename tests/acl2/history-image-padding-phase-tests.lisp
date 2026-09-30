; Actual decoded-source trajectory through all five canonical padding regions.
; Every test evaluates complete literal hypotheses and conclusions. No native claim.
(in-package "ACL2")
(include-book "../../books/history-image-padding-phase")
(include-book "../../books/history-image-effect-boundary")
(local (defun hpizs-test-buffer-copy (fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (list (fn-hpb-prefix-aux 0 2048 fn-hpb) (fn-hpb-used fn-hpb)
       (fn-hpb-epoch fn-hpb) (fn-hpb-lease fn-hpb))))
(local (defun hpizs-test-digest-frames (n pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons (pgs-dc-framesi (1- n) pgs-digest-state)
                     (hpizs-test-digest-frames (1- n) pgs-digest-state)))))
(local (defun hpizs-test-digest-copy (pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
 (list (pgs-dc-mode pgs-digest-state) (pgs-dc-sel pgs-digest-state)
       (pgs-dc-base pgs-digest-state) (pgs-dc-total pgs-digest-state)
       (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state)
       (pgs-dc-pos pgs-digest-state) (pgs-dc-counter pgs-digest-state)
       (pgs-dc-power pgs-digest-state) (pgs-dc-depth pgs-digest-state)
       (pgs-dc-cv pgs-digest-state) (pgs-dc-output pgs-digest-state)
       (pgs-dc-capture pgs-digest-state) (pgs-dc-lease pgs-digest-state)
       (pgs-dc-answer pgs-digest-state) (hpizs-test-digest-frames 64 pgs-digest-state))))

(local (defun hpizs-test-selected-copy (region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (case region (0 (hpizs-test-buffer-copy fn-hpq0)) (1 (hpizs-test-buffer-copy fn-hpq1))
              (2 (hpizs-test-buffer-copy fn-hpq2)) (3 (hpizs-test-buffer-copy fn-hpq3))
              (otherwise (hpizs-test-buffer-copy fn-hpb)))))
(local (defun hpizs-test-selected-invariant (region c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (let ((raw (nth region (fn-hp-regs '("ABC") (fn-omk-at 12 c))))
       (page (nfix (fn-omk-at region (fn-omk-at 15 c)))) (cap (fn-hpi-region-cap region c)))
  (case region (0 (fn-hpiz-region-invariantp raw page cap fn-hpq0))
               (1 (fn-hpiz-region-invariantp raw page cap fn-hpq1))
               (2 (fn-hpiz-region-invariantp raw page cap fn-hpq2))
               (3 (fn-hpiz-region-invariantp raw page cap fn-hpq3))
               (otherwise (fn-hpiz-region-invariantp raw page cap fn-hpb))))))

(local (defun hpizs-test-to-point (fuel region used c observation ledger
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
       (hpizs-test-to-point (1- fuel) region used c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
    ((member-eq status '(:funded :continue :write :written :need-byte :row-done))
     (hpizs-test-to-point (1- fuel) region used c
      (cond ((eq status :write) (fn-hie-observation c effect (fn-omk-at 3 c) ledger 16384 :ok nil))
            ((eq status :need-byte) (list :supply (fn-omk-at 1 effect) (nth (fn-omk-at 1 effect) '(0 65 66 67))))
            (t nil)) ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
    (t (mv (list :unexpected status c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))



(local (defun hpizs-test-case (region mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
   (mv-let (point fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpizs-test-to-point 18000 (if (and (equal region 5) (eq mode :cap)) 4 region)
      (cond ((eq mode :cap) 1) ((equal region 5) 0) (t 2048)) initial nil ledger
      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let ((c (nth 1 point)) (ledger (nth 2 point)))
     (mv-let (ignored c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (if (or (eq mode :cap) (equal region 5))
       (mv :already c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
       (mv-let (issued effect c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (declare (ignore issued))
        (mv-let (word ignored-effect c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
         (fn-hpi-tick c (fn-hie-observation c effect (fn-omk-at 3 c) ledger 16384 :ok nil)
           ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
         (declare (ignore ignored-effect))
         (mv word c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
      (declare (ignore ignored))
      (let* ((baseline (and (eq admitted :admitted) (eq (car point) :reached) (fn-hpi-grant-matchesp c ledger)
              (fn-hpizp-five-invariantp '("ABC") (fn-omk-at 12 c) (fn-omk-at 15 c) (fn-omk-at 9 c) (fn-omk-at 10 c)
                 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
             ; Terminal :cap is separately labelled premature final-region corruption.
             (c (if (and (equal region 5) (eq mode :cap)) (fn-hpi-set 18 5 c) c))
             (c (if (eq mode :context) (fn-hpi-set 0 :body c) c))
             (c (if (eq mode :status) (fn-hpi-set 22 nil c) c))
             (other (if (equal region 5) 4 (mod (+ 1 region) 5)))
             (fn-hpq0 (if (and (eq mode :canonical) (equal other 0)) (let ((fn-hpq0 (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq0)) fn-hpq0))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpq0)) fn-hpq0)) fn-hpq0))
             (fn-hpq1 (if (and (eq mode :canonical) (equal other 1)) (let ((fn-hpq1 (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq1)) fn-hpq1))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpq1)) fn-hpq1)) fn-hpq1))
             (fn-hpq2 (if (and (eq mode :canonical) (equal other 2)) (let ((fn-hpq2 (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq2)) fn-hpq2))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpq2)) fn-hpq2)) fn-hpq2))
             (fn-hpq3 (if (and (eq mode :canonical) (equal other 3)) (let ((fn-hpq3 (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq3)) fn-hpq3))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpq3)) fn-hpq3)) fn-hpq3))
             (fn-hpb (if (and (eq mode :canonical) (equal other 4)) (let ((fn-hpb (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpb)) fn-hpb))) (update-fn-hpb-used (max 1 (fn-hpb-used fn-hpb)) fn-hpb)) fn-hpb))
             (context (if (equal region 5) (fn-hpizs-terminal-contextp c) (fn-hpizs-region-contextp c)))
             (cap (if (equal region 5) (fn-hpizs-pages-complete-p c)
                    (equal (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c))))
             (canonical (fn-hpizp-five-invariantp '("ABC") (fn-omk-at 12 c) (fn-omk-at 15 c) (fn-omk-at 9 c) (fn-omk-at 10 c)
                           fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
             (old0 (hpizs-test-buffer-copy fn-hpq0)) (old1 (hpizs-test-buffer-copy fn-hpq1))
             (old2 (hpizs-test-buffer-copy fn-hpq2)) (old3 (hpizs-test-buffer-copy fn-hpq3))
             (old4 (hpizs-test-buffer-copy fn-hpb)) (old-digest (hpizs-test-digest-copy pgs-digest-state)))
       (mv-let (status effect next next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (let ((conclusion
               (and (equal status :continue) (equal effect nil) (equal next-ledger ledger)
                    (equal next (if (equal region 5) (fn-hpi-set 0 :data-digest-start c) (fn-hpi-set 18 (+ 1 region) c)))
                    (equal (hpizs-test-buffer-copy fn-hpq0) old0) (equal (hpizs-test-buffer-copy fn-hpq1) old1)
                    (equal (hpizs-test-buffer-copy fn-hpq2) old2) (equal (hpizs-test-buffer-copy fn-hpq3) old3)
                    (equal (hpizs-test-buffer-copy fn-hpb) old4) (equal (hpizs-test-digest-copy pgs-digest-state) old-digest)
                    (if (equal region 5)
                     (and (equal (fn-hpb-used fn-hpq0) 0) (equal (fn-hpb-used fn-hpq1) 0) (equal (fn-hpb-used fn-hpq2) 0)
                          (equal (fn-hpb-used fn-hpq3) 0) (equal (fn-hpb-used fn-hpb) 0))
                     (equal (fn-hpi-region-used region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 0))
                    (fn-hpizp-five-invariantp '("ABC") (fn-omk-at 12 next) (fn-omk-at 15 next) (fn-omk-at 9 next) (fn-omk-at 10 next)
                      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))
         (mv (and baseline (equal (list (if context t nil) (if canonical t nil) (if cap t nil) (eq status :continue) (if conclusion t nil))
              (case mode (:positive '(t t t t t)) (:context '(nil t t t nil))
                         (:canonical '(t nil t t nil)) (:cap '(t t nil t nil)) (:status '(t t t nil nil)))))
             fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))))))
(local (defun hpizs-test-local (region mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpizs-test-case region mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))
; Actual decoded-source complete positive through all preceding region writes/ACKs.
(assert-event (hpizs-test-local 0 :positive))
; Labelled body-phase mutation: retain full canonical/counts/actualcontinue, fail context/conclusion.
(assert-event (hpizs-test-local 0 :context))
; Labelled buffer corruption: retain context/counts/actualcontinue, fail canonical/fullconclusion.
(assert-event (hpizs-test-local 0 :canonical))
; Reachable unfinished-region alternative
(assert-event (hpizs-test-local 0 :cap))
; Labelled receipt removal: retain context/canonical/counts, fail actualcontinue/fullconclusion.
(assert-event (hpizs-test-local 0 :status))
; Actual decoded-source complete positive through all preceding region writes/ACKs.
(assert-event (hpizs-test-local 1 :positive))
; Labelled body-phase mutation: retain full canonical/counts/actualcontinue, fail context/conclusion.
(assert-event (hpizs-test-local 1 :context))
; Labelled buffer corruption: retain context/counts/actualcontinue, fail canonical/fullconclusion.
(assert-event (hpizs-test-local 1 :canonical))
; Reachable unfinished-region alternative
(assert-event (hpizs-test-local 1 :cap))
; Labelled receipt removal: retain context/canonical/counts, fail actualcontinue/fullconclusion.
(assert-event (hpizs-test-local 1 :status))
; Actual decoded-source complete positive through all preceding region writes/ACKs.
(assert-event (hpizs-test-local 2 :positive))
; Labelled body-phase mutation: retain full canonical/counts/actualcontinue, fail context/conclusion.
(assert-event (hpizs-test-local 2 :context))
; Labelled buffer corruption: retain context/counts/actualcontinue, fail canonical/fullconclusion.
(assert-event (hpizs-test-local 2 :canonical))
; Reachable unfinished-region alternative
(assert-event (hpizs-test-local 2 :cap))
; Labelled receipt removal: retain context/canonical/counts, fail actualcontinue/fullconclusion.
(assert-event (hpizs-test-local 2 :status))
; Actual decoded-source complete positive through all preceding region writes/ACKs.
(assert-event (hpizs-test-local 3 :positive))
; Labelled body-phase mutation: retain full canonical/counts/actualcontinue, fail context/conclusion.
(assert-event (hpizs-test-local 3 :context))
; Labelled buffer corruption: retain context/counts/actualcontinue, fail canonical/fullconclusion.
(assert-event (hpizs-test-local 3 :canonical))
; Reachable unfinished-region alternative
(assert-event (hpizs-test-local 3 :cap))
; Labelled receipt removal: retain context/canonical/counts, fail actualcontinue/fullconclusion.
(assert-event (hpizs-test-local 3 :status))
; Actual decoded-source complete positive through all preceding region writes/ACKs.
(assert-event (hpizs-test-local 4 :positive))
; Labelled body-phase mutation: retain full canonical/counts/actualcontinue, fail context/conclusion.
(assert-event (hpizs-test-local 4 :context))
; Labelled buffer corruption: retain context/counts/actualcontinue, fail canonical/fullconclusion.
(assert-event (hpizs-test-local 4 :canonical))
; Reachable unfinished-region alternative
(assert-event (hpizs-test-local 4 :cap))
; Labelled receipt removal: retain context/canonical/counts, fail actualcontinue/fullconclusion.
(assert-event (hpizs-test-local 4 :status))
; Actual decoded-source complete positive through all preceding region writes/ACKs.
(assert-event (hpizs-test-local 5 :positive))
; Labelled body-phase mutation: retain full canonical/counts/actualcontinue, fail context/conclusion.
(assert-event (hpizs-test-local 5 :context))
; Labelled buffer corruption: retain context/counts/actualcontinue, fail canonical/fullconclusion.
(assert-event (hpizs-test-local 5 :canonical))
; Labelled premature final-region corruption; not a reachable final transition
(assert-event (hpizs-test-local 5 :cap))
; Labelled receipt removal: retain context/canonical/counts, fail actualcontinue/fullconclusion.
(assert-event (hpizs-test-local 5 :status))
