; Actual executor reads every octet of actual canonical padding page issuance.
; Source-visible-byte boundary only; no private FD/INITIAL/native completion.
(in-package "ACL2")
(include-book "../../books/history-image-canonical-payload")
(local (defun hpicb-test-to-point (fuel region used c observation ledger
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
       (hpicb-test-to-point (1- fuel) region used c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
    ((member-eq status '(:funded :continue :write :written :need-byte :row-done))
     (hpicb-test-to-point (1- fuel) region used c
      (cond ((eq status :write) (fn-hie-observation c effect (fn-omk-at 3 c) ledger 16384 :ok nil))
            ((eq status :need-byte) (list :supply (fn-omk-at 1 effect) (nth (fn-omk-at 1 effect) '(0 65 66 67))))
            (t nil)) ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
    (t (mv (list :unexpected status c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))


(local (defun hpicb-test-octets (i expected c effect stage ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil :measure (len expected)))
 (if (atom expected) (equal i 16384)
  (mv-let (word byte) (fn-hie-page-byte c effect stage ledger i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
   (and (fn-hpib-page-byte-contextp c effect stage ledger i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (equal word :octet) (equal byte (car expected))
        (hpicb-test-octets (+ 1 i) (cdr expected) c effect stage ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))
(local (defun hpicb-test-case (region mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
   (mv-let (point fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpicb-test-to-point 18000 region 2048 initial nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let* ((c (nth 1 point)) (ledger (nth 2 point))
           (baseline (and (eq admitted :admitted) (eq (car point) :reached) (fn-hpi-grant-matchesp c ledger)
             (fn-hpiz-writer-ready-p '("ABC") c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
           ; Labelled selected canonical word corruption after full reached baseline.
           (fn-hpq0 (if (and (eq mode :canonical) (equal region 0)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq0)) fn-hpq0) fn-hpq0))
           (fn-hpq1 (if (and (eq mode :canonical) (equal region 1)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq1)) fn-hpq1) fn-hpq1))
           (fn-hpq2 (if (and (eq mode :canonical) (equal region 2)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq2)) fn-hpq2) fn-hpq2))
           (fn-hpq3 (if (and (eq mode :canonical) (equal region 3)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq3)) fn-hpq3) fn-hpq3))
           (fn-hpb (if (and (eq mode :canonical) (equal region 4)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpb)) fn-hpb) fn-hpb))
           (ready (fn-hpiz-writer-ready-p '("ABC") c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
           (expected (pgs-words-le-octets (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at region (fn-omk-at 15 c))))
                          (fn-hp-wpad (nth region (fn-hp-regs '("ABC") (fn-omk-at 12 c)))))))))
     (mv-let (status effect next next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (let* ((stage (if (eq mode :context) (+ 1 (fn-omk-at 3 next)) (fn-omk-at 3 next)))
             (context (fn-hpib-page-byte-contextp next effect stage next-ledger 0 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
             ; All16KiB actual FnHIEPageByte outputs + literal context are checked,
             ; comparing against the independent original padded canonical page.
             (conclusion (hpicb-test-octets 0 expected next effect stage next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
       (mv (and baseline (equal status :write)
                (equal (list (if ready t nil) (if context t nil) (if conclusion t nil))
                 (case mode (:positive '(t t t)) (:canonical '(nil t nil)) (:context '(t nil nil)))))
           fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))))
(local (defun hpicb-test-local (region mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpicb-test-case region mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))
; Actual decoded-source full page; compare all16384 actual executor octets and complete context to original canonical page.
(assert-event (hpicb-test-local 0 :positive))
; Labelled selected word corruption: retain exact executor context, fail original ready and complete first-octet conclusion.
(assert-event (hpicb-test-local 0 :canonical))
; Labelled stale stage incarnation: retain complete original ready, fail executor context and complete first-octet output.
(assert-event (hpicb-test-local 0 :context))
; Actual decoded-source full page; compare all16384 actual executor octets and complete context to original canonical page.
(assert-event (hpicb-test-local 1 :positive))
; Labelled selected word corruption: retain exact executor context, fail original ready and complete first-octet conclusion.
(assert-event (hpicb-test-local 1 :canonical))
; Labelled stale stage incarnation: retain complete original ready, fail executor context and complete first-octet output.
(assert-event (hpicb-test-local 1 :context))
; Actual decoded-source full page; compare all16384 actual executor octets and complete context to original canonical page.
(assert-event (hpicb-test-local 2 :positive))
; Labelled selected word corruption: retain exact executor context, fail original ready and complete first-octet conclusion.
(assert-event (hpicb-test-local 2 :canonical))
; Labelled stale stage incarnation: retain complete original ready, fail executor context and complete first-octet output.
(assert-event (hpicb-test-local 2 :context))
; Actual decoded-source full page; compare all16384 actual executor octets and complete context to original canonical page.
(assert-event (hpicb-test-local 3 :positive))
; Labelled selected word corruption: retain exact executor context, fail original ready and complete first-octet conclusion.
(assert-event (hpicb-test-local 3 :canonical))
; Labelled stale stage incarnation: retain complete original ready, fail executor context and complete first-octet output.
(assert-event (hpicb-test-local 3 :context))
; Actual decoded-source full page; compare all16384 actual executor octets and complete context to original canonical page.
(assert-event (hpicb-test-local 4 :positive))
; Labelled selected word corruption: retain exact executor context, fail original ready and complete first-octet conclusion.
(assert-event (hpicb-test-local 4 :canonical))
; Labelled stale stage incarnation: retain complete original ready, fail executor context and complete first-octet output.
(assert-event (hpicb-test-local 4 :context))
