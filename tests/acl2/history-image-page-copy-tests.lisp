; Full actual native accessor-loop observation and private visible-role join.
; Named physical assumptions are instantiated by their local witness models.
; These assertions are not evidence of physical truth, native activation or INITIAL.
(in-package "ACL2")
(include-book "../../books/history-image-page-copy")
(local (defun hpicopy-test-to-point (fuel region used c observation ledger
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
       (hpicopy-test-to-point (1- fuel) region used c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
    ((member-eq status '(:funded :continue :write :written :need-byte :row-done))
     (hpicopy-test-to-point (1- fuel) region used c
      (cond ((eq status :write) (fn-hie-observation c effect (fn-omk-at 3 c) ledger 16384 :ok nil))
            ((eq status :need-byte) (list :supply (fn-omk-at 1 effect) (nth (fn-omk-at 1 effect) '(0 65 66 67))))
            (t nil)) ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
    (t (mv (list :unexpected status c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))


(local (defun hpicopy-model-write (before after file offset octets got outcome)
 (declare (xargs :guard t :verify-guards nil))
 (or (not (eq outcome :ok))
     (and (natp offset) (equal got (len octets))
          (equal (fn-bs-content after file)
                 (fn-bs-splice (fn-bs-content before file) offset octets))))))
(local (defun hpicopy-model-other-role (before after file other outcome)
 (declare (xargs :guard t :verify-guards nil))
 (or (not (eq outcome :ok)) (equal file other)
     (equal (fn-bs-content after other) (fn-bs-content before other)))))
(local (defun hpicopy-model-step-p (before step files)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((after (nth 0 step)) (role (nth 1 step)) (offset (nth 2 step))
        (payload (nth 3 step)) (got (nth 4 step)) (file (nth role files)))
  (and (true-listp files) (equal (len files) 3) (no-duplicatesp-equal files)
       (natp role) (< role 3)
       (hpicopy-model-write before after file offset payload got :ok)
       (hpicopy-model-other-role before after file (nth 0 files) :ok)
       (hpicopy-model-other-role before after file (nth 1 files) :ok)
       (hpicopy-model-other-role before after file (nth 2 files) :ok)))))
(local (defun hpicopy-model-three-files (stage data table)
 (declare (xargs :guard t :verify-guards nil))
 (fn-bs-make 1 (list (cons 1 stage) (cons 2 data) (cons 3 table)) nil nil 4)))
(local (defthm hpicopy-model-actual-issued-write-has-canonical-roles
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
    (hpicopy-model-step-p before (list after 0 (fn-omk-at 3 (fn-hie-plan (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r))) (mv-nth 1 (fn-hpicopy-page 0 (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))) got) files))
   (equal (fn-hpit-role-view after files)
    (fn-hpit-model-role-write (fn-hpit-role-view before files) (list after 0 (fn-omk-at 3 (fn-hie-plan (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r))) (pgs-words-le-octets (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at (fn-omk-at 18 c) (fn-omk-at 15 c)))) (fn-hp-wpad (nth (fn-omk-at 18 c) (fn-hp-regs h (fn-omk-at 12 c))))))) got)))))
 :rule-classes nil
 :hints (("Goal" :use ((:functional-instance fn-hpicopy-issued-padding-write-has-canonical-visible-roles
 (fn-assume-hpi-positional-write hpicopy-model-write)
 (fn-assume-hpi-positional-other-role hpicopy-model-other-role)
 (fn-hpit-private-write-step-p hpicopy-model-step-p)))))))
(local (defun hpicopy-test-case (region mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
   (mv-let (point fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpicopy-test-to-point 18000 region 2048 initial nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let* ((c (nth 1 point)) (ledger (nth 2 point))
           (baseline (and (eq admitted :admitted) (eq (car point) :reached) (fn-hpi-grant-matchesp c ledger)
             (fn-hpiz-writer-ready-p '("ABC") c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
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
             (plan (fn-hie-plan next effect stage next-ledger)) (offset (fn-omk-at 3 plan)))
       (mv-let (copied payload) (fn-hpicopy-page 0 next effect stage next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (let* ((files '(1 2 3)) (before (hpicopy-model-three-files '(100 101 102) '(9 8) '(7 6)))
               (after (if (eq mode :private-write) before
                 (hpicopy-model-three-files (fn-bs-splice '(100 101 102) offset payload)
                   (if (eq mode :private-frame) '(88) '(9 8)) '(7 6))))
               (got (len payload)) (step (list after 0 offset payload got))
               (private (hpicopy-model-step-p before step files))
               (payload-result (equal (list copied payload) (list :complete expected)))
               (role-result (equal (fn-hpit-role-view after files)
                 (fn-hpit-model-role-write (fn-hpit-role-view before files) (list after 0 offset expected got))))
               (payload-triple (list (if ready t nil) (if context t nil) (if payload-result t nil)))
               (role-triple (list (if ready t nil) (if private t nil) (if role-result t nil))))
         (mv (and baseline (eq status :write)
               (equal payload-triple (case mode (:canonical '(nil t nil)) (:context '(t nil nil)) (otherwise '(t t t))))
               (equal role-triple (case mode (:canonical '(nil t nil)) (:positive '(t t t)) (otherwise '(t nil nil))))
               (if (eq mode :private-frame)
                 (and (hpicopy-model-write before after 1 offset payload got :ok)
                  (hpicopy-model-other-role before after 1 1 :ok)
                  (not (hpicopy-model-other-role before after 1 2 :ok))
                  (hpicopy-model-other-role before after 1 3 :ok)) t))
             fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))))))
(local (defun hpicopy-test-local (region mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpicopy-test-case region mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))
; Full actual decoded-source page-copy output and canonical three-role visible result.
(assert-event (hpicopy-test-local 0 :positive))
; Labelled canonical-buffer mutation retains executor context and complete private write/frame relation; both full conclusions fail.
(assert-event (hpicopy-test-local 0 :canonical))
; Stale stage removes payload context and fails complete payload; it also removes the private observation premise, not a separate private theorem hypothesis.
(assert-event (hpicopy-test-local 0 :context))
; Lying full-count private write retains actual canonical page/context/payload but removes named observation and fails whole role conclusion.
(assert-event (hpicopy-test-local 0 :private-write))
; Cross-file mutation retains actual canonical page/context/payload and exact target write plus other role frames, but removes one required spool frame and fails whole role conclusion.
(assert-event (hpicopy-test-local 0 :private-frame))
; Full actual decoded-source page-copy output and canonical three-role visible result.
(assert-event (hpicopy-test-local 1 :positive))
; Labelled canonical-buffer mutation retains executor context and complete private write/frame relation; both full conclusions fail.
(assert-event (hpicopy-test-local 1 :canonical))
; Stale stage removes payload context and fails complete payload; it also removes the private observation premise, not a separate private theorem hypothesis.
(assert-event (hpicopy-test-local 1 :context))
; Lying full-count private write retains actual canonical page/context/payload but removes named observation and fails whole role conclusion.
(assert-event (hpicopy-test-local 1 :private-write))
; Cross-file mutation retains actual canonical page/context/payload and exact target write plus other role frames, but removes one required spool frame and fails whole role conclusion.
(assert-event (hpicopy-test-local 1 :private-frame))
; Full actual decoded-source page-copy output and canonical three-role visible result.
(assert-event (hpicopy-test-local 2 :positive))
; Labelled canonical-buffer mutation retains executor context and complete private write/frame relation; both full conclusions fail.
(assert-event (hpicopy-test-local 2 :canonical))
; Stale stage removes payload context and fails complete payload; it also removes the private observation premise, not a separate private theorem hypothesis.
(assert-event (hpicopy-test-local 2 :context))
; Lying full-count private write retains actual canonical page/context/payload but removes named observation and fails whole role conclusion.
(assert-event (hpicopy-test-local 2 :private-write))
; Cross-file mutation retains actual canonical page/context/payload and exact target write plus other role frames, but removes one required spool frame and fails whole role conclusion.
(assert-event (hpicopy-test-local 2 :private-frame))
; Full actual decoded-source page-copy output and canonical three-role visible result.
(assert-event (hpicopy-test-local 3 :positive))
; Labelled canonical-buffer mutation retains executor context and complete private write/frame relation; both full conclusions fail.
(assert-event (hpicopy-test-local 3 :canonical))
; Stale stage removes payload context and fails complete payload; it also removes the private observation premise, not a separate private theorem hypothesis.
(assert-event (hpicopy-test-local 3 :context))
; Lying full-count private write retains actual canonical page/context/payload but removes named observation and fails whole role conclusion.
(assert-event (hpicopy-test-local 3 :private-write))
; Cross-file mutation retains actual canonical page/context/payload and exact target write plus other role frames, but removes one required spool frame and fails whole role conclusion.
(assert-event (hpicopy-test-local 3 :private-frame))
; Full actual decoded-source page-copy output and canonical three-role visible result.
(assert-event (hpicopy-test-local 4 :positive))
; Labelled canonical-buffer mutation retains executor context and complete private write/frame relation; both full conclusions fail.
(assert-event (hpicopy-test-local 4 :canonical))
; Stale stage removes payload context and fails complete payload; it also removes the private observation premise, not a separate private theorem hypothesis.
(assert-event (hpicopy-test-local 4 :context))
; Lying full-count private write retains actual canonical page/context/payload but removes named observation and fails whole role conclusion.
(assert-event (hpicopy-test-local 4 :private-write))
; Cross-file mutation retains actual canonical page/context/payload and exact target write plus other role frames, but removes one required spool frame and fails whole role conclusion.
(assert-event (hpicopy-test-local 4 :private-frame))
