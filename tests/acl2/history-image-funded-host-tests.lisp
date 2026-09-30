(in-package "ACL2")
(include-book "../../host/history-image-effect-host")

; Test driver invokes the actual funded host-called writer; it does not
; fabricate a receipt, pending effect, position, or buffer generation.
(defun hpie-test-first-write (fuel c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool) :verify-guards nil :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-owner-history-image-tick)))))
  (if (zp fuel) (mv :fuel nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
    (mv-let (v effect next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
      (fn-owner-history-image-tick c nil fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb
                                  pgs-digest-state fn-page-read-pool)
      (if (member-eq v '(:continue :funded))
          (hpie-test-first-write (1- fuel) next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
        (mv v effect next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)))))

(defun hpie-test-funded-attempt (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool) :verify-guards nil))
  (mv-let (installed fn-page-read-pool)
    (fn-owner-page-read-install '(10000000 10000000 4 1 10) 0 0 0 10000000 fn-page-read-pool)
    (mv-let (admitted maintenance fn-page-read-pool)
      (fn-owner-maintenance-admit 7 1 '(1000000 16384 3 1 1) fn-page-read-pool)
      (let ((c (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance
                              (nth 1 maintenance) 10000000 "node" 17 "trail")))
        (mv-let (v effect c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
          (hpie-test-first-write 2055 c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
          (let* ((stage (nth 1 maintenance))
                 (plan (fn-owner-history-image-effect-plan c effect stage fn-page-read-pool))
                 (good (fn-owner-history-image-effect-result c effect stage 16384 :ok nil fn-page-read-pool))
                 (short (fn-owner-history-image-effect-result c effect stage 16383 :ok nil fn-page-read-pool))
                 (lost (fn-owner-history-image-effect-result c effect (+ 1 stage) 16384 :ok nil fn-page-read-pool))
                 (antecedent
                   (and (eq installed :installed) (eq admitted :admitted) (eq v :write)
                        (fn-hpi-grant-matchesp c (fn-owner-page-read-ledger fn-page-read-pool))
                        (equal (nth 0 c) :wait-write) (equal (nth 5 c) effect)
                        (equal (fn-hpb-used fn-hpb) 2048)
                        (equal plan '(:io :write :target 16384 16384 4 nil))
                        (equal (fn-hpi-written-status effect good) :written)
                        (equal (fn-hpi-written-status effect short) :recovery-required)
                        (equal lost '(:retained :image-effect-observation)))))
            (mv-let (uv ue uc fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
              (fn-owner-history-image-tick c short fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb
                                           pgs-digest-state fn-page-read-pool)
              (mv (and antecedent (eq uv :recovery-required) (null ue)
                       (equal (nth 0 uc) :recovery-required)
                       (equal (nth 5 uc) effect) (equal (nth 16 uc) (nth 16 c))
                       (equal (fn-hpb-used fn-hpb) 2048)
                       (fn-hpi-grant-matchesp uc (fn-owner-page-read-ledger fn-page-read-pool)))
                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool))))))))

(defun hpie-test-local-funded ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hpq0
    (mv-let (result fn-hpq0)
  (with-local-stobj fn-hpq1
    (mv-let (result fn-hpq0 fn-hpq1)
  (with-local-stobj fn-hpq2
    (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2)
  (with-local-stobj fn-hpq3
    (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
  (with-local-stobj fn-hpb
    (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (with-local-stobj pgs-digest-state
    (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
  (with-local-stobj fn-page-read-pool
    (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
      (hpie-test-funded-attempt fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
      (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
      (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
      (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)))
      (mv result fn-hpq0 fn-hpq1 fn-hpq2)))
      (mv result fn-hpq0 fn-hpq1)))
      (mv result fn-hpq0)))
      result))
)
(assert-event (hpie-test-local-funded))
