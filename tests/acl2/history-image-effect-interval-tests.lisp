(in-package "ACL2")
(include-book "history-image-funded-host-tests")
; Positive is the actual funded host's first issued page, not a synthetic grant.
; The out-of-extent case deliberately corrupts only the outstanding request.
(defun hie-int-attempt (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
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
            (ledger (fn-owner-page-read-ledger fn-page-read-pool))
            (plan (fn-owner-history-image-effect-plan c effect stage fn-page-read-pool))
            (extent (fn-omk-at 7 (fn-omk-at 22 c)))
            (bad-effect (fn-hpi-set 7 extent effect))
            (bad-c (fn-hpi-set 5 bad-effect c)))
      (mv
       (and (eq installed :installed) (eq admitted :admitted) (eq v :write)
            (equal (fn-omk-at 0 plan) :io)
            (fn-hie-currentp c effect stage ledger)
            (fn-osj-native-slicep extent (fn-omk-at 3 plan) (fn-omk-at 4 plan))
            (natp (fn-omk-at 3 plan)) (natp (fn-omk-at 4 plan))
            (<= (+ (fn-omk-at 3 plan) (fn-omk-at 4 plan)) (fn-osj-native-offset-max))
            ; Corrupted-state mutation keeps current grant/pending identity.
            (fn-hie-currentp bad-c bad-effect stage ledger)
            (not (fn-osj-native-slicep extent extent 16384))
            (equal (fn-owner-history-image-effect-plan bad-c bad-effect stage fn-page-read-pool)
                   '(:refused :image-effect-phase))
            (equal (fn-owner-history-image-effect-result bad-c bad-effect stage 16384 :ok nil fn-page-read-pool)
                   '(:retained :image-effect-observation)))
       fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)))))))

(defun hie-int-local ()
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
      (hie-int-attempt fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
      (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
      (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
      (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)))
      (mv result fn-hpq0 fn-hpq1 fn-hpq2)))
      (mv result fn-hpq0 fn-hpq1)))
      (mv result fn-hpq0)))
      result))
)

(assert-event (hie-int-local))
(assert-event
 (let* ((c nil) (effect nil) (stage 7) (ledger nil)
        (plan (fn-hie-plan c effect stage ledger)))
  (and (not (equal (fn-omk-at 0 plan) :io))
       (not (and (fn-hie-currentp c effect stage ledger)
                 (fn-osj-native-slicep nil (fn-omk-at 3 plan) (fn-omk-at 4 plan))
                 (natp (fn-omk-at 3 plan)) (natp (fn-omk-at 4 plan))
                 (<= (+ (nfix (fn-omk-at 3 plan)) (nfix (fn-omk-at 4 plan)))
                     (fn-osj-native-offset-max)))))))
