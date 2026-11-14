; Issuance history through the concrete core's completion and wake boundaries.
; Loaded as events after fn2-core-events: no second core implementation.
(in-package "ACL2")
(include-book "ops-issued-harvest")

(defmacro fn2-core-issued-events ()
 '(progn
(make-event
 (value `(defthm fn2-harvest-one-issued-total
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
   ,(fn2-run-issued-claim 0 '(fn2-core-ops fn2-core)
                          '(fn2-core-ops (mv-nth 10 (fn2-harvest-one fn2-core)))))
  :hints (("Goal" :in-theory (e/d (fn2-harvest-one fn2-core-stop)
   (fn2-core-ops fn2-corep fn2-core-wfp fn2-ops-issued-count
    fn2-op-issued-weight fn2-ops-rows fn2-opsp fn2-ops-wfp
    fn2-harvest-next fn2-op-finish fn2-op-cell fn2-op-range fn2-op-phase
    fn2-pool-complete-in fn2-pool-release-out)))))))

(make-event
 (value `(defthm fn2-issue-arm-wake-issued-total
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
   ,(fn2-run-issued-claim
      '(if (eq (car (fn2-issue-arm-wake deadline observation-gen fn2-core)) :ok) 1 0)
      '(fn2-core-ops fn2-core)
      '(fn2-core-ops (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen fn2-core)))))
  :hints (("Goal" :in-theory (e/d (fn2-issue-arm-wake fn2-core-stop)
   (fn2-core-ops fn2-corep fn2-core-wfp fn2-ops-issued-count
    fn2-op-issued-weight fn2-ops-rows fn2-opsp fn2-ops-wfp
    fn2-core-outbox-ready fn2-op-reserve fn2-op-set-wake fn2-op-enqueue)))))))
))
