; Prepared actual actor/operation admission inverse. No physical READY or
; cache row is seeded. Empty OPEN writes and writer HELD tuple are explicit
; semantic premises; actual take/resolve creates the private operation receipt.
(in-package "ACL2")
(include-book "../books/assembly-callbacks-e-auth")
(defconst *fn2-tal-profile*
 (put-assoc-equal :authority 2 (put-assoc-equal :t 8
  (put-assoc-equal :pool-classes '((32 . 4096) (8 . 65536)) *fn2-profile-tiny*))))
(defun fn2-tal-capacity-view (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-run-loads (fn2-core-run-loads fn2-core)) (fn2-pool (fn2-core-pool fn2-core))) (view)
  (list (fn2-run-loads-admissions fn2-run-loads)
        (fn2-pool-class-countsi 0 fn2-pool) (fn2-pool-class-countsi 1 fn2-pool)) view))
(defun fn2-txn-auth-loader-admission-unit-body (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-tal-profile* fn2-core))
      ((mv born0 id0 gen0 fn2-core) (fn2-machine-take-fn2-auth *fn2-none* *fn2-none* 0 7 0 0 *fn2-none* 0 1 0 1 fn2-core))
      ((mv born1 id1 gen1 fn2-core) (fn2-machine-take-fn2-auth *fn2-none* *fn2-none* 0 7 0 0 *fn2-none* 0 1 0 1 fn2-core))
      ((mv plan0 & tx0 & & & & &) (fn2-c-actor-loader-plan id0 gen0 fn2-core))
      ((mv plan1 & tx1 & & & & &) (fn2-c-actor-loader-plan id1 gen1 fn2-core))
      (fn2-core (stobj-let ((fn2-succ-txns (fn2-core-succ-txns fn2-core))) (fn2-succ-txns)
       (fn2-succ-txns-put tx0 (phase *fn2-succ-phase-open*) (ri 0)) fn2-core))
      ((mv resolved fn2-core) (fn2-successor-resolve tx0 4096 fn2-core))
      ((mv pending fn2-core) (stobj-let ((fn2-c-source-control (fn2-core-c-source-control fn2-core))) (code fn2-c-source-control)
       (fn2-c-source-writer-begin 2 3 4 5 6 7 fn2-c-source-control) (mv code fn2-core)))
      (H (and (eq born0 :ok) (eq born1 :ok) (eq plan0 :ok) (eq plan1 :ok) (not (equal tx0 tx1))
              (eq resolved :more) (eq pending :waiting) (fn2-core-wfp fn2-core)))
      (before (fn2-tal-capacity-view fn2-core))
      ; Another actor cannot spend the positive global reader count.
      ((mv blocked complete fn2-core) (fn2-c-actor-loader-reserve id1 gen1 fn2-core))
      (blocked-kept (equal before (fn2-tal-capacity-view fn2-core)))
      ; The exact old operation may finish. Count0 physical sources means its
      ; admitted turn needs no loader loan and must not latch a capability.
      ((mv existing existing-complete fn2-core) (fn2-c-actor-loader-reserve id0 gen0 fn2-core))
      (existing-kept (equal before (fn2-tal-capacity-view fn2-core)))
      ((mv released fn2-core) (fn2-successor-release tx0 fn2-core))
      ((mv exclusive fn2-core) (stobj-let ((fn2-c-source-control (fn2-core-c-source-control fn2-core))) (code fn2-c-source-control)
       (fn2-c-source-writer-poll 2 3 4 5 6 7 fn2-c-source-control) (mv code fn2-core)))
      ((mv after-close after-complete fn2-core) (fn2-c-actor-loader-reserve id0 gen0 fn2-core)))
  (mv (and H (eq blocked :blocked) (equal complete 0) blocked-kept
       (eq existing :resident) (equal existing-complete 0) existing-kept
       (eq released :ok) (eq exclusive :exclusive) (eq after-close :blocked) (equal after-complete 0)
       (equal before (fn2-tal-capacity-view fn2-core)) (fn2-core-wfp fn2-core)) fn2-core)))
(assert-event (with-local-stobj fn2-core
 (mv-let (good fn2-core) (fn2-txn-auth-loader-admission-unit-body fn2-core) good)))
