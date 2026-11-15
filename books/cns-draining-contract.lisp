; Independent, proof-only application semantics for the served CNS cleanup.
; The checking side is list arithmetic: no handler, release, reclaim or timer
; operation is called. Schema metadata supplies positions, never decisions.
(in-package "ACL2")
(include-book "assembly-callbacks-e-cns")
(include-book "cns-draining-model")

; Logical evidence can name the complete actual five-value result. This
; view does not replace or weaken the application predicate below.
(defun-nx fn2-cns-draining-observed (id budget core)
  (mv-let (b s d r after) (fn2-cns-run id budget core)
    (list b s d r after)))
(defthm fn2-cns-draining-resultp-unfolds
  (equal
   (mv-let (b s d r after) (fn2-cns-run id budget core)
     (fn2-cns-draining-resultp id core b s d r after))
   (equal (fn2-cns-draining-observed id budget core)
          (fn2-cns-draining-expected id core)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories '(fn2-cns-draining-resultp fn2-cns-draining-observed)
                           (theory 'minimal-theory)))))

; Cleanup is sequential. A failure of NS preserves the already completed
; WS release. No row reclamation or timer clear precedes either refusal.
(defun fn2-cns-draining-refusal-resultp (id before stage bytes steps descriptors runnable after)
  (let* ((dir (fn2-cns-drain-child 'fn2-machines before))
         (slot (fn2-cns-drain-cell 'fn2-machines-slot id dir))
         (own (fn2-cns-drain-child 'fn2-cns before))
         (pool (fn2-cns-drain-child 'fn2-pool before))
         (pool (if (eq stage :name)
                   (fn2-cns-drain-released-pool (fn2-cns-drain-cell 'fn2-cns-ws-slot slot own) pool)
                 pool))
         (ctl (fn2-cns-drain-child 'fn2-control before))
         (ctl (fn2-cns-drain-put 'fn2-control-stop 1
                (fn2-cns-drain-put 'fn2-control-stop-reason *fn2-stop-reason-pool-release* ctl)))
         (expected (fn2-cns-drain-put-child 'fn2-control ctl
                     (fn2-cns-drain-put-child 'fn2-pool pool before))))
    (and (member-eq stage '(:workspace :name))
         (equal (list bytes steps descriptors runnable after)
                (list 0 *fn2-work-state* 0 nil expected)))))

; Complete scheduler output/effect refinement, including all sibling rows.
(defthm fn2-cns-drain-clear-scheduler-by-definition
  (implies (and (natp id) (< id (fn2-sched-rows sched)))
    (equal (fn2-sched-clear-deadline id sched)
           (list :ok (fn2-cns-drain-cleared-sched id sched))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn2-sched-clear-deadline fn2-sched-rows
      fn2-sched-deadline fn2-sched-set-deadline fn2-sched-set-expired
      update-fn2-sched-deadline$ai update-fn2-sched-expired$ai
      fn2-sched-armed-timers fn2-sched-earliest-deadline
      update-fn2-sched-armed-timers update-fn2-sched-earliest-deadline
      fn2-cns-drain-cleared-sched fn2-cns-drain-put-cell
      fn2-cns-drain-put fn2-cns-drain-cell fn2-cns-drain-get
      fn2-cns-drain-index))))

; This is the actual core operation called by final draining and answer.
; Equality frames every other child and all protected scheduler siblings.
(defthm fn2-cns-clear-wait-timer-independent
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp id) (< id (fn2-sched-rows (fn2-core-sched core))))
    (equal (fn2-cns-clear-wait-timer id core)
           (list :ok
             (fn2-cns-drain-put-child 'fn2-sched
               (fn2-cns-drain-cleared-sched id (fn2-core-sched core)) core))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-cns-drain-clear-scheduler-by-definition
                            (sched (fn2-core-sched core))))
           :in-theory
           (e/d (fn2-cns-clear-wait-timer fn2-core-sched update-fn2-core-sched
                 fn2-cns-drain-put-child fn2-cns-drain-child-index)
                (fn2-sched-clear-deadline fn2-cns-drain-cleared-sched)))))
; Even a failed held-lease release cannot alter any timer/queue. The lease
; premise is necessary: the final draining step clears its own timer.
(defthm fn2-cns-draining-held-keeps-timer
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (equal (fn2-cns-snapshot-read-code id core) :ok)
                (equal (fn2-cns-row-lease id core) *fn2-cns-lease-held*))
    (equal (fn2-core-sched (mv-nth 4 (fn2-cns-run-draining id budget core)))
           (fn2-core-sched core)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (e/d (fn2-cns-run-draining fn2-cns-lease-release
                 fn2-cns-write+lslot+lgen+lease fn2-core-stop
                 fn2-machine-refuse-write fn2-core-sched
                 update-fn2-core-pool update-fn2-core-control update-fn2-cns-table)
                (fn2-cns-snapshot-read-code fn2-core-release-children
                 fn2-control-record-stop)))))
(defthm fn2-cns-run-draining-held-keeps-timer
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (equal (fn2-cns-snapshot-read-code id core) :ok)
                (equal (fn2-cns-row-phase id core) *fn2-cns-state-draining*)
                (equal (fn2-cns-row-lease id core) *fn2-cns-lease-held*))
    (equal (fn2-core-sched (mv-nth 4 (fn2-cns-run id budget core)))
           (fn2-core-sched core)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-cns-draining-held-keeps-timer))
           :in-theory
           (e/d (fn2-cns-run fn2-machine-contract-check fn2-core-stop
                 fn2-core-sched update-fn2-core-control)
                (fn2-cns-run-draining fn2-cns-snapshot-read-code
                 fn2-cns-row-phase fn2-cns-row-lease fn2-cns-arm-ok-p
                 fn2-control-record-stop)))))
(defthm-owed fn2-cns-draining-held-scheduler-contract (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (equal (fn2-cns-snapshot-read-code id core) :ok)
                (equal (fn2-cns-row-phase id core) *fn2-cns-state-draining*)
                (equal (fn2-cns-row-lease id core) *fn2-cns-lease-held*))
    (equal (fn2-core-sched (mv-nth 4 (fn2-cns-run id budget core)))
           (fn2-core-sched core)))
  :schema :invariant :claim :semantic
  :boundary :unreachable-in-composition
  :teeth (fn2-cns-drain-held-witness fn2-cns-drain-without-held-counterexample)
  :doc "unreachable-in-composition (source-audited, reachability proof pending): hand/cancel release held leases before entering draining. This defensive actual-run theorem preserves all scheduler state on a held-lease input; it is not public served-path coverage. Removing the premise admits the timer-clearing final step.")
(fn2-owed-discharge fn2-cns-draining-held-scheduler-contract
                    fn2-cns-run-draining-held-keeps-timer)

; Refuted draft retained verbatim as a proposition, not an active obligation.
; Two owned slots plus count<rows does not imply two releases have room:
; tests/cns-draining-count-counterexample.lisp executes the complete H/not-C.
(defun-nx fn2-cns-draining-uncounted-claim (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp budget) (fn2-cns-draining-domainp id core))
    (mv-let (b s d r after) (fn2-cns-run id budget core)
      (fn2-cns-draining-resultp id core b s d r after))))

; Callers must carry accounting and reservations, not rescan the whole state
; while serving. Their entry/preservation links remain separate obligations.
; These full-H/C runtime controls are not yet formula-bound by the current
; witness generator; the universal claim remains explicitly owed.
(defthm-owed fn2-cns-draining-counted-independent (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp budget) (fn2-cns-draining-domainp id core)
                (fn2-cns-draining-reservedp core)
                (fn2-pool-semanticp (fn2-core-pool core)))
    (mv-let (b s d r after) (fn2-cns-run id budget core)
      (fn2-cns-draining-resultp id core b s d r after)))
  :schema :invariant :claim :semantic
  :teeth (fn2-cns-drain-positive fn2-cns-drain-without-pool-accounting
          fn2-cns-drain-without-reservation
          fn2-cns-drain-refusal-control fn2-cns-drain-negative)
  :case (:run fn2-cns :draining) :boundary :application-reclamation
  :doc "Given pool accounting and partition reservations, actual CNS draining releases exactly its owned resources, preserves siblings, clears its incarnation timer and returns reusable credit. Held/draining is defensive unreachable-in-composition input coverage; successful final reclaim is the served case. Universal proof and caller invariant links remain owed.")
