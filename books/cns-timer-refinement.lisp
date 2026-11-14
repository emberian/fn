; Complete timer output/effect relation for the actual CNS draining call.
; The independent oracle is owned by cns-draining-contract, not this bridge.
(in-package "ACL2")
(include-book "cns-draining-contract")

(defthm fn2-cns-clear-deadline-independent
  (implies (and (fn2-schedp sched) (fn2-sched-wfp sched)
                (natp id) (< id (fn2-sched-rows sched)))
    (equal (fn2-sched-clear-deadline id sched)
           (list :ok (fn2-cns-drain-cleared-sched id sched))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn2-sched-clear-deadline
                 fn2-sched-deadline fn2-sched-expired
                 fn2-sched-set-deadline fn2-sched-set-expired
                 update-fn2-sched-deadline$ai update-fn2-sched-expired$ai
                 fn2-sched-armed-timers fn2-sched-earliest-deadline
                 update-fn2-sched-armed-timers update-fn2-sched-earliest-deadline
                 fn2-cns-drain-cleared-sched fn2-cns-drain-cell
                 fn2-cns-drain-get fn2-cns-drain-index
                 fn2-cns-drain-put fn2-cns-drain-put-cell)
                (fn2-schedp fn2-sched-wfp)))))

; Exactly the actual generated core face, including its complete core frame.
; No new runtime wrapper, attachment substitution or selected-body assumption.
(defthm fn2-cns-clear-wait-timer-independent
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp id) (< id (fn2-sched-rows (fn2-core-sched core))))
    (equal (fn2-cns-clear-wait-timer id core)
           (list :ok
             (fn2-cns-drain-put-child 'fn2-sched
               (fn2-cns-drain-cleared-sched id (fn2-core-sched core)) core))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-cns-clear-deadline-independent
                            (sched (fn2-core-sched core))))
           :in-theory
           (e/d (fn2-cns-clear-wait-timer fn2-cns-drain-put-child
                 fn2-cns-drain-child-index update-fn2-core-sched)
                (fn2-sched-clear-deadline fn2-cns-drain-cleared-sched
                 fn2-core-sched fn2-corep fn2-core-wfp)))))
