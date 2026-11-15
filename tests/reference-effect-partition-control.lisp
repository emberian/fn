; Defensive logical-input control for the ORIGINAL paired-domain premise.
; The shared-tail state is deliberately not asserted reachable from init.
; Execution must first establish every typed/WFP/R antecedent; source
; inspection alone is not a counterexample or a theorem discharge.
(in-package "ACL2")
(include-book "../books/reference-effect-semantics")
(include-book "cns-query-support")

(defun fn2-ref-partition-control-run (fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (b* (((mv setup a b fn2-core) (fn2-cns-drain-setup nil fn2-core))
       ; The second real admitted owner belongs to principal 1. This is
       ; a typed defensive row update, not a served admission witness.
       (fn2-core (fn2-cns-put-core b (principal-slot 1)))
       (fn2-core
        (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (fn2-sched)
          (let* ((fn2-sched (fn2-sched-set-principal a 0 fn2-sched))
                 (fn2-sched (fn2-sched-set-in-queue a 1 fn2-sched))
                 (fn2-sched (fn2-sched-set-prev a *fn2-none* fn2-sched))
                 (fn2-sched (fn2-sched-set-next a *fn2-none* fn2-sched))
                 (fn2-sched (update-fn2-sched-headsi 0 a fn2-sched))
                 (fn2-sched (update-fn2-sched-tailsi 0 a fn2-sched))
                 (fn2-sched (update-fn2-sched-countsi 0 1 fn2-sched))
                 (fn2-sched (update-fn2-sched-headsi 1 a fn2-sched))
                 (fn2-sched (update-fn2-sched-tailsi 1 a fn2-sched))
                 (fn2-sched (update-fn2-sched-countsi 1 1 fn2-sched)))
            (update-fn2-sched-queued 2 fn2-sched)) fn2-core))
       (lists (list (fn2-ref-calendar (fn2-profile-weights *fn2-cns-drain-profile*)) 0
                    (list (list 0 a) (list 1 a)) '(0 0 0 0) nil))
       (fn2-ref-core (fn2-ref-reset *fn2-cns-drain-profile* fn2-core fn2-ref-core))
       (whole-h (and setup (not (equal a b))
                     (fn2-corep fn2-core) (fn2-ref-corep fn2-ref-core)
                     (fn2-core-wfp fn2-core) (fn2-core-wfp fn2-ref-core)
                     (fn2-representation-relation fn2-core fn2-ref-core lists)))
       (fn2-core (fn2-core-scheduler-wake b fn2-core))
       ((mv fn2-ref-core after-lists) (fn2-ref-effect-scheduler-wake b fn2-ref-core lists)))
    (mv (and whole-h (not (fn2-core-stopped-p fn2-core))
             (not (fn2-core-stopped-p fn2-ref-core))
             (equal (fn2-ref-queue 0 (nth 2 after-lists)) (list a))
             (equal (fn2-ref-queue 1 (nth 2 after-lists)) (list a b))
             (not (fn2-representation-relation fn2-core fn2-ref-core after-lists)))
        fn2-core fn2-ref-core)))
(defun fn2-ref-partition-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (yes fn2-core)
      (with-local-stobj fn2-ref-core
        (mv-let (yes fn2-core fn2-ref-core)
          (fn2-ref-partition-control-run fn2-core fn2-ref-core)
          (mv yes fn2-core))) yes)))
(assert-event (fn2-ref-partition-control))
