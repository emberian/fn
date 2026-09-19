; Finite-event closure for the workflow/node binding invariant.
(in-package "ACL2")

(include-book "bp-workflow-binding-core")

(defthm fn-bp-observe-transport-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-observe-transport s work-id attempt-id generation status)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-binding-state-implies-statep)
          (:instance fn-bp-binding-state-implies-works-boundp)
          (:instance fn-bp-statep-components)
          (:instance fn-bp-find-work-when-work-listp
                     (config (fn-bp-state-config s))
                     (works (fn-bp-state-works s))
                     (id work-id))
          (:instance fn-bp-find-work-boundp
                     (node (fn-bp-state-node s))
                     (works (fn-bp-state-works s))
                     (id work-id))
          (:instance fn-bp-status-update-preserves-binding-state
                     (work (fn-bp-find-work
                            work-id (fn-bp-state-works s)))))
    :in-theory
    (e/d (fn-bp-observe-transport fn-bp-transport-transition-okp)
         (fn-bp-binding-statep fn-bp-statep fn-bp-works-boundp
          fn-bp-work-boundp fn-bp-workp fn-bp-attemptp
          fn-bp-transport-statusp fn-bp-find-work
          fn-bp-work-with-status fn-bp-replace-work fn-bp-make-state
          fn-bp-live-statusp fn-bp-status-rank)))))

(defthm fn-bp-request-retry-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-request-retry s work-id attempt-id generation policy-id)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-binding-state-implies-statep)
          (:instance fn-bp-binding-state-implies-works-boundp)
          (:instance fn-bp-statep-components)
          (:instance fn-bp-find-work-when-work-listp
                     (config (fn-bp-state-config s))
                     (works (fn-bp-state-works s))
                     (id work-id))
          (:instance fn-bp-find-work-boundp
                     (node (fn-bp-state-node s))
                     (works (fn-bp-state-works s))
                     (id work-id))
          (:instance fn-bp-status-update-preserves-binding-state
                     (work (fn-bp-find-work
                            work-id (fn-bp-state-works s)))
                     (status :unknown)))
    :in-theory
    (e/d (fn-bp-request-retry fn-bp-work-outstandingp)
         (fn-bp-binding-statep fn-bp-statep fn-bp-works-boundp
          fn-bp-work-boundp fn-bp-workp fn-bp-attemptp
          fn-bp-transport-statusp fn-bp-find-work
          fn-bp-work-with-status fn-bp-replace-work fn-bp-make-state)))))

(defthm fn-bp-restart-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep (fn-bp-restart s)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-restart-preserves-state)
          (:instance fn-bp-restart-works-preserves-boundp
                     (node (fn-bp-state-node s))
                     (works (fn-bp-state-works s))))
    :in-theory
    (e/d (fn-bp-binding-statep fn-bp-restart)
         (fn-bp-statep fn-bp-works-boundp fn-bp-pending-boundp
          fn-bp-restart-works fn-bp-make-state)))))

(defthm fn-bp-step-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-result-state (fn-bp-step s event))))
  :hints
  (("Goal"
    :in-theory
    (e/d (fn-bp-step)
         (fn-bp-binding-statep fn-bp-result-state fn-bp-make-result
          fn-bp-prepare-enqueue fn-bp-prepare-attempt
          fn-bp-prepare-receipt fn-bp-complete fn-bp-recover
          fn-bp-observe-transport fn-bp-request-retry fn-bp-restart
          fn-bp-complete-result-state-formula
          fn-bp-recover-result-state-formula)))))

(defthm fn-bp-trace-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep (fn-bp-trace s events)))
  :hints
  (("Goal" :induct (fn-bp-trace s events)
    :in-theory (e/d (fn-bp-trace)
                     (fn-bp-binding-statep fn-bp-step
                      fn-bp-result-state)))))
