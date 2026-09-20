; Joint workflow/node binding invariant.
(in-package "ACL2")

(include-book "bp-workflow-invariants")
(local (in-theory (enable fn-node-statep)))

; Plain fn-bp-statep intentionally accepts structurally valid work whose
; article/archive fields were not derived from its node.  This stronger,
; reachable invariant covers both durable work and the currently prepared work.
(defun fn-bp-pending-boundp (node pending)
  (declare (xargs :guard t))
  (or (null pending)
      (and (consp pending)
           (fn-bp-work-boundp node (fn-bp-pending-work pending)))))

(defun fn-bp-binding-statep (s)
  (declare (xargs :guard t))
  (and (fn-bp-statep s)
       (fn-bp-works-boundp (fn-bp-state-node s) (fn-bp-state-works s))
       (fn-bp-pending-boundp (fn-bp-state-node s)
                             (fn-bp-state-pending s))))

(defthm fn-bp-binding-state-implies-statep
  (implies (fn-bp-binding-statep s) (fn-bp-statep s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bp-binding-statep))))

(defthm fn-bp-binding-state-implies-works-boundp
  (implies (fn-bp-binding-statep s)
           (fn-bp-works-boundp (fn-bp-state-node s)
                               (fn-bp-state-works s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bp-binding-statep))))

(defthm fn-bp-binding-state-implies-pending-boundp
  (implies (fn-bp-binding-statep s)
           (fn-bp-pending-boundp (fn-bp-state-node s)
                                 (fn-bp-state-pending s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bp-binding-statep))))

(defthm fn-bp-work-boundp-with-attempt
  (equal (fn-bp-work-boundp node (fn-bp-work-with-attempt work attempt))
         (fn-bp-work-boundp node work))
  :hints (("Goal" :in-theory (enable fn-bp-work-boundp
                                      fn-bp-work-with-attempt))))

(defthm fn-bp-work-boundp-with-receipt
  (equal (fn-bp-work-boundp node (fn-bp-work-with-receipt work receipt))
         (fn-bp-work-boundp node work))
  :hints (("Goal" :in-theory (enable fn-bp-work-boundp
                                      fn-bp-work-with-receipt))))

(defthm fn-bp-work-boundp-with-status
  (equal (fn-bp-work-boundp node (fn-bp-work-with-status work status))
         (fn-bp-work-boundp node work))
  :hints (("Goal" :in-theory (enable fn-bp-work-with-status))))

(defthm fn-bp-find-work-boundp
  (implies (and (fn-bp-works-boundp node works)
                (consp (fn-bp-find-work id works)))
           (fn-bp-work-boundp node (fn-bp-find-work id works)))
  :hints (("Goal" :induct (fn-bp-find-work id works)
           :in-theory (enable fn-bp-find-work fn-bp-works-boundp))))

(defthm fn-bp-replace-work-preserves-boundp
  (implies (and (fn-bp-works-boundp node works)
                (fn-bp-work-boundp node work))
           (fn-bp-works-boundp node (fn-bp-replace-work work works)))
  :hints (("Goal" :induct (fn-bp-replace-work work works)
           :in-theory (enable fn-bp-replace-work fn-bp-works-boundp))))

(defthm fn-bp-restart-work-preserves-boundp
  (implies (fn-bp-work-boundp node work)
           (fn-bp-work-boundp node (fn-bp-restart-work work)))
  :hints (("Goal" :in-theory (enable fn-bp-restart-work))))

(defthm fn-bp-restart-works-preserves-boundp
  (implies (fn-bp-works-boundp node works)
           (fn-bp-works-boundp node (fn-bp-restart-works works)))
  :hints (("Goal" :induct (fn-bp-restart-works works)
           :in-theory (enable fn-bp-restart-works fn-bp-works-boundp))))

(defthm fn-bp-recovery-pending-preserves-boundp
  (implies (fn-bp-pending-boundp node pending)
           (fn-bp-pending-boundp node (fn-bp-recovery-pending pending)))
  :hints (("Goal" :in-theory (enable fn-bp-pending-boundp
                                      fn-bp-recovery-pending))))

(defthm fn-bp-initial-state-is-binding-state
  (implies (and (fn-node-statep node) (fn-bp-configp config))
           (fn-bp-binding-statep (fn-bp-initial-state node config)))
  :hints (("Goal" :in-theory (enable fn-bp-binding-statep
                                      fn-bp-initial-state
                                      fn-bp-works-boundp
                                      fn-bp-pending-boundp))))

(defthm fn-bp-derived-enqueue-work-boundp
  (implies (consp (fn-node-find-binding msgid (fn-node-bindings node)))
           (fn-bp-work-boundp
            node
            (fn-bp-make-work
             work-id msgid
             (fn-node-binding-subject
              (fn-node-find-binding msgid (fn-node-bindings node)))
             (fn-node-binding-id
              (fn-node-find-binding msgid (fn-node-bindings node)))
             obligation-id peer policy incarnation auth-context terms
             0 nil nil)))
  :hints (("Goal" :in-theory (enable fn-bp-work-boundp))))

(defthm fn-bp-prepare-enqueue-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-prepare-enqueue s txid generation work-id msgid
                                   obligation-id policy-id terms-id)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-prepare-enqueue-preserves-state)
          (:instance fn-bp-derived-enqueue-work-boundp
                     (node (fn-bp-state-node s))
                     (peer (fn-bp-config-peer-eid
                            (fn-bp-state-config s)))
                     (policy policy-id)
                     (incarnation (fn-bp-config-incarnation
                                   (fn-bp-state-config s)))
                     (auth-context (fn-bp-config-auth-context
                                    (fn-bp-state-config s)))
                     (terms terms-id)))
    :in-theory
    (e/d (fn-bp-binding-statep fn-bp-prepare-enqueue
                               fn-bp-pending-boundp)
         (fn-bp-statep fn-bp-works-boundp fn-bp-work-boundp
          fn-node-find-binding fn-bp-make-work)))))

(defthm fn-bp-prepare-attempt-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-prepare-attempt s txid generation work-id attempt-id)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-prepare-attempt-preserves-state)
          (:instance fn-bp-find-work-boundp
                     (node (fn-bp-state-node s))
                     (works (fn-bp-state-works s))
                     (id work-id)))
    :in-theory
    (e/d (fn-bp-binding-statep fn-bp-prepare-attempt
                               fn-bp-pending-boundp)
         (fn-bp-statep fn-bp-works-boundp fn-bp-work-boundp
          fn-bp-find-work fn-bp-work-with-attempt)))))

(defthm fn-bp-prepare-receipt-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-prepare-receipt s txid generation receipt authorizedp)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-prepare-receipt-preserves-state)
          (:instance fn-bp-find-work-boundp
                     (node (fn-bp-state-node s))
                     (works (fn-bp-state-works s))
                     (id (fn-bp-receipt-work-id receipt))))
    :in-theory
    (e/d (fn-bp-binding-statep fn-bp-prepare-receipt
                               fn-bp-pending-boundp)
         (fn-bp-statep fn-bp-works-boundp fn-bp-work-boundp
          fn-bp-find-work fn-bp-work-with-receipt)))))

(defthm fn-bp-works-boundp-of-cons
  (implies (and (fn-bp-work-boundp node work)
                (fn-bp-works-boundp node works))
           (fn-bp-works-boundp node (cons work works)))
  :hints (("Goal" :in-theory (enable fn-bp-works-boundp))))

(defthm fn-bp-pendingp-implies-consp
  (implies (fn-bp-pendingp config pending)
           (consp pending))
  :hints (("Goal" :in-theory (enable fn-bp-pendingp))))

(defthm fn-bp-pending-boundp-implies-work-boundp
  (implies (and (fn-bp-pending-boundp node pending)
                (consp pending))
           (fn-bp-work-boundp node (fn-bp-pending-work pending)))
  :hints (("Goal" :in-theory (enable fn-bp-pending-boundp))))

(defthm fn-bp-apply-pending-preserves-binding-state
  (implies (and (fn-bp-binding-statep s)
                (fn-bp-pending-boundp (fn-bp-state-node s) pending)
                (fn-bp-pendingp (fn-bp-state-config s) pending))
           (fn-bp-binding-statep (fn-bp-apply-pending s pending)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-apply-pending-preserves-state)
          (:instance fn-bp-pendingp-implies-consp
                     (config (fn-bp-state-config s)))
          (:instance fn-bp-pending-boundp-implies-work-boundp
                     (node (fn-bp-state-node s)))
          (:instance fn-bp-works-boundp-of-cons
                     (node (fn-bp-state-node s))
                     (work (fn-bp-pending-work pending))
                     (works (fn-bp-state-works s)))
          (:instance fn-bp-replace-work-preserves-boundp
                     (node (fn-bp-state-node s))
                     (work (fn-bp-pending-work pending))
                     (works (fn-bp-state-works s))))
    :in-theory
    (e/d (fn-bp-binding-statep fn-bp-apply-pending
                               fn-bp-pending-boundp)
         (fn-bp-statep fn-bp-works-boundp fn-bp-work-boundp
          fn-bp-pendingp fn-bp-workp fn-bp-receiptp
          fn-bp-apply-pending-preserves-state
          fn-bp-works-boundp-of-cons
          fn-bp-replace-work-preserves-boundp
          fn-bp-replace-work)))))

(defthm fn-bp-state-works-of-make-state
  (equal (fn-bp-state-works
          (fn-bp-make-state node config works receipts pending fenced used))
         works)
  :hints (("Goal" :in-theory (enable fn-bp-state-works
                                      fn-bp-make-state))))

(defthm fn-bp-state-pending-of-make-state
  (equal (fn-bp-state-pending
          (fn-bp-make-state node config works receipts pending fenced used))
         pending)
  :hints (("Goal" :in-theory (enable fn-bp-state-pending
                                      fn-bp-make-state))))

(defthm fn-bp-clear-pending-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-make-state
             (fn-bp-state-node s) (fn-bp-state-config s)
             (fn-bp-state-works s) (fn-bp-state-receipts s)
             nil nil (fn-bp-state-used-txs s))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-clear-pending-preserves-state))
    :in-theory
    (e/d (fn-bp-binding-statep fn-bp-pending-boundp)
         (fn-bp-statep fn-bp-works-boundp fn-bp-make-state)))))

(defthm fn-bp-fence-pending-preserves-binding-state
  (implies (and (fn-bp-binding-statep s)
                (consp (fn-bp-state-pending s)))
           (fn-bp-binding-statep
            (fn-bp-make-state
             (fn-bp-state-node s) (fn-bp-state-config s)
             (fn-bp-state-works s) (fn-bp-state-receipts s)
             (fn-bp-state-pending s) t (fn-bp-state-used-txs s))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-fence-pending-preserves-state))
    :in-theory
    (e/d (fn-bp-binding-statep)
         (fn-bp-statep fn-bp-works-boundp fn-bp-pending-boundp
          fn-bp-make-state)))))

(defthm fn-bp-complete-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-result-state
             (fn-bp-complete s txid generation outcome))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-binding-state-implies-statep)
          (:instance fn-bp-binding-state-implies-pending-boundp)
          (:instance fn-bp-pending-matches-implies-consp)
          (:instance fn-bp-pendingp-when-statep-and-consp)
          (:instance fn-bp-apply-pending-preserves-binding-state
                     (pending (fn-bp-state-pending s)))
          (:instance fn-bp-clear-pending-preserves-binding-state)
          (:instance fn-bp-fence-pending-preserves-binding-state))
    :cases ((fn-bp-pending-matchesp s txid generation)
            (fn-bp-state-fenced s)
            (equal outcome :durable)
            (equal outcome :aborted)
            (equal outcome :indeterminate))
    :in-theory
    (disable fn-bp-binding-statep fn-bp-statep fn-bp-complete
             fn-bp-pending-matchesp fn-bp-apply-pending fn-bp-make-state
             fn-bp-effect-for-pending fn-bp-result-state
             fn-bp-pending-boundp fn-bp-pendingp))))

(defthm fn-bp-recover-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-result-state
             (fn-bp-recover s txid generation result))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-binding-state-implies-statep)
          (:instance fn-bp-binding-state-implies-pending-boundp)
          (:instance fn-bp-pending-matches-implies-consp)
          (:instance fn-bp-pendingp-when-statep-and-consp)
          (:instance fn-bp-recovery-pending-preserves-pendingp
                     (config (fn-bp-state-config s))
                     (pending (fn-bp-state-pending s)))
          (:instance fn-bp-recovery-pending-preserves-boundp
                     (node (fn-bp-state-node s))
                     (pending (fn-bp-state-pending s)))
          (:instance fn-bp-apply-pending-preserves-binding-state
                     (pending
                      (fn-bp-recovery-pending
                       (fn-bp-state-pending s))))
          (:instance fn-bp-clear-pending-preserves-binding-state))
    :cases ((fn-bp-pending-matchesp s txid generation)
            (equal (fn-bp-state-fenced s) t)
            (equal result :committed)
            (equal result :absent))
    :in-theory
    (disable fn-bp-binding-statep fn-bp-statep fn-bp-recover
             fn-bp-pending-matchesp fn-bp-apply-pending fn-bp-make-state
             fn-bp-effect-for-pending fn-bp-recovery-pending
             fn-bp-result-state fn-bp-pending-boundp fn-bp-pendingp))))

(defthm fn-bp-status-update-preserves-binding-state
  (implies (and (fn-bp-binding-statep s)
                (fn-bp-workp (fn-bp-state-config s) work)
                (consp (fn-bp-work-attempt work))
                (fn-bp-transport-statusp status)
                (fn-bp-work-boundp (fn-bp-state-node s) work))
           (fn-bp-binding-statep
            (fn-bp-make-state
             (fn-bp-state-node s) (fn-bp-state-config s)
             (fn-bp-replace-work (fn-bp-work-with-status work status)
                                 (fn-bp-state-works s))
             (fn-bp-state-receipts s) nil nil
             (fn-bp-state-used-txs s))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-status-update-preserves-state)
          (:instance fn-bp-binding-state-implies-works-boundp)
          (:instance fn-bp-replace-work-preserves-boundp
                     (node (fn-bp-state-node s))
                     (work (fn-bp-work-with-status work status))
                     (works (fn-bp-state-works s))))
    :in-theory
    (e/d (fn-bp-binding-statep fn-bp-pending-boundp)
         (fn-bp-statep fn-bp-works-boundp fn-bp-work-boundp
          fn-bp-workp fn-bp-attemptp fn-bp-transport-statusp
          fn-bp-status-update-preserves-state
          fn-bp-replace-work-preserves-boundp
          fn-bp-work-with-status fn-bp-replace-work fn-bp-make-state)))))
