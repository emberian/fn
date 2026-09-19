(in-package "ACL2")

(include-book "bp-workflow")
; withdrawn at node's export (core, 2026-09-19); this book opens them.
(local (in-theory (enable fn-node-statep fn-node-bindingp)))

; -----------------------------------------------------------------------------
; Typed list and constructor facts

(defthm fn-bp-find-binding-when-binding-listp
  (implies (and (fn-node-binding-listp bindings)
                (consp (fn-node-find-binding msgid bindings)))
           (fn-node-bindingp (fn-node-find-binding msgid bindings)))
  :hints (("Goal" :induct (fn-node-binding-listp bindings)
           :in-theory (e/d (fn-node-find-binding fn-node-binding-listp)
                            (fn-node-bindingp)))))

(defthm fn-bp-node-state-has-binding-listp
  (implies (fn-node-statep node)
           (fn-node-binding-listp (fn-node-bindings node)))
  :hints (("Goal" :in-theory (enable fn-node-statep))))

(defthm fn-bp-find-work-when-work-listp
  (implies (and (fn-bp-work-listp config works)
                (consp (fn-bp-find-work id works)))
           (fn-bp-workp config (fn-bp-find-work id works)))
  :hints (("Goal" :induct (fn-bp-work-listp config works)
           :in-theory (e/d (fn-bp-find-work fn-bp-work-listp)
                            (fn-bp-workp)))))

(defthm fn-bp-replace-work-preserves-work-listp
  (implies (and (fn-bp-work-listp config works)
                (fn-bp-workp config work))
           (fn-bp-work-listp config (fn-bp-replace-work work works)))
  :hints (("Goal" :induct (fn-bp-work-listp config works)
           :in-theory (e/d (fn-bp-replace-work fn-bp-work-listp)
                            (fn-bp-workp)))))

(defthm fn-bp-work-listp-of-cons
  (implies (and (fn-bp-workp config work)
                (fn-bp-work-listp config works))
           (fn-bp-work-listp config (cons work works)))
  :hints (("Goal" :in-theory (e/d (fn-bp-work-listp)
                                    (fn-bp-workp)))))

(defthm fn-bp-receipt-listp-of-cons
  (implies (and (fn-bp-receiptp receipt)
                (fn-bp-receipt-listp receipts))
           (fn-bp-receipt-listp (cons receipt receipts)))
  :hints (("Goal" :in-theory (e/d (fn-bp-receipt-listp)
                                    (fn-bp-receiptp)))))

(defthm fn-bp-work-with-attempt-preserves-workp
  (implies (and (fn-bp-workp config work)
                (fn-bp-attemptp attempt)
                (equal (fn-bp-attempt-generation attempt)
                       (fn-bp-work-next-generation work)))
           (fn-bp-workp config (fn-bp-work-with-attempt work attempt)))
  :hints (("Goal" :in-theory (enable fn-bp-workp fn-bp-attemptp
                                      fn-bp-work-with-attempt))))

(defthm fn-bp-work-attempt-of-work-with-attempt
  (equal (fn-bp-work-attempt (fn-bp-work-with-attempt work attempt))
         attempt)
  :hints (("Goal" :in-theory (enable fn-bp-work-with-attempt))))

(defthm fn-bp-work-with-receipt-preserves-workp
  (implies (and (fn-bp-workp config work)
                (fn-bp-receiptp receipt))
           (fn-bp-workp config (fn-bp-work-with-receipt work receipt)))
  :hints (("Goal" :in-theory (enable fn-bp-workp
                                      fn-bp-work-with-receipt))))

(defthm fn-bp-work-receipt-of-work-with-receipt
  (equal (fn-bp-work-receipt (fn-bp-work-with-receipt work receipt))
         receipt)
  :hints (("Goal" :in-theory (enable fn-bp-work-with-receipt))))

(defthm fn-bp-work-with-status-preserves-workp
  (implies (and (fn-bp-workp config work)
                (consp (fn-bp-work-attempt work))
                (fn-bp-transport-statusp status))
           (fn-bp-workp config (fn-bp-work-with-status work status)))
  :hints (("Goal" :in-theory (enable fn-bp-work-with-status
                                      fn-bp-attemptp))))

(defthm fn-bp-new-attemptp
  (implies (and (fn-bp-configp config)
                (fn-bp-workp config work)
                (stringp attempt-id))
           (fn-bp-attemptp
            (fn-bp-make-attempt
             attempt-id (fn-bp-work-next-generation work) :intent
             (fn-bp-config-lifetime config))))
  :hints (("Goal" :in-theory (enable fn-bp-configp fn-bp-workp
                                      fn-bp-attemptp))))

(defthm fn-bp-restart-work-preserves-workp
  (implies (fn-bp-workp config work)
           (fn-bp-workp config (fn-bp-restart-work work)))
  :hints (("Goal" :in-theory (enable fn-bp-restart-work))))

(defthm fn-bp-restart-works-preserves-work-listp
  (implies (fn-bp-work-listp config works)
           (fn-bp-work-listp config (fn-bp-restart-works works)))
  :hints (("Goal" :induct (fn-bp-work-listp config works)
           :in-theory (e/d (fn-bp-restart-works fn-bp-work-listp)
                            (fn-bp-workp fn-bp-restart-work)))))

(defthm fn-bp-derived-enqueue-workp
  (implies (and (fn-bp-configp config)
                (fn-node-bindingp binding)
                (stringp work-id)
                (stringp msgid)
                (stringp obligation-id)
                (stringp terms-id)
                (equal policy-id (fn-bp-config-policy-id config)))
           (fn-bp-workp
            config
            (fn-bp-make-work
             work-id msgid (fn-node-binding-subject binding)
             (fn-node-binding-id binding) obligation-id
             (fn-bp-config-peer-eid config) policy-id
             (fn-bp-config-incarnation config)
             (fn-bp-config-auth-context config)
             terms-id 0 nil nil)))
  :hints (("Goal" :in-theory (enable fn-bp-configp fn-bp-workp
                                      fn-node-bindingp))))

(defthm fn-bp-initial-state-is-state
  (implies (and (fn-node-statep node) (fn-bp-configp config))
           (fn-bp-statep (fn-bp-initial-state node config)))
  :hints (("Goal" :in-theory (enable fn-bp-initial-state fn-bp-statep
                                      fn-bp-work-listp
                                      fn-bp-receipt-listp))))

(defthm fn-bp-statep-components
  (implies (fn-bp-statep s)
           (and (fn-node-statep (fn-bp-state-node s))
                (fn-bp-configp (fn-bp-state-config s))
                (fn-bp-work-listp (fn-bp-state-config s)
                                  (fn-bp-state-works s))
                (fn-bp-receipt-listp (fn-bp-state-receipts s))
                (or (null (fn-bp-state-pending s))
                    (fn-bp-pendingp (fn-bp-state-config s)
                                    (fn-bp-state-pending s)))
                (or (null (fn-bp-state-fenced s))
                    (equal (fn-bp-state-fenced s) t))
                (or (null (fn-bp-state-fenced s))
                    (consp (fn-bp-state-pending s)))
                (fn-bp-tx-key-listp (fn-bp-state-used-txs s))))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-statep)
                (fn-node-statep fn-bp-configp fn-bp-work-listp
                 fn-bp-receipt-listp fn-bp-pendingp
                 fn-bp-tx-key-listp)))))

(defthm fn-bp-statep-of-make-state
  (implies (and (fn-node-statep node)
                (fn-bp-configp config)
                (fn-bp-work-listp config works)
                (fn-bp-receipt-listp receipts)
                (or (null pending) (fn-bp-pendingp config pending))
                (or (null fenced) (equal fenced t))
                (or (null fenced) (consp pending))
                (fn-bp-tx-key-listp used-txs))
           (fn-bp-statep
            (fn-bp-make-state node config works receipts pending fenced
                              used-txs)))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-statep)
                (fn-node-statep fn-bp-configp fn-bp-work-listp
                 fn-bp-receipt-listp fn-bp-pendingp
                 fn-bp-tx-key-listp)))))

(defthm fn-bp-tx-key-listp-of-cons
  (implies (and (natp txid) (natp generation)
                (fn-bp-tx-key-listp used-txs))
           (fn-bp-tx-key-listp
            (cons (fn-bp-make-tx-key txid generation) used-txs)))
  :hints (("Goal" :in-theory (enable fn-bp-tx-key-listp
                                      fn-bp-tx-keyp))))

; -----------------------------------------------------------------------------
; State preservation

(defthm fn-bp-result-state-of-make-result
  (equal (fn-bp-result-state (fn-bp-make-result st effects)) st)
  :hints (("Goal" :in-theory (enable fn-bp-result-state
                                      fn-bp-make-result))))

(defthm fn-bp-prepare-enqueue-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep
            (fn-bp-prepare-enqueue s txid generation work-id msgid
                                   obligation-id policy-id terms-id)))
  :hints (("Goal"
           :use ((:instance fn-bp-statep-components)
                 (:instance fn-bp-node-state-has-binding-listp
                            (node (fn-bp-state-node s)))
                 (:instance fn-bp-find-binding-when-binding-listp
                            (bindings
                             (fn-node-bindings (fn-bp-state-node s))))
                 (:instance fn-bp-derived-enqueue-workp
                            (config (fn-bp-state-config s))
                            (binding
                             (fn-node-find-binding
                              msgid
                              (fn-node-bindings (fn-bp-state-node s)))))
                 (:instance fn-bp-tx-key-listp-of-cons
                            (generation generation)
                            (used-txs (fn-bp-state-used-txs s)))
                 (:instance fn-bp-statep-of-make-state
                            (node (fn-bp-state-node s))
                            (config (fn-bp-state-config s))
                            (works (fn-bp-state-works s))
                            (receipts (fn-bp-state-receipts s))
                            (pending
                             (fn-bp-make-pending
                              :enqueue txid generation
                              (fn-bp-make-work
                               work-id msgid
                               (fn-node-binding-subject
                                (fn-node-find-binding
                                 msgid
                                 (fn-node-bindings (fn-bp-state-node s))))
                               (fn-node-binding-id
                                (fn-node-find-binding
                                 msgid
                                 (fn-node-bindings (fn-bp-state-node s))))
                               obligation-id
                               (fn-bp-config-peer-eid
                                (fn-bp-state-config s))
                               policy-id
                               (fn-bp-config-incarnation
                                (fn-bp-state-config s))
                               (fn-bp-config-auth-context
                                (fn-bp-state-config s))
                               terms-id 0 nil nil)
                              nil))
                            (fenced nil)
                            (used-txs
                             (cons (fn-bp-make-tx-key txid generation)
                                   (fn-bp-state-used-txs s)))))
           :in-theory (e/d (fn-bp-prepare-enqueue fn-bp-pendingp)
                            (fn-bp-statep fn-bp-workp
                             fn-bp-configp fn-node-bindingp
                             fn-node-statep fn-bp-work-listp
                             fn-bp-receipt-listp fn-bp-tx-key-listp
                             fn-bp-make-state
                             fn-bp-make-work fn-bp-make-tx-key)))))

(defthm fn-bp-prepare-attempt-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep
            (fn-bp-prepare-attempt s txid generation work-id attempt-id)))
  :hints
  (("Goal"
    :use
    ((:instance fn-bp-statep-components)
     (:instance fn-bp-find-work-when-work-listp
                (config (fn-bp-state-config s))
                (works (fn-bp-state-works s)) (id work-id))
     (:instance fn-bp-new-attemptp
                (config (fn-bp-state-config s))
                (work (fn-bp-find-work work-id (fn-bp-state-works s))))
     (:instance fn-bp-work-with-attempt-preserves-workp
                (config (fn-bp-state-config s))
                (work (fn-bp-find-work work-id (fn-bp-state-works s)))
                (attempt
                 (fn-bp-make-attempt
                  attempt-id
                  (fn-bp-work-next-generation
                   (fn-bp-find-work work-id (fn-bp-state-works s)))
                  :intent
                  (fn-bp-config-lifetime (fn-bp-state-config s)))))
     (:instance fn-bp-tx-key-listp-of-cons
                (generation generation)
                (used-txs (fn-bp-state-used-txs s)))
     (:instance fn-bp-statep-of-make-state
                (node (fn-bp-state-node s))
                (config (fn-bp-state-config s))
                (works (fn-bp-state-works s))
                (receipts (fn-bp-state-receipts s))
                (pending
                 (fn-bp-make-pending
                  :attempt txid generation
                  (fn-bp-work-with-attempt
                   (fn-bp-find-work work-id (fn-bp-state-works s))
                   (fn-bp-make-attempt
                    attempt-id
                    (fn-bp-work-next-generation
                     (fn-bp-find-work work-id (fn-bp-state-works s)))
                    :intent
                    (fn-bp-config-lifetime (fn-bp-state-config s))))
                  nil))
                (fenced nil)
                (used-txs
                 (cons (fn-bp-make-tx-key txid generation)
                       (fn-bp-state-used-txs s)))))
    :in-theory
    (e/d (fn-bp-prepare-attempt fn-bp-pendingp
                                fn-bp-work-retryablep)
         (fn-bp-statep fn-bp-workp fn-bp-configp fn-bp-attemptp
          fn-node-statep fn-bp-work-listp fn-bp-receipt-listp
          fn-bp-tx-key-listp fn-bp-make-state fn-bp-make-work
          fn-bp-work-with-attempt fn-bp-make-tx-key)))))

(defthm fn-bp-prepare-receipt-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep
            (fn-bp-prepare-receipt s txid generation receipt authorizedp)))
  :hints
  (("Goal"
    :use
    ((:instance fn-bp-statep-components)
     (:instance fn-bp-find-work-when-work-listp
                (config (fn-bp-state-config s))
                (works (fn-bp-state-works s))
                (id (fn-bp-receipt-work-id receipt)))
     (:instance fn-bp-work-with-receipt-preserves-workp
                (config (fn-bp-state-config s))
                (work
                 (fn-bp-find-work
                  (fn-bp-receipt-work-id receipt)
                  (fn-bp-state-works s))))
     (:instance fn-bp-tx-key-listp-of-cons
                (generation generation)
                (used-txs (fn-bp-state-used-txs s)))
     (:instance fn-bp-statep-of-make-state
                (node (fn-bp-state-node s))
                (config (fn-bp-state-config s))
                (works (fn-bp-state-works s))
                (receipts (fn-bp-state-receipts s))
                (pending
                 (fn-bp-make-pending
                  :receipt txid generation
                  (fn-bp-work-with-receipt
                   (fn-bp-find-work
                    (fn-bp-receipt-work-id receipt)
                    (fn-bp-state-works s))
                   receipt)
                  receipt))
                (fenced nil)
                (used-txs
                 (cons (fn-bp-make-tx-key txid generation)
                       (fn-bp-state-used-txs s)))))
    :in-theory
    (e/d (fn-bp-prepare-receipt fn-bp-pendingp
                                fn-bp-authorized-receiptp
                                fn-bp-work-outstandingp)
         (fn-bp-statep fn-bp-workp fn-bp-configp fn-bp-receiptp
          fn-node-statep fn-bp-work-listp fn-bp-receipt-listp
          fn-bp-tx-key-listp fn-bp-make-state
          fn-bp-work-with-receipt fn-bp-make-tx-key)))))

(defthm fn-bp-apply-pending-preserves-state
  (implies (and (fn-bp-statep s)
                (fn-bp-pendingp (fn-bp-state-config s) pending))
           (fn-bp-statep (fn-bp-apply-pending s pending)))
  :hints
  (("Goal"
    :use
    ((:instance fn-bp-statep-components)
     (:instance fn-bp-work-listp-of-cons
                (config (fn-bp-state-config s))
                (work (fn-bp-pending-work pending))
                (works (fn-bp-state-works s)))
     (:instance fn-bp-replace-work-preserves-work-listp
                (config (fn-bp-state-config s))
                (work (fn-bp-pending-work pending))
                (works (fn-bp-state-works s)))
     (:instance fn-bp-receipt-listp-of-cons
                (receipt (fn-bp-pending-receipt pending))
                (receipts (fn-bp-state-receipts s)))
     (:instance fn-bp-statep-of-make-state
                (node (fn-bp-state-node s))
                (config (fn-bp-state-config s))
                (works
                 (if (equal (fn-bp-pending-kind pending) :enqueue)
                     (cons (fn-bp-pending-work pending)
                           (fn-bp-state-works s))
                   (fn-bp-replace-work (fn-bp-pending-work pending)
                                       (fn-bp-state-works s))))
                (receipts
                 (if (equal (fn-bp-pending-kind pending) :receipt)
                     (cons (fn-bp-pending-receipt pending)
                           (fn-bp-state-receipts s))
                   (fn-bp-state-receipts s)))
                (pending nil) (fenced nil)
                (used-txs (fn-bp-state-used-txs s))))
    :in-theory
    (e/d (fn-bp-apply-pending fn-bp-pendingp)
         (fn-bp-statep fn-bp-workp fn-bp-configp fn-bp-receiptp
          fn-node-statep fn-bp-work-listp fn-bp-receipt-listp
          fn-bp-tx-key-listp fn-bp-make-state)))))

(defthm fn-bp-recovery-pending-preserves-pendingp
  (implies (fn-bp-pendingp config pending)
           (fn-bp-pendingp config (fn-bp-recovery-pending pending)))
  :hints (("Goal" :in-theory (enable fn-bp-recovery-pending
                                      fn-bp-pendingp))))

(defthm fn-bp-clear-pending-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep
            (fn-bp-make-state
             (fn-bp-state-node s) (fn-bp-state-config s)
             (fn-bp-state-works s) (fn-bp-state-receipts s)
             nil nil (fn-bp-state-used-txs s))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-statep-components)
          (:instance fn-bp-statep-of-make-state
                     (node (fn-bp-state-node s))
                     (config (fn-bp-state-config s))
                     (works (fn-bp-state-works s))
                     (receipts (fn-bp-state-receipts s))
                     (pending nil) (fenced nil)
                     (used-txs (fn-bp-state-used-txs s))))
    :in-theory (disable fn-bp-statep fn-bp-make-state
                        fn-node-statep fn-bp-configp fn-bp-work-listp
                        fn-bp-receipt-listp fn-bp-pendingp
                        fn-bp-tx-key-listp))))

(defthm fn-bp-fence-pending-preserves-state
  (implies (and (fn-bp-statep s)
                (consp (fn-bp-state-pending s)))
           (fn-bp-statep
            (fn-bp-make-state
             (fn-bp-state-node s) (fn-bp-state-config s)
             (fn-bp-state-works s) (fn-bp-state-receipts s)
             (fn-bp-state-pending s) t (fn-bp-state-used-txs s))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-statep-components)
          (:instance fn-bp-statep-of-make-state
                     (node (fn-bp-state-node s))
                     (config (fn-bp-state-config s))
                     (works (fn-bp-state-works s))
                     (receipts (fn-bp-state-receipts s))
                     (pending (fn-bp-state-pending s)) (fenced t)
                     (used-txs (fn-bp-state-used-txs s))))
    :in-theory (disable fn-bp-statep fn-bp-make-state
                        fn-node-statep fn-bp-configp fn-bp-work-listp
                        fn-bp-receipt-listp fn-bp-pendingp
                        fn-bp-tx-key-listp))))

(defthm fn-bp-pendingp-when-statep-and-consp
  (implies (and (fn-bp-statep s)
                (consp (fn-bp-state-pending s)))
           (fn-bp-pendingp (fn-bp-state-config s)
                           (fn-bp-state-pending s)))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-statep)
                (fn-node-statep fn-bp-configp fn-bp-work-listp
                 fn-bp-receipt-listp fn-bp-pendingp
                 fn-bp-tx-key-listp)))))

(defthm fn-bp-pending-matches-implies-consp
  (implies (fn-bp-pending-matchesp s txid generation)
           (consp (fn-bp-state-pending s)))
  :hints (("Goal" :in-theory (enable fn-bp-pending-matchesp))))

(defthm fn-bp-complete-result-state-formula
  (equal
   (fn-bp-result-state (fn-bp-complete s txid generation outcome))
   (if (or (not (fn-bp-pending-matchesp s txid generation))
           (fn-bp-state-fenced s))
       s
     (if (equal outcome :durable)
         (fn-bp-apply-pending s (fn-bp-state-pending s))
       (if (or (equal outcome :aborted)
               (equal outcome :indeterminate))
           (fn-bp-make-state
            (fn-bp-state-node s) (fn-bp-state-config s)
            (fn-bp-state-works s) (fn-bp-state-receipts s)
            (if (equal outcome :indeterminate)
                (fn-bp-state-pending s) nil)
            (if (equal outcome :indeterminate) t nil)
            (fn-bp-state-used-txs s))
         s))))
  :hints
  (("Goal" :in-theory
    (e/d (fn-bp-complete fn-bp-result-state fn-bp-make-result)
         (fn-bp-pending-matchesp fn-bp-state-fenced fn-bp-state-pending
          fn-bp-state-node fn-bp-state-config fn-bp-state-works
          fn-bp-state-receipts fn-bp-state-used-txs fn-bp-apply-pending
          fn-bp-effect-for-pending fn-bp-make-state)))))

(defthm fn-bp-complete-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep (fn-bp-result-state
                          (fn-bp-complete s txid generation outcome))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-pending-matches-implies-consp)
          (:instance fn-bp-pendingp-when-statep-and-consp)
          (:instance fn-bp-apply-pending-preserves-state
                     (pending (fn-bp-state-pending s)))
          (:instance fn-bp-clear-pending-preserves-state)
          (:instance fn-bp-fence-pending-preserves-state))
    :cases ((fn-bp-pending-matchesp s txid generation)
            (fn-bp-state-fenced s)
            (equal outcome :durable)
            (equal outcome :aborted)
            (equal outcome :indeterminate))
    :in-theory (disable fn-bp-statep fn-bp-complete
                        fn-bp-pending-matchesp fn-bp-apply-pending
                        fn-bp-make-state fn-bp-effect-for-pending
                        fn-bp-result-state fn-bp-pendingp fn-bp-workp
                        fn-bp-attemptp fn-bp-receiptp fn-bp-configp
                        fn-bp-transport-statusp))))

(defthm fn-bp-recover-result-state-formula
  (equal
   (fn-bp-result-state (fn-bp-recover s txid generation result))
   (if (or (not (fn-bp-pending-matchesp s txid generation))
           (not (equal (fn-bp-state-fenced s) t)))
       s
     (if (equal result :committed)
         (fn-bp-apply-pending
          s (fn-bp-recovery-pending (fn-bp-state-pending s)))
       (if (equal result :absent)
           (fn-bp-make-state
            (fn-bp-state-node s) (fn-bp-state-config s)
            (fn-bp-state-works s) (fn-bp-state-receipts s)
            nil nil (fn-bp-state-used-txs s))
         s))))
  :hints
  (("Goal" :in-theory
    (e/d (fn-bp-recover fn-bp-result-state fn-bp-make-result)
         (fn-bp-pending-matchesp fn-bp-state-fenced fn-bp-state-pending
          fn-bp-state-node fn-bp-state-config fn-bp-state-works
          fn-bp-state-receipts fn-bp-state-used-txs fn-bp-apply-pending
          fn-bp-effect-for-pending fn-bp-make-state
          fn-bp-recovery-pending)))))

(defthm fn-bp-recover-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep (fn-bp-result-state
                          (fn-bp-recover s txid generation result))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-pending-matches-implies-consp)
          (:instance fn-bp-pendingp-when-statep-and-consp)
          (:instance fn-bp-recovery-pending-preserves-pendingp
                     (config (fn-bp-state-config s))
                     (pending (fn-bp-state-pending s)))
          (:instance fn-bp-apply-pending-preserves-state
                     (pending
                      (fn-bp-recovery-pending
                      (fn-bp-state-pending s))))
          (:instance fn-bp-clear-pending-preserves-state))
    :cases ((fn-bp-pending-matchesp s txid generation)
            (equal (fn-bp-state-fenced s) t)
            (equal result :committed)
            (equal result :absent))
    :in-theory
    (disable fn-bp-statep fn-bp-recover fn-bp-pending-matchesp
             fn-bp-apply-pending fn-bp-make-state fn-bp-effect-for-pending
             fn-bp-recovery-pending fn-bp-result-state fn-bp-pendingp
             fn-bp-workp fn-bp-attemptp fn-bp-receiptp fn-bp-configp
             fn-bp-transport-statusp))))

(defthm fn-bp-status-update-preserves-state
  (implies (and (fn-bp-statep s)
                (fn-bp-workp (fn-bp-state-config s) work)
                (consp (fn-bp-work-attempt work))
                (fn-bp-transport-statusp status))
           (fn-bp-statep
            (fn-bp-make-state
             (fn-bp-state-node s) (fn-bp-state-config s)
             (fn-bp-replace-work (fn-bp-work-with-status work status)
                                 (fn-bp-state-works s))
             (fn-bp-state-receipts s) nil nil
             (fn-bp-state-used-txs s))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-statep-components)
          (:instance fn-bp-work-with-status-preserves-workp
                     (config (fn-bp-state-config s)))
          (:instance fn-bp-replace-work-preserves-work-listp
                     (config (fn-bp-state-config s))
                     (work (fn-bp-work-with-status work status))
                     (works (fn-bp-state-works s)))
          (:instance fn-bp-statep-of-make-state
                     (node (fn-bp-state-node s))
                     (config (fn-bp-state-config s))
                     (works
                      (fn-bp-replace-work
                       (fn-bp-work-with-status work status)
                       (fn-bp-state-works s)))
                     (receipts (fn-bp-state-receipts s))
                     (pending nil) (fenced nil)
                     (used-txs (fn-bp-state-used-txs s))))
    :in-theory
    (disable fn-bp-statep fn-bp-workp fn-bp-configp fn-bp-attemptp
             fn-node-statep fn-bp-work-listp fn-bp-receipt-listp
             fn-bp-pendingp fn-bp-tx-key-listp fn-bp-make-state
             fn-bp-work-with-status))))

(defthm fn-bp-observe-transport-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep
            (fn-bp-observe-transport s work-id attempt-id generation status)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-statep-components)
          (:instance fn-bp-find-work-when-work-listp
                     (config (fn-bp-state-config s))
                     (works (fn-bp-state-works s)) (id work-id))
          (:instance fn-bp-status-update-preserves-state
                     (work (fn-bp-find-work
                            work-id (fn-bp-state-works s)))))
    :in-theory
    (e/d (fn-bp-observe-transport fn-bp-transport-transition-okp)
         (fn-bp-statep fn-bp-workp fn-bp-configp fn-bp-attemptp
          fn-node-statep fn-bp-work-listp fn-bp-receipt-listp
          fn-bp-pendingp fn-bp-tx-key-listp fn-bp-make-state
          fn-bp-work-with-status fn-bp-live-statusp fn-bp-status-rank)))))

(defthm fn-bp-request-retry-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep
            (fn-bp-request-retry s work-id attempt-id generation policy-id)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-statep-components)
          (:instance fn-bp-find-work-when-work-listp
                     (config (fn-bp-state-config s))
                     (works (fn-bp-state-works s)) (id work-id))
          (:instance fn-bp-status-update-preserves-state
                     (work (fn-bp-find-work
                            work-id (fn-bp-state-works s)))
                     (status :unknown)))
    :in-theory
    (e/d (fn-bp-request-retry fn-bp-work-outstandingp)
         (fn-bp-statep fn-bp-workp fn-bp-configp fn-bp-attemptp
          fn-node-statep fn-bp-work-listp fn-bp-receipt-listp
          fn-bp-pendingp fn-bp-tx-key-listp fn-bp-make-state
          fn-bp-work-with-status)))))

(defthm fn-bp-restart-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep (fn-bp-restart s)))
  :hints
  (("Goal"
    :use ((:instance fn-bp-statep-components)
          (:instance fn-bp-restart-works-preserves-work-listp
                     (config (fn-bp-state-config s))
                     (works (fn-bp-state-works s)))
          (:instance fn-bp-statep-of-make-state
                     (node (fn-bp-state-node s))
                     (config (fn-bp-state-config s))
                     (works
                      (fn-bp-restart-works (fn-bp-state-works s)))
                     (receipts (fn-bp-state-receipts s))
                     (pending (fn-bp-state-pending s))
                     (fenced
                      (if (consp (fn-bp-state-pending s))
                          t (fn-bp-state-fenced s)))
                     (used-txs (fn-bp-state-used-txs s))))
    :in-theory
    (e/d (fn-bp-restart)
         (fn-bp-statep fn-bp-configp fn-node-statep
          fn-bp-work-listp fn-bp-receipt-listp fn-bp-pendingp
          fn-bp-tx-key-listp fn-bp-make-state fn-bp-restart-works)))))

(defthm fn-bp-step-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep (fn-bp-result-state (fn-bp-step s event))))
  :hints
  (("Goal" :in-theory
    (e/d (fn-bp-step)
         (fn-bp-statep fn-bp-result-state fn-bp-make-result
          fn-bp-prepare-enqueue fn-bp-prepare-attempt
          fn-bp-prepare-receipt fn-bp-complete fn-bp-recover
          fn-bp-observe-transport fn-bp-request-retry fn-bp-restart
          fn-bp-complete-result-state-formula
          fn-bp-recover-result-state-formula)))))

(defthm fn-bp-trace-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep (fn-bp-trace s events)))
  :hints (("Goal" :induct (fn-bp-trace s events)
           :in-theory (e/d (fn-bp-trace)
                            (fn-bp-statep fn-bp-step
                             fn-bp-result-state)))))

; The node, and therefore every accepted article, local membership number,
; immutable subject binding, and committed archive pin, is unchanged.
(defthm fn-bp-prepare-enqueue-preserves-node
  (equal (fn-bp-state-node
          (fn-bp-prepare-enqueue s txid generation work-id msgid
                                 obligation-id policy-id terms-id))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-prepare-enqueue fn-bp-state-node fn-bp-make-state)
                (fn-bp-statep fn-bp-find-work fn-bp-find-work-by-msgid
                 fn-node-find-binding)))))

(defthm fn-bp-prepare-attempt-preserves-node
  (equal (fn-bp-state-node
          (fn-bp-prepare-attempt s txid generation work-id attempt-id))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-prepare-attempt fn-bp-state-node fn-bp-make-state)
                (fn-bp-statep fn-bp-find-work fn-bp-work-retryablep)))))

(defthm fn-bp-prepare-receipt-preserves-node
  (equal (fn-bp-state-node
          (fn-bp-prepare-receipt s txid generation receipt authorizedp))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-prepare-receipt fn-bp-state-node fn-bp-make-state)
                (fn-bp-statep fn-bp-find-work fn-bp-work-outstandingp
                 fn-bp-authorized-receiptp)))))

(defthm fn-bp-apply-pending-preserves-node
  (equal (fn-bp-state-node (fn-bp-apply-pending s pending))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory (enable fn-bp-apply-pending
                                      fn-bp-state-node fn-bp-make-state))))

(defthm fn-bp-state-node-of-make-state
  (equal (fn-bp-state-node
          (fn-bp-make-state node config works receipts pending fenced used))
         node)
  :hints (("Goal" :in-theory (enable fn-bp-state-node
                                      fn-bp-make-state))))

(defthm fn-bp-complete-preserves-node
  (equal (fn-bp-state-node
          (fn-bp-result-state (fn-bp-complete s txid generation outcome)))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-complete-result-state-formula)
                (fn-bp-complete fn-bp-result-state fn-bp-state-node
                 fn-bp-make-state fn-bp-apply-pending)))))

(defthm fn-bp-recover-preserves-node
  (equal (fn-bp-state-node
          (fn-bp-result-state (fn-bp-recover s txid generation result)))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-recover-result-state-formula)
                (fn-bp-recover fn-bp-result-state fn-bp-state-node
                 fn-bp-make-state fn-bp-apply-pending
                 fn-bp-recovery-pending)))))

(defthm fn-bp-observe-transport-preserves-node
  (equal (fn-bp-state-node
          (fn-bp-observe-transport s work-id attempt-id generation status))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-observe-transport fn-bp-state-node fn-bp-make-state)
                (fn-bp-statep fn-bp-find-work
                 fn-bp-transport-transition-okp)))))

(defthm fn-bp-request-retry-preserves-node
  (equal (fn-bp-state-node
          (fn-bp-request-retry s work-id attempt-id generation policy-id))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-request-retry fn-bp-state-node fn-bp-make-state)
                (fn-bp-statep fn-bp-find-work
                 fn-bp-work-outstandingp)))))

(defthm fn-bp-restart-preserves-node
  (equal (fn-bp-state-node (fn-bp-restart s))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-restart fn-bp-state-node fn-bp-make-state)
                (fn-bp-statep fn-bp-restart-works)))))

(defthm fn-bp-step-preserves-node
  (equal (fn-bp-state-node (fn-bp-result-state (fn-bp-step s event)))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-step)
                (fn-bp-state-node fn-bp-result-state fn-bp-make-result
                 fn-bp-prepare-enqueue fn-bp-prepare-attempt
                 fn-bp-prepare-receipt fn-bp-complete fn-bp-recover
                 fn-bp-observe-transport fn-bp-request-retry
                 fn-bp-restart fn-bp-complete-result-state-formula
                 fn-bp-recover-result-state-formula)))))

(defthm fn-bp-trace-preserves-node
  (equal (fn-bp-state-node (fn-bp-trace s events))
         (fn-bp-state-node s))
  :hints (("Goal" :induct (fn-bp-trace s events)
           :in-theory (e/d (fn-bp-trace)
                            (fn-bp-step fn-bp-result-state
                             fn-bp-state-node)))))


; -----------------------------------------------------------------------------
; Effects.  Which event can emit which effect, and from which pre-state.
; These formulas expose the effect branches of the production transitions so
; that the durable-intent-before-submission result below is about fn-bp-step,
; the dispatcher every host entry point goes through.

(defthm fn-bp-result-effects-of-make-result
  (equal (fn-bp-result-effects (fn-bp-make-result st effects)) effects)
  :hints (("Goal" :in-theory (enable fn-bp-result-effects
                                      fn-bp-make-result))))

(defthm fn-bp-complete-effects-formula
  (equal (fn-bp-result-effects (fn-bp-complete s txid generation outcome))
         (if (or (not (fn-bp-pending-matchesp s txid generation))
                 (fn-bp-state-fenced s))
             nil
           (if (equal outcome :durable)
               (list (fn-bp-effect-for-pending s (fn-bp-state-pending s)))
             (if (equal outcome :indeterminate)
                 (list (list :recover-required txid generation))
               nil))))
  :hints
  (("Goal" :in-theory
    (e/d (fn-bp-complete fn-bp-result-effects fn-bp-make-result)
         (fn-bp-pending-matchesp fn-bp-state-fenced fn-bp-state-pending
          fn-bp-state-node fn-bp-state-config fn-bp-state-works
          fn-bp-state-receipts fn-bp-state-used-txs fn-bp-apply-pending
          fn-bp-effect-for-pending fn-bp-make-state)))))

(defthm fn-bp-recover-effects-formula
  (equal (fn-bp-result-effects (fn-bp-recover s txid generation result))
         (if (or (not (fn-bp-pending-matchesp s txid generation))
                 (not (equal (fn-bp-state-fenced s) t))
                 (not (equal result :committed))
                 (equal (fn-bp-pending-kind (fn-bp-state-pending s)) :attempt))
             nil
           (list (fn-bp-effect-for-pending s (fn-bp-state-pending s)))))
  :hints
  (("Goal" :in-theory
    (e/d (fn-bp-recover fn-bp-result-effects fn-bp-make-result)
         (fn-bp-pending-matchesp fn-bp-state-fenced fn-bp-state-pending
          fn-bp-state-node fn-bp-state-config fn-bp-state-works
          fn-bp-state-receipts fn-bp-state-used-txs fn-bp-apply-pending
          fn-bp-effect-for-pending fn-bp-make-state
          fn-bp-recovery-pending fn-bp-pending-kind)))))

(defthm fn-bp-step-effects-formula
  (equal (fn-bp-result-effects (fn-bp-step s event))
         (let ((kind (fn-bp-event-kind event)))
           (if (equal kind :storage-complete)
               (fn-bp-result-effects
                (fn-bp-complete s (fn-bp-nth 1 event) (fn-bp-nth 2 event)
                                (fn-bp-nth 3 event)))
             (if (equal kind :storage-recover)
                 (fn-bp-result-effects
                  (fn-bp-recover s (fn-bp-nth 1 event) (fn-bp-nth 2 event)
                                 (fn-bp-nth 3 event)))
               nil))))
  :hints
  (("Goal" :in-theory
    (e/d (fn-bp-step)
         (fn-bp-result-effects fn-bp-make-result fn-bp-complete fn-bp-recover
          fn-bp-prepare-enqueue fn-bp-prepare-attempt fn-bp-prepare-receipt
          fn-bp-observe-transport fn-bp-request-retry fn-bp-restart
          fn-bp-event-kind fn-bp-nth
          fn-bp-complete-effects-formula fn-bp-recover-effects-formula)))))

(defthm fn-bp-nth-0-of-cons
  (equal (fn-bp-nth 0 (cons a b)) a)
  :hints (("Goal" :in-theory (enable fn-bp-nth))))

(defthm fn-bp-effect-for-pending-kind
  (equal (fn-bp-nth 0 (fn-bp-effect-for-pending s pending))
         (if (equal (fn-bp-pending-kind pending) :enqueue)
             :enqueue-ack
           (if (equal (fn-bp-pending-kind pending) :attempt)
               :submit
             :receipt-ack)))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-effect-for-pending)
                (fn-bp-pending-kind fn-bp-pending-work fn-bp-pending-receipt
                 fn-bp-work-id fn-bp-work-attempt fn-bp-attempt-id
                 fn-bp-attempt-generation fn-bp-attempt-lifetime
                 fn-bp-state-config fn-bp-config-local-eid
                 fn-bp-config-peer-eid fn-bp-receipt-id)))))

(defthm fn-bp-effect-for-pending-attempt-unfolds
  (implies (equal (fn-bp-pending-kind pending) :attempt)
           (equal (fn-bp-effect-for-pending s pending)
                  (list :submit
                        (fn-bp-work-id (fn-bp-pending-work pending))
                        (fn-bp-attempt-id
                         (fn-bp-work-attempt (fn-bp-pending-work pending)))
                        (fn-bp-attempt-generation
                         (fn-bp-work-attempt (fn-bp-pending-work pending)))
                        (fn-bp-config-local-eid (fn-bp-state-config s))
                        (fn-bp-config-peer-eid (fn-bp-state-config s))
                        (fn-bp-attempt-lifetime
                         (fn-bp-work-attempt (fn-bp-pending-work pending))))))
  :hints (("Goal" :in-theory
           (e/d (fn-bp-effect-for-pending)
                (fn-bp-pending-kind fn-bp-pending-work fn-bp-pending-receipt
                 fn-bp-work-id fn-bp-work-attempt fn-bp-attempt-id
                 fn-bp-attempt-generation fn-bp-attempt-lifetime
                 fn-bp-state-config fn-bp-config-local-eid
                 fn-bp-config-peer-eid fn-bp-receipt-id)))))

; Durable intent before submission (D8).  A :submit effect leaves fn-bp-step
; only from the :durable branch of fn-bp-complete, only when the pre-state
; holds an unfenced pending :attempt intent whose transaction pair the
; completion names, and the effect names exactly that intent's work, attempt
; id and attempt generation.  It is the only effect of that step.  The
; "durable" word is the host's: A-HOST is that the intent record was on disk
; before fn-bp-prepare-attempt was called and the :durable outcome record was
; on disk before this completion event was fed (specs/bp-workflow-host.md).
(defthm fn-bp-step-submit-requires-matching-durable-attempt-completion
  (implies (and (member-equal e (fn-bp-result-effects (fn-bp-step s event)))
                (equal (fn-bp-nth 0 e) :submit))
           (let ((pending (fn-bp-state-pending s)))
             (and (fn-bp-statep s)
                  (not (fn-bp-state-fenced s))
                  (consp pending)
                  (equal (fn-bp-pending-kind pending) :attempt)
                  (equal (fn-bp-event-kind event) :storage-complete)
                  (equal (fn-bp-nth 1 event) (fn-bp-pending-txid pending))
                  (equal (fn-bp-nth 2 event) (fn-bp-pending-generation pending))
                  (equal (fn-bp-nth 3 event) :durable)
                  (equal (fn-bp-result-effects (fn-bp-step s event)) (list e))
                  (equal e
                         (list :submit
                               (fn-bp-work-id (fn-bp-pending-work pending))
                               (fn-bp-attempt-id
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending)))
                               (fn-bp-attempt-generation
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending)))
                               (fn-bp-config-local-eid (fn-bp-state-config s))
                               (fn-bp-config-peer-eid (fn-bp-state-config s))
                               (fn-bp-attempt-lifetime
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending))))))))
  :rule-classes nil
  :hints
  (("Goal" :in-theory
    (e/d (fn-bp-step-effects-formula fn-bp-complete-effects-formula
          fn-bp-recover-effects-formula fn-bp-pending-matchesp
          fn-bp-effect-for-pending-kind
          fn-bp-effect-for-pending-attempt-unfolds member-equal)
         (fn-bp-step fn-bp-complete fn-bp-recover fn-bp-effect-for-pending
          fn-bp-statep fn-bp-state-pending fn-bp-state-fenced
          fn-bp-pending-kind fn-bp-pending-txid fn-bp-pending-generation
          fn-bp-pending-work fn-bp-work-id fn-bp-work-attempt
          fn-bp-attempt-id fn-bp-attempt-generation fn-bp-attempt-lifetime
          fn-bp-state-config fn-bp-config-local-eid fn-bp-config-peer-eid
          fn-bp-event-kind fn-bp-nth fn-bp-result-effects)))))
