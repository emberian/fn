; Keystones for the relay undertaking (wave 2, packet B; C2-07, D12).
;
; Subject: fn-relay-undertake, fn-relay-record-undertaking,
; fn-relay-commit-receipt, fn-relay-accept, fn-relay-sender-step and
; fn-relay-crash-recover over books/relay.lisp's composed state.
;
; Keystones (cite these, not the -by-definition lemmas):
;   fn-relay-step-monotone                      (sender never loses a work)
;   fn-relay-sender-step-preserves-invp
;   fn-relay-accept-preserves-invp
;   fn-relay-record-undertaking-preserves-invp
;   fn-relay-undertake-preserves-invp
;   fn-relay-commit-receipt-preserves-invp
; The crash argument and what the invariant buys are in
; books/relay-crash-invariants.lisp (split so each book certifies inside
; the 1800-second budget).
(in-package "ACL2")
(include-book "relay")
; The relay proofs open the receiver definitions; enable them here, locally.
(local (in-theory (enable fn-bp-receiver-vocabulary fn-bp-receiver-records-vocabulary)))

; Opening either of these turns a one-line shape lemma into an 80-second
; proof (measured); every theorem below that mentions fn-relay-statep pays
; it.  The node is compared, never inspected, so both stay opaque.
(in-theory (disable fn-sn-node fn-bp-state-node))

; -----------------------------------------------------------------------------
; Selector arithmetic

(defthm fn-relay-bp-nth-cons
  (implies (natp n)
           (equal (fn-bp-nth n (cons a b))
                  (if (equal n 0) a (fn-bp-nth (1- n) b))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-nth fn-ag-car fn-ag-cdr fn-ag-less))))

(defthm fn-relay-bp-nth-nil
  (implies (natp n) (equal (fn-bp-nth n nil) nil))
  :hints (("Goal" :induct (fn-bp-nth n nil) :in-theory (enable fn-bp-nth fn-ag-car fn-ag-cdr fn-ag-less))))

(defthm fn-relay-bpa-nth-cons
  (implies (natp n)
           (equal (fn-bpa-nth n (cons a b))
                  (if (equal n 0) a (fn-bpa-nth (1- n) b))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bpa-nth fn-bpa-car fn-bpa-cdr))))

(defthm fn-relay-bpa-nth-nil
  (implies (natp n) (equal (fn-bpa-nth n nil) nil))
  :hints (("Goal" :induct (fn-bpa-nth n nil) :in-theory (enable fn-bpa-nth fn-bpa-car fn-bpa-cdr))))

(defthm fn-relay-state-components
  (and (equal (fn-relay-store (fn-relay-make-state st rc sn tm u)) st)
       (equal (fn-relay-receiver (fn-relay-make-state st rc sn tm u)) rc)
       (equal (fn-relay-sender (fn-relay-make-state st rc sn tm u)) sn)
       (equal (fn-relay-terms (fn-relay-make-state st rc sn tm u)) tm)
       (equal (fn-relay-undertakings (fn-relay-make-state st rc sn tm u)) u)
       (equal (fn-relay-node (fn-relay-make-state st rc sn tm u))
              (fn-bp-state-node sn)))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-relay-store fn-relay-receiver
                                      fn-relay-sender fn-relay-terms
                                      fn-relay-undertakings fn-relay-node
                                      fn-relay-make-state))))

(defthm fn-relay-bpr-state-components
  (and (equal (fn-bpr-state-config (fn-bpr-make-state c x r p)) c)
       (equal (fn-bpr-state-contexts (fn-bpr-make-state c x r p)) x)
       (equal (fn-bpr-state-receipts (fn-bpr-make-state c x r p)) r)
       (equal (fn-bpr-state-pending (fn-bpr-make-state c x r p)) p))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bpr-state-config fn-bpr-state-contexts
                                      fn-bpr-state-receipts fn-bpr-state-pending
                                      fn-bpr-make-state))))

(defthm fn-relay-receipt-entry-components
  (and (consp (fn-bpr-make-receipt-entry c r))
       (equal (fn-bpr-receipt-entry-context (fn-bpr-make-receipt-entry c r)) c)
       (equal (fn-bpr-receipt-entry-receipt (fn-bpr-make-receipt-entry c r)) r))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bpr-receipt-entry-context
                                      fn-bpr-receipt-entry-receipt
                                      fn-bpr-make-receipt-entry))))

(defthm fn-relay-undertaking-components
  (and (consp (fn-relay-make-undertaking up onward))
       (true-listp (fn-relay-make-undertaking up onward))
       (equal (len (fn-relay-make-undertaking up onward)) 2)
       (equal (fn-relay-undertaking-upstream (fn-relay-make-undertaking up onward)) up)
       (equal (fn-relay-undertaking-onward (fn-relay-make-undertaking up onward)) onward))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-relay-make-undertaking
                                      fn-relay-undertaking-upstream
                                      fn-relay-undertaking-onward))))

(defthm fn-relay-statep-components
  (implies (fn-relay-statep rs)
           (and (fn-bp-binding-statep (fn-relay-sender rs))
                (fn-bp-statep (fn-relay-sender rs))
                (equal (fn-bp-state-node (fn-relay-sender rs))
                       (fn-sn-node (fn-relay-store rs)))
                (fn-relay-terms-tablep (fn-relay-terms rs))
                (fn-relay-undertaking-listp (fn-relay-undertakings rs))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bp-binding-state-implies-statep
                            (s (fn-relay-sender rs))))
           :in-theory (e/d (fn-relay-statep)
                           (fn-bp-binding-statep fn-bp-statep
                                                 fn-relay-terms-tablep
                                                 fn-relay-undertaking-listp)))))

(defthm fn-relay-invp-implies-statep
  (implies (fn-relay-invp rs) (fn-relay-statep rs))
  :hints (("Goal" :in-theory (e/d (fn-relay-invp) (fn-relay-statep)))))

(defthm fn-relay-make-statep
  (implies (and (fn-bp-binding-statep sn)
                (equal (fn-bp-state-node sn) (fn-sn-node st))
                (fn-relay-terms-tablep tm)
                (fn-relay-undertaking-listp u))
           (fn-relay-statep (fn-relay-make-state st rc sn tm u)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-relay-statep fn-relay-make-state)
                                  (fn-bp-binding-statep fn-relay-terms-tablep
                                                        fn-relay-undertaking-listp)))))

(defthm fn-relay-find-context-work-id
  (implies (consp (fn-bpr-find-context upstream xs))
           (equal (fn-bpr-context-work-id (fn-bpr-find-context upstream xs))
                  upstream))
  :hints (("Goal" :induct (fn-bpr-find-context upstream xs)
           :in-theory (enable fn-bpr-find-context))))

; From here on selectors, constructors and the two positional accessors are
; opaque; the component lemmas above and the rules from bp-workflow-invariants
; and bp-workflow-binding-core are the interface, so rules stated in accessor
; form match syntactically.
(in-theory (disable fn-bp-nth fn-bpa-nth
                    fn-bp-state-node fn-bp-state-config fn-bp-state-works
                    fn-bp-state-receipts fn-bp-state-pending fn-bp-state-fenced
                    fn-bp-state-used-txs fn-bp-make-state
                    fn-bp-make-result fn-bp-result-state fn-bp-result-effects
                    fn-bp-work-id fn-bp-make-work fn-bp-work-with-attempt
                    fn-bp-work-with-receipt fn-bp-work-with-status
                    fn-bp-restart-work
                    fn-bp-pending-kind fn-bp-pending-txid fn-bp-pending-generation
                    fn-bp-pending-work fn-bp-pending-receipt
                    fn-bpr-state-config fn-bpr-state-contexts
                    fn-bpr-state-receipts fn-bpr-state-pending fn-bpr-make-state
                    fn-bpr-receipt-entry-context fn-bpr-receipt-entry-receipt
                    fn-bpr-make-receipt-entry
                    fn-bpr-context-work-id fn-bpr-context-msgid
                    fn-bpr-context-subject fn-bpr-context-archive-id
                    fn-bpr-context-terms-id fn-bpa-receipt-id
                    fn-relay-store fn-relay-receiver fn-relay-sender
                    fn-relay-terms fn-relay-undertakings fn-relay-make-state
                    fn-relay-undertaking-upstream fn-relay-undertaking-onward
                    fn-relay-make-undertaking))

; -----------------------------------------------------------------------------
; The sender never loses a durable work.  Works are only consed, replaced by
; identity, or mapped by restart.

(defthm fn-relay-work-id-with-attempt
  (equal (fn-bp-work-id (fn-bp-work-with-attempt w a)) (fn-bp-work-id w))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-work-with-attempt fn-bp-make-work
                                      fn-bp-work-id))))

(defthm fn-relay-work-id-with-receipt
  (equal (fn-bp-work-id (fn-bp-work-with-receipt w r)) (fn-bp-work-id w))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-work-with-receipt fn-bp-make-work
                                      fn-bp-work-id))))

(defthm fn-relay-work-id-with-status
  (equal (fn-bp-work-id (fn-bp-work-with-status w st)) (fn-bp-work-id w))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-work-with-status))))

(defthm fn-relay-work-id-restart-work
  (equal (fn-bp-work-id (fn-bp-restart-work w)) (fn-bp-work-id w))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-restart-work))))

(defthm fn-relay-with-attempt-consp
  (consp (fn-bp-work-with-attempt w a))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-work-with-attempt fn-bp-make-work))))

(defthm fn-relay-with-receipt-consp
  (consp (fn-bp-work-with-receipt w r))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-work-with-receipt fn-bp-make-work))))

(defthm fn-relay-with-status-consp
  (consp (fn-bp-work-with-status w st))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-work-with-status))))

(defthm fn-relay-restart-work-consp
  (implies (consp w) (consp (fn-bp-restart-work w)))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-restart-work))))

(defthm fn-relay-find-work-cons
  (implies (and (consp w) (consp (fn-bp-find-work id xs)))
           (consp (fn-bp-find-work id (cons w xs))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-find-work))))

(defthm fn-relay-find-work-replace
  (implies (and (consp w) (consp (fn-bp-find-work id xs)))
           (consp (fn-bp-find-work id (fn-bp-replace-work w xs))))
  :hints (("Goal" :induct (fn-bp-replace-work w xs)
           :in-theory (enable fn-bp-find-work fn-bp-replace-work))))

(defthm fn-relay-find-work-restart
  (implies (consp (fn-bp-find-work id xs))
           (consp (fn-bp-find-work id (fn-bp-restart-works xs))))
  :hints (("Goal" :induct (fn-bp-restart-works xs)
           :in-theory (e/d (fn-bp-find-work fn-bp-restart-works)
                           (fn-bp-restart-work)))))

(defthm fn-relay-prepare-enqueue-works
  (equal (fn-bp-state-works
          (fn-bp-prepare-enqueue s txid gen work-id msgid obligation-id
                                 policy-id terms-id))
         (fn-bp-state-works s))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bp-prepare-enqueue)
                                  (fn-bp-statep fn-bp-find-work fn-bp-find-work-by-msgid
                                   fn-node-find-binding fn-bp-state-works
                                   fn-bp-make-state fn-bp-nth fn-bp-make-work
                                   fn-bp-make-pending fn-ag-member
                                   fn-bp-make-tx-key fn-bp-state-config
                                   fn-bp-config-policy-id fn-bp-config-lifetime
                                   fn-bp-state-pending fn-bp-state-fenced
                                   fn-bp-state-used-txs fn-bp-state-node
                                   fn-bp-state-receipts fn-bp-config-peer-eid
                                   fn-bp-config-incarnation
                                   fn-bp-config-auth-context fn-node-bindings
                                   fn-node-binding-subject fn-node-binding-id
                                   fn-bp-work-retryablep fn-bp-work-with-attempt
                                   fn-bp-make-attempt fn-bp-work-next-generation
                                   fn-bp-work-outstandingp
                                   fn-bp-authorized-receiptp
                                   fn-bp-work-with-receipt fn-bp-receipt-work-id)))))

(defthm fn-relay-prepare-attempt-works
  (equal (fn-bp-state-works (fn-bp-prepare-attempt s txid gen work-id attempt-id))
         (fn-bp-state-works s))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bp-prepare-attempt)
                                  (fn-bp-statep fn-bp-find-work fn-bp-find-work-by-msgid
                                   fn-node-find-binding fn-bp-state-works
                                   fn-bp-make-state fn-bp-nth fn-bp-make-work
                                   fn-bp-make-pending fn-ag-member
                                   fn-bp-make-tx-key fn-bp-state-config
                                   fn-bp-config-policy-id fn-bp-config-lifetime
                                   fn-bp-state-pending fn-bp-state-fenced
                                   fn-bp-state-used-txs fn-bp-state-node
                                   fn-bp-state-receipts fn-bp-config-peer-eid
                                   fn-bp-config-incarnation
                                   fn-bp-config-auth-context fn-node-bindings
                                   fn-node-binding-subject fn-node-binding-id
                                   fn-bp-work-retryablep fn-bp-work-with-attempt
                                   fn-bp-make-attempt fn-bp-work-next-generation
                                   fn-bp-work-outstandingp
                                   fn-bp-authorized-receiptp
                                   fn-bp-work-with-receipt fn-bp-receipt-work-id)))))

(defthm fn-relay-prepare-receipt-works
  (equal (fn-bp-state-works (fn-bp-prepare-receipt s txid gen receipt auth))
         (fn-bp-state-works s))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bp-prepare-receipt)
                                  (fn-bp-statep fn-bp-find-work fn-bp-find-work-by-msgid
                                   fn-node-find-binding fn-bp-state-works
                                   fn-bp-make-state fn-bp-nth fn-bp-make-work
                                   fn-bp-make-pending fn-ag-member
                                   fn-bp-make-tx-key fn-bp-state-config
                                   fn-bp-config-policy-id fn-bp-config-lifetime
                                   fn-bp-state-pending fn-bp-state-fenced
                                   fn-bp-state-used-txs fn-bp-state-node
                                   fn-bp-state-receipts fn-bp-config-peer-eid
                                   fn-bp-config-incarnation
                                   fn-bp-config-auth-context fn-node-bindings
                                   fn-node-binding-subject fn-node-binding-id
                                   fn-bp-work-retryablep fn-bp-work-with-attempt
                                   fn-bp-make-attempt fn-bp-work-next-generation
                                   fn-bp-work-outstandingp
                                   fn-bp-authorized-receiptp
                                   fn-bp-work-with-receipt fn-bp-receipt-work-id)))))

(defthm fn-relay-pending-work-consp
  (implies (fn-bp-pendingp config pending)
           (consp (fn-bp-pending-work pending)))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-pendingp fn-bp-workp))))

(defthm fn-relay-recovery-pending-work-consp
  (implies (consp (fn-bp-pending-work pending))
           (consp (fn-bp-pending-work (fn-bp-recovery-pending pending))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-bp-recovery-pending fn-bp-make-pending
                                      fn-bp-pending-work))))

(defthm fn-relay-apply-pending-monotone
  (implies (and (consp (fn-bp-pending-work pending))
                (consp (fn-bp-find-work id (fn-bp-state-works s))))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works (fn-bp-apply-pending s pending)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bp-apply-pending)
                                  (fn-bp-find-work fn-bp-replace-work)))))

(defthm fn-relay-complete-monotone
  (implies (and (fn-bp-statep s)
                (consp (fn-bp-find-work id (fn-bp-state-works s))))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works
                       (fn-bp-result-state (fn-bp-complete s txid gen outcome))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bp-pending-matches-implies-consp
                            (generation gen))
                 (:instance fn-bp-pendingp-when-statep-and-consp))
           :in-theory (e/d ()
                           (fn-bp-statep fn-bp-complete fn-bp-find-work
                                         fn-bp-apply-pending
                                         fn-bp-pending-matchesp fn-bp-pendingp
                                         fn-bp-pending-matches-implies-consp
                                         fn-bp-pendingp-when-statep-and-consp)))))

(defthm fn-relay-recover-monotone
  (implies (and (fn-bp-statep s)
                (consp (fn-bp-find-work id (fn-bp-state-works s))))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works
                       (fn-bp-result-state (fn-bp-recover s txid gen result))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bp-pending-matches-implies-consp
                            (generation gen))
                 (:instance fn-bp-pendingp-when-statep-and-consp))
           :in-theory (e/d ()
                           (fn-bp-statep fn-bp-recover fn-bp-find-work
                                         fn-bp-apply-pending
                                         fn-bp-recovery-pending
                                         fn-bp-pending-matchesp fn-bp-pendingp
                                         fn-bp-pending-matches-implies-consp
                                         fn-bp-pendingp-when-statep-and-consp)))))

(defthm fn-relay-observe-transport-monotone
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works
                       (fn-bp-observe-transport s work-id attempt-id gen status)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bp-observe-transport)
                                  (fn-bp-statep fn-bp-find-work
                                                fn-bp-replace-work
                                                fn-bp-work-with-status
                                                fn-bp-transport-transition-okp)))))

(defthm fn-relay-request-retry-monotone
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works
                       (fn-bp-request-retry s work-id attempt-id gen policy-id)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bp-request-retry)
                                  (fn-bp-statep fn-bp-find-work
                                                fn-bp-replace-work
                                                fn-bp-work-with-status
                                                fn-bp-work-outstandingp)))))

(defthm fn-relay-restart-monotone
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work id (fn-bp-state-works (fn-bp-restart s)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bp-restart)
                                  (fn-bp-statep fn-bp-find-work
                                                fn-bp-restart-works)))))

(defthm fn-relay-step-monotone
  (implies (and (fn-bp-statep s)
                (consp (fn-bp-find-work id (fn-bp-state-works s))))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works
                       (fn-bp-result-state (fn-bp-step s event))))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bp-step)
                                  (fn-bp-statep fn-bp-find-work
                                                fn-bp-result-state
                                                fn-bp-make-result
                                                fn-bp-prepare-enqueue
                                                fn-bp-prepare-attempt
                                                fn-bp-prepare-receipt
                                                fn-bp-complete fn-bp-recover
                                                fn-bp-observe-transport
                                                fn-bp-request-retry
                                                fn-bp-restart
                                                fn-bp-complete-result-state-formula
                                                fn-bp-recover-result-state-formula)))))

; -----------------------------------------------------------------------------
; Backing predicates are monotone in the sender's works and insensitive to a
; new undertaking.

(defthm fn-relay-entry-backedp-step
  (implies (and (fn-bp-statep s)
                (fn-relay-entry-backedp entry node terms u (fn-bp-state-works s)))
           (fn-relay-entry-backedp
            entry node terms u
            (fn-bp-state-works (fn-bp-result-state (fn-bp-step s event)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-relay-entry-backedp)
                                  (fn-bp-statep fn-bp-step fn-bp-find-work
                                                fn-bp-result-state
                                                fn-relay-content-durablep
                                                fn-relay-terms-kind
                                                fn-relay-find-undertaking)))))

(defthm fn-relay-entries-backedp-step
  (implies (and (fn-bp-statep s)
                (fn-relay-entries-backedp entries node terms u (fn-bp-state-works s)))
           (fn-relay-entries-backedp
            entries node terms u
            (fn-bp-state-works (fn-bp-result-state (fn-bp-step s event)))))
  :hints (("Goal" :induct (fn-relay-entries-backedp entries node terms u
                                                    (fn-bp-state-works s))
           :in-theory (e/d (fn-relay-entries-backedp)
                           (fn-bp-statep fn-bp-step fn-bp-result-state
                                         fn-relay-entry-backedp)))))

(defthm fn-relay-undertakings-backedp-step
  (implies (and (fn-bp-statep s)
                (fn-relay-undertakings-backedp u (fn-bp-state-works s)))
           (fn-relay-undertakings-backedp
            u (fn-bp-state-works (fn-bp-result-state (fn-bp-step s event)))))
  :hints (("Goal" :induct (fn-relay-undertakings-backedp u (fn-bp-state-works s))
           :in-theory (e/d (fn-relay-undertakings-backedp)
                           (fn-bp-statep fn-bp-step fn-bp-result-state
                                         fn-bp-find-work)))))

(defthm fn-relay-entry-backedp-cons-undertaking
  (implies (and (fn-relay-entry-backedp entry node terms u works)
                (consp (fn-bp-find-work onward works)))
           (fn-relay-entry-backedp
            entry node terms (cons (fn-relay-make-undertaking upstream onward) u)
            works))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-relay-entry-backedp
                                   fn-relay-find-undertaking
                                   fn-relay-make-undertaking
                                   fn-relay-undertaking-upstream
                                   fn-relay-undertaking-onward)
                                  (fn-bp-find-work fn-relay-content-durablep
                                                   fn-relay-terms-kind)))))

(defthm fn-relay-entries-backedp-cons-undertaking
  (implies (and (fn-relay-entries-backedp entries node terms u works)
                (consp (fn-bp-find-work onward works)))
           (fn-relay-entries-backedp
            entries node terms (cons (fn-relay-make-undertaking upstream onward) u)
            works))
  :hints (("Goal" :induct (fn-relay-entries-backedp entries node terms u works)
           :in-theory (e/d (fn-relay-entries-backedp)
                           (fn-relay-entry-backedp fn-bp-find-work)))))

; -----------------------------------------------------------------------------
; Invariant preservation, transition by transition

(defthm fn-relay-invp-sender-step
  (implies (fn-relay-invp rs)
           (fn-relay-invp
            (fn-relay-make-state
             (fn-relay-store rs) (fn-relay-receiver rs)
             (fn-bp-result-state (fn-bp-step (fn-relay-sender rs) event))
             (fn-relay-terms rs) (fn-relay-undertakings rs))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-relay-statep-components)
                 (:instance fn-bp-step-preserves-binding-state
                            (s (fn-relay-sender rs)))
                 (:instance fn-bp-step-preserves-node (s (fn-relay-sender rs)))
                 (:instance fn-relay-entries-backedp-step
                            (s (fn-relay-sender rs))
                            (entries (fn-bpr-state-receipts (fn-relay-receiver rs)))
                            (node (fn-relay-node rs))
                            (terms (fn-relay-terms rs))
                            (u (fn-relay-undertakings rs)))
                 (:instance fn-relay-entry-backedp-step
                            (s (fn-relay-sender rs))
                            (entry (fn-bpr-state-pending (fn-relay-receiver rs)))
                            (node (fn-relay-node rs))
                            (terms (fn-relay-terms rs))
                            (u (fn-relay-undertakings rs)))
                 (:instance fn-relay-undertakings-backedp-step
                            (s (fn-relay-sender rs))
                            (u (fn-relay-undertakings rs))))
           :in-theory (e/d (fn-relay-invp fn-relay-node)
                           (fn-relay-statep fn-bp-step fn-bp-result-state
                                            fn-bp-statep fn-bp-binding-statep
                                            fn-relay-entries-backedp
                                            fn-relay-entry-backedp
                                            fn-relay-undertakings-backedp
                                            fn-relay-terms-tablep
                                            fn-relay-undertaking-listp
                                            fn-relay-statep-components
                                            fn-bp-step-preserves-binding-state
                                            fn-bp-step-preserves-node
                                            fn-relay-entries-backedp-step
                                            fn-relay-entry-backedp-step
                                            fn-relay-undertakings-backedp-step)))))

(defthm fn-relay-sender-step-preserves-invp
  (implies (fn-relay-invp rs)
           (fn-relay-invp (car (fn-relay-sender-step rs event))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-relay-sender-step)
                                  (fn-relay-invp fn-bp-step fn-bp-result-state
                                                 fn-bp-result-effects
                                                 fn-relay-make-state)))))

; Accept changes only the receiver's contexts; a live receipt intent makes it
; refuse outright.
(defthm fn-relay-accept-request-receipts
  (equal (fn-bpr-state-receipts
          (car (cdr (fn-bpr-accept-request st store record request auth))))
         (fn-bpr-state-receipts st))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bpr-accept-request)
                                  (fn-bpr-statep fn-bpr-request-acceptablep
                                                 fn-bpr-context-from-request
                                                 fn-bpr-find-context
                                                 fn-bpr-find-context-msgid)))))

(defthm fn-relay-accept-request-pending
  (implies (null (fn-bpr-state-pending st))
           (null (fn-bpr-state-pending
                  (car (cdr (fn-bpr-accept-request st store record
                                                   request auth))))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bpr-accept-request)
                                  (fn-bpr-statep fn-bpr-request-acceptablep
                                                 fn-bpr-context-from-request
                                                 fn-bpr-find-context
                                                 fn-bpr-find-context-msgid)))))

(defthm fn-relay-accept-request-with-pending
  (implies (consp (fn-bpr-state-pending st))
           (equal (car (cdr (fn-bpr-accept-request st store record request auth)))
                  st))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bpr-accept-request)
                                  (fn-bpr-statep fn-bpr-request-acceptablep
                                                 fn-bpr-context-from-request
                                                 fn-bpr-find-context
                                                 fn-bpr-find-context-msgid)))))

(defthm fn-relay-accept-state-formula
  (equal (car (cdr (fn-relay-accept rs record request auth)))
         (fn-relay-make-state
          (fn-relay-store rs)
          (car (cdr (fn-bpr-accept-request (fn-relay-receiver rs)
                                           (fn-relay-store rs)
                                           record request auth)))
          (fn-relay-sender rs) (fn-relay-terms rs) (fn-relay-undertakings rs)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-relay-accept) (fn-bpr-accept-request)))))

(in-theory (disable fn-relay-accept))

(defthm fn-relay-accept-preserves-invp
  (implies (fn-relay-invp rs)
           (fn-relay-invp (car (cdr (fn-relay-accept rs record request auth)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-relay-statep-components)
                 (:instance fn-relay-accept-request-receipts
                            (st (fn-relay-receiver rs))
                            (store (fn-relay-store rs)))
                 (:instance fn-relay-accept-request-pending
                            (st (fn-relay-receiver rs))
                            (store (fn-relay-store rs)))
                 (:instance fn-relay-accept-request-with-pending
                            (st (fn-relay-receiver rs))
                            (store (fn-relay-store rs))))
           :cases ((consp (fn-bpr-state-pending (fn-relay-receiver rs))))
           :in-theory (e/d (fn-relay-invp fn-relay-node)
                           (fn-relay-statep fn-bpr-accept-request
                                            fn-bp-statep fn-bp-binding-statep
                                            fn-relay-entries-backedp
                                            fn-relay-entry-backedp
                                            fn-relay-undertakings-backedp
                                            fn-relay-terms-tablep
                                            fn-relay-undertaking-listp
                                            fn-relay-content-durablep
                                            fn-relay-terms-kind
                                            fn-relay-find-undertaking
                                            fn-relay-kindp fn-sn-node
                                            fn-bp-find-work
                                            fn-relay-statep-components
                                            fn-relay-accept-request-receipts
                                            fn-relay-accept-request-pending
                                            fn-relay-accept-request-with-pending)))))

(defthm fn-relay-record-undertaking-preserves-invp
  (implies (fn-relay-invp rs)
           (fn-relay-invp (fn-relay-record-undertaking rs upstream onward)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-relay-statep-components))
           :in-theory (e/d (fn-relay-invp fn-relay-record-undertaking
                                          fn-relay-onward-durablep
                                          fn-relay-undertakings-backedp
                                          fn-relay-undertaking-listp
                                          fn-relay-node)
                           (fn-relay-statep fn-bp-statep fn-bp-binding-statep
                                            fn-relay-entries-backedp
                                            fn-relay-entry-backedp
                                            fn-relay-terms-tablep
                                            fn-relay-content-durablep
                                            fn-bpr-find-context
                                            fn-relay-find-undertaking
                                            fn-bp-find-work
                                            fn-relay-statep-components)))))

; Preparing a receipt keeps the receiver's history and installs one pending
; entry whose context is the one found.
(defthm fn-relay-prepare-receipt-shape
  (implies (not (equal (fn-bpr-prepare-receipt st work-id receipt-id auth) st))
           (and (equal (fn-bpr-state-receipts
                        (fn-bpr-prepare-receipt st work-id receipt-id auth))
                       (fn-bpr-state-receipts st))
                (consp (fn-bpr-state-pending
                        (fn-bpr-prepare-receipt st work-id receipt-id auth)))
                (equal (fn-bpr-receipt-entry-context
                        (fn-bpr-state-pending
                         (fn-bpr-prepare-receipt st work-id receipt-id auth)))
                       (fn-bpr-find-context work-id (fn-bpr-state-contexts st)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bpr-prepare-receipt)
                                  (fn-bpr-statep fn-bpr-find-context
                                                 fn-bpr-find-receipt
                                                 fn-bpr-receipt-for
                                                 fn-bpa-receiptp)))))

(defthm fn-relay-undertake-preserves-invp
  (implies (fn-relay-invp rs)
           (fn-relay-invp (car (cdr (fn-relay-undertake rs upstream receipt-id auth)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-relay-statep-components)
                 (:instance fn-relay-prepare-receipt-shape
                            (st (fn-relay-receiver rs))
                            (work-id upstream))
                 (:instance fn-relay-find-context-work-id
                            (xs (fn-bpr-state-contexts (fn-relay-receiver rs)))))
           :in-theory (e/d (fn-relay-invp fn-relay-undertake
                                          fn-relay-entry-backedp
                                          fn-relay-onward-presentp
                                          fn-relay-node)
                           (fn-relay-statep fn-bp-statep fn-bp-binding-statep
                                            fn-relay-entries-backedp
                                            fn-relay-undertakings-backedp
                                            fn-relay-terms-tablep
                                            fn-relay-undertaking-listp
                                            fn-relay-content-durablep
                                            fn-relay-terms-kind
                                            fn-bpr-find-context
                                            fn-bpr-prepare-receipt
                                            fn-relay-find-undertaking
                                            fn-bp-find-work
                                            fn-relay-statep-components
                                            fn-relay-prepare-receipt-shape
                                            fn-relay-find-context-work-id)))))

(defthm fn-relay-commit-receipt-backing
  (implies (and (fn-relay-entries-backedp (fn-bpr-state-receipts st)
                                          node terms u works)
                (or (null (fn-bpr-state-pending st))
                    (and (consp (fn-bpr-state-pending st))
                         (fn-relay-entry-backedp (fn-bpr-state-pending st)
                                                 node terms u works))))
           (and (fn-relay-entries-backedp
                 (fn-bpr-state-receipts
                  (fn-bpr-commit-receipt st work-id receipt-id outcome))
                 node terms u works)
                (or (null (fn-bpr-state-pending
                           (fn-bpr-commit-receipt st work-id receipt-id outcome)))
                    (and (consp (fn-bpr-state-pending
                                 (fn-bpr-commit-receipt st work-id receipt-id outcome)))
                         (fn-relay-entry-backedp
                          (fn-bpr-state-pending
                           (fn-bpr-commit-receipt st work-id receipt-id outcome))
                          node terms u works)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bpr-commit-receipt fn-relay-entries-backedp)
                                  (fn-bpr-statep fn-relay-entry-backedp
                                                 fn-bpr-receipt-entry-context
                                                 fn-bpr-receipt-entry-receipt
                                                 fn-bpr-context-work-id
                                                 fn-bpa-receipt-id)))))

(defthm fn-relay-commit-receipt-preserves-invp
  (implies (fn-relay-invp rs)
           (fn-relay-invp (fn-relay-commit-receipt rs upstream receipt-id outcome)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-relay-statep-components)
                 (:instance fn-relay-commit-receipt-backing
                            (st (fn-relay-receiver rs))
                            (work-id upstream)
                            (node (fn-relay-node rs))
                            (terms (fn-relay-terms rs))
                            (u (fn-relay-undertakings rs))
                            (works (fn-bp-state-works (fn-relay-sender rs)))))
           :in-theory (e/d (fn-relay-invp fn-relay-commit-receipt fn-relay-node)
                           (fn-relay-statep fn-bp-statep fn-bp-binding-statep
                                            fn-relay-entries-backedp
                                            fn-relay-entry-backedp
                                            fn-relay-undertakings-backedp
                                            fn-relay-terms-tablep
                                            fn-relay-undertaking-listp
                                            fn-bpr-commit-receipt
                                            fn-relay-statep-components
                                            fn-relay-commit-receipt-backing)))))
