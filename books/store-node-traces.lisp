; fn: inductive mixed traces of the actual live node/file composition.
(in-package "ACL2")
(include-book "store-node-traces-prepare")
(include-book "store-node-invariants")
(include-book "topic-history-identity-disjoint")
(include-book "store-files-traces")
(include-book "records-seam")
(local (include-book "arithmetic/top" :dir :system))
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-shape-vocabulary)))

; The core definitions these correspondence proofs open (the core exports
; keystones only, docs/proof-style.md s2); local, named once.
(local (deftheory fn-snx-core-definitions
         (union-theories (union-theories '(fn-articlep fn-pendingp fn-statep fn-initial-state fn-install-pending
            fn-clear-pending fn-accept-prepare fn-accept-complete fn-accept-recover
            fn-pending-matchesp
            fn-retain-obligationp fn-retain-releasep fn-retain-statep
            fn-retain-initial-state fn-retain-admissiblep fn-retain-admit
            fn-retain-release
            fn-node-stagep fn-node-bindingp fn-node-statep fn-node-initial-state
            fn-node-pending-matchesp fn-node-prepare fn-node-complete fn-node-recover
            fn-replay-okp fn-replay-advance-okp fn-replay-advance-txid) (theory 'fn-acceptance-invariants-vocabulary)) (theory 'fn-node-invariants-vocabulary))))
; `fn-sn-identity-context' is withdrawn at store-node's export since
; 2026-09-23; the io-step proofs here carry it across `fn-sn-make-v2' by
; reading its two fields, so it stays open in this book as it was before.
(local (in-theory (e/d (fn-sn-statep fn-sn-initial fn-sn-pending-record
                        fn-sn-record-bindsp fn-sn-prepare
                        fn-sn-identity-context
                        fn-sn-completion-record fn-sn-completion-core-enabledp
                        fn-sn-finish fn-sn-file-step fn-sn-io fn-sn-crash
                        fn-sn-recover fn-sn-committed-recordp
                        fn-sf-phase-shapep fn-sf-initial-state
                        fn-sf-start-frontier fn-sf-frontier-file-result
                        fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                        fn-sf-history-recoverablep fn-sf-refuse-reservation
                        fn-sf-prepare-record fn-sf-record-file-result
                        fn-sf-prepublish-abort fn-sf-abort-completion
                        fn-sf-record-link-result fn-sf-record-dir-result
                        fn-sf-core-completion fn-sf-emit-success
                        fn-sf-lose-success fn-sf-crash-imagep fn-sf-crash
                        fn-sf-recover fn-sf-recovery-barrier
                        fn-replay-apply-record fn-replay-okp fn-replay-faultp
                        fn-replay-advance-okp fn-node-pending-matchesp
                        fn-store-files-invariants-vocabulary
                        fn-store-files-traces-vocabulary
                        fn-store-node-invariants-vocabulary)
                       (fn-node-statep fn-sf-statep fn-record-p
                        fn-node-prepare fn-node-complete fn-node-recover
                        fn-replay-advance-txid fn-replay fn-replay-loop
                        fn-sf-replay-node fn-sn-prepare-node
                        fn-sn-completion-enabledp
                        fn-retain-statep fn-node-initial-state
                         fn-state-next-txid
                          ))))

; Measured 2026-09-24 on persvati (REPL, whole book 18.3 s to 11.9 s):
; `fn-cp-idp-true-listp' is an unconditional-looking rewrite rule on
; `true-listp' that backchains into the consumer id's octet recognizer, and
; `fn-cp-id-length-bound' does the same on every `len' (40 759 tries of
; `fn-cp-idp' across this book, none needed); `fn-replay-identity-step' and
; the topic anchor recognizer split the preparation goals on arms they only
; carry.  A proof that reads one of them enables it in its hint.
(local (in-theory (disable fn-cp-idp-true-listp fn-cp-id-length-bound
                           fn-replay-identity-step fn-th-topic-v1-anchorp
                           fn-snt-history-recoverable-under-record-bound
                           fn-sn-new-success-requires-actual-matching-durable-node-completion)))

; The first part of this book is books/store-node-traces-prepare (split
; 2026-09-25, D26).  Its local theory above is restated; the local steps it
; used that the proofs below also use (read from the certify log's Rules and
; :use hints) are restated here, locally, unchanged.
(local (in-theory (disable fn-snt-relation-implies-structural-state)))
(local (in-theory (disable fn-sn-make-v6 fn-sn-make-v7)))
(local
 (defthm fn-snt-recoverable-frontier-is-natural
   (implies (fn-sf-history-recoverablep groups capacity history frontier)
            (natp frontier))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (fn-sf-history-recoverablep fn-node-statep
                                    fn-statep fn-snx-core-definitions)
                                   (fn-sf-replay-node))))))
(local
 (defthm fn-snt-store-event-nth-is-nth
   (implies (natp n)
            (equal (fn-store-event-nth n x) (nth n x)))
   :hints (("Goal" :induct (fn-store-event-nth n x)
            :in-theory (enable fn-store-event-nth nth)))))
(local
 (defthm fn-snt-topic-event-is-not-retention-event
   (implies (fn-th-topic-eventp event)
            (not (fn-store-retention-event-p event)))
   :hints (("Goal" :in-theory
            (e/d (fn-th-topic-eventp fn-store-retention-event-p
                   fn-th-local-admin-eventp fn-th-at fn-store-event-nth)
                 (fn-th-source-id-p fn-th-auth-ref-p
                  fn-th-exact-octets-p))))))
(local
 (defthm fn-snt-topic-event-is-not-consumer-event
   (implies (fn-th-topic-eventp event)
            (not (fn-cpe-eventp event)))
   :hints (("Goal" :in-theory
            (e/d (fn-th-topic-eventp fn-cpe-eventp
                   fn-th-local-admin-eventp fn-th-at)
                 (fn-th-source-id-p fn-th-auth-ref-p
                  fn-th-exact-octets-p))))))
(local
 (defthm fn-snt-topic-event-is-not-identity-event
   (implies (fn-th-topic-eventp event)
            (and (not (fn-stxe-p event))
                 (not (fn-stxk-p event))
                 (not (fn-stxa-p event))))
   :hints (("Goal" :in-theory
            (e/d (fn-th-topic-eventp fn-stxe-p fn-stxk-p fn-stxa-p
                   fn-stxe-shapep fn-stxk-shapep fn-stxa-shapep
                   fn-stxe-sequence fn-stxk-sequence fn-stxa-sequence
                   fn-th-local-admin-eventp fn-th-at)
                 (fn-th-source-id-p fn-th-auth-ref-p
                  fn-th-exact-octets-p))))))
(local
 (defthm fn-snt-store-event-fields-of-an-article-record
   (implies (fn-record-p record)
            (and (equal (fn-store-event-sequence record)
                        (fn-record-sequence record))
                 (equal (fn-store-event-txid record) (fn-record-txid record))
                 (equal (fn-store-event-generation record)
                        (fn-record-generation record))))
   :hints (("Goal" :in-theory (enable fn-store-event-sequence
                                      fn-store-event-txid
                                      fn-store-event-generation)))))
(local
 (defthm fn-snt-candidate-is-frontier-predecessor
   (implies (fn-sf-candidatep record records frontier)
            (equal (+ -1 frontier) (fn-store-event-txid record)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-sf-candidatep)
                                   (fn-sf-next-lower fn-record-p
                                    fn-store-event-p
                                    fn-record-sequence fn-record-txid
                                    fn-record-generation))))))
(local
 (defthm fn-snt-apply-record-of-a-retention-event
   (implies (fn-store-retention-event-p event)
            (equal (fn-replay-apply-record node event)
                   (fn-replay-apply-retention-event node event)))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-record)
                                   (fn-replay-apply-retention-event
                                    fn-replay-apply-identity-neutral
                                    fn-replay-composite-record
                                    fn-replay-advance-txid
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary
                                    fn-store-event-p fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p))))))

(defthm fn-snt-prepare-consumer-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
    :cases ((and (fn-sn-statep s)
                 (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                 (fn-cpe-eventp event)
                 (eq (car (fn-cpe-projection-step
                           (fn-sn-consumer s) event
                           (fn-sn-identity-next s))) :ok)
                 (consp (fn-replay-apply-record (fn-sn-node s) event))
                 (equal (fn-sf-phase (fn-sf-prepare-record
                                      (fn-sn-files s) event
                                      (fn-sn-groups s) (fn-sn-capacity s)))
                        :record-staged)))
    :in-theory (e/d (fn-sf-prepare-record fn-sn-prepare-consumer)
                    (fn-sn-statep fn-sn-record-bindsp fn-sf-history-recoverablep
                     fn-sn-completion-enabledp fn-sn-completion-record
                     fn-sf-recover fn-sf-record-listp
                     fn-replay-apply-record fn-replay-apply-retention-event
                     fn-replay-apply-identity-neutral fn-replay-composite-record
                     fn-replay-identity-step fn-cpe-projection-step
                     fn-snt-completion-linkp
                     fn-record-shape-vocabulary fn-record-record-vocabulary
                     fn-store-event-p fn-store-retention-event-p
                     fn-stxe-p fn-stxk-p fn-stxa-p fn-cpe-eventp
                     fn-th-topic-eventp fn-th-prefix-step)))
          ("Subgoal 1"
    :use (fn-sn-prepare-consumer-preserves-state
          fn-snt-topic-event-is-not-consumer-event
          (:instance fn-snt-an-article-record-is-no-other-store-event
            (record event))
          (:instance fn-snt-candidate-is-frontier-predecessor
            (record event)
            (records (fn-sf-records (fn-sn-files s)))
            (frontier (fn-sf-frontier (fn-sn-files s))))
          (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
          (:instance fn-snt-deferred-preparation-outcome
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (history (fn-sf-records (fn-sn-files s)))
            (txid (+ -1 (fn-sf-frontier (fn-sn-files s)))))))))

(defthm fn-snt-prepare-topic-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-prepare-topic s event)))
  :hints (("Goal"
    :cases ((and (fn-sn-statep s)
                 (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                 (fn-th-topic-eventp event)
                 (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) event)) :ok)
                 (consp (fn-replay-apply-record (fn-sn-node s) event))
                 (equal (fn-sf-phase (fn-sf-prepare-record
                                      (fn-sn-files s) event
                                      (fn-sn-groups s) (fn-sn-capacity s)))
                        :record-staged)))
    :in-theory (e/d (fn-sf-prepare-record fn-sn-prepare-topic)
                    (fn-sn-statep fn-sn-record-bindsp fn-sf-history-recoverablep
                     fn-sn-completion-enabledp fn-sn-completion-record
                     fn-sf-recover fn-sf-record-listp
                     fn-replay-apply-record fn-replay-apply-retention-event
                     fn-replay-apply-identity-neutral fn-replay-composite-record
                     fn-th-prefix-step
                     fn-snt-completion-linkp
                     fn-record-shape-vocabulary fn-record-record-vocabulary
                     fn-store-event-p fn-store-retention-event-p
                     fn-stxe-p fn-stxk-p fn-stxa-p fn-cpe-eventp
                     fn-th-topic-eventp fn-th-local-admin-eventp)))
          ("Subgoal 1"
    :use (fn-sn-prepare-topic-preserves-state
          fn-snt-topic-event-is-not-retention-event
          fn-snt-topic-event-is-not-consumer-event
          fn-snt-topic-event-is-not-identity-event
          (:instance fn-snt-an-article-record-is-no-other-store-event
            (record event))
          (:instance fn-snt-candidate-is-frontier-predecessor
            (record event)
            (records (fn-sf-records (fn-sn-files s)))
            (frontier (fn-sf-frontier (fn-sn-files s))))
          (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
          (:instance fn-snt-deferred-preparation-outcome
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (history (fn-sf-records (fn-sn-files s)))
            (txid (+ -1 (fn-sf-frontier (fn-sn-files s)))))))))

; File stages that do not publish a record retain the same live proposal.
(defthm fn-snt-start-frontier-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :start-frontier result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :start-frontier)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-frontier-file-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :frontier-file result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :frontier-file)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-frontier-replace-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :frontier-replace result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :frontier-replace)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-frontier-directory-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :frontier-directory result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :frontier-directory))
                        (:instance fn-snt-typed-frontier-phase (files (fn-sn-files s)))
                        (:instance fn-snt-typed-frontier-natural (files (fn-sn-files s)))
                        (:instance fn-snt-history-recoverable-monotone
                          (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                          (records (fn-sf-records (fn-sn-files s)))
                          (first (fn-sf-frontier (fn-sn-files s)))
                          (second (1+ (fn-sf-frontier (fn-sn-files s))))))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-record-file-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :record-file result)))
  ; The staged candidate, the durable history and the frontier are all
  ; carried over, so whichever of the two links the state was on it is on
  ; after.  Both stay open for that and the codec stays closed.
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :record-file)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-completion-enabledp
                               fn-snt-completion-linkp
                     fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-replay-identity-step))))

(defthm fn-snt-record-link-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :record-link result)))
  ; The staged candidate, the durable history and the frontier are all
  ; carried over, so whichever of the two links the state was on it is on
  ; after.  Both stay open for that and the codec stays closed.
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :record-link)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-completion-enabledp
                               fn-snt-completion-linkp
                     fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-replay-identity-step))))

; This is the step that publishes the candidate and enters `:completing', so
; it is the step that owes the completing arm's article conjunct.  It owes it
; because `6ab2c783' and `4bb7bb3d' gave `fn-sn-completion-enabledp' a
; retention arm and an identity arm: with the candidate's kind unknown the
; goal reduced to `(NOT (FN-STORE-RETENTION-EVENT-P (FN-SF-RECORD-CANDIDATE
; (FN-SN-FILES S))))' and the book stopped there (hbox
; certify-20260922T114635Z-2909699).  The candidate's kind is not unknown: in
; a record phase the relation carries `fn-sn-record-bindsp' of it, which is
; `fn-snt-bound-record-is-an-article-record' above, and an article record is
; none of the other four store events by length
; (`fn-snt-an-article-record-is-no-other-store-event').  Those two are what
; dismiss the two new arms and establish the conjunct, and the published
; completion record is the candidate itself
; (`fn-snt-find-published-candidate').
(defthm fn-snt-record-directory-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :record-directory result)))
  ; Only the observed durable directory in :record-attempted publishes
  ; anything; every other case leaves the files, history and node as they
  ; were, or fences the record.  The instances about the published
  ; candidate belong to that one case, and given to the whole goal they
  ; were carried through all 286 cases of its first split (9110 subgoals,
  ; 34.2 s on the seam run of 2026-09-23;
  ; planning/evidence/chain-remainder-cost-2026-09-23.md).  So the goal is
  ; split on that case, and Subgoal 1, where it holds, alone gets them.
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                   (operation :record-directory)))
           :cases ((and (fn-sn-statep s)
                       (equal (fn-sf-phase (fn-sn-files s)) :record-attempted)
                       (equal result :ok)))
           ; The five event recognizers and the three appliers stay closed,
           ; as they do in books/replay and books/store-node-invariants for
           ; the same reason: this goal DISPATCHES on the candidate's kind and
           ; does not look inside it, and with them open the two `cond's --
           ; `fn-store-event-p' under `fn-sf-candidatep' and
           ; `fn-sn-completion-enabledp' over the completion record -- unfold
           ; the record and statement codecs, which split Goal'' into 4970
           ; subgoals, the first of those into 4803, and exhaust the control
           ; stack (hbox certify-20260922T122534Z-2932993).  The instance of
           ; the disjointness lemma above supplies the four negations against
           ; the closed terms.
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-find-record
                               fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-replay-identity-step))
          ("Subgoal 1" :use ((:instance fn-snt-typed-record-phase (files (fn-sn-files s)))
                        (:instance fn-snt-advance-that-lands-was-not-past-it
                          (node (fn-sn-node s))
                          (k (fn-store-event-txid
                              (fn-sf-record-candidate (fn-sn-files s)))))
                        (:instance fn-snt-an-article-record-is-no-other-store-event
                          (record (fn-sf-record-candidate (fn-sn-files s))))
                        (:instance fn-snt-bound-record-is-an-article-record
                          (node (fn-sn-node s))
                          (record (fn-sf-record-candidate (fn-sn-files s))))
                        (:instance fn-snt-find-published-candidate
                          (files (fn-sn-files s))
                          (record (fn-sf-record-candidate (fn-sn-files s))))))))

(defthm fn-snt-recovery-barrier-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :recovery-barrier result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :recovery-barrier)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-finish-image
  (implies (fn-sn-completion-enabledp s)
           (and (equal (fn-sf-phase (fn-sn-files (fn-sn-finish s))) :ready)
                (equal (fn-sf-records (fn-sn-files (fn-sn-finish s)))
                       (fn-sf-records (fn-sn-files s)))
                (equal (fn-sf-frontier (fn-sn-files (fn-sn-finish s)))
                       (fn-sf-frontier (fn-sn-files s)))
                (equal (fn-sn-groups (fn-sn-finish s)) (fn-sn-groups s))
                (equal (fn-sn-capacity (fn-sn-finish s)) (fn-sn-capacity s))))
  ; `fn-store-event-sequence' and `fn-store-event-txid', not the article
  ; accessors: `6ab2c783' changed the pair `fn-sn-finish' hands
  ; `fn-sf-core-completion' to the composed ones, so the instance this proof
  ; supplied was about a different file step and its hypothesis reached the
  ; goal as `(CONS (CAR record) (CADR record))' against a `:completing' state
  ; whose completion pair is the composed one (hbox
  ; certify-20260922T123415Z-2939324).  All three arms of `fn-sn-finish' hand
  ; the same file state on, so the image is one equation and not three; the
  ; recognizers and appliers stay closed because nothing here looks inside
  ; the record.
  :hints (("Goal"
           :use ((:instance fn-sf-core-completion-preserves-state
                    (s (fn-sn-files s))
                    (sequence (fn-store-event-sequence (fn-sn-completion-record s)))
                    (txid (fn-store-event-txid (fn-sn-completion-record s)))))
           :in-theory (e/d (fn-sn-completion-enabledp)
                           (fn-sn-record-bindsp fn-sn-completion-record
                               fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-sn-identity-context
                               fn-replay-identity-step)))))

; The node the OTHER two arms of `fn-sn-finish' publish.  `6ab2c783' and
; `4bb7bb3d' added them and no theorem said what they produce;
; `fn-sn-finish-is-actual-durable-completion' (books/store-node-invariants)
; is the article arm's equation and names its arm, so this is the rest of the
; dispatch.  The hypothesis is enough to select them: on the remaining arm
; `fn-sn-completion-enabledp' demands `fn-sn-record-bindsp' of the completion
; record, which is `fn-record-p' of it.
(defthm fn-snt-finish-is-the-applied-event
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-record-p (fn-sn-completion-record s))))
           (equal (fn-sn-node (fn-sn-finish s))
                  (fn-replay-apply-record (fn-sn-node s)
                                          (fn-sn-completion-record s))))
  :hints (("Goal"
           :use ((:instance fn-snt-bound-record-is-an-article-record
                   (node (fn-sn-node s))
                   (record (fn-sn-completion-record s))))
           :in-theory (e/d (fn-sn-finish fn-sn-completion-enabledp)
                           (fn-sn-completion-record fn-sn-record-bindsp
                            fn-record-shape-vocabulary
                            fn-record-record-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p fn-th-topic-eventp
                            fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-replay-apply-identity-neutral
                            fn-replay-composite-record
                            fn-replay-identity-step fn-sn-identity-context
                            fn-sn-accepted-delta fn-sn-composite-delta
                            fn-node-complete
                            fn-sf-core-completion fn-sf-emit-success)))))

; `fn-sn-finish-is-actual-durable-completion' (books/store-node-invariants)
; names the arm it is about: since `6ab2c783' and `4bb7bb3d' the node
; `fn-sn-finish' publishes is the durable completion only when the completion
; record is an article record.  The completing arm of the relation carries
; exactly that, and the disjointness lemma turns it into the four negative
; hypotheses that theorem asks for; the other arm is the equation above.
(defthm fn-snt-finish-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-finish s)))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-preserves-state fn-snt-finish-image
                 fn-sn-finish-is-actual-durable-completion
                 fn-snt-finish-is-the-applied-event
                 fn-sn-finish-disabled-is-no-op
                 (:instance fn-snt-an-article-record-is-no-other-store-event
                   (record (fn-sn-completion-record s))))
           ; Closed for the same reason as the directory step above: this
           ; goal dispatches on the completion record's kind through
           ; `fn-sn-completion-enabledp' and never looks inside it.
           :in-theory (e/d (fn-sn-completion-enabledp)
                           (fn-sn-finish fn-sn-statep fn-sn-record-bindsp
                               fn-sf-history-recoverablep fn-snt-pending-linkp fn-snt-deferred-linkp
                               fn-sn-completion-record
                               fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-sn-identity-context
                               fn-replay-identity-step)))))

(defthm fn-snt-crash-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal"
    :use (fn-sn-crash-preserves-state
          (:instance fn-snt-typed-frontier-phase (files (fn-sn-files s)))
                        (:instance fn-snt-typed-frontier-natural (files (fn-sn-files s)))
          (:instance fn-snt-history-recoverable-monotone
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (records (fn-sf-records (fn-sn-files s)))
            (first (fn-sf-frontier (fn-sn-files s)))
            (second (1+ (fn-sf-frontier (fn-sn-files s))))))
    :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                        fn-sn-record-bindsp fn-sn-completion-enabledp
                        fn-snt-completion-linkp
                     fn-record-shape-vocabulary
                        fn-store-event-p fn-store-retention-event-p
                        fn-stxe-p fn-stxk-p fn-stxa-p fn-th-topic-eventp
                        fn-replay-apply-record
                        fn-replay-apply-retention-event
                        fn-replay-apply-identity-neutral
                        fn-replay-composite-record
                        fn-replay-identity-step))))

; Two arms since `40bb3f74', and the relation now has a case for each.  A
; related `:replaying' state has a recoverable history, so `fn-sf-recover'
; reaches `:recovering' over the same records and frontier; whether
; `fn-sn-recover' then publishes that phase or the `:fault' one turns on the
; identity replay alone, and on the fault arm it keeps those records and that
; frontier and does not touch the node.
(defthm fn-snt-recover-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-recover s)))
  :hints (("Goal" :use fn-sn-recover-preserves-state
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-completion-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp
                               fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-sn-identity-context fn-replay-identity-step))))

; -by-definition: the otherwise branch of fn-sn-file-step.
(defthm fn-snt-unknown-io-is-no-op
  (implies (not (member-equal operation
                  '(:start-frontier :frontier-file :frontier-replace
                    :frontier-directory :record-file :record-link
                    :record-directory :recovery-barrier)))
           (equal (fn-sn-io s operation result) s))
  :rule-classes nil
  :hints (("Goal" :use (fn-snt-state-reconstruction)
           :in-theory (disable fn-sn-statep))))

(defthm fn-snt-io-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s operation result)))
  :hints (("Goal"
    :cases ((equal operation :start-frontier) (equal operation :frontier-file)
            (equal operation :frontier-replace) (equal operation :frontier-directory)
            (equal operation :record-file) (equal operation :record-link)
            (equal operation :record-directory) (equal operation :recovery-barrier))
    :use fn-snt-unknown-io-is-no-op
    :in-theory (disable fn-snt-relation fn-sn-io))))

; Events are already-decoded logical data, never a raw external reader format.
; This dispatcher simply selects the actual wrapper operations.  It does not
; inspect the relation of the result, roll back failed proof checks, or assume
; that a trace preserves any invariant.
(defun fn-snt-step (s event)
  (case (car event)
    (:prepare (fn-sn-prepare s (cadr event)))
    (:io (fn-sn-io s (cadr event) (caddr event)))
    (:finish (fn-sn-finish s))
    (:crash (fn-sn-crash s (cadr event) (caddr event)))
    (:recover (fn-sn-recover s))
    (otherwise s)))
(defun fn-snt-run (s events)
  (if (consp events)
      (fn-snt-run (fn-snt-step s (car events)) (cdr events))
    s))

(defthm fn-snt-step-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-snt-step s event)))
  :hints (("Goal" :in-theory (disable fn-snt-relation fn-sn-prepare fn-sn-io
                      fn-sn-finish fn-sn-crash fn-sn-recover))))

(defthm fn-snt-mixed-trace-preserves-live-history-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-snt-run s events)))
  :hints (("Goal" :induct (fn-snt-run s events)
           :in-theory (disable fn-snt-relation fn-snt-step))))

(defthm fn-snt-initialized-mixed-trace-has-live-history-relation
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups) (natp capacity))
           (fn-snt-relation (fn-snt-run (fn-sn-initial groups capacity) events)))
  :hints (("Goal" :in-theory (disable fn-snt-relation fn-snt-run fn-sn-initial))))

; Isolate the one relation arm used by the public exact-replay claim.  The
; other arms contain record codecs and replay steps irrelevant to an idle
; phase; opening them in the final theorem makes a simple projection costly.
(local
 (defthm fn-snt-ready-or-recovered-phase-is-idle
   (implies (member-equal phase '(:ready :recovering :fenced-recovery))
            (fn-snt-idle-phasep phase))
   :hints (("Goal" :in-theory (enable fn-snt-idle-phasep)))))

(local
 (defthm fn-snt-idle-relation-node-is-exact-replay
   (implies (and (fn-snt-relation s)
                 (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files s))))
            (equal (fn-sn-node s)
                   (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                      (fn-sf-records (fn-sn-files s))
                                      (fn-sf-frontier (fn-sn-files s)))))
   :hints (("Goal" :in-theory '(fn-snt-relation)))))

(defthm fn-snt-ready-or-recovered-node-is-exact-replay
  (implies (and (fn-snt-relation s)
                (member-equal (fn-sf-phase (fn-sn-files s))
                              '(:ready :recovering :fenced-recovery)))
           (equal (fn-sn-node s)
                  (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                     (fn-sf-records (fn-sn-files s))
                                     (fn-sf-frontier (fn-sn-files s)))))
  :hints (("Goal" :use ((:instance fn-snt-ready-or-recovered-phase-is-idle
                        (phase (fn-sf-phase (fn-sn-files s))))
                         fn-snt-idle-relation-node-is-exact-replay)
           :in-theory nil)))

(defthm fn-snt-mixed-trace-ready-node-is-exact-replay
  (let ((final (fn-snt-run s events)))
    (implies (and (fn-snt-relation s)
                  (member-equal (fn-sf-phase (fn-sn-files final))
                                '(:ready :recovering :fenced-recovery)))
             (equal (fn-sn-node final)
                    (fn-sf-replay-node (fn-sn-groups final) (fn-sn-capacity final)
                      (fn-sf-records (fn-sn-files final))
                      (fn-sf-frontier (fn-sn-files final))))))
  :hints (("Goal" :use ((:instance fn-snt-ready-or-recovered-node-is-exact-replay
                                   (s (fn-snt-run s events))))
           :in-theory (disable fn-snt-relation fn-snt-run))))

(defthm fn-snt-step-success-history-monotone
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-successes (fn-sn-files s))
                          (fn-sf-successes (fn-sn-files (fn-snt-step s event)))))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-acknowledges-exact-pair
                 fn-sn-finish-disabled-is-no-op
                 (:instance fn-sf-state-successes-are-true-list (s (fn-sn-files s))))
           :in-theory (disable fn-sn-prepare fn-sn-io fn-sn-finish fn-sn-crash
             fn-sn-recover fn-sn-completion-enabledp 
              fn-sf-prefixp fn-snt-relation))))

(defthm fn-snt-related-successes-true-list
  (implies (fn-snt-relation s)
           (true-listp (fn-sf-successes (fn-sn-files s))))
  :hints (("Goal" :use (fn-snt-relation-implies-structural-state
                         fn-snt-typed-store-components
                         (:instance fn-sf-state-successes-are-true-list
                          (s (fn-sn-files s))))
           :in-theory (disable fn-snt-relation fn-sn-statep))))

(defthm fn-snt-mixed-trace-success-history-monotone
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-successes (fn-sn-files s))
                          (fn-sf-successes (fn-sn-files (fn-snt-run s events)))))
  :hints (("Goal" :induct (fn-snt-run s events)
           :in-theory (disable fn-snt-relation fn-snt-step 
                                fn-sf-prefixp))
          ("Subgoal *1/1" :use ((:instance fn-sf-prefixp-transitive
                                 (xs (fn-sf-successes (fn-sn-files s)))
                                 (ys (fn-sf-successes (fn-sn-files (fn-snt-step s (car events)))))
                                 (zs (fn-sf-successes (fn-sn-files (fn-snt-run
                                       (fn-snt-step s (car events)) (cdr events))))))))))

; Prior acknowledged pairs survive arbitrary mixed wrapper traces.  Whenever
; the final live node is ready/recovered it equals replay of precisely this
; surviving history, rather than an independently trusted completion cache.
(defthm fn-snt-acknowledged-history-retained-through-mixed-trace
  (let ((final (fn-snt-run s events)))
    (implies (and (fn-snt-relation s)
                  (member-equal pair (fn-sf-successes (fn-sn-files s))))
             (and (member-equal pair (fn-sf-successes (fn-sn-files final)))
                  (fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files final))))))
  :hints (("Goal"
    :use (fn-snt-mixed-trace-success-history-monotone
          fn-snt-mixed-trace-preserves-live-history-relation
          (:instance fn-snt-relation-implies-structural-state (s (fn-snt-run s events)))
          (:instance fn-snt-typed-store-components (s (fn-snt-run s events)))
          (:instance fn-sf-state-success-member-has-record
            (s (fn-sn-files (fn-snt-run s events))))
          (:instance fn-sf-member-preserved-by-prefix
            (x pair) (xs (fn-sf-successes (fn-sn-files s)))
            (ys (fn-sf-successes (fn-sn-files (fn-snt-run s events))))))
    :in-theory (disable fn-snt-run fn-snt-relation 
                          fn-sf-record-has-pairp))))

; -----------------------------------------------------------------------------
; Stable records only grow along composed traces.  These footprint theorems
; carry the kernel's record prefix through every composed operation, so a
; record present when a process reopens remains present for the rest of that
; process (used across the reopen boundary by store-observed.lisp).

(defthm fn-snt-prepare-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-prepare s record)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare fn-sn-update )
                                  (fn-sn-statep fn-sn-record-bindsp
                                   fn-sf-prepare-record )))))

; The same of the two deferred preparations (`6ab2c783', `4bb7bb3d'): they
; stage through the same `fn-sf-prepare-record', which publishes nothing.
(defthm fn-snt-prepare-retention-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-prepare-retention s event)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare-retention fn-sn-update)
                                  (fn-sn-statep fn-sf-prepare-record
                                   fn-replay-apply-retention-event
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-snt-prepare-identity-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-prepare-identity s event)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare-identity fn-sn-update)
                                  (fn-sn-statep fn-sf-prepare-record
                                   fn-replay-apply-record
                                   fn-replay-identity-step
                                   fn-sn-identity-context
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-snt-prepare-consumer-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-prepare-consumer s event)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare-consumer fn-sn-update)
                                  (fn-sn-statep fn-sf-prepare-record
                                   fn-replay-apply-record
                                   fn-cpe-projection-step
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-cpe-eventp)))))

; The event-index update on a successful record-directory observation changes
; only the derived index.  Project files before proving the file-kernel prefix
; property, so this proof never opens the index insertion or its bounds codec.
(local
 (defthm fn-snt-files-of-io
   (equal (fn-sn-files (fn-sn-io s operation result))
          (if (fn-sn-statep s)
              (fn-sn-file-step (fn-sn-files s) operation result)
            (fn-sn-files s)))
   :hints (("Goal"
            :in-theory '(fn-sn-io
                         fn-sn-files-of-fn-sn-update
                         fn-sn-files-of-fn-sn-with-event-index)))))

(defthm fn-snt-io-records-prefix
  (implies (fn-sn-statep s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-sn-io s operation result)))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                 (:instance fn-sf-stable-records-prefix-of-record-dir-result
                            (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-file-step)
                           (fn-sn-statep fn-sf-statep  fn-sf-prefixp
                            fn-sn-io fn-sn-update fn-sn-with-event-index
                            fn-cei-put fn-cp-uintp
                            fn-sf-start-frontier fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result fn-sf-recovery-barrier)))))

; The three arms `6ab2c783' and `4bb7bb3d' gave `fn-sn-finish' hand the same
; file state on, so this is still one equation; the recognizers and the
; identity step stay closed so the dispatch does not unfold the codec under
; it.
(local
 (defthm fn-snt-files-of-with-topic
   (equal (fn-sn-files (fn-sn-with-topic s topic)) (fn-sn-files s))
   :hints (("Goal" :in-theory
            '(fn-sn-with-topic fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-with-consumer
   (equal (fn-sn-files (fn-sn-with-consumer s consumer)) (fn-sn-files s))
   :hints (("Goal" :in-theory
            '(fn-sn-with-consumer fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-advance-identity-next
   (equal (fn-sn-files (fn-sn-advance-identity-next s)) (fn-sn-files s))
   :hints (("Goal" :in-theory
            '(fn-sn-advance-identity-next fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-update-indexed
   (equal (fn-sn-files (fn-sn-update-indexed s files node index)) files)
   :hints (("Goal" :in-theory
            '(fn-sn-update-indexed fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-update-accepted
   (equal (fn-sn-files (fn-sn-update-accepted
                         s files node index msgid verdict)) files)
   :hints (("Goal" :in-theory
            '(fn-sn-update-accepted fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-finish-identity
   (equal (fn-sn-files (fn-sn-finish-identity s files record node)) files)
   :hints (("Goal" :in-theory
            '(fn-sn-finish-identity fn-sn-files-of-fn-sn-make-v6)))))

(defthm fn-snt-finish-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-finish s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory
           '(fn-sn-finish
             fn-snt-files-of-with-topic fn-snt-files-of-with-consumer
             fn-snt-files-of-advance-identity-next
             fn-snt-files-of-update-indexed fn-snt-files-of-update-accepted
             fn-snt-files-of-finish-identity
             fn-sf-records-of-core-completion fn-sf-records-of-emit-success))))

(defthm fn-snt-crash-records-prefix
  (implies (fn-sn-statep s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records
                           (fn-sn-files (fn-sn-crash s frontier-choice record-choice)))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                 (:instance fn-sf-stable-records-prefix-of-crash (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-crash fn-sn-update )
                           (fn-sn-statep fn-sf-statep  fn-sf-prefixp
                            fn-sf-crash fn-sf-crash-choicep)))))

(defthm fn-snt-recover-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-recover s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-recover fn-sn-update )
                                  (fn-sn-statep  fn-sf-recover
                                   fn-sf-replay-node)))))

(defthm fn-snt-related-records-true-list
  (implies (fn-snt-relation s)
           (true-listp (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :use (fn-snt-relation-implies-structural-state
                         fn-snt-typed-store-components
                         (:instance fn-sf-state-records-are-true-list
                          (s (fn-sn-files s))))
           :in-theory (disable fn-snt-relation fn-sn-statep))))

(defthm fn-snt-step-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snt-step s event)))))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-snt-related-records-true-list
                 (:instance fn-snt-io-records-prefix
                            (operation (cadr event)) (result (caddr event)))
                 (:instance fn-snt-crash-records-prefix
                            (frontier-choice (cadr event)) (record-choice (caddr event))))
           :in-theory (e/d (fn-snt-step)
                           (fn-snt-relation fn-sn-statep fn-sn-prepare fn-sn-io
                            fn-sn-finish fn-sn-crash fn-sn-recover 
                             fn-sf-prefixp
                            fn-snt-io-records-prefix fn-snt-crash-records-prefix)))))

(defthm fn-snt-mixed-trace-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snt-run s events)))))
  :hints (("Goal" :induct (fn-snt-run s events)
           :in-theory (disable fn-snt-relation fn-snt-step 
                                fn-sf-prefixp))
          ("Subgoal *1/1" :use ((:instance fn-sf-prefixp-transitive
                                 (xs (fn-sf-records (fn-sn-files s)))
                                 (ys (fn-sf-records (fn-sn-files (fn-snt-step s (car events)))))
                                 (zs (fn-sf-records (fn-sn-files (fn-snt-run
                                       (fn-snt-step s (car events)) (cdr events))))))))))

; An admissible crash image of a related live state is replayable at its own
; frontier.  This is the fact that lets the observed reopen path succeed on
; every image the platform may leave behind (A-DURABILITY as hypothesis).
(defthm fn-snt-admissible-crash-image-is-recoverable
  (implies (and (fn-snt-relation s)
                (fn-sf-crash-imagep (fn-sn-files s) frontier records))
           (fn-sf-history-recoverablep (fn-sn-groups s) (fn-sn-capacity s)
                                       records frontier))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 (:instance fn-snt-crash-preserves-relation
                            (frontier-choice
                             (fn-sf-image-frontier-choice (fn-sn-files s) frontier))
                            (record-choice
                             (fn-sf-image-record-choice (fn-sn-files s) records)))
                 (:instance fn-snt-relation-implies-structural-state
                            (s (fn-sn-crash s
                                 (fn-sf-image-frontier-choice (fn-sn-files s) frontier)
                                 (fn-sf-image-record-choice (fn-sn-files s) records)))))
           :in-theory (e/d (fn-snt-relation)
                           (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                            fn-sf-replay-node fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp
                            fn-sn-completion-enabledp
                            fn-sn-completion-core-enabledp fn-snt-idle-phasep
                            fn-sf-record-phasep fn-sn-crash fn-sf-crash
                            fn-sf-crash-imagep fn-sf-image-frontier-choice
                            fn-sf-image-record-choice  
                              
                             
                            fn-snt-crash-preserves-relation)))))

; The PLATFORM twin (D14-b, and K2f).  Every image the platform may leave --
; the two namespace choices, the record rollback and the frontier rollback --
; is replayable at its own frontier, so the observed reopen path succeeds on
; all of them.  The reliance-predicate theorem above is UNCHANGED and is this
; one's special case (fn-sf-crash-imagep-implies-recovery-crash-imagep); the
; host's reopen gate (fn-own-reopen, owner.lisp:911) still takes the narrow
; premise, which is the whole of D14-b.
;
; The record arm is fn-snt-history-recoverable-of-but-last.  The frontier arm
; is fn-snt-history-recoverable-under-record-bound at the rolled-back value,
; and its fn-sf-record-listp hypothesis is exactly the gate that
; fn-sf-frontier-rollback-visiblep carries -- the same conjunct that makes
; the rolled-back image a kernel state makes it replayable.
(defthm fn-snt-recovery-admissible-crash-image-is-recoverable
  (implies (and (fn-snt-relation s)
                (fn-sf-recovery-crash-imagep (fn-sn-files s) frontier records))
           (fn-sf-history-recoverablep (fn-sn-groups s) (fn-sn-capacity s)
                                       records frontier))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-snt-typed-store-components
                 fn-snt-related-records-true-list
                 fn-snt-admissible-crash-image-is-recoverable
                 (:instance fn-snt-admissible-crash-image-is-recoverable
                            (frontier (fn-sf-frontier (fn-sn-files s)))
                            (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-snt-recoverable-prefix-facts
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (history (fn-sf-records (fn-sn-files s)))
                            (frontier (fn-sf-frontier (fn-sn-files s))))
                 (:instance fn-snt-history-recoverable-of-but-last
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (records (fn-sf-records (fn-sn-files s)))
                            (frontier (fn-sf-frontier (fn-sn-files s))))
                 (:instance fn-snt-history-recoverable-under-record-bound
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (records (fn-sf-records (fn-sn-files s)))
                            (bound (1- (fn-sf-frontier (fn-sn-files s)))))
                 ; cited by :use and not left to forward chaining: the
                 ; trigger (fn-sf-frontier-rollback-visiblep ...) only
                 ; appears once fn-sf-recovery-crash-imagep opens during
                 ; this goal's own simplification, which is after forward
                 ; chaining has run.
                 (:instance fn-sf-frontier-rollback-visiblep-unfolds
                            (s (fn-sn-files s))))
           ; fn-sf-crash-imagep stays OPEN (the book's default): the
           ; identity image of a related state is admissible by it, and that
           ; instance of the narrow theorem is what the two rollback arms
           ; are then derived from.
           :in-theory (e/d (fn-sf-recovery-crash-imagep fn-sf-crash-imagep)
                           (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                            fn-sf-replay-node fn-sf-record-listp
                            fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-snt-idle-phasep
                            fn-sn-completion-enabledp
                            fn-sn-completion-core-enabledp fn-sf-record-phasep
                            fn-sn-crash fn-sf-crash
                            fn-sf-image-frontier-choice fn-sf-image-record-choice
                            fn-snt-relation-implies-structural-state
                            fn-snt-typed-store-components
                            fn-snt-related-records-true-list
                            fn-snt-admissible-crash-image-is-recoverable
                            fn-snt-recoverable-prefix-facts
                            fn-snt-history-recoverable-of-but-last
                            fn-snt-history-recoverable-under-record-bound
                            fn-sf-frontier-rollback-visiblep-unfolds)))))

; -----------------------------------------------------------------------------
; Export theory.  Withdrawn: the relation and its two links (proof relations,
; never executed), the dispatcher, and under a name the typed, footprint and
; canonical-preparation lemmas.  Enabled on include: the
; relation keystones (initial, preserved by every step, mixed traces), the
; exact-replay and acknowledged-history keystones, fn-snt-run and the two
; typed-list facts.
(deftheory fn-store-node-traces-vocabulary
  '(fn-snt-recoverable-prefix-facts fn-snt-prepare-replayed-node
    fn-snt-canonical-preparation-advance-ok fn-snt-canonical-preparation-outcomes
    fn-snt-record-counters-natural fn-snt-state-reconstruction
    fn-snt-typed-frontier-phase fn-snt-typed-frontier-natural
    fn-snt-typed-record-phase fn-snt-record-pair-after-prefix-absent
    fn-snt-find-record-append-absent fn-snt-find-published-candidate
    fn-snt-bound-record-is-matching-proposal
    fn-snt-bound-record-is-an-article-record
    fn-snt-an-article-record-is-no-other-store-event fn-snt-finish-image
    fn-snt-prepare-keeps-records
    fn-snt-prepare-retention-keeps-records
    fn-snt-prepare-identity-keeps-records fn-snt-io-records-prefix
    fn-snt-finish-keeps-records fn-snt-crash-records-prefix
    fn-snt-recover-keeps-records))
(in-theory (disable fn-store-node-traces-vocabulary
                    fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp
                    fn-snt-relation fn-snt-step))
