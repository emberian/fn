; fn: correspondence for the served store prepare projection.
;
; `fn-sn-prepare' is the logical specification.  Its file-side gate replays
; the complete durable history plus the candidate, which is the right
; independent check for a bare file state and the wrong cost for a live
; composed state whose node already corresponds to that history.
;
; This book supplies the executable projection used by the host.  It does not
; execute `fn-snt-relation' or any whole-state recognizer.  The correspondence
; theorem below licenses the projection only for related live states, and the
; open/root and transition theorems establish and preserve that relation.

(in-package "ACL2")

(include-book "store-observed")
(include-book "store-sweep")
(include-book "records-seam")

(local (in-theory (enable fn-record-record-vocabulary
                          fn-record-shape-vocabulary)))

; The optimized file projection.  Its body retains the specification's exact
; candidate predicate and omits only the appended-history replay.  The guard
; is discharged by fn-spc-prepare's existing structural contract; the body
; does not call fn-sf-statep.  In particular, execution here mentions neither
; fn-sf-history-recoverablep nor fn-sf-replay-node.
(defun fn-spc-stage-record (files record)
  (declare (xargs :guard (fn-sf-statep files) :verify-guards nil))
  (if (and (equal (fn-sf-phase files) :reserved)
           (fn-sf-candidatep record (fn-sf-records files)
                             (fn-sf-frontier files)))
      (fn-sf-remake :record-staged (fn-sf-frontier files) nil
                    record nil (fn-sf-barriers files) files)
    files))

(local
 (defthm fn-spc-record-list-implies-values
   (implies (fn-sf-record-listp records sequence lower frontier)
            (fn-sf-record-valuesp records))
   :hints (("Goal" :induct (fn-sf-record-listp
                             records sequence lower frontier)))))

(local
 (defthm fn-spc-state-has-candidate-guard-domain
   (implies (fn-sf-statep files)
            (and (fn-sf-record-valuesp (fn-sf-records files))
                 (natp (fn-sf-frontier files))))
   :hints (("Goal" :in-theory (enable fn-sf-statep)
            :use ((:instance fn-spc-record-list-implies-values
                             (records (fn-sf-records files))
                             (sequence 0) (lower 0)
                             (frontier (fn-sf-frontier files))))))))

(verify-guards fn-spc-stage-record
  :hints (("Goal" :use fn-spc-state-has-candidate-guard-domain
           :in-theory (disable fn-sf-statep fn-sf-candidatep))))

; The executable composition projection.  The guard is the same structural
; contract as the specification's guard; its body adds no relation check.
(defun fn-spc-prepare (s record)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-held-p record)
           ; fn-sn-prepare's gate: the row's context is of the generation in force.
           (equal (fn-hc-generation (fn-held-context record))
                  (fn-sn-keyring-generation s))
           (eq (car (fn-cpe-projection-step
                     (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok))
      (let* ((node (fn-sn-prepare-node (fn-sn-node s) record))
             (files (fn-spc-stage-record (fn-sn-files s) record)))
        (if (and (fn-sn-record-bindsp node record)
                 (equal (fn-sf-phase files) :record-staged))
            (fn-sn-update s files node)
          s))
    s))

(verify-guards fn-spc-prepare
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep)
                (fn-sf-statep fn-node-statep fn-node-pending-matchesp
                 fn-sn-pending-record fn-sn-prepare-node)))))

; On an article record the composed store-event accessors are the record's
; own.  `books/store-node-traces' and `books/store-node-invariants' each keep
; a copy of this local; this book needs it because `fn-sf-candidatep' orders
; the composed sequence while the goals here carry the record's own, and with
; the record accessors open the two reach the goal as `(CAR RECORD)' against
; `(FN-STORE-EVENT-SEQUENCE RECORD)' and nothing joins them (hbox
; certify-20260922T163635Z-3095374).
(local
 (defthm fn-spc-store-event-fields-of-an-article-record
   (implies (fn-held-p record)
            (and (equal (fn-store-event-sequence record)
                        (fn-record-sequence record))
                 (equal (fn-store-event-txid record) (fn-record-txid record))
                 (equal (fn-store-event-generation record)
                        (fn-record-generation record))))
   :hints (("Goal" :in-theory (e/d (fn-store-event-sequence
                                    fn-store-event-txid
                                    fn-store-event-generation)
                                   (fn-held-p fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-hstxa-p))))))

; `fn-sf-candidatep' pins the COMPOSED transaction id: since `6ab2c783' and
; `4bb7bb3d' a staged candidate is not always an article record, and this book
; has not certified since 2026-09-21.  On an article record -- which is what
; `fn-sn-record-bindsp' in the theorem below gives -- the two accessors are
; the same value by `fn-store-event-txid's first `cond' arm, so the article
; hypothesis is what carries the old statement over.
(local
 (defthm fn-spc-candidate-txid-is-frontier-predecessor
   (implies (and (fn-sf-candidatep record records frontier)
                 (fn-held-p record))
            (equal (fn-record-txid record) (+ -1 frontier)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (e/d (fn-sf-candidatep fn-store-event-txid)
                 (fn-sf-next-lower fn-held-p fn-record-txid
                  fn-store-event-p fn-store-retention-event-p
                  fn-stxe-p fn-stxk-p fn-hstxa-p))))))

; The semantic bridge.  In a related reserved state the node is exact replay
; at frontier-1.  If the actual prepared node binds the candidate, the
; canonical preparation theorem proves that replaying the appended history
; succeeds at frontier.  This is the expensive condition the projection may
; omit at execution time.
(defthm fn-spc-related-candidate-is-recoverable
  (implies
   (and (fn-snt-relation s)
        (equal (fn-sf-phase (fn-sn-files s)) :reserved)
        (fn-sf-candidatep record
                          (fn-sf-records (fn-sn-files s))
                          (fn-sf-frontier (fn-sn-files s)))
        (fn-sn-record-bindsp
         (fn-sn-prepare-node (fn-sn-node s) record) record))
   (fn-sf-history-recoverablep
    (fn-sn-groups s) (fn-sn-capacity s)
    (append (fn-sf-records (fn-sn-files s)) (list record))
    (fn-sf-frontier (fn-sn-files s))))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 (:instance fn-spc-candidate-txid-is-frontier-predecessor
                  (records (fn-sf-records (fn-sn-files s)))
                  (frontier (fn-sf-frontier (fn-sn-files s))))
                 (:instance fn-snt-bound-record-is-an-article-record
                  (node (fn-sn-prepare-node (fn-sn-node s) record)))
                 (:instance fn-sf-state-records-are-true-list
                  (s (fn-sn-files s)))
                 (:instance fn-snt-bound-record-is-matching-proposal
                  (node (fn-sn-prepare-node (fn-sn-node s) record)))
                 (:instance fn-snt-canonical-preparation-outcomes
                  (groups (fn-sn-groups s))
                  (capacity (fn-sn-capacity s))
                  (history (fn-sf-records (fn-sn-files s)))))
           :in-theory
           (e/d (fn-snt-relation fn-snt-idle-phasep fn-sf-candidatep)
                (fn-sn-statep fn-sf-statep fn-record-p fn-held-p
                 fn-sf-record-listp fn-sf-history-recoverablep
                 fn-sf-replay-node fn-snt-pending-linkp
                 fn-sn-completion-enabledp fn-sn-record-bindsp
                 fn-node-pending-matchesp
                 fn-snt-relation-implies-structural-state
                 fn-sf-state-records-are-true-list
                 fn-snt-bound-record-is-matching-proposal
                 fn-snt-canonical-preparation-outcomes)))))

; Keystone: the function the host calls is extensionally the specification on
; every state admitted by the maintained live-history relation.
(defthm fn-spc-prepare-equals-specification-under-relation
  (implies (fn-snt-relation s)
           (equal (fn-spc-prepare s record)
                  (fn-sn-prepare s record)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-spc-related-candidate-is-recoverable)
           :in-theory
           (e/d (fn-spc-prepare fn-spc-stage-record fn-sn-prepare
                                fn-sf-prepare-record)
                (fn-snt-relation fn-sn-statep fn-sf-statep
                 fn-sn-record-bindsp fn-sn-prepare-node
                 fn-sf-history-recoverablep
                 fn-snt-relation-implies-structural-state
                 fn-spc-related-candidate-is-recoverable)))))

(defthm fn-spc-prepare-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-spc-prepare s record)))
  :hints (("Goal"
           :use (fn-spc-prepare-equals-specification-under-relation
                 fn-snt-prepare-preserves-relation)
           :in-theory (disable fn-spc-prepare fn-sn-prepare fn-snt-relation))))

;; ---------------------------------------------------------------------------
;; The identity prepare's bridge (PRF-144 part 2).  A keyring snapshot or a
;; signed POST's composite is staged by `fn-sn-prepare-identity', whose file
;; gate `fn-sf-prepare-record' replays the whole appended history
;; (`fn-sf-history-recoverablep' over (append records (list event))): O(N*L)
;; per signed POST, and 46.7 % of one in carry-kind's profile.  In a related
;; reserved state that replay is already carried: the live node IS the replay
;; of the history at the reservation's transaction id (`fn-snt-relation''s
;; :reserved arm), and the prepare's own gate has applied the event to that
;; node.  `fn-snt-deferred-preparation-outcome' then says the extended history
;; replays to the applied node at the frontier.  So the replay is redundant
;; exactly where the host calls the prepare, and
;; books/owner-commit-carried.lisp's `fn-ccar-sn-prepare-identity' stages
;; through `fn-spc-stage-record' instead.
(defthm fn-spc-related-identity-candidate-is-recoverable
  (implies
   (and (fn-snt-relation s)
        (equal (fn-sf-phase (fn-sn-files s)) :reserved)
        (fn-sf-candidatep event
                          (fn-sf-records (fn-sn-files s))
                          (fn-sf-frontier (fn-sn-files s)))
        (consp (fn-replay-apply-record (fn-sn-node s) event)))
   (fn-sf-history-recoverablep
    (fn-sn-groups s) (fn-sn-capacity s)
    (append (fn-sf-records (fn-sn-files s)) (list event))
    (fn-sf-frontier (fn-sn-files s))))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 (:instance fn-snt-typed-store-components)
                 (:instance fn-sf-state-records-are-true-list
                  (s (fn-sn-files s)))
                 (:instance fn-replay-apply-record-non-nil-is-node-state
                  (node (fn-sn-node s)) (record event))
                 (:instance fn-snt-deferred-preparation-outcome
                  (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                  (history (fn-sf-records (fn-sn-files s)))
                  (txid (+ -1 (fn-sf-frontier (fn-sn-files s))))))
           :in-theory
           (e/d (fn-snt-relation fn-snt-idle-phasep fn-sf-candidatep)
                (fn-sn-statep fn-sf-statep fn-node-statep fn-record-p fn-held-p
                 fn-sf-record-listp fn-sf-history-recoverablep
                 fn-sf-replay-node fn-snt-pending-linkp
                 fn-snt-deferred-linkp fn-snt-completion-linkp
                 fn-sn-completion-enabledp fn-sf-next-lower
                 fn-replay-apply-record fn-store-event-p
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-snt-relation-implies-structural-state
                 fn-snt-typed-store-components
                 fn-sf-state-records-are-true-list
                 fn-replay-apply-record-non-nil-is-node-state)))))

; Reconfiguration changes the keyring, its generation and the index, and
; (after the flip) re-contexts every retained row: the rows' wire positions,
; facts, numbers and withdrawal stay (fn-held-with-context-fields), and the
; replay reads none of what changed.  So the live-history relation, which
; concerns the storage history and the node, is preserved.  It changes the
; store only at :ready (fn-sn-set-keyring's gate), where the relation's arm is
; the idle one.

; A held row is a Store event of the article kind and of no other.
(local
 (defthm fn-spc-held-kind-facts
   (implies (fn-held-p x)
            (and (fn-store-event-p x)
                 (not (fn-store-retention-event-p x))
                 (not (fn-stxe-p x)) (not (fn-stxk-p x)) (not (fn-hstxa-p x))
                 (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x))))
   :hints (("Goal" :in-theory (enable fn-store-event-p fn-held-p
                                      fn-held-shapep fn-store-retention-event-p
                                      fn-stxe-p fn-stxe-shapep fn-stxk-p
                                      fn-stxk-shapep fn-hstxa-p
                                      fn-cpe-eventp fn-th-topic-eventp)))))

(local
 (defthm fn-spc-hstxa-kind-facts
   (implies (fn-hstxa-p x)
            (and (fn-store-event-p x)
                 (not (fn-held-p x))
                 (not (fn-store-retention-event-p x))
                 (not (fn-stxe-p x)) (not (fn-stxk-p x))
                 (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x))))
   :hints (("Goal" :in-theory (enable fn-store-event-p fn-held-p
                                      fn-held-shapep fn-store-retention-event-p
                                      fn-stxe-p fn-stxe-shapep fn-stxk-p
                                      fn-stxk-shapep fn-hstxa-p
                                      fn-cpe-eventp fn-th-topic-eventp)))))

(local
 (defthm fn-spc-replay-reads-no-context-held
   (implies (and (fn-held-p r) (fn-hc-p c))
            (and (fn-store-event-p (fn-held-with-context r c))
                 (equal (fn-store-event-sequence (fn-held-with-context r c))
                        (fn-store-event-sequence r))
                 (equal (fn-replay-apply-record node (fn-held-with-context r c))
                        (fn-replay-apply-record node r))))
   :hints (("Goal" :use ((:instance fn-spc-held-kind-facts (x r))
                         (:instance fn-spc-held-kind-facts
                                    (x (fn-held-with-context r c))))
            :in-theory (e/d (fn-replay-apply-record fn-store-event-sequence
                             fn-store-event-txid)
                            (fn-spc-held-kind-facts fn-store-event-p fn-held-p
                             fn-hstxa-p fn-store-retention-event-p fn-stxe-p
                             fn-stxk-p fn-cpe-eventp fn-th-topic-eventp
                             fn-held-with-context fn-node-prepare
                             fn-node-complete fn-replay-advance-txid))))))

(local
 (defthm fn-spc-replay-reads-no-context-hstxa
   (implies (and (fn-hstxa-p r) (fn-hc-p c))
            (let ((y (fn-hstxa-make (fn-hstxa-stxa r)
                                    (fn-held-with-context (fn-hstxa-held r) c))))
              (and (fn-store-event-p y)
                   (equal (fn-store-event-sequence y) (fn-store-event-sequence r))
                   (equal (fn-replay-apply-record node y)
                          (fn-replay-apply-record node r)))))
   :hints (("Goal" :use ((:instance fn-spc-hstxa-kind-facts (x r))
                         (:instance fn-spc-hstxa-kind-facts
                                    (x (fn-hstxa-make (fn-hstxa-stxa r)
                                                      (fn-held-with-context
                                                       (fn-hstxa-held r) c)))))
            :in-theory (e/d (fn-replay-apply-record fn-store-event-sequence
                             fn-store-event-txid fn-replay-composite-held)
                            (fn-spc-hstxa-kind-facts fn-store-event-p fn-held-p
                             fn-hstxa-p fn-store-retention-event-p fn-stxe-p
                             fn-stxk-p fn-cpe-eventp fn-th-topic-eventp
                             fn-held-with-context fn-hstxa-make fn-node-prepare
                             fn-node-complete fn-replay-advance-txid))))))

(local
 (defun fn-spc-rc-induct (node rows contexts generation seq)
   (declare (xargs :measure (len rows)))
   (cond ((atom rows) (list node contexts generation seq))
         ((or (fn-held-p (car rows)) (fn-hstxa-p (car rows)))
          (fn-spc-rc-induct (fn-replay-apply-record node (car rows)) (cdr rows)
                            (cdr contexts) generation (1+ seq)))
         (t (fn-spc-rc-induct (fn-replay-apply-record node (car rows)) (cdr rows)
                              contexts generation (1+ seq))))))

(local
 (defthm fn-spc-replay-loop-of-recontext
   (implies (and (true-listp rows)
                 (not (eq (fn-sn-recontext-rows rows contexts generation) :mismatch)))
            (equal (fn-replay-loop node (fn-sn-recontext-rows rows contexts generation) seq)
                   (fn-replay-loop node rows seq)))
   :hints (("Goal" :induct (fn-spc-rc-induct node rows contexts generation seq)
            :expand ((fn-sn-recontext-rows rows contexts generation)
                     (fn-replay-loop node rows seq)
                     (:free (r) (fn-replay-loop node (cons (car rows) r) seq))
                     (:free (r c) (fn-replay-loop node (cons (fn-held-with-context (car rows) c) r) seq))
                     (:free (r c) (fn-replay-loop node (cons (fn-hstxa-make
                                                              (fn-hstxa-stxa (car rows))
                                                              (fn-held-with-context
                                                               (fn-hstxa-held (car rows)) c))
                                                             r) seq)))
            :in-theory (disable fn-replay-apply-record fn-store-event-p fn-held-p
                                fn-hstxa-p fn-held-with-context fn-hstxa-make
                                fn-store-event-sequence fn-node-statep)))))

(local
 (defthm fn-spc-replay-node-of-recontext
   (implies (and (true-listp rows)
                 (not (eq (fn-sn-recontext-rows rows contexts generation) :mismatch)))
            (and (equal (fn-sf-replay-node groups capacity
                                           (fn-sn-recontext-rows rows contexts generation)
                                           frontier)
                        (fn-sf-replay-node groups capacity rows frontier))
                 (equal (fn-sf-history-recoverablep groups capacity
                                                    (fn-sn-recontext-rows rows contexts generation)
                                                    frontier)
                        (fn-sf-history-recoverablep groups capacity rows frontier))))
   :hints (("Goal" :in-theory (e/d (fn-sf-replay-node fn-sf-history-recoverablep fn-replay)
                                   (fn-replay-loop fn-sn-recontext-rows))))))

(defthm fn-spc-set-keyring-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-set-keyring s keyring contexts)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-sn-set-keyring-preserves-state
                 (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s))))
           :in-theory (e/d (fn-snt-relation fn-sn-set-keyring fn-snt-idle-phasep)
                           (fn-sn-statep fn-sf-statep fn-node-statep
                            fn-sf-history-recoverablep fn-sf-replay-node
                            fn-sn-recontext-rows fn-sn-index-of-rows fn-cei-build
                            fn-snt-pending-linkp fn-snt-deferred-linkp
                            fn-snt-completion-linkp
                            fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                            fn-snt-relation-implies-structural-state
                            fn-sn-set-keyring-preserves-state
                            fn-sf-state-records-are-true-list)))))

; The actual post-open store mutations, expressed as already-decoded logical
; events.  The dispatcher never tests the relation and never rolls a failed
; check back.  Recovery is intentionally absent: a process begins at the
; observed open (the host calls fn-cpo-open-observed; fn-sn-open-observed,
; below, is the store-only model open), and recovery remains the
; authoritative replay.
(defun fn-spc-step (s event)
  (case (car event)
    (:prepare (fn-spc-prepare s (cadr event)))
    (:io (fn-sn-io s (cadr event) (caddr event)))
    (:finish (fn-sn-finish s))
    (:refuse-reservation (fn-sn-refuse-reservation s (cadr event)))
    (:known-abort (fn-sn-known-abort s))
    (:set-keyring (fn-sn-set-keyring s (cadr event) (caddr event)))
    (:sweep-staging (cdr (fn-sn-sweep-staging s (cadr event) (caddr event))))
    (otherwise s)))

(defun fn-spc-run (s events)
  (if (consp events)
      (fn-spc-run (fn-spc-step s (car events)) (cdr events))
    s))

(defthm fn-spc-step-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-spc-step s event)))
  :hints (("Goal"
           :use (fn-spc-prepare-preserves-relation
                 (:instance fn-snt-io-preserves-relation
                            (operation (cadr event)) (result (caddr event)))
                 fn-snt-finish-preserves-relation
                 (:instance fn-sn-refuse-reservation-preserves-relation
                            (txid (cadr event)))
                 fn-sn-known-abort-preserves-relation
                 (:instance fn-spc-set-keyring-preserves-relation
                            (keyring (cadr event)) (contexts (caddr event)))
                 (:instance fn-sn-sweep-staging-preserves-relation
                            (observed (cadr event)) (held (caddr event))))
           :in-theory (e/d (fn-spc-step)
                           (fn-snt-relation fn-spc-prepare fn-sn-io
                            fn-sn-finish fn-sn-refuse-reservation
                            fn-sn-known-abort fn-sn-set-keyring
                            fn-sn-sweep-staging
                            fn-spc-prepare-preserves-relation
                            fn-snt-io-preserves-relation
                            fn-snt-finish-preserves-relation
                            fn-sn-refuse-reservation-preserves-relation
                            fn-sn-known-abort-preserves-relation
                            fn-spc-set-keyring-preserves-relation
                            )))))

(defthm fn-spc-run-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-spc-run s events)))
  :hints (("Goal" :induct (fn-spc-run s events)
           :in-theory (disable fn-snt-relation fn-spc-step))))

; Reset and observed recovery are the two process roots used by the host.  A
; successful observed open followed by any finite sequence of actual live
; mutators therefore retains the hypothesis of the prepare equality theorem.
(defthm fn-spc-reset-establishes-relation
  (fn-snt-relation (fn-sn-initial nil 0))
  :hints (("Goal" :use ((:instance fn-snt-initial-relation
                                  (groups nil) (capacity 0)))
           :in-theory (disable fn-snt-relation fn-sn-initial))))

(defthm fn-spc-observed-open-run-maintains-relation
  (implies (fn-sn-open-okp
            (fn-sn-open-observed groups capacity frontier records))
           (fn-snt-relation
            (fn-spc-run
             (fn-sn-open-state
              (fn-sn-open-observed groups capacity frontier records))
             events)))
  :hints (("Goal"
           :use (fn-sn-open-observed-success-has-live-history-relation
                 (:instance fn-spc-run-preserves-relation
                            (s (fn-sn-open-state
                                (fn-sn-open-observed groups capacity
                                                     frontier records)))))
           :in-theory (disable fn-sn-open-observed fn-sn-open-okp
                               fn-snt-relation fn-spc-run
                               fn-spc-run-preserves-relation))))

; Export only the executable entry and the two keystones.  The projection's
; internal predicates remain available by explicit enable in its test book.
(in-theory (disable fn-spc-stage-record fn-spc-prepare fn-spc-step))
