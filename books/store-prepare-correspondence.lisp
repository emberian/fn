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
      (fn-sf-make :record-staged (fn-sf-frontier files) nil
                  (fn-sf-records files) record nil
                  (fn-sf-successes files) (fn-sf-barriers files))
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
           (fn-record-p record)
           (not (equal (fn-record-stamp record) :legacy)))
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
   (implies (fn-record-p record)
            (and (equal (fn-store-event-sequence record)
                        (fn-record-sequence record))
                 (equal (fn-store-event-txid record) (fn-record-txid record))
                 (equal (fn-store-event-generation record)
                        (fn-record-generation record))))
   :hints (("Goal" :in-theory (e/d (fn-store-event-sequence
                                    fn-store-event-txid
                                    fn-store-event-generation)
                                   (fn-record-p fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p))))))

; `fn-sf-candidatep' pins the COMPOSED transaction id: since `6ab2c783' and
; `4bb7bb3d' a staged candidate is not always an article record, and this book
; has not certified since 2026-09-21.  On an article record -- which is what
; `fn-sn-record-bindsp' in the theorem below gives -- the two accessors are
; the same value by `fn-store-event-txid's first `cond' arm, so the article
; hypothesis is what carries the old statement over.
(local
 (defthm fn-spc-candidate-txid-is-frontier-predecessor
   (implies (and (fn-sf-candidatep record records frontier)
                 (fn-record-p record))
            (equal (fn-record-txid record) (+ -1 frontier)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (e/d (fn-sf-candidatep fn-store-event-txid)
                 (fn-sf-next-lower fn-record-p fn-record-txid
                  fn-store-event-p fn-store-retention-event-p
                  fn-stxe-p fn-stxk-p fn-stxa-p))))))

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
                (fn-sn-statep fn-sf-statep fn-record-p
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

; Reconfiguration changes only the keyring/index pair.  The live-history
; relation deliberately concerns the storage history and node, so it is
; preserved while the statement index is recomputed under its own D21 proof.
(local
 (defthm fn-spc-set-keyring-preserves-state
   (implies (fn-sn-statep s)
            (fn-sn-statep (fn-sn-set-keyring s keyring)))
   :hints (("Goal"
            :in-theory (e/d (fn-sn-set-keyring fn-sn-statep)
                             (fn-sf-statep fn-node-statep
                              fn-stx-index-of-store))))))

(local
 (defthm fn-spc-set-keyring-keeps-store-components
   (and (equal (fn-sn-groups (fn-sn-set-keyring s keyring))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-set-keyring s keyring))
               (fn-sn-capacity s))
        (equal (fn-sn-files (fn-sn-set-keyring s keyring))
               (fn-sn-files s))
        (equal (fn-sn-node (fn-sn-set-keyring s keyring))
               (fn-sn-node s)))
   :hints (("Goal" :in-theory (enable fn-sn-set-keyring)))))

(local
 (defthm fn-spc-set-keyring-keeps-completion-record
   (equal (fn-sn-completion-record (fn-sn-set-keyring s keyring))
          (fn-sn-completion-record s))
   :hints (("Goal" :in-theory (enable fn-sn-set-keyring
                                       fn-sn-completion-record)))))

; Reconfiguration keeps the snapshot list and the identity cursor, so it
; keeps the identity replay context `6e992351' and `4bb7bb3d' made
; `fn-sn-completion-enabledp' consult.
(local
 (defthm fn-spc-set-keyring-keeps-identity-context
   (equal (fn-sn-identity-context (fn-sn-set-keyring s keyring))
          (fn-sn-identity-context s))
   :hints (("Goal" :in-theory (e/d (fn-sn-set-keyring fn-sn-identity-context)
                                   (fn-stx-index-of-store))))))

; The five event recognizers and the three appliers stay closed: since
; `6ab2c783' and `4bb7bb3d' this equality is a dispatch on the completion
; record's kind and nothing here looks inside it, while with them open the
; goal unfolds the record and statement codec on every arm.
(local
 (defthm fn-spc-set-keyring-keeps-completion-enabledp
   (implies (fn-sn-statep s)
            (equal (fn-sn-completion-enabledp (fn-sn-set-keyring s keyring))
                   (fn-sn-completion-enabledp s)))
   :hints (("Goal"
            :use (fn-spc-set-keyring-preserves-state
                  fn-spc-set-keyring-keeps-store-components
                  fn-spc-set-keyring-keeps-completion-record)
            :in-theory (e/d (fn-sn-completion-enabledp)
                            (fn-sn-set-keyring fn-sn-statep
                             fn-sn-record-bindsp
                             fn-record-shape-vocabulary
                             fn-record-record-vocabulary
                             fn-store-event-p fn-store-retention-event-p
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-replay-apply-record
                             fn-replay-apply-retention-event
                             fn-replay-apply-identity-neutral
                             fn-replay-composite-record
                             fn-replay-identity-step))))))

; The two links reconfiguration has to carry, each stated once over the
; accessors `fn-sn-set-keyring' keeps (the store components, the completion
; record, the identity context) with the replay and the codec closed: the
; deferred link reads the files, the node and the identity context, the
; completing link the files, the node and the completion record, and
; neither reads the keyring or the index.
(local
 (defthm fn-spc-set-keyring-keeps-deferred-link
   (equal (fn-snt-deferred-linkp (fn-sn-set-keyring s keyring))
          (fn-snt-deferred-linkp s))
   :hints (("Goal" :in-theory (e/d (fn-snt-deferred-linkp)
                                   (fn-sn-set-keyring
                                    fn-sf-history-recoverablep fn-sf-replay-node
                                    fn-sn-identity-context
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary
                                    fn-store-event-p fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-replay-apply-record
                                    fn-replay-apply-retention-event
                                    fn-replay-apply-identity-neutral
                                    fn-replay-composite-record
                                    fn-replay-identity-step))))))

(local
 (defthm fn-spc-set-keyring-keeps-completion-link
   (equal (fn-snt-completion-linkp (fn-sn-set-keyring s keyring))
          (fn-snt-completion-linkp s))
   :hints (("Goal" :in-theory (e/d (fn-snt-completion-linkp)
                                   (fn-sn-set-keyring fn-sn-completion-record
                                    fn-sf-replay-node fn-node-complete
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary
                                    fn-store-event-p fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-replay-apply-record
                                    fn-replay-apply-retention-event
                                    fn-replay-apply-identity-neutral
                                    fn-replay-composite-record
                                    fn-replay-identity-step))))))

; The relation's arms dispatch on the phase and the candidate's kind; every
; link stays CLOSED and is carried by the two lemmas above.  With the
; deferred link open the goal asked for it on the reconfigured state and
; nothing said the keyring was not among what it reads (hbox
; certify-20260922T181346Z-3153839, Subgoal 6).
(defthm fn-spc-set-keyring-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-set-keyring s keyring)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-spc-set-keyring-preserves-state)
           :in-theory (e/d (fn-snt-relation)
                           (fn-sn-statep fn-sf-statep fn-node-statep
                            fn-sn-set-keyring
                            fn-sf-history-recoverablep fn-sf-replay-node
                            fn-snt-pending-linkp fn-snt-deferred-linkp
                            fn-snt-completion-linkp
                            fn-sn-completion-enabledp
                            fn-record-shape-vocabulary
                            fn-record-record-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-replay-apply-identity-neutral
                            fn-replay-composite-record
                            fn-replay-identity-step
                            fn-snt-relation-implies-structural-state
                            fn-spc-set-keyring-preserves-state)))))

; The actual post-open store mutations, expressed as already-decoded logical
; events.  The dispatcher never tests the relation and never rolls a failed
; check back.  Recovery is intentionally absent: a process begins at
; fn-sn-open-observed, below, and recovery remains the authoritative replay.
(defun fn-spc-step (s event)
  (case (car event)
    (:prepare (fn-spc-prepare s (cadr event)))
    (:io (fn-sn-io s (cadr event) (caddr event)))
    (:finish (fn-sn-finish s))
    (:refuse-reservation (fn-sn-refuse-reservation s (cadr event)))
    (:known-abort (fn-sn-known-abort s))
    (:set-keyring (fn-sn-set-keyring s (cadr event)))
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
                            (keyring (cadr event)))
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
