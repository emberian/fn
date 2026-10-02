; fn: the deferred Store prepares the host calls -- retention, consumer and
; topic -- without the appended-history replay (lane served-incremental-2,
; 2026-10-01; audit S1 of build/coordinator/audit-incremental-2026-10-02.md).
; Prefix fn-pdc-.
;
; The reference prepares (books/store-node.lisp fn-sn-prepare-retention,
; -consumer, -topic) stage through fn-sf-prepare-record, whose gate
; fn-sf-history-recoverablep REPLAYS the whole durable history with the
; candidate appended (fn-replay over (append (fn-sf-records s) (list e))).
; That is O(N * L) work per retention event (every BP undertake or release),
; consumer acknowledgement and topic operation, and fn-sf-records of a based
; records field decodes the whole on-disk history image
; (books/store-records-field.lisp fn-sfr-list) before the replay starts.
;
; The identity prepare dropped the same replay (PRF-144 part 2,
; books/owner-commit-carried.lisp fn-ccar-sn-prepare-identity): in a reserved
; state the maintained store relation admits, the live node IS the replay of
; the history at the reservation's transaction id, and the prepare's own gate
; has applied the event to it, which is what the replay would establish
; (books/store-prepare-correspondence.lisp
; fn-spc-related-identity-candidate-is-recoverable -- its statement names no
; event kind).  The three prepares below are their references with the file
; stage replaced by fn-pcar-stage-record (books/owner-prepare-carried.lisp:
; the reference's exact candidate predicate, the txid fold read from the last
; record, the length from the snoc-list's count) and the consumer projection
; step by its carried twin (fn-ccar-cpe-projection-step).
;
; What is proved, per prepare:
;   * EQUAL to the reference on every store the unconfigured live-history
;     relation fn-snt-relation admits (the premise of the identity keystone);
;   * EQUAL to the reference, with no hypothesis, whenever the reference
;     stages (the two can differ only where the reference's replay refuses);
;   * under the CONFIGURED relation fn-cst-relation (the one the host
;     carries), stage-iff-configured-admits: the carried prepare stages
;     exactly when the configured replay admits the appended history
;     (fn-pdc-configured-admitsp; both directions, below) -- at a
;     :reserved store, for an event of the prepare's own kind
;     (fn-store-retention-event-p, fn-cpe-eventp, fn-th-topic-eventp) whose
;     gate test passes: the consumer projection step answers :ok
;     (retention, consumer) or the topic prefix step does (topic).  A
;     projection or topic refusal is outside these theorems;
;   * the host-carried owner invariant fn-lgoc-invariantp is preserved by the
;     owner entries over them (fn-pdc-ocfg-prepare-*), so the staged state
;     satisfies the CONFIGURED relation (fn-cst-relation): the configured
;     replay of the appended history is the applied node.
; Under a configuration history the reference's replay is the UNconfigured
; one over the final groups and capacity (fn-sf-history-recoverablep calls
; fn-replay with fn-sn-groups/fn-sn-capacity), which is not the relation the
; host carries; the carried prepare decides by the configured node.
(in-package "ACL2")
(include-book "owner-prepare-outcome")

; -----------------------------------------------------------------------------
; Event-kind facts the gates need.

(local
 (defthm fn-pdc-retention-event-is-a-store-event
   (implies (fn-store-retention-event-p event)
            (and (fn-store-event-p event) (true-listp event)))
   :hints (("Goal" :in-theory (enable fn-store-event-p fn-store-retention-event-p)))))

; -----------------------------------------------------------------------------
; The Store-level prepares.

; fn-sn-prepare-retention with the carried file stage.
(defun fn-pdc-sn-prepare-retention (s event)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (fn-store-retention-event-p event)
           (eq (car (fn-ccar-cpe-projection-step
                     (fn-sn-consumer s) event (fn-sn-identity-next s))) :ok)
           (consp (fn-replay-apply-retention-event (fn-sn-node s) event)))
      (let ((files (fn-pcar-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged)
            (fn-sn-update s files (fn-sn-node s))
          s))
    s))

; fn-sn-prepare-consumer with the carried file stage.
(defun fn-pdc-sn-prepare-consumer (s event)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (fn-cpe-eventp event)
           (eq (car (fn-ccar-cpe-projection-step
                     (fn-sn-consumer s) event (fn-sn-identity-next s))) :ok)
           (consp (fn-replay-apply-record (fn-sn-node s) event)))
      (let ((files (fn-pcar-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged)
            (fn-sn-update s files (fn-sn-node s))
          s))
    s))

; fn-sn-prepare-topic with the carried file stage.
(defun fn-pdc-sn-prepare-topic (s event)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (fn-th-topic-eventp event)
           (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) event)) :ok)
           (consp (fn-replay-apply-record (fn-sn-node s) event)))
      (let ((files (fn-pcar-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged)
            (fn-sn-update s files (fn-sn-node s))
          s))
    s))

; -----------------------------------------------------------------------------
; KEYSTONES (Store).  Equal to the reference on every store the live-history
; relation admits: the gates are the same terms (the carried projection step
; is the reference's), the file stages agree off the replay
; (fn-pcar-stage-record-is-stage-record), and where the gate holds and the
; candidate is well placed the reference's replay succeeds
; (fn-spc-related-identity-candidate-is-recoverable, whose antecedent names
; the gate's own applied-node test).

(defthm fn-pdc-sn-prepare-retention-is-sn-prepare-retention-under-relation
  (implies (fn-snt-relation s)
           (equal (fn-pdc-sn-prepare-retention s event)
                  (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 (:instance fn-snt-typed-store-components)
                 (:instance fn-spc-related-identity-candidate-is-recoverable))
           :in-theory (union-theories
                       '(fn-pdc-sn-prepare-retention fn-sn-prepare-retention
                         fn-sf-prepare-record fn-spc-stage-record
                         fn-pcar-stage-record-is-stage-record
                         fn-replay-apply-record
                         fn-ccar-cpe-projection-step-is-cpe-projection-step
                         fn-pdc-retention-event-is-a-store-event)
                       (theory 'minimal-theory)))))

(defthm fn-pdc-sn-prepare-consumer-is-sn-prepare-consumer-under-relation
  (implies (fn-snt-relation s)
           (equal (fn-pdc-sn-prepare-consumer s event)
                  (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 (:instance fn-snt-typed-store-components)
                 (:instance fn-spc-related-identity-candidate-is-recoverable))
           :in-theory (union-theories
                       '(fn-pdc-sn-prepare-consumer fn-sn-prepare-consumer
                         fn-sf-prepare-record fn-spc-stage-record
                         fn-pcar-stage-record-is-stage-record
                         fn-ccar-cpe-projection-step-is-cpe-projection-step)
                       (theory 'minimal-theory)))))

(defthm fn-pdc-sn-prepare-topic-is-sn-prepare-topic-under-relation
  (implies (fn-snt-relation s)
           (equal (fn-pdc-sn-prepare-topic s event)
                  (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 (:instance fn-snt-typed-store-components)
                 (:instance fn-spc-related-identity-candidate-is-recoverable))
           :in-theory (union-theories
                       '(fn-pdc-sn-prepare-topic fn-sn-prepare-topic
                         fn-sf-prepare-record fn-spc-stage-record
                         fn-pcar-stage-record-is-stage-record)
                       (theory 'minimal-theory)))))

; KEYSTONES (no hypothesis).  Wherever the reference stages, the carried
; prepare is the reference: the two differ only where the reference's
; appended-history replay refuses.
(defthm fn-pdc-sn-prepare-retention-is-sn-prepare-retention-when-staged
  (implies (not (equal (fn-sn-prepare-retention s event) s))
           (equal (fn-pdc-sn-prepare-retention s event)
                  (fn-sn-prepare-retention s event)))
  :hints (("Goal" :use ((:instance fn-cstp-sn-statep-files (st s)))
           :in-theory (union-theories
                              '(fn-pdc-sn-prepare-retention fn-sn-prepare-retention
                                fn-sf-prepare-record fn-spc-stage-record
                                fn-pcar-stage-record-is-stage-record
                                fn-ccar-cpe-projection-step-is-cpe-projection-step
                                fn-pdc-retention-event-is-a-store-event)
                              (theory 'minimal-theory)))))

(defthm fn-pdc-sn-prepare-consumer-is-sn-prepare-consumer-when-staged
  (implies (not (equal (fn-sn-prepare-consumer s event) s))
           (equal (fn-pdc-sn-prepare-consumer s event)
                  (fn-sn-prepare-consumer s event)))
  :hints (("Goal" :use ((:instance fn-cstp-sn-statep-files (st s)))
           :in-theory (union-theories
                              '(fn-pdc-sn-prepare-consumer fn-sn-prepare-consumer
                                fn-sf-prepare-record fn-spc-stage-record
                                fn-pcar-stage-record-is-stage-record
                                fn-ccar-cpe-projection-step-is-cpe-projection-step)
                              (theory 'minimal-theory)))))

(defthm fn-pdc-sn-prepare-topic-is-sn-prepare-topic-when-staged
  (implies (not (equal (fn-sn-prepare-topic s event) s))
           (equal (fn-pdc-sn-prepare-topic s event)
                  (fn-sn-prepare-topic s event)))
  :hints (("Goal" :use ((:instance fn-cstp-sn-statep-files (st s)))
           :in-theory (union-theories
                              '(fn-pdc-sn-prepare-topic fn-sn-prepare-topic
                                fn-sf-prepare-record fn-spc-stage-record
                                fn-pcar-stage-record-is-stage-record)
                              (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; Both directions against the CONFIGURED replay (Codex r54, the coordinator's
; 2026-10-01 ruling).  Under fn-cst-relation, the relation the host carries,
; each carried prepare stages EXACTLY when the configured replay admits the
; appended history: the candidate is well placed and the configured replay
; of the history with it appended recovers at the frontier
; (fn-pdc-configured-admitsp).  Scope: a :reserved store, an event of the
; prepare's kind, and the gate's projection test passing (the consumer
; projection step :ok for retention and consumer events, the topic prefix
; step :ok for topic events); the theorems say nothing where that test
; refuses.  The reference prepares decide by the
; UNconfigured replay over the final groups and capacity, which refuses a
; history the configuration admitted once capacity was lowered after a
; charge (tests/acl2/owner-prepare-deferred-carried-tests.lisp *pdt-bad-cap*);
; that refusal is the reference's, not the configured semantics.

(defun fn-pdc-configured-admitsp (s e)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((files (fn-sn-files s))
         (records (fn-sf-records files))
         (frontier (fn-sf-frontier files)))
    (and (fn-sf-candidatep e records frontier)
         (fn-cst-recoverablep (fn-sn-config-history s)
                              (append records (list e)) frontier))))

(local
 (defthm fn-pdc-candidate-facts
   (implies (fn-sf-candidatep e records frontier)
            (and (fn-store-event-p e)
                 (equal (fn-store-event-sequence e) (len records))
                 (equal (fn-store-event-txid e) (+ -1 frontier))
                 (posp frontier)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-psrv-event-txid-natp))
            :in-theory (enable fn-sf-candidatep)))))

; The core, both directions, under the relation at a reservation, for an
; event the configured fold serves (no article: fn-cpr-event-servedp).
(local
 (defthm fn-pdc-applied-gives-configured-admits
   (let* ((files (fn-sn-files s))
          (records (fn-sf-records files))
          (frontier (fn-sf-frontier files)))
     (implies (and (fn-cst-relation s)
                   (equal (fn-sf-phase files) :reserved)
                   (not (fn-held-p e))
                   (not (fn-hstxa-p e))
                   (fn-sf-candidatep e records frontier)
                   (consp (fn-replay-apply-record (fn-sn-node s) e)))
              (fn-cst-recoverablep (fn-sn-config-history s)
                                   (append records (list e)) frontier)))
   :hints (("Goal"
            :use ((:instance fn-psrv-reserved-relation-facts)
                  (:instance fn-pdc-candidate-facts
                             (records (fn-sf-records (fn-sn-files s)))
                             (frontier (fn-sf-frontier (fn-sn-files s))))
                  (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                  (:instance fn-cstp-sn-statep-files (st s))
                  (:instance fn-cstp-replay-append-event
                             (configs (fn-sn-config-history s))
                             (events (fn-sf-records (fn-sn-files s)))
                             (txid (+ -1 (fn-sf-frontier (fn-sn-files s))))
                             (event e))
                  (:instance fn-psrv-recoverable-node-statep
                             (configs (fn-sn-config-history s))
                             (events (fn-sf-records (fn-sn-files s)))
                             (frontier (+ -1 (fn-sf-frontier (fn-sn-files s)))))
                  (:instance fn-replay-apply-record-non-nil-is-node-state
                             (node (fn-sn-node s)) (record e)))
            :in-theory '(fn-cpr-event-servedp fn-psrv-successor-of-predecessor posp
                         (:executable-counterpart equal))))))

(local
 (defthm fn-pdc-configured-admits-gives-applied
   (let* ((files (fn-sn-files s))
          (records (fn-sf-records files))
          (frontier (fn-sf-frontier files)))
     (implies (and (fn-cst-relation s)
                   (equal (fn-sf-phase files) :reserved)
                   (fn-sf-candidatep e records frontier)
                   (fn-cst-recoverablep (fn-sn-config-history s)
                                        (append records (list e)) frontier))
              (consp (fn-replay-apply-record (fn-sn-node s) e))))
   :hints (("Goal"
            :use ((:instance fn-psrv-reserved-relation-facts)
                  (:instance fn-pdc-candidate-facts
                             (records (fn-sf-records (fn-sn-files s)))
                             (frontier (fn-sf-frontier (fn-sn-files s))))
                  (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                  (:instance fn-cstp-sn-statep-files (st s))
                  (:instance fn-cstp-replay-append-event-fold
                             (configs (fn-sn-config-history s))
                             (events (fn-sf-records (fn-sn-files s)))
                             (txid (+ -1 (fn-sf-frontier (fn-sn-files s))))
                             (event e))
                  (:instance fn-cstp-recoverable-facts
                             (configs (fn-sn-config-history s))
                             (events (append (fn-sf-records (fn-sn-files s)) (list e)))
                             (frontier (fn-sf-frontier (fn-sn-files s))))
                  (:instance fn-cstp-recoverable-facts
                             (configs (fn-sn-config-history s))
                             (events (fn-sf-records (fn-sn-files s)))
                             (frontier (+ -1 (fn-sf-frontier (fn-sn-files s)))))
                  (:instance fn-cstp-cpr-loop-one-event
                             (cn (fn-cstp-fold (fn-sn-config-history s)
                                               (fn-sf-records (fn-sn-files s))))
                             (event e)
                             (cs (len (fn-sn-config-history s)))
                             (es (len (fn-sf-records (fn-sn-files s)))))
                  (:instance fn-cstp-apply-after-advance-to-its-txid
                             (node (fn-cnode-node (fn-cstp-fold (fn-sn-config-history s)
                                                                (fn-sf-records (fn-sn-files s)))))
                             (event e)))
            :in-theory '(fn-cpr-apply-event fn-replay-result-kind-of-fn-replay-fault
                         fn-replay-result-kind-of-fn-replay-ok
                         fn-cstp-cnode-make-consp
                         (:type-prescription len) natp (:executable-counterpart fn-cnode-statep)
                         (:executable-counterpart consp) (:executable-counterpart not)
                         (:executable-counterpart equal))))))

(defthm fn-pdc-configured-admits-is-applied-node
  (let* ((files (fn-sn-files s))
         (records (fn-sf-records files))
         (frontier (fn-sf-frontier files)))
    (implies (and (fn-cst-relation s)
                  (equal (fn-sf-phase files) :reserved)
                  (not (fn-held-p e))
                  (not (fn-hstxa-p e)))
             (iff (fn-pdc-configured-admitsp s e)
                  (and (fn-sf-candidatep e records frontier)
                       (consp (fn-replay-apply-record (fn-sn-node s) e))))))
  :hints (("Goal" :use (fn-pdc-applied-gives-configured-admits
                        fn-pdc-configured-admits-gives-applied)
           :in-theory '(fn-pdc-configured-admitsp))))

(local
 (defthm fn-pdc-retention-event-store-kind
   (implies (fn-store-retention-event-p event)
            (and (fn-store-event-p event) (true-listp event)))
   :hints (("Goal" :in-theory (enable fn-store-event-p fn-store-retention-event-p)))))

(local
 (defthm fn-pdc-stage-record-phase
   (implies (equal (fn-sf-phase files) :reserved)
            (iff (equal (fn-sf-phase (fn-pcar-stage-record files e)) :record-staged)
                 (fn-sf-candidatep e (fn-sf-records files) (fn-sf-frontier files))))
   :hints (("Goal" :in-theory (e/d (fn-pcar-stage-record-is-stage-record fn-spc-stage-record)
                                   (fn-sf-candidatep fn-sf-statep))))))

; KEYSTONES (both directions, configured).  Under the relation the host
; carries, at a reservation, with the gate's own event-kind and projection
; tests, each carried prepare stages exactly when the configured replay
; admits the appended history.
(defthm fn-pdc-sn-prepare-consumer-stages-iff-configured-admits
  (implies (and (fn-cst-relation s)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (fn-cpe-eventp e)
                (eq (car (fn-cpe-projection-step (fn-sn-consumer s) e
                                                 (fn-sn-identity-next s)))
                    :ok))
           (iff (equal (fn-sf-phase (fn-sn-files (fn-pdc-sn-prepare-consumer s e)))
                       :record-staged)
                (fn-pdc-configured-admitsp s e)))
  :hints (("Goal" :use ((:instance fn-pdc-configured-admits-is-applied-node)
                        (:instance fn-psrv-consumer-event-kinds)
                        (:instance fn-cstp-relation-is-statep (st s)))
           :in-theory (e/d (fn-pdc-sn-prepare-consumer
                            fn-ccar-cpe-projection-step-is-cpe-projection-step)
                           (fn-pdc-configured-admitsp fn-cst-relation fn-sn-statep fn-pcar-stage-record-is-stage-record
                            fn-pcar-stage-record fn-sf-candidatep fn-cpe-eventp
                            fn-replay-apply-record fn-cpe-projection-step
                            fn-ccar-cpe-projection-step fn-held-p fn-hstxa-p)))))

(defthm fn-pdc-sn-prepare-retention-stages-iff-configured-admits
  (implies (and (fn-cst-relation s)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (fn-store-retention-event-p e)
                (eq (car (fn-cpe-projection-step (fn-sn-consumer s) e
                                                 (fn-sn-identity-next s)))
                    :ok))
           (iff (equal (fn-sf-phase (fn-sn-files (fn-pdc-sn-prepare-retention s e)))
                       :record-staged)
                (fn-pdc-configured-admitsp s e)))
  :hints (("Goal" :use ((:instance fn-pdc-configured-admits-is-applied-node)
                        (:instance fn-psrv-retention-event-kinds)
                        (:instance fn-pdc-retention-event-store-kind (event e))
                        (:instance fn-cstp-relation-is-statep (st s)))
           :in-theory (e/d (fn-pdc-sn-prepare-retention fn-replay-apply-record
                            fn-ccar-cpe-projection-step-is-cpe-projection-step)
                           (fn-pdc-configured-admitsp fn-cst-relation fn-sn-statep fn-pcar-stage-record-is-stage-record
                            fn-pcar-stage-record fn-sf-candidatep
                            fn-store-retention-event-p fn-replay-apply-retention-event
                            fn-cpe-projection-step fn-node-prepare fn-node-complete
                            fn-ccar-cpe-projection-step fn-held-p fn-hstxa-p)))))

(defthm fn-pdc-sn-prepare-topic-stages-iff-configured-admits
  (implies (and (fn-cst-relation s)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (fn-th-topic-eventp e)
                (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) e)) :ok))
           (iff (equal (fn-sf-phase (fn-sn-files (fn-pdc-sn-prepare-topic s e)))
                       :record-staged)
                (fn-pdc-configured-admitsp s e)))
  :hints (("Goal" :use ((:instance fn-pdc-configured-admits-is-applied-node)
                        (:instance fn-psrv-topic-event-kinds)
                        (:instance fn-cstp-relation-is-statep (st s)))
           :in-theory (e/d (fn-pdc-sn-prepare-topic)
                           (fn-pdc-configured-admitsp fn-cst-relation fn-sn-statep fn-pcar-stage-record-is-stage-record
                            fn-pcar-stage-record fn-sf-candidatep fn-th-topic-eventp
                            fn-replay-apply-record fn-th-prefix-step fn-th-at
                            fn-held-p fn-hstxa-p)))))

; -----------------------------------------------------------------------------
; Guards: the reference guard (fn-sn-statep), as the references'.

(local
 (defthm fn-pdc-consumer-event-is-a-store-event
   (implies (fn-cpe-eventp event)
            (and (fn-store-event-p event) (true-listp event)))
   :hints (("Goal" :in-theory (enable fn-store-event-p fn-cpe-eventp)))))

(local
 (defthm fn-pdc-topic-event-is-a-store-event
   (implies (fn-th-topic-eventp event)
            (and (fn-store-event-p event) (true-listp event)))
   :hints (("Goal" :in-theory (enable fn-store-event-p)))))

(verify-guards fn-pdc-sn-prepare-retention
  :hints (("Goal" :in-theory (e/d (fn-sn-statep)
                                  (fn-sf-statep fn-node-statep fn-store-event-p
                                   fn-store-retention-event-p
                                   fn-replay-apply-retention-event
                                   fn-ccar-cpe-projection-step
                                   fn-spc-stage-record fn-pcar-stage-record)))))
(verify-guards fn-pdc-sn-prepare-consumer
  :hints (("Goal" :in-theory (e/d (fn-sn-statep)
                                  (fn-sf-statep fn-node-statep fn-store-event-p
                                   fn-cpe-eventp fn-replay-apply-record
                                   fn-ccar-cpe-projection-step
                                   fn-spc-stage-record fn-pcar-stage-record)))))
(verify-guards fn-pdc-sn-prepare-topic
  :hints (("Goal" :in-theory (e/d (fn-sn-statep)
                                  (fn-sf-statep fn-node-statep fn-store-event-p
                                   fn-th-topic-eventp fn-replay-apply-record
                                   fn-th-prefix-step
                                   fn-spc-stage-record fn-pcar-stage-record)))))

; -----------------------------------------------------------------------------
; What the carried prepares leave: the store, or the reservation with EVENT
; staged over the same history, configuration history and node.

(defthm fn-pdc-sn-prepares-stage-or-keep
  (and (or (equal (fn-pdc-sn-prepare-retention s e) s)
           (fn-pout-stagedp s (fn-pdc-sn-prepare-retention s e)))
       (or (equal (fn-pdc-sn-prepare-consumer s e) s)
           (fn-pout-stagedp s (fn-pdc-sn-prepare-consumer s e)))
       (or (equal (fn-pdc-sn-prepare-topic s e) s)
           (fn-pout-stagedp s (fn-pdc-sn-prepare-topic s e))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pdc-sn-prepare-retention fn-pdc-sn-prepare-consumer
                                   fn-pdc-sn-prepare-topic fn-pout-stagedp)
                                  (fn-pcar-stage-record fn-sn-statep
                                   fn-store-retention-event-p fn-cpe-eventp
                                   fn-th-topic-eventp fn-replay-apply-record
                                   fn-replay-apply-retention-event
                                   fn-ccar-cpe-projection-step fn-th-prefix-step)))))

(defthm fn-pdc-sn-prepares-keep-histories
  (and (equal (fn-sn-config-history (fn-pdc-sn-prepare-retention s e)) (fn-sn-config-history s))
       (equal (fn-sf-records (fn-sn-files (fn-pdc-sn-prepare-retention s e)))
              (fn-sf-records (fn-sn-files s)))
       (equal (fn-sn-config-history (fn-pdc-sn-prepare-consumer s e)) (fn-sn-config-history s))
       (equal (fn-sf-records (fn-sn-files (fn-pdc-sn-prepare-consumer s e)))
              (fn-sf-records (fn-sn-files s)))
       (equal (fn-sn-config-history (fn-pdc-sn-prepare-topic s e)) (fn-sn-config-history s))
       (equal (fn-sf-records (fn-sn-files (fn-pdc-sn-prepare-topic s e)))
              (fn-sf-records (fn-sn-files s))))
  :hints (("Goal"
           :use ((:instance fn-psrv-pcar-stage-record-staged (files (fn-sn-files s))))
           :in-theory (e/d (fn-pdc-sn-prepare-retention fn-pdc-sn-prepare-consumer
                            fn-pdc-sn-prepare-topic)
                           (fn-pcar-stage-record fn-sn-statep
                            fn-store-retention-event-p fn-cpe-eventp
                            fn-th-topic-eventp fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-ccar-cpe-projection-step fn-th-prefix-step)))))

; -----------------------------------------------------------------------------
; The configured relation and its carried companion (the store half of the
; host-carried fn-lgoc-invariantp) across each carried prepare: the staged
; record's configured replay is the applied node
; (fn-psrv-deferred-stage-preserves over the carried stage).

(defthm fn-pdc-sn-prepare-retention-preserves
  (implies (and (fn-cst-relation s) (fn-cstp-carriedp s))
           (and (fn-cst-relation (fn-pdc-sn-prepare-retention s e))
                (fn-cstp-carriedp (fn-pdc-sn-prepare-retention s e))))
  :hints (("Goal"
           :cases ((not (equal (fn-pdc-sn-prepare-retention s e) s)))
           :in-theory nil)
          ("Subgoal 1"
           :use ((:instance fn-psrv-deferred-stage-preserves
                            (f (fn-pcar-stage-record (fn-sn-files s) e)))
                 (:instance fn-psrv-pcar-stage-record-staged (files (fn-sn-files s)))
                 (:instance fn-cstp-sn-update-preserves-state
                            (files (fn-pcar-stage-record (fn-sn-files s) e))
                            (node (fn-sn-node s)))
                 (:instance fn-cstp-stage-record-preserves-state
                            (files (fn-sn-files s)) (record e))
                 (:instance fn-pcar-stage-record-is-stage-record
                            (files (fn-sn-files s)) (record e))
                 (:instance fn-psrv-sn-statep-node-statep)
                 (:instance fn-psrv-retention-event-kinds))
           :in-theory '(fn-pdc-sn-prepare-retention fn-replay-apply-record
                        fn-cstp-relation-is-statep fn-cstp-sn-statep-files
                        fn-cpr-event-servedp
                        fn-ccar-cpe-projection-step-is-cpe-projection-step))))

(defthm fn-pdc-sn-prepare-consumer-preserves
  (implies (and (fn-cst-relation s) (fn-cstp-carriedp s))
           (and (fn-cst-relation (fn-pdc-sn-prepare-consumer s e))
                (fn-cstp-carriedp (fn-pdc-sn-prepare-consumer s e))))
  :hints (("Goal"
           :cases ((not (equal (fn-pdc-sn-prepare-consumer s e) s)))
           :in-theory nil)
          ("Subgoal 1"
           :use ((:instance fn-psrv-deferred-stage-preserves
                            (f (fn-pcar-stage-record (fn-sn-files s) e)))
                 (:instance fn-psrv-pcar-stage-record-staged (files (fn-sn-files s)))
                 (:instance fn-cstp-sn-update-preserves-state
                            (files (fn-pcar-stage-record (fn-sn-files s) e))
                            (node (fn-sn-node s)))
                 (:instance fn-cstp-stage-record-preserves-state
                            (files (fn-sn-files s)) (record e))
                 (:instance fn-pcar-stage-record-is-stage-record
                            (files (fn-sn-files s)) (record e))
                 (:instance fn-psrv-sn-statep-node-statep)
                 (:instance fn-psrv-consumer-event-kinds)
                 (:instance fn-psrv-consumer-event-is-no-identity-event)
                 (:instance fn-psrv-projection-ok-sequence
                            (c (fn-sn-consumer s)) (expected (fn-sn-identity-next s)))
                 (:instance fn-psrv-identity-step-of-plain-event))
           :in-theory '(fn-pdc-sn-prepare-consumer
                        fn-cstp-relation-is-statep fn-cstp-sn-statep-files
                        fn-cpr-event-servedp
                        fn-ccar-cpe-projection-step-is-cpe-projection-step))))

; The topic prepare's completion also needs the consumer projection to admit
; EVENT, which fn-sn-prepare-topic does not test; the host's entry tests it
; (fn-pdc-psrv-prepare-topic, below), as the reference's does.
(defthm fn-pdc-sn-prepare-topic-preserves
  (implies (and (fn-cst-relation s) (fn-cstp-carriedp s)
                (eq (car (fn-cpe-projection-step (fn-sn-consumer s) e
                                                 (fn-sn-identity-next s)))
                    :ok))
           (and (fn-cst-relation (fn-pdc-sn-prepare-topic s e))
                (fn-cstp-carriedp (fn-pdc-sn-prepare-topic s e))))
  :hints (("Goal"
           :cases ((not (equal (fn-pdc-sn-prepare-topic s e) s)))
           :in-theory nil)
          ("Subgoal 1"
           :use ((:instance fn-psrv-deferred-stage-preserves
                            (f (fn-pcar-stage-record (fn-sn-files s) e)))
                 (:instance fn-psrv-pcar-stage-record-staged (files (fn-sn-files s)))
                 (:instance fn-cstp-sn-update-preserves-state
                            (files (fn-pcar-stage-record (fn-sn-files s) e))
                            (node (fn-sn-node s)))
                 (:instance fn-cstp-stage-record-preserves-state
                            (files (fn-sn-files s)) (record e))
                 (:instance fn-pcar-stage-record-is-stage-record
                            (files (fn-sn-files s)) (record e))
                 (:instance fn-psrv-sn-statep-node-statep)
                 (:instance fn-psrv-topic-event-kinds)
                 (:instance fn-psrv-topic-event-is-no-identity-event)
                 (:instance fn-psrv-projection-ok-sequence
                            (c (fn-sn-consumer s)) (expected (fn-sn-identity-next s)))
                 (:instance fn-psrv-identity-step-of-plain-event))
           :in-theory '(fn-pdc-sn-prepare-topic
                        fn-cstp-relation-is-statep fn-cstp-sn-statep-files
                        fn-cpr-event-servedp))))

; -----------------------------------------------------------------------------
; The configured owner's prepares: the reference's (:store (:prepare-X E))
; through fn-ocfg-step is fn-ocl-owner-with-store over the Store's step
; (fn-psrv-store-step-is-owner-with-store); these are that with the carried
; Store prepare.

(defun fn-pdc-ocfg-prepare-retention (oc event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (fn-ocfg-with-owner
   oc (fn-ocl-owner-with-store
       (fn-ocfg-owner oc)
       (fn-pdc-sn-prepare-retention (fn-own-store (fn-ocfg-owner oc)) event))))

(defun fn-pdc-ocfg-prepare-consumer (oc event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (fn-ocfg-with-owner
   oc (fn-ocl-owner-with-store
       (fn-ocfg-owner oc)
       (fn-pdc-sn-prepare-consumer (fn-own-store (fn-ocfg-owner oc)) event))))

; fn-psrv-prepare-topic (books/owner-prepare-served.lisp) with the carried
; Store prepare: the consumer projection's admission first, as there.
(defun fn-pdc-psrv-prepare-topic (oc event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o)))
    (if (and (fn-store-event-p event)
             (eq (car (fn-ccar-cpe-projection-step
                       (fn-sn-consumer s) event (fn-sn-identity-next s)))
                 :ok))
        (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                o (fn-pdc-sn-prepare-topic s event)))
      oc)))

; KEYSTONES (owner).  On every owner whose Store the live-history relation
; admits, each is the reference the host called before.
(defthm fn-pdc-ocfg-prepare-retention-is-ocfg-step-under-relation
  (implies (fn-snt-relation (fn-own-store (fn-ocfg-owner oc)))
           (equal (fn-pdc-ocfg-prepare-retention oc event)
                  (fn-ocfg-step oc (list :store (list :prepare-retention event)) fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-pdc-sn-prepare-retention-is-sn-prepare-retention-under-relation
                            (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-pdc-ocfg-prepare-retention fn-psrv-store-step-is-owner-with-store
                        fn-snrt-step car-cons cdr-cons (:executable-counterpart equal)))))

(defthm fn-pdc-ocfg-prepare-consumer-is-ocfg-step-under-relation
  (implies (fn-snt-relation (fn-own-store (fn-ocfg-owner oc)))
           (equal (fn-pdc-ocfg-prepare-consumer oc event)
                  (fn-ocfg-step oc (list :store (list :prepare-consumer event)) fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-pdc-sn-prepare-consumer-is-sn-prepare-consumer-under-relation
                            (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-pdc-ocfg-prepare-consumer fn-psrv-store-step-is-owner-with-store
                        fn-snrt-step car-cons cdr-cons (:executable-counterpart equal)))))

(defthm fn-pdc-psrv-prepare-topic-is-psrv-prepare-topic-under-relation
  (implies (fn-snt-relation (fn-own-store (fn-ocfg-owner oc)))
           (equal (fn-pdc-psrv-prepare-topic oc event)
                  (fn-psrv-prepare-topic oc event)))
  :hints (("Goal"
           :use ((:instance fn-pdc-sn-prepare-topic-is-sn-prepare-topic-under-relation
                            (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-pdc-psrv-prepare-topic fn-psrv-prepare-topic-cases
                        fn-ccar-cpe-projection-step-is-cpe-projection-step))))

; With no hypothesis: where the reference stages, the owner is the reference's.
(defthm fn-pdc-ocfg-prepare-retention-is-ocfg-step-when-staged
  (implies (not (equal (fn-sn-prepare-retention (fn-own-store (fn-ocfg-owner oc)) event)
                       (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-pdc-ocfg-prepare-retention oc event)
                  (fn-ocfg-step oc (list :store (list :prepare-retention event)) fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-pdc-sn-prepare-retention-is-sn-prepare-retention-when-staged
                            (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-pdc-ocfg-prepare-retention fn-psrv-store-step-is-owner-with-store
                        fn-snrt-step car-cons cdr-cons (:executable-counterpart equal)))))

(defthm fn-pdc-ocfg-prepare-consumer-is-ocfg-step-when-staged
  (implies (not (equal (fn-sn-prepare-consumer (fn-own-store (fn-ocfg-owner oc)) event)
                       (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-pdc-ocfg-prepare-consumer oc event)
                  (fn-ocfg-step oc (list :store (list :prepare-consumer event)) fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-pdc-sn-prepare-consumer-is-sn-prepare-consumer-when-staged
                            (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-pdc-ocfg-prepare-consumer fn-psrv-store-step-is-owner-with-store
                        fn-snrt-step car-cons cdr-cons (:executable-counterpart equal)))))

(defthm fn-pdc-psrv-prepare-topic-is-psrv-prepare-topic-when-staged
  (implies (not (equal (fn-sn-prepare-topic (fn-own-store (fn-ocfg-owner oc)) event)
                       (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-pdc-psrv-prepare-topic oc event)
                  (fn-psrv-prepare-topic oc event)))
  :hints (("Goal"
           :use ((:instance fn-pdc-sn-prepare-topic-is-sn-prepare-topic-when-staged
                            (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-pdc-psrv-prepare-topic fn-psrv-prepare-topic-cases
                        fn-ccar-cpe-projection-step-is-cpe-projection-step))))

; KEYSTONES (owner).  Each keeps the invariant the host carries.
(defthm fn-pdc-ocfg-prepare-retention-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-pdc-ocfg-prepare-retention oc e)))
  :hints (("Goal"
           :use ((:instance fn-pdc-sn-prepare-retention-preserves
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-psrv-owner-with-store-preserves-invariant
                            (st (fn-pdc-sn-prepare-retention
                                 (fn-own-store (fn-ocfg-owner oc)) e)))
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-pdc-ocfg-prepare-retention fn-pdc-sn-prepares-keep-histories
                        fn-lgoc-invariantp))))

(defthm fn-pdc-ocfg-prepare-consumer-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-pdc-ocfg-prepare-consumer oc e)))
  :hints (("Goal"
           :use ((:instance fn-pdc-sn-prepare-consumer-preserves
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-psrv-owner-with-store-preserves-invariant
                            (st (fn-pdc-sn-prepare-consumer
                                 (fn-own-store (fn-ocfg-owner oc)) e)))
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-pdc-ocfg-prepare-consumer fn-pdc-sn-prepares-keep-histories
                        fn-lgoc-invariantp))))

(defthm fn-pdc-psrv-prepare-topic-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-pdc-psrv-prepare-topic oc e)))
  :hints (("Goal"
           :use ((:instance fn-pdc-sn-prepare-topic-preserves
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-psrv-owner-with-store-preserves-invariant
                            (st (fn-pdc-sn-prepare-topic
                                 (fn-own-store (fn-ocfg-owner oc)) e)))
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-pdc-psrv-prepare-topic fn-pdc-sn-prepares-keep-histories
                        fn-ccar-cpe-projection-step-is-cpe-projection-step
                        fn-lgoc-invariantp))))

; -----------------------------------------------------------------------------
; The entries' words: :prepared exactly when the Store staged a record.

(defthm fn-pdc-store-of-owner-prepares
  (and (equal (fn-sbud-oc-store (fn-pdc-ocfg-prepare-retention oc e))
              (fn-pdc-sn-prepare-retention (fn-sbud-oc-store oc) e))
       (equal (fn-sbud-oc-store (fn-pdc-ocfg-prepare-consumer oc e))
              (fn-pdc-sn-prepare-consumer (fn-sbud-oc-store oc) e))
       (or (equal (fn-sbud-oc-store (fn-pdc-psrv-prepare-topic oc e)) (fn-sbud-oc-store oc))
           (equal (fn-sbud-oc-store (fn-pdc-psrv-prepare-topic oc e))
                  (fn-pdc-sn-prepare-topic (fn-sbud-oc-store oc) e))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-pdc-ocfg-prepare-retention fn-pdc-ocfg-prepare-consumer
                               fn-pdc-psrv-prepare-topic fn-lgoc-store-of-owner-with-store
                               fn-sbud-oc-store))))

(defun fn-pdc-pout-prepare-retention (oc e)
  (declare (xargs :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))))
  (let ((next (fn-pdc-ocfg-prepare-retention oc e)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          :refused)
        next)))

(defun fn-pdc-pout-prepare-consumer (oc e)
  (declare (xargs :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))))
  (let ((next (fn-pdc-ocfg-prepare-consumer oc e)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          :refused)
        next)))

(defun fn-pdc-pout-prepare-topic (oc e)
  (declare (xargs :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))))
  (let ((next (fn-pdc-psrv-prepare-topic oc e)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          :refused)
        next)))

(defthm fn-pdc-pout-prepares-answer-the-store-change
  (and (let ((r (fn-pdc-pout-prepare-retention oc e)))
         (and (equal (mv-nth 1 r) (fn-pdc-ocfg-prepare-retention oc e))
              (equal (mv-nth 0 r)
                     (if (equal (fn-sbud-oc-store (mv-nth 1 r)) (fn-sbud-oc-store oc))
                         :refused :prepared))))
       (let ((r (fn-pdc-pout-prepare-consumer oc e)))
         (and (equal (mv-nth 1 r) (fn-pdc-ocfg-prepare-consumer oc e))
              (equal (mv-nth 0 r)
                     (if (equal (fn-sbud-oc-store (mv-nth 1 r)) (fn-sbud-oc-store oc))
                         :refused :prepared))))
       (let ((r (fn-pdc-pout-prepare-topic oc e)))
         (and (equal (mv-nth 1 r) (fn-pdc-psrv-prepare-topic oc e))
              (equal (mv-nth 0 r)
                     (if (equal (fn-sbud-oc-store (mv-nth 1 r)) (fn-sbud-oc-store oc))
                         :refused :prepared)))))
  :hints (("Goal"
           :use (fn-pdc-store-of-owner-prepares
                 (:instance fn-pdc-sn-prepares-stage-or-keep (s (fn-sbud-oc-store oc)))
                 (:instance fn-pout-stagedp-is-a-change
                            (before (fn-sbud-oc-store oc))
                            (after (fn-sbud-oc-store (fn-pdc-ocfg-prepare-retention oc e))))
                 (:instance fn-pout-stagedp-is-a-change
                            (before (fn-sbud-oc-store oc))
                            (after (fn-sbud-oc-store (fn-pdc-ocfg-prepare-consumer oc e))))
                 (:instance fn-pout-stagedp-is-a-change
                            (before (fn-sbud-oc-store oc))
                            (after (fn-sbud-oc-store (fn-pdc-psrv-prepare-topic oc e)))))
           :in-theory '(fn-pdc-pout-prepare-retention fn-pdc-pout-prepare-consumer
                        fn-pdc-pout-prepare-topic
                        mv-nth car-cons cdr-cons (:executable-counterpart zp)
                        (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))

; And the words are the reference entries' where the store relation holds.
(defthm fn-pdc-pout-prepares-are-pout-prepares-under-relation
  (implies (fn-snt-relation (fn-sbud-oc-store oc))
           (and (equal (fn-pdc-pout-prepare-retention oc e)
                       (mv-list 2 (fn-pout-prepare-retention oc e fn-arena)))
                (equal (fn-pdc-pout-prepare-consumer oc e)
                       (mv-list 2 (fn-pout-prepare-consumer oc e fn-arena)))
                (equal (fn-pdc-pout-prepare-topic oc e)
                       (fn-pout-prepare-topic oc e))))
  :hints (("Goal"
           :use ((:instance fn-pdc-ocfg-prepare-retention-is-ocfg-step-under-relation (event e))
                 (:instance fn-pdc-ocfg-prepare-consumer-is-ocfg-step-under-relation (event e))
                 (:instance fn-pdc-psrv-prepare-topic-is-psrv-prepare-topic-under-relation (event e)))
           :in-theory '(fn-pdc-pout-prepare-retention fn-pdc-pout-prepare-consumer
                        fn-pdc-pout-prepare-topic fn-pout-prepare-retention
                        fn-pout-prepare-consumer fn-pout-prepare-topic fn-sbud-oc-store
                        mv-list))))

(in-theory (disable fn-pdc-sn-prepare-retention fn-pdc-sn-prepare-consumer
                    fn-pdc-sn-prepare-topic fn-pdc-ocfg-prepare-retention
                    fn-pdc-ocfg-prepare-consumer fn-pdc-psrv-prepare-topic
                    fn-pdc-pout-prepare-retention fn-pdc-pout-prepare-consumer
                    fn-pdc-pout-prepare-topic))
