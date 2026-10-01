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
   :hints (("Goal" :in-theory '(fn-store-event-p fn-store-retention-event-p-forward-shape)))))

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
