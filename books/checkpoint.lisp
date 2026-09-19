; Logical checkpoint capture and suffix recovery over the actual fn node/replay
; machine.  This book deliberately does not choose checkpoint bytes, checksums,
; generation publication, or a physical crash-selection rule.

(in-package "ACL2")
(include-book "store-node-invariants")
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary)))
(local (in-theory (enable fn-store-files-invariants-vocabulary
                          fn-store-node-invariants-vocabulary)))

; A checkpoint stores the exact core node after its committed journal prefix.
; The durable allocator frontier is separate: known-aborted reservations need
; not appear in the journal and can therefore be ahead of the core's next txid.
; Layout: (:fn-checkpoint 1 groups capacity frontier next-sequence node)
; The checkpoint is an opaque record below its lemmas (docs/proof-style.md s1).
(defun fn-checkpoint-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 7)
       (equal (car x) :fn-checkpoint) (equal (cadr x) 1)))

(defun fn-checkpoint-groups (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(verify-guards fn-checkpoint-groups)

(defun fn-checkpoint-capacity (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(verify-guards fn-checkpoint-capacity)

(defun fn-checkpoint-frontier (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(verify-guards fn-checkpoint-frontier)

(defun fn-checkpoint-sequence (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                      (fn-ag-cdr (fn-ag-cdr x))))))))
(verify-guards fn-checkpoint-sequence)

(defun fn-checkpoint-node (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))
(verify-guards fn-checkpoint-node)

; The core accessors are total, so the constructor is.  The stored groups
; and capacity are the node's own (the recognizer below rechecks the binding).
(defun fn-checkpoint-make (frontier sequence node)
  (declare (xargs :guard t))
  (list :fn-checkpoint 1
        (fn-state-groups (fn-node-acceptance node))
        (fn-retain-capacity (fn-node-retention node))
        frontier sequence node))

(defthm fn-checkpoint-shapep-of-fn-checkpoint-make
  (fn-checkpoint-shapep (fn-checkpoint-make frontier sequence node)))
(defthm fn-checkpoint-groups-of-fn-checkpoint-make
  (equal (fn-checkpoint-groups (fn-checkpoint-make frontier sequence node))
         (fn-state-groups (fn-node-acceptance node))))
(defthm fn-checkpoint-capacity-of-fn-checkpoint-make
  (equal (fn-checkpoint-capacity (fn-checkpoint-make frontier sequence node))
         (fn-retain-capacity (fn-node-retention node))))
(defthm fn-checkpoint-frontier-of-fn-checkpoint-make
  (equal (fn-checkpoint-frontier (fn-checkpoint-make frontier sequence node))
         frontier))
(defthm fn-checkpoint-sequence-of-fn-checkpoint-make
  (equal (fn-checkpoint-sequence (fn-checkpoint-make frontier sequence node))
         sequence))
(defthm fn-checkpoint-node-of-fn-checkpoint-make
  (equal (fn-checkpoint-node (fn-checkpoint-make frontier sequence node))
         node))
(in-theory (disable (:d fn-checkpoint-shapep) (:d fn-checkpoint-groups)
                    (:d fn-checkpoint-capacity) (:d fn-checkpoint-frontier)
                    (:d fn-checkpoint-sequence) (:d fn-checkpoint-node)
                    (:d fn-checkpoint-make)))

; Shape facts type reasoning used to supply while the record opened
; (docs/proof-style.md s1), exported as forward-chaining rules only.
(defthm fn-checkpoint-shapep-forward-shape
  (implies (fn-checkpoint-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-checkpoint-shapep))))
(defthm fn-checkpoint-accessors-forward-consp
  (and (implies (fn-checkpoint-groups x) (consp x))
       (implies (fn-checkpoint-capacity x) (consp x))
       (implies (fn-checkpoint-frontier x) (consp x))
       (implies (fn-checkpoint-sequence x) (consp x))
       (implies (fn-checkpoint-node x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-checkpoint-groups x) (consp x))
                                    :trigger-terms ((fn-checkpoint-groups x)))
                 (:forward-chaining :corollary (implies (fn-checkpoint-capacity x) (consp x))
                                    :trigger-terms ((fn-checkpoint-capacity x)))
                 (:forward-chaining :corollary (implies (fn-checkpoint-frontier x) (consp x))
                                    :trigger-terms ((fn-checkpoint-frontier x)))
                 (:forward-chaining :corollary (implies (fn-checkpoint-sequence x) (consp x))
                                    :trigger-terms ((fn-checkpoint-sequence x)))
                 (:forward-chaining :corollary (implies (fn-checkpoint-node x) (consp x))
                                    :trigger-terms ((fn-checkpoint-node x))))
  :hints (("Goal" :in-theory (enable fn-checkpoint-groups fn-checkpoint-capacity fn-checkpoint-frontier fn-checkpoint-sequence fn-checkpoint-node))))

; Capture below derives sequence from actual replay.  A later byte refinement
; must integrity-bind every stored field together; the logical recognizer
; cannot detect a coordinated replacement by another well-formed checkpoint.
(defun fn-checkpointp (x)
  (declare (xargs :guard t :verify-guards nil))
  (let ((node (fn-checkpoint-node x)))
    (and (fn-checkpoint-shapep x)
         (fn-string-listp (fn-checkpoint-groups x))
         (fn-no-duplicatesp (fn-checkpoint-groups x))
         (natp (fn-checkpoint-capacity x))
         (fn-record-uint32p (fn-checkpoint-frontier x))
         (natp (fn-checkpoint-sequence x))
         (fn-node-statep node)
         (equal (fn-state-groups (fn-node-acceptance node))
                (fn-checkpoint-groups x))
         (equal (fn-retain-capacity (fn-node-retention node))
                (fn-checkpoint-capacity x))
         (fn-replay-advance-okp node (fn-checkpoint-frontier x)))))
(verify-guards fn-checkpointp)
(defthm fn-checkpointp-forward-shape
  (implies (fn-checkpointp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-checkpointp fn-checkpoint-shapep))))

; Guard-proof facts, local (docs/proof-style.md s3): flat one-step unfoldings
; of FN-REPLAY-OKP and FN-RECORD-UINT32P over a free ANSWER/N, so no call
; site has to open FN-REPLAY-OKP beside FN-REPLAY.
(local
 (defthm fn-replay-okp-implies-node-statep
   (implies (fn-replay-okp answer)
            (fn-node-statep (fn-replay-result-node answer)))
   :hints (("Goal" :in-theory (enable fn-replay-okp)))))

(local
 (defthm fn-record-uint32p-implies-natp
   (implies (fn-record-uint32p n) (natp n))
   :hints (("Goal" :in-theory (enable fn-record-uint32p)))))

; Capture returns either (:ok checkpoint) or (:error reason).  The prefix is
; replayed here once to obtain the exact state being snapshotted.  Restore below
; has no prefix argument and cannot reconstruct this state by replaying it.
(defun fn-checkpoint-capture (groups capacity records frontier)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (and (fn-string-listp groups)
              (fn-no-duplicatesp groups)
              (natp capacity)))
    (list :error :configuration))
   ((not (fn-record-uint32p frontier))
    (list :error :frontier))
   ((not (fn-sf-record-listp records 0 0 frontier))
    (list :error :history))
   (t
    (let ((answer (fn-replay groups capacity records)))
      (if (and (fn-replay-okp answer)
               (fn-replay-advance-okp
                (fn-replay-result-node answer) frontier))
          (list :ok
                (fn-checkpoint-make
                 frontier
                 (fn-replay-result-sequence answer)
                 (fn-replay-result-node answer)))
        (list :error :replay))))))
(verify-guards fn-checkpoint-capture
  :hints (("Goal"
           :in-theory (disable fn-replay fn-replay-loop fn-replay-okp
                               fn-node-statep fn-retain-statep))))

(defun fn-checkpoint-capture-value (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr result))
       :exec (fn-ag-car (fn-ag-cdr result))))
(verify-guards fn-checkpoint-capture-value)

; A successful replay is normalized to the persistent allocator frontier.
; The result preserves the actual replay sequence and exact node state.
(defun fn-checkpoint-finish (answer frontier)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-replay-okp answer))
      (list :error :replay)
    (if (not (fn-replay-advance-okp
              (fn-replay-result-node answer) frontier))
        (list :error :frontier)
      (list :ok
            (fn-replay-advance-txid
             (fn-replay-result-node answer) frontier)
            (fn-replay-result-sequence answer)
            frontier))))
(verify-guards fn-checkpoint-finish
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp))))

; Restore validates the checkpoint's configuration binding and the suffix's
; journal/allocator interval before invoking the actual replay loop.  In
; particular, no suffix txid may reuse a reservation below the checkpoint's
; consumed frontier, while later aborted gaps remain legal.
(defun fn-checkpoint-restore (checkpoint groups capacity records frontier)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (fn-checkpointp checkpoint))
    (list :error :checkpoint))
   ((or (not (equal groups (fn-checkpoint-groups checkpoint)))
        (not (equal capacity (fn-checkpoint-capacity checkpoint))))
    (list :error :configuration))
   ((or (not (fn-record-uint32p frontier))
        (< frontier (fn-checkpoint-frontier checkpoint)))
    (list :error :frontier))
   ((not (fn-sf-record-listp records
                             (fn-checkpoint-sequence checkpoint)
                             (fn-checkpoint-frontier checkpoint)
                             frontier))
    (list :error :suffix))
   (t
    (fn-checkpoint-finish
     (fn-replay-loop (fn-checkpoint-node checkpoint)
                     records
                     (fn-checkpoint-sequence checkpoint))
     frontier))))
(verify-guards fn-checkpoint-restore
  :hints (("Goal" :in-theory (e/d (fn-checkpointp fn-record-uint32p)
                                  (fn-replay fn-replay-loop)))))

; Reference result for full committed-history replay under the same persistent
; allocator frontier.  It is used by the correspondence theorem and tests; it
; is not called by checkpoint restore.
(defun fn-checkpoint-full-replay (groups capacity records frontier)
  (declare (xargs :guard t :verify-guards nil))
  (fn-checkpoint-finish (fn-replay groups capacity records) frontier))
(verify-guards fn-checkpoint-full-replay)


; This recognizer states the executable admissibility conditions for a split.
; It contains no equality between checkpoint and full results.  In particular,
; both journal intervals are ordered, both actual replays succeed, and each
; exact replay node may be reconciled with its durable allocator frontier.
(defun fn-checkpoint-admissible-splitp
  (groups capacity prefix checkpoint-frontier suffix final-frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((prefix-answer (fn-replay groups capacity prefix))
        ; APPEND's guard needs (TRUE-LISTP PREFIX), not guaranteed for this
        ; guard-T function's unconstrained parameter; FN-AG-APPEND is the
        ; guard-T equivalent (FN-AG-APPEND-IS-APPEND, acceptance.lisp).
        (full-answer (fn-replay groups capacity (fn-ag-append prefix suffix))))
    (and (fn-string-listp groups)
         (fn-no-duplicatesp groups)
         (natp capacity)
         (fn-record-uint32p checkpoint-frontier)
         (fn-record-uint32p final-frontier)
         (<= checkpoint-frontier final-frontier)
         (fn-sf-record-listp prefix 0 0 checkpoint-frontier)
         (fn-sf-record-listp suffix (len prefix) checkpoint-frontier
                             final-frontier)
         (fn-replay-okp prefix-answer)
         (equal (fn-replay-result-sequence prefix-answer) (len prefix))
         (equal (fn-state-groups
                 (fn-node-acceptance
                  (fn-replay-result-node prefix-answer)))
                groups)
         (equal (fn-retain-capacity
                 (fn-node-retention
                  (fn-replay-result-node prefix-answer)))
                capacity)
         (fn-replay-advance-okp (fn-replay-result-node prefix-answer)
                                checkpoint-frontier)
         (fn-replay-okp full-answer)
         (fn-replay-advance-okp (fn-replay-result-node full-answer)
                                final-frontier))))
(verify-guards fn-checkpoint-admissible-splitp
  :hints (("Goal"
           :in-theory (disable fn-replay fn-replay-loop fn-replay-okp
                               fn-node-statep fn-retain-statep
                               fn-record-uint32p)
           :use ((:instance fn-record-uint32p-implies-natp
                            (n checkpoint-frontier))
                 (:instance fn-record-uint32p-implies-natp
                            (n final-frontier))))))

; -----------------------------------------------------------------------------
; Correspondence facts

; Keep the large node and storage recognizers opaque in the checkpoint proofs.
; The admissibility predicate exposes exactly the projections required here.
(local
 (in-theory
  (disable fn-node-statep fn-statep fn-retain-statep fn-record-p
           fn-replay fn-replay-loop fn-replay-apply-record
           fn-replay-okp fn-replay-faultp fn-replay-advance-okp
           fn-replay-advance-txid fn-sf-record-listp fn-record-uint32p
           fn-replay-result-kind fn-replay-result-node
           fn-replay-result-sequence  fn-node-retention
            fn-retain-capacity
           fn-string-listp fn-no-duplicatesp
           binary-append len fn-node-initial-state
           fn-snt-successful-replay-sequence
           fn-snt-successful-replay-history-length)))

(local
 (defthm fn-checkpoint-replay-ok-projections
   (implies (fn-replay-okp answer)
            (and (fn-node-statep (fn-replay-result-node answer))
                 (natp (fn-replay-result-sequence answer))))
   :hints (("Goal" :in-theory (enable fn-replay-okp)))))

(local
 (defthm fn-checkpoint-make-is-valid
   (implies
    (and (fn-node-statep node)
         (fn-string-listp
          (fn-state-groups (fn-node-acceptance node)))
         (fn-no-duplicatesp
          (fn-state-groups (fn-node-acceptance node)))
         (natp
          (fn-retain-capacity (fn-node-retention node)))
         (fn-record-uint32p frontier)
         (natp sequence)
         (fn-replay-advance-okp node frontier))
    (fn-checkpointp (fn-checkpoint-make frontier sequence node)))
   :hints (("Goal" :in-theory (enable fn-checkpointp)))))

(defthm fn-checkpoint-admissible-capture-is-exact
  (implies
   (fn-checkpoint-admissible-splitp
    groups capacity prefix checkpoint-frontier suffix final-frontier)
   (equal
    (fn-checkpoint-capture groups capacity prefix checkpoint-frontier)
    (list
     :ok
     (fn-checkpoint-make
      checkpoint-frontier
      (len prefix)
      (fn-replay-result-node (fn-replay groups capacity prefix))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (e/d (fn-checkpoint-admissible-splitp fn-checkpoint-capture)
                (fn-checkpoint-make)))))

(defthm fn-checkpoint-admissible-capture-value-is-valid
  (implies
   (fn-checkpoint-admissible-splitp
    groups capacity prefix checkpoint-frontier suffix final-frontier)
   (fn-checkpointp
   (fn-checkpoint-capture-value
     (fn-checkpoint-capture groups capacity prefix checkpoint-frontier))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-checkpoint-admissible-capture-is-exact)
                 (:instance fn-checkpoint-make-is-valid
                            (node (fn-replay-result-node
                                   (fn-replay groups capacity prefix)))
                            (frontier checkpoint-frontier)
                            (sequence (len prefix))))
           :in-theory
           (e/d (fn-checkpoint-admissible-splitp
                  fn-checkpoint-capture-value)
                (fn-checkpoint-make fn-checkpointp)))))

; Existing replay concatenation specialized to the public replay entry point.
; This lemma is the nontrivial semantic bridge used below: full replay reaches
; the prefix's exact result node and continues with the actual suffix loop.
(defthm fn-checkpoint-full-replay-splits-at-successful-prefix
  (implies
   (and (true-listp prefix)
        (fn-replay-okp (fn-replay groups capacity prefix)))
   (equal
    (fn-replay groups capacity (append prefix suffix))
    (fn-replay-loop
     (fn-replay-result-node (fn-replay groups capacity prefix))
     suffix
     (fn-replay-result-sequence (fn-replay groups capacity prefix)))))
  :hints (("Goal"
           :use ((:instance fn-sn-replay-loop-append
                            (node (fn-node-initial-state groups capacity))
                            (sequence 0)))
           :in-theory (e/d (fn-replay fn-replay-okp)
                           (fn-replay-loop binary-append)))))

; PRF-008 logical core: capture a reachable prefix, discard the prefix input,
; then restore by running the actual suffix loop from the stored exact node.
; The result equals full actual replay of prefix++suffix, including allocator
; normalization and any known-aborted txid gaps represented by the frontiers.
(defthm fn-checkpoint-plus-suffix-equals-full-replay
  (implies
   (fn-checkpoint-admissible-splitp
    groups capacity prefix checkpoint-frontier suffix final-frontier)
   (equal
    (fn-checkpoint-restore
     (fn-checkpoint-capture-value
      (fn-checkpoint-capture groups capacity prefix checkpoint-frontier))
     groups capacity suffix final-frontier)
    (fn-checkpoint-full-replay
     groups capacity (append prefix suffix) final-frontier)))
  :hints (("Goal"
           :use ((:instance fn-checkpoint-admissible-capture-is-exact)
                 (:instance
                  fn-checkpoint-admissible-capture-value-is-valid)
                 (:instance
                  fn-checkpoint-full-replay-splits-at-successful-prefix))
           :in-theory
           (e/d (fn-checkpoint-admissible-splitp fn-checkpoint-capture
                  fn-checkpoint-capture-value fn-checkpoint-restore
                  fn-checkpoint-full-replay)
                (fn-checkpointp fn-replay fn-replay-loop
                 fn-replay-okp fn-replay-advance-okp
                 fn-sf-record-listp fn-record-uint32p
                 fn-string-listp fn-no-duplicatesp)))))

; The equivalence theorem above never exercises rejection: both sides reduce
; to the same FN-SN-REPLAY-LOOP-APPEND expression when the split is
; admissible, so it says nothing about the checkpoint frontier's rejecting
; role.  This theorem does: a suffix whose first record's transaction id
; reuses a value below the checkpoint's consumed frontier is refused with
; (:ERROR :SUFFIX) before FN-REPLAY-LOOP ever runs, for any continuation of
; the suffix and regardless of whether the record is otherwise well formed.
; FN-SF-RECORD-LISTP's own LOWER bound (:guard (and (natp sequence) (natp
; lower) (natp frontier)); body clause (<= lower (fn-record-txid record))) is
; the mechanism: passing the checkpoint's stored frontier as LOWER is what
; makes reuse impossible to satisfy.
(defthm fn-checkpoint-restore-rejects-frontier-reuse
  (implies
   (and (fn-checkpointp checkpoint)
        (equal groups (fn-checkpoint-groups checkpoint))
        (equal capacity (fn-checkpoint-capacity checkpoint))
        (fn-record-uint32p frontier)
        (<= (fn-checkpoint-frontier checkpoint) frontier)
        (< (fn-record-txid record) (fn-checkpoint-frontier checkpoint)))
   (equal
    (fn-checkpoint-restore checkpoint groups capacity
                           (cons record more) frontier)
    (list :error :suffix)))
  :hints (("Goal" :in-theory (enable fn-checkpoint-restore fn-sf-record-listp))))

; -----------------------------------------------------------------------------
; Export theory.  Withdrawn: the recognizer, capture, finish, restore, the
; reference full replay, the split admissibility recognizer, and under a name
; the replay-splitting lemma.  Enabled on include: the record lemmas and the
; keystones fn-checkpoint-plus-suffix-equals-full-replay (PRF-008) and
; fn-checkpoint-restore-rejects-frontier-reuse.
(deftheory fn-checkpoint-vocabulary
  '(fn-checkpoint-full-replay-splits-at-successful-prefix))
(in-theory (disable fn-checkpoint-vocabulary fn-checkpointp
                    fn-checkpoint-capture fn-checkpoint-capture-value
                    fn-checkpoint-finish fn-checkpoint-restore
                    fn-checkpoint-full-replay fn-checkpoint-admissible-splitp))
