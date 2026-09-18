; Logical checkpoint capture and suffix recovery over the actual fn node/replay
; machine.  This book deliberately does not choose checkpoint bytes, checksums,
; generation publication, or a physical crash-selection rule.

(in-package "ACL2")
(include-book "store-node-invariants")

; A checkpoint stores the exact core node after its committed journal prefix.
; The durable allocator frontier is separate: known-aborted reservations need
; not appear in the journal and can therefore be ahead of the core's next txid.
; Layout: (:fn-checkpoint 1 groups capacity frontier next-sequence node)
(defun fn-checkpoint-groups (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(defun fn-checkpoint-capacity (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(defun fn-checkpoint-frontier (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))

(defun fn-checkpoint-sequence (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                      (fn-ag-cdr (fn-ag-cdr x))))))))

(defun fn-checkpoint-node (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))

(defun fn-checkpoint-make (frontier sequence node)
  (declare (xargs :guard t :verify-guards nil))
  (list :fn-checkpoint 1
        (fn-state-groups (fn-node-acceptance node))
        (fn-retain-capacity (fn-node-retention node))
        frontier sequence node))

; Capture below derives sequence from actual replay.  A later byte refinement
; must integrity-bind every stored field together; the logical recognizer
; cannot detect a coordinated replacement by another well-formed checkpoint.
(defun fn-checkpointp (x)
  (declare (xargs :guard t :verify-guards nil))
  (let ((node (fn-checkpoint-node x)))
    (and (true-listp x)
         (equal (len x) 7)
         (equal (car x) :fn-checkpoint)
         (equal (cadr x) 1)
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

(defun fn-checkpoint-capture-value (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr result))
       :exec (fn-ag-car (fn-ag-cdr result))))

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

; Reference result for full committed-history replay under the same persistent
; allocator frontier.  It is used by the correspondence theorem and tests; it
; is not called by checkpoint restore.
(defun fn-checkpoint-full-replay (groups capacity records frontier)
  (declare (xargs :guard t :verify-guards nil))
  (fn-checkpoint-finish (fn-replay groups capacity records) frontier))

; This recognizer states the executable admissibility conditions for a split.
; It contains no equality between checkpoint and full results.  In particular,
; both journal intervals are ordered, both actual replays succeed, and each
; exact replay node may be reconciled with its durable allocator frontier.
(defun fn-checkpoint-admissible-splitp
  (groups capacity prefix checkpoint-frontier suffix final-frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((prefix-answer (fn-replay groups capacity prefix))
        (full-answer (fn-replay groups capacity (append prefix suffix))))
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
           fn-replay-result-sequence fn-node-acceptance fn-node-retention
           fn-state-groups fn-retain-capacity
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
   :hints (("Goal"
            :in-theory
            (enable fn-checkpointp fn-checkpoint-make len
                    fn-checkpoint-groups fn-checkpoint-capacity
                    fn-checkpoint-frontier fn-checkpoint-sequence
                    fn-checkpoint-node)))))

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
