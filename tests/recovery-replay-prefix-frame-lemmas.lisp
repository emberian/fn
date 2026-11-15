; Actual mutation frame leaves, SOURCE-ONLY and UNEXECUTED.
(in-package "ACL2")
(include-book "recovery-replay-prefix-identity")
; This helper never writes candidate/directory/digest geometry carriers.
(defthm fn2-recovery-selected-adopt-position-chain-frame
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
  (and
   (equal (fn2-recovery-payload-head journal commit je ja
           (mv-nth 1 (fn2-recovery-selected-adopt-position id gen p stage fn2-core)))
          (fn2-recovery-payload-head journal commit je ja fn2-core))
   (equal (fn2-recovery-payload-node journal commit je ja token left
           (mv-nth 1 (fn2-recovery-selected-adopt-position id gen p stage fn2-core)))
          (fn2-recovery-payload-node journal commit je ja token left fn2-core))))
 :hints (("Goal" :in-theory (enable fn2-recovery-selected-adopt-position
  fn2-recovery-payload-head fn2-recovery-payload-node fn2-recovery-payload-journal fn2-recovery-geometry))))
; Free-list predecessor mutations cannot change an already ALLOCATED row:
; previous and current are checked FREE before unlinking. The existing-row
; arm changes only the current p, and the journal edge arm changes only p.
(defthm fn2-recovery-selected-adopt-position-other-owned-frame
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (not (equal q p))
       (fn2-recovery-replay-position-owned-p q qe qa qkind qowner fn2-core))
  (fn2-recovery-replay-position-owned-p q qe qa qkind qowner
   (mv-nth 1 (fn2-recovery-selected-adopt-position id gen p stage fn2-core))))
 :hints (("Goal" :in-theory (enable fn2-recovery-selected-adopt-position
  fn2-recovery-replay-position-owned-p fn2-checkpoint-suffix-allocation-begin-record
  fn2-checkpoint-suffix-allocation-existing-record fn2-checkpoint-suffix-allocation-walk
  fn2-recovery-selected-journal-edge fn2-alloc-adopt-transition
  fn2-alloc-commit-allocation-transition fn2-alloc-cold-observe-identity
  fn2-alloc-edge-add-transition))))
; A new historical identity must be compatible with every live row. This
; premise is not supplied merely by authentication or physical-position
; uniqueness. It is the exact missing producer→prepass obligation.
(defthm fn2-recovery-selected-adopt-position-preserves-allocator-with-compatible-identity
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core)) (fn2-alloc-edges (fn2-core-alloc-edges fn2-core))) (valid)
        (fn2-alloc-ownership-invp fn2-extents fn2-alloc-edges) valid)
       (fn2-recovery-replay-identity-compatible-row-p (mv-nth 0 (fn2-recovery-geometry fn2-core)) p
        (fn2-recovery-cand-epoch p fn2-core) (fn2-recovery-cand-allocation p fn2-core) fn2-core)
       (member-eq (mv-nth 0 (fn2-recovery-selected-adopt-position id gen p stage fn2-core)) '(:more :adopted)))
  (let ((after (mv-nth 1 (fn2-recovery-selected-adopt-position id gen p stage fn2-core))))
   (stobj-let ((fn2-extents (fn2-core-extents after)) (fn2-alloc-edges (fn2-core-alloc-edges after))) (valid)
    (fn2-alloc-ownership-invp fn2-extents fn2-alloc-edges) valid)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-recovery-selected-adopt-position
  fn2-checkpoint-suffix-allocation-begin-record fn2-checkpoint-suffix-allocation-existing-record
  fn2-checkpoint-suffix-allocation-walk fn2-recovery-selected-journal-edge
  fn2-alloc-adopt-transition fn2-alloc-commit-allocation-transition
  fn2-alloc-cold-observe-identity fn2-alloc-edge-add-transition))))
; Only the replay wrapper's terminal branch returns :owned; an allocation
; worker may not smuggle that answer through the wrapper's fallback arm.
(defthm fn2-recovery-selected-adopt-position-never-owned
 (not (equal (mv-nth 0 (fn2-recovery-selected-adopt-position id gen p stage fn2-core)) :owned))
 :hints (("Goal" :in-theory (enable fn2-recovery-selected-adopt-position
  fn2-checkpoint-suffix-allocation-begin-record fn2-checkpoint-suffix-allocation-existing-record
  fn2-checkpoint-suffix-allocation-walk fn2-recovery-selected-journal-edge
  fn2-alloc-adopt-transition fn2-alloc-commit-allocation-transition
  fn2-alloc-cold-observe-identity fn2-alloc-edge-add-transition))))
(defthm fn2-recovery-selected-adopt-position-establishes-recorded-owner
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (eq (mv-nth 0 (fn2-recovery-selected-adopt-position id gen p stage fn2-core)) :adopted))
  (let ((after (mv-nth 1 (fn2-recovery-selected-adopt-position id gen p stage fn2-core)))
        (epoch (fn2-recovery-cand-epoch p fn2-core))
        (allocation (fn2-recovery-cand-allocation p fn2-core)))
   (if (equal (fn2-recovery-cand-status p fn2-core) *fn2-rec-status-chained*)
    (fn2-recovery-replay-journal-owned-p p (fn2-recovery-cand-commit p fn2-core) epoch allocation after)
    (fn2-recovery-replay-position-owned-p p epoch allocation
     (fn2-recovery-cand-owner-kind p fn2-core) (fn2-recovery-cand-owner p fn2-core) after))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-recovery-selected-adopt-position
  fn2-recovery-replay-journal-owned-p fn2-recovery-replay-position-owned-p
  fn2-recovery-selected-journal-edge fn2-checkpoint-suffix-allocation-existing-record
  fn2-checkpoint-suffix-allocation-walk fn2-alloc-adopt-transition
  fn2-alloc-commit-allocation-transition fn2-alloc-edge-add-transition))))
; The actual wrapper chooses only the journal or the current canonical node.
; Pairwise candidate uniqueness is needed as well as live-row compatibility:
; adopting the first of two FREE nodes otherwise invalidates the second.
(defthm fn2-recovery-replay-adopt-preserves-identity-compatibility
 (implies
  (and (fn2-corep fn2-core)
       (fn2-recovery-replay-carried-prefix-p id gen journal commit je ja tag fn2-core)
       (fn2-recovery-replay-identities-compatible-p journal commit je ja fn2-core)
       (eq (mv-nth 0 (fn2-recovery-replay-adopt id gen fn2-core)) :more))
  (fn2-recovery-replay-identities-compatible-p journal commit je ja
   (mv-nth 1 (fn2-recovery-replay-adopt id gen fn2-core))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-recovery-replay-adopt
  fn2-recovery-replay-carried-prefix-p fn2-recovery-replay-identities-compatible-p
  fn2-recovery-replay-chain-live-compatible-p fn2-recovery-replay-chain-identities
  fn2-recovery-replay-identity-compatible-row-p
  fn2-recovery-selected-adopt-position fn2-checkpoint-suffix-allocation-walk
  fn2-checkpoint-suffix-allocation-existing-record fn2-alloc-adopt-transition
  fn2-alloc-commit-allocation-transition fn2-alloc-cold-observe-identity))))
