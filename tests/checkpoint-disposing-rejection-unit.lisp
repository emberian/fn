; Actual completed runtime bank transfer supplies the full retained identity.
; Installed/Fence/C-release premises are explicitly synthetic in its fixture.
; This tests real inspection/selection refusal, not a model or FREE path.
(in-package "ACL2")
(include-book "checkpoint-teardown-transfer-unit")
(defun fn2-cdru-body (fn2-checkpoint-teardown-debt fn2-checkpoint-lifecycle fn2-csnapshot fn2-extents fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-commit-root fn2-fc fn2-checkpoint-bytes fn2-digests fn2-checkpoint-construction fn2-ops fn2-alloc-edges)
 (declare (xargs :stobjs (fn2-checkpoint-teardown-debt fn2-checkpoint-lifecycle fn2-csnapshot fn2-extents fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-commit-root fn2-fc fn2-checkpoint-bytes fn2-digests fn2-checkpoint-construction fn2-ops fn2-alloc-edges) :verify-guards nil))
 (b* (((mv setup fn2-checkpoint-teardown-debt fn2-checkpoint-lifecycle fn2-csnapshot fn2-extents fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-commit-root fn2-fc fn2-checkpoint-bytes fn2-digests) (fn2-cttu-body nil fn2-checkpoint-teardown-debt fn2-checkpoint-lifecycle fn2-csnapshot fn2-extents fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-commit-root fn2-fc fn2-checkpoint-bytes fn2-digests))
      (open (fn2-checkpoint-teardown-admission-ownerp 0 19 7 0 1 fn2-checkpoint-teardown-debt fn2-checkpoints fn2-checkpoint-bytes))
      (fn2-checkpoints (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-disposing* fn2-checkpoints))
      (fn2-checkpoint-teardown-debt (fn2-checkpoint-teardown-debt-put 0 (dispose-phase *fn2-checkpoint-dispose-phase-sources*) (dispose-cursor 0)))
      (before (fn2-test-table-snapshot-fn2-checkpoint-teardown-debt fn2-checkpoint-teardown-debt))
      (identity (fn2-checkpoint-teardown-retained-ownerp 0 19 7 0 1 fn2-checkpoint-teardown-debt fn2-checkpoints fn2-checkpoint-bytes))
      ((mv inspected cursor & & &)
       (fn2-checkpoint-teardown-inspect-children 0 19 7 0 1 0 fn2-checkpoint-teardown-debt fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-ops fn2-alloc-edges))
      ((mv selected & & & & & & & &) (fn2-checkpoint-teardown-select 0 7 0 1 fn2-checkpoint-teardown-debt fn2-checkpoints fn2-checkpoint-bytes)))
  (mv (and setup open identity
           (not (fn2-checkpoint-teardown-admission-ownerp 0 19 7 0 1 fn2-checkpoint-teardown-debt fn2-checkpoints fn2-checkpoint-bytes))
           (eq inspected :state) (= cursor 0) (eq selected :state)
           (equal before (fn2-test-table-snapshot-fn2-checkpoint-teardown-debt fn2-checkpoint-teardown-debt)))
      fn2-checkpoint-teardown-debt fn2-checkpoint-lifecycle fn2-csnapshot fn2-extents fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-commit-root fn2-fc fn2-checkpoint-bytes fn2-digests fn2-checkpoint-construction fn2-ops fn2-alloc-edges)))
(assert-event
 (fn2-run-with-local (fn2-checkpoint-teardown-debt fn2-checkpoint-lifecycle fn2-csnapshot fn2-extents fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-commit-root fn2-fc fn2-checkpoint-bytes fn2-digests fn2-checkpoint-construction fn2-ops fn2-alloc-edges)
  (fn2-cdru-body fn2-checkpoint-teardown-debt fn2-checkpoint-lifecycle fn2-csnapshot fn2-extents fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-commit-root fn2-fc fn2-checkpoint-bytes fn2-digests fn2-checkpoint-construction fn2-ops fn2-alloc-edges)))
