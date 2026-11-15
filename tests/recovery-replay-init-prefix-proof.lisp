; SOURCE-ONLY structural prefix initialization from the ACTUAL scanner.
; Identity-index refinement is preserved by the exact allocator child frame,
; but its construction/admission producer proof is deliberately not asserted.
(in-package "ACL2")
(include-book "recovery-replay-init-proof")
(include-book "recovery-replay-prefix-state")
(defun fn2-recovery-frontier-current-chain-p (id fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (and (fn2-recovery-idp id fn2-core)
  (let* ((journal (fn2-machine-rc-pos id fn2-core))
         (commit (fn2-machine-rc-commit id fn2-core))
         (epoch (fn2-recovery-cand-epoch journal fn2-core))
         (allocation (fn2-recovery-cand-allocation journal fn2-core)))
   (mv-let (code head count) (fn2-recovery-payload-head journal commit epoch allocation fn2-core)
    (and (eq code :ok)
     (fn2-recovery-replay-canonical-chain-p count head journal commit epoch allocation fn2-core))))))
(defthm fn2-recovery-frontier-done-frames-payload-observers
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (equal (mv-nth 0 (fn2-recovery-frontier-step id fn2-core)) :done))
  (let ((after (mv-nth 1 (fn2-recovery-frontier-step id fn2-core))))
   (and (equal (fn2-recovery-payload-head journal commit epoch allocation after)
               (fn2-recovery-payload-head journal commit epoch allocation fn2-core))
        (equal (fn2-recovery-payload-node journal commit epoch allocation token left after)
               (fn2-recovery-payload-node journal commit epoch allocation token left fn2-core)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-recovery-payload-head fn2-recovery-payload-node
  fn2-recovery-payload-journal fn2-recovery-geometry))))
(defthm fn2-recovery-frontier-done-frames-canonical-chain
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (equal (mv-nth 0 (fn2-recovery-frontier-step id fn2-core)) :done))
  (equal (fn2-recovery-replay-canonical-chain-p rank token journal commit epoch allocation
           (mv-nth 1 (fn2-recovery-frontier-step id fn2-core)))
         (fn2-recovery-replay-canonical-chain-p rank token journal commit epoch allocation fn2-core)))
 :rule-classes nil
 :hints (("Goal"
  :induct (fn2-recovery-replay-canonical-chain-p rank token journal commit epoch allocation fn2-core)
  :in-theory (enable fn2-recovery-replay-canonical-chain-p)
  :use fn2-recovery-frontier-done-frames-payload-observers)))
(defthm fn2-recovery-frontier-done-initializes-actual-selected-prefix
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (equal (mv-nth 0 (fn2-recovery-frontier-step id fn2-core)) :done)
       (fn2-recovery-selected-current-p id fn2-core)
       (fn2-recovery-frontier-current-chain-p id fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))
                   (fn2-alloc-edges (fn2-core-alloc-edges fn2-core))) (valid)
        (fn2-alloc-ownership-invp fn2-extents fn2-alloc-edges) valid))
  (let ((journal (fn2-machine-rc-pos id fn2-core)))
   (fn2-recovery-replay-carried-prefix-p id (fn2-machine-generation id fn2-core)
    journal (fn2-machine-rc-commit id fn2-core)
    (fn2-recovery-cand-epoch journal fn2-core) (fn2-recovery-cand-allocation journal fn2-core)
    (fn2-machine-rc-base-tag id fn2-core)
    (mv-nth 1 (fn2-recovery-frontier-step id fn2-core)))))
 :rule-classes nil
 :hints (("Goal"
  :in-theory (enable fn2-recovery-frontier-current-chain-p fn2-recovery-replay-carried-prefix-p)
  :use (fn2-recovery-frontier-done-enters-authenticated-ownership
        fn2-recovery-frontier-frames-ownership-carriers
        fn2-recovery-frontier-done-frames-canonical-chain))))
