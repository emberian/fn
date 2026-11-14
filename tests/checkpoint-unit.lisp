(in-package "ACL2")
(include-book "../books/checkpoint")

; Local frontier control only: exercise physical reuse through the allocator,
; then ask the new location decision about the old and new identities. This is
; not a served recovery/checkpoint publication witness.
(defun fn2-checkpoint-location-test-body (fn2-extents)
 (declare (xargs :stobjs fn2-extents :verify-guards nil))
 (b* ((fn2-extents (fn2-alloc-init 1 fn2-extents))
      ((mv begun fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents))
      ((mv reserved & e epoch old fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv committed fn2-extents) (fn2-alloc-commit-allocation e epoch old 1 11 fn2-extents))
      ((mv retired fn2-extents) (fn2-alloc-retire e epoch old 2 fn2-extents))
      ((mv covered fn2-extents) (fn2-alloc-checkpoint-advance 2 1 fn2-extents))
      ((mv released fn2-extents) (fn2-alloc-release e epoch old fn2-extents))
      ((mv reused & next next-epoch fresh fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv installed fn2-extents) (fn2-alloc-commit-allocation next next-epoch fresh 1 12 fn2-extents))
      (antecedent (and (eq begun :ok) (eq reserved :ok) (eq committed :ok) (eq retired :ok)
                       (eq covered :ok) (eq released :ok) (eq reused :ok) (eq installed :ok)
                       (equal e next) (not (equal old fresh)) (fn2-alloc-invp fn2-extents)))
      (historical (fn2-checkpoint-location-code 2 1 e epoch old fn2-extents))
      ; Removal control: without the covering cut, the same old ref conflicts.
      (uncovered (fn2-checkpoint-location-code 0 1 e epoch old fn2-extents))
      (current (fn2-checkpoint-location-code 2 3 next next-epoch fresh fn2-extents))
      (stale (fn2-checkpoint-location-code 2 3 e epoch old fn2-extents)))
  (mv (and antecedent (eq historical :historical) (eq uncovered :conflict)
           (eq current :current) (eq stale :conflict)) fn2-extents)))
(defun fn2-checkpoint-location-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-extents
  (mv-let (answer fn2-extents) (fn2-checkpoint-location-test-body fn2-extents) answer)))
(assert-event (fn2-checkpoint-location-test))
