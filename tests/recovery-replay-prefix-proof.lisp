; SOURCE-ONLY owed actual transition theorems, not admitted/certified.
(in-package "ACL2")
(include-book "recovery-replay-prefix-state")
; Owed preservation statement over the actual mutation, not a second machine.
(defthm fn2-recovery-replay-adopt-preserves-carried-prefix
 (implies
  (and (fn2-corep fn2-core)
       (fn2-recovery-replay-carried-prefix-p id gen journal commit je ja tag fn2-core)
       (eq (mv-nth 0 (fn2-recovery-replay-adopt id gen fn2-core)) :more))
  (fn2-recovery-replay-carried-prefix-p id gen journal commit je ja tag
   (mv-nth 1 (fn2-recovery-replay-adopt id gen fn2-core))))
 :rule-classes nil)
; Completion is deliberately conditional on the reachable carried invariant.
; Raw-domain fabricated token0/left0 with unowned nodes is NOT covered.
(defthm fn2-recovery-replay-adopt-owned-settles-canonical-chain
 (implies
  (and (fn2-corep fn2-core)
       (fn2-recovery-replay-carried-prefix-p id gen journal commit je ja tag fn2-core)
       (eq (mv-nth 0 (fn2-recovery-replay-adopt id gen fn2-core)) :owned))
  (mv-let (code head count) (fn2-recovery-payload-head journal commit je ja fn2-core)
   (and (eq code :ok)
    (fn2-recovery-replay-journal-owned-p journal commit je ja fn2-core)
    (fn2-recovery-replay-consumed-prefix-p count head count 0 0 journal commit je ja fn2-core))))
 :rule-classes nil)
