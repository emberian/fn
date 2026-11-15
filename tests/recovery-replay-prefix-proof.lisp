; SOURCE-ONLY owed actual transition theorems, not admitted/certified.
(in-package "ACL2")
(include-book "recovery-replay-prefix-chain-lemmas")
(include-book "recovery-replay-prefix-frame-lemmas")
; Preserve the exact original formula as evidence. Source tracing identifies
; a duplicate historical identity counterexample; the executable control is
; unrun. This original obligation must not be presented as proved.
(defconst *fn2-recovery-replay-original-preservation-formula*
 ' (implies
  (and (fn2-corep fn2-core)
       (fn2-recovery-replay-carried-prefix-p id gen journal commit je ja tag fn2-core)
       (eq (mv-nth 0 (fn2-recovery-replay-adopt id gen fn2-core)) :more))
  (fn2-recovery-replay-carried-prefix-p id gen journal commit je ja tag
   (mv-nth 1 (fn2-recovery-replay-adopt id gen fn2-core)))))
; Strengthening is explicit and separately named: initialization must establish
; compatibility from actual producer/prepass evidence, not assume it silently.
(defthm fn2-recovery-replay-adopt-preserves-compatible-carried-prefix
 (implies
  (and (fn2-corep fn2-core)
       (fn2-recovery-replay-carried-prefix-p id gen journal commit je ja tag fn2-core)
       (fn2-recovery-replay-identities-compatible-p journal commit je ja fn2-core)
       (eq (mv-nth 0 (fn2-recovery-replay-adopt id gen fn2-core)) :more))
  (and
   (fn2-recovery-replay-carried-prefix-p id gen journal commit je ja tag
    (mv-nth 1 (fn2-recovery-replay-adopt id gen fn2-core)))
   (fn2-recovery-replay-identities-compatible-p journal commit je ja
    (mv-nth 1 (fn2-recovery-replay-adopt id gen fn2-core)))))
 :rule-classes nil
 :hints (("Goal"
  :cases ((member-equal (fn2-machine-rc-stage id fn2-core) '(5 6))
          (equal (mv-nth 0
            (fn2-recovery-selected-adopt-position id gen
             (if (member-equal (fn2-machine-rc-stage id fn2-core) '(5 6)) journal
              (mv-nth 1 (fn2-recovery-payload-node journal commit je ja
               (fn2-machine-rc-own-token id fn2-core) (fn2-machine-rc-own-left id fn2-core) fn2-core)))
             (if (member-equal (fn2-machine-rc-stage id fn2-core) '(5 7)) 2 3) fn2-core)) :adopted))
  :in-theory (enable fn2-recovery-replay-adopt fn2-recovery-replay-carried-prefix-p)
  :use (fn2-recovery-replay-prefix-extend-one
        fn2-recovery-replay-adopt-preserves-identity-compatibility
        fn2-recovery-selected-adopt-position-establishes-recorded-owner
        fn2-recovery-selected-adopt-position-preserves-allocator-with-compatible-identity))))
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
 :rule-classes nil
 :hints (("Goal"
  :in-theory (enable fn2-recovery-replay-adopt fn2-recovery-replay-carried-prefix-p)
  :use (fn2-recovery-selected-adopt-position-never-owned))))
