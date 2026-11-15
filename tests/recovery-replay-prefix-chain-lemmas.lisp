; Source proof leaves over ACTUAL candidate traversal. Unexecuted.
(in-package "ACL2")
(include-book "recovery-replay-prefix-state")
(defthm fn2-recovery-replay-canonical-zero
 (equal (fn2-recovery-replay-canonical-chain-p 0 token journal commit je ja fn2-core)
        (equal token 0))
 :hints (("Goal" :in-theory (enable fn2-recovery-replay-canonical-chain-p))))
(defthm fn2-recovery-replay-prefix-zero
 (equal (fn2-recovery-replay-consumed-prefix-p 0 cursor rank token left journal commit je ja fn2-core)
        (and (equal cursor token) (equal rank left)
             (fn2-recovery-replay-canonical-chain-p rank cursor journal commit je ja fn2-core)))
 :hints (("Goal" :in-theory (enable fn2-recovery-replay-consumed-prefix-p))))
(defthm fn2-recovery-replay-canonical-tail
 (implies
  (and (posp rank)
       (fn2-recovery-replay-canonical-chain-p rank token journal commit je ja fn2-core))
  (and (eq (mv-nth 0 (fn2-recovery-payload-node journal commit je ja token rank fn2-core)) :ok)
       (fn2-recovery-replay-canonical-chain-p (- rank 1)
        (mv-nth 6 (fn2-recovery-payload-node journal commit je ja token rank fn2-core))
        journal commit je ja fn2-core)))
 :hints (("Goal" :in-theory (enable fn2-recovery-replay-canonical-chain-p))))
; Extend exactly one actual consumed node once that node's adoption has
; settled. This lemma contains no allocator transition or alternate machine.
(defthm fn2-recovery-replay-prefix-extend-one
 (implies
  (and (natp consumed) (posp left)
       (fn2-recovery-replay-consumed-prefix-p consumed cursor rank token left journal commit je ja fn2-core)
       (eq (mv-nth 0 (fn2-recovery-payload-node journal commit je ja token left fn2-core)) :ok)
       (fn2-recovery-replay-position-owned-p
        (mv-nth 1 (fn2-recovery-payload-node journal commit je ja token left fn2-core))
        (mv-nth 2 (fn2-recovery-payload-node journal commit je ja token left fn2-core))
        (mv-nth 3 (fn2-recovery-payload-node journal commit je ja token left fn2-core))
        (mv-nth 4 (fn2-recovery-payload-node journal commit je ja token left fn2-core))
        (mv-nth 5 (fn2-recovery-payload-node journal commit je ja token left fn2-core)) fn2-core))
  (fn2-recovery-replay-consumed-prefix-p (+ 1 consumed) cursor rank
   (mv-nth 6 (fn2-recovery-payload-node journal commit je ja token left fn2-core))
   (- left 1) journal commit je ja fn2-core))
 :hints (("Goal"
  :induct (fn2-recovery-replay-consumed-prefix-p consumed cursor rank token left journal commit je ja fn2-core)
  :in-theory (enable fn2-recovery-replay-consumed-prefix-p fn2-recovery-replay-canonical-chain-p))))
; This is the non-vacuous arithmetic join COUNT = consumed + remaining.
(defthm fn2-recovery-replay-prefix-rank-accounting
 (implies
  (and (natp consumed) (natp rank) (natp left)
       (fn2-recovery-replay-consumed-prefix-p consumed cursor rank token left journal commit je ja fn2-core))
  (equal rank (+ consumed left)))
 :hints (("Goal"
  :induct (fn2-recovery-replay-consumed-prefix-p consumed cursor rank token left journal commit je ja fn2-core)
  :in-theory (enable fn2-recovery-replay-consumed-prefix-p fn2-recovery-payload-node
                    fn2-recovery-payload-linkp))))
