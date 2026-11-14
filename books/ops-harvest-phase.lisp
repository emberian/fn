; Proof-side legal lifecycle admission for pending completion cells.
(in-package "ACL2")
(include-book "vocab")

(defthm fn2-post-eligiblep-completion-phase
 (implies (fn2-post-eligiblep cell slot gen fn2-ops)
          (fn2-completion-phasep cell (fn2-ops-phase slot fn2-ops)))
 :hints (("Goal" :in-theory (e/d (fn2-post-eligiblep fn2-completion-phasep)
  (fn2-op-handle-code fn2-ops-phase fn2-ops-c0-posted fn2-ops-c1-posted fn2-ops-may-release)))))
(defthm fn2-row-semantic-pending-phase
 (implies (and (fn2-ops-row-semanticp n fn2-ops)
               (natp n) (natp slot) (< slot n) (natp (fn2-ops-phase slot fn2-ops))
               (unsigned-byte-p 1 cell)
               (if (equal cell 0)
                 (and (equal (fn2-ops-c0-posted slot fn2-ops) 1) (equal (fn2-ops-c0-harvested slot fn2-ops) 0))
                 (and (equal (fn2-ops-c1-posted slot fn2-ops) 1) (equal (fn2-ops-c1-harvested slot fn2-ops) 0))))
          (fn2-completion-phasep cell (fn2-ops-phase slot fn2-ops)))
 :hints (("Goal" :induct (fn2-ops-row-semanticp n fn2-ops)
   :in-theory (e/d (fn2-ops-row-semanticp fn2-completion-phasep)
    (fn2-ops-phase fn2-ops-kind fn2-ops-gen fn2-ops-gen-limit fn2-ops-c0-posted fn2-ops-c0-harvested
     fn2-ops-c1-posted fn2-ops-c1-harvested fn2-ops-may-release fn2-ops-c0-aux0 fn2-post-payloadp
     fn2-ops-c0-event fn2-ops-c1-event fn2-ops-c0-outcome fn2-ops-c1-outcome fn2-ops-c0-reason fn2-ops-c1-reason
     fn2-action-completionp)))))
(defthm fn2-peek-posted-legal-phase
 (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)
               (fn2-ops-row-semanticp (fn2-ops-rows fn2-ops) fn2-ops)
               (equal (mv-nth 0 (fn2-ops-peek-posted fn2-ops)) t))
          (fn2-completion-phasep
           (mv-nth 2 (fn2-ops-peek-posted fn2-ops))
           (fn2-ops-phase (mv-nth 1 (fn2-ops-peek-posted fn2-ops)) fn2-ops)))
 :hints (("Goal"
  :use ((:instance fn2-row-semantic-pending-phase
          (n (fn2-ops-rows fn2-ops))
          (slot (mv-nth 1 (fn2-ops-peek-posted fn2-ops)))
          (cell (mv-nth 2 (fn2-ops-peek-posted fn2-ops)))))
  :in-theory (e/d (fn2-ops-peek-posted fn2-op-slotp)
   (fn2-row-semantic-pending-phase fn2-ops-row-semanticp fn2-completion-phasep fn2-opsp fn2-ops-wfp
    fn2-ops-rows fn2-ops-phase fn2-ops-post-head fn2-ops-post-count fn2-ops-posted-fifo-length fn2-ops-posted-fifoi
    fn2-ops-c0-posted fn2-ops-c0-harvested fn2-ops-c1-posted fn2-ops-c1-harvested)))))
