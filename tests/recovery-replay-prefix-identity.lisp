; Proof-only actual-carrier identity compatibility. Never a served scan.
; Establishing this from recorded allocator producers is a separate obligation.
(in-package "ACL2")
(include-book "recovery-replay-prefix-state")
(defun fn2-recovery-replay-identity-compatible-row-p (n p epoch allocation fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
 (if (zp n) t
  (and
   (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (compatible)
    (let ((q (- n 1)))
     (and (fn2-alloc-slotp q fn2-extents)
      (or (= q p) (= (fn2-extents-state q fn2-extents) *fn2-extent-state-free*)
          (not (and (= (fn2-extents-epoch q fn2-extents) epoch)
                    (= (fn2-extents-counter q fn2-extents) allocation)))))) compatible)
   (fn2-recovery-replay-identity-compatible-row-p (- n 1) p epoch allocation fn2-core))))
(defun fn2-recovery-replay-chain-identities (rank token journal commit je ja fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix rank)))
 (if (zp rank) nil
  (mv-let (code p epoch allocation kind owner next)
   (fn2-recovery-payload-node journal commit je ja token rank fn2-core)
   (declare (ignore p kind owner))
   (if (eq code :ok)
    (cons (cons epoch allocation)
     (fn2-recovery-replay-chain-identities (- rank 1) next journal commit je ja fn2-core)) nil))))
(defun fn2-recovery-replay-chain-live-compatible-p (rank token journal commit je ja fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix rank)))
 (if (zp rank) (and (equal rank 0) (equal token 0))
  (mv-let (code p epoch allocation kind owner next)
   (fn2-recovery-payload-node journal commit je ja token rank fn2-core)
   (declare (ignore kind owner))
   (and (eq code :ok)
    (fn2-recovery-replay-identity-compatible-row-p
     (mv-nth 0 (fn2-recovery-geometry fn2-core)) p epoch allocation fn2-core)
    (fn2-recovery-replay-chain-live-compatible-p (- rank 1) next journal commit je ja fn2-core)))))
(defun fn2-recovery-replay-identities-compatible-p (journal commit je ja fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (mv-let (code head count) (fn2-recovery-payload-head journal commit je ja fn2-core)
  (and (eq code :ok)
       (fn2-recovery-replay-canonical-chain-p count head journal commit je ja fn2-core)
       (fn2-recovery-replay-identity-compatible-row-p
        (mv-nth 0 (fn2-recovery-geometry fn2-core)) journal je ja fn2-core)
       (fn2-recovery-replay-chain-live-compatible-p count head journal commit je ja fn2-core)
       (no-duplicatesp-equal
        (cons (cons je ja) (fn2-recovery-replay-chain-identities count head journal commit je ja fn2-core))))))
