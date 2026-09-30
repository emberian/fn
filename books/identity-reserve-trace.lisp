; RET-010 / PRF-1134: the actual ordinary reservation gate followed by
; the actual post-reservation semantic refusal. Logical trace reference only:
; fn-olr-sn-reserve remains an unguard-verified boundary driver. This does
; not establish host serialization, incarnation isolation, or physical funding.
(in-package "ACL2")
(include-book "store-identity-reserve")
(include-book "refusal-headroom")

(defun fn-idrt-step (s debt)
  (declare (xargs :guard t :verify-guards nil))
  (if (natp (fn-idr-reservation s debt nil)) (fn-rfh-step s) s))

(defun fn-idrt-run (n s debt)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (zp n) s (fn-idrt-run (1- n) (fn-idrt-step s debt) debt)))

(local
 (defthm fn-idrt-gate-on-ready
   (implies (fn-rfh-ready-p s)
    (equal (fn-idr-reservation s debt nil)
           (fn-idr-next (fn-sf-frontier (fn-sn-files s)) debt :ordinary)))
   :hints (("Goal" :in-theory (enable fn-rfh-ready-p fn-idr-reservation
                                      fn-idr-purpose)))))

(local
 (defthm fn-idrt-step-preserves-ready
  (implies (fn-rfh-ready-p s) (fn-rfh-ready-p (fn-idrt-step s debt)))
  :hints (("Goal" :in-theory (enable fn-idrt-step)))))

(local
 (defthm fn-idrt-step-keeps-promised-identity-headroom
  (implies (and (fn-rfh-ready-p s)
                (<= (nfix debt)
                    (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files s)))))
   (<= (nfix debt)
       (- *fn-sf-max-uint*
          (fn-sf-frontier (fn-sn-files (fn-idrt-step s debt))))))
  :hints (("Goal"
           :use ((:instance fn-idr-ordinary-leaves-promised-release-identities
                    (frontier (fn-sf-frontier (fn-sn-files s))))
                 fn-rfh-step-below-ceiling-advances-one)
           :in-theory (enable fn-idrt-step fn-idr-next)))))

(defthm fn-idrt-run-keeps-promised-identity-headroom
  (implies (and (fn-rfh-ready-p s)
                (<= (nfix debt)
                    (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files s)))))
   (and (fn-rfh-ready-p (fn-idrt-run n s debt))
        (<= (nfix debt)
            (- *fn-sf-max-uint*
               (fn-sf-frontier (fn-sn-files (fn-idrt-run n s debt)))))))
  :hints (("Goal" :induct (fn-idrt-run n s debt)
           :in-theory (e/d (fn-idrt-run) (fn-idrt-step fn-rfh-ready-p)) )
          ("Subgoal *1/2"
           :use (fn-idrt-step-preserves-ready
                 fn-idrt-step-keeps-promised-identity-headroom)
           :in-theory (disable fn-idrt-step fn-rfh-ready-p
                         fn-idrt-step-preserves-ready
                         fn-idrt-step-keeps-promised-identity-headroom)) ))


(local
 (defthm fn-idrt-step-keeps-records-and-configuration
   (and (equal (fn-sf-records (fn-sn-files (fn-idrt-step s debt)))
               (fn-sf-records (fn-sn-files s)))
        (equal (fn-sn-groups (fn-idrt-step s debt)) (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-idrt-step s debt)) (fn-sn-capacity s)))
   :hints (("Goal" :in-theory (enable fn-idrt-step)))))

(defthm fn-idrt-run-keeps-records-and-configuration
  (and (equal (fn-sf-records (fn-sn-files (fn-idrt-run n s debt)))
              (fn-sf-records (fn-sn-files s)))
       (equal (fn-sn-groups (fn-idrt-run n s debt)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-idrt-run n s debt)) (fn-sn-capacity s)))
  :hints (("Goal" :induct (fn-idrt-run n s debt)
           :in-theory (e/d (fn-idrt-run) (fn-idrt-step fn-rfh-step)))))


; Exact immutable Store field frame, not a new full W8 abstraction. Payload
; handles are unchanged on this refusal path. No arena relocation is claimed.
; The two spent identity coordinates (file frontier and node next-txid) and
; transient physical file phases belong to the separate resource effect.
(defun fn-idrt-node-frame (node)
  (declare (xargs :guard t))
  (let ((a (fn-node-acceptance node)))
    (list (fn-state-groups a) (fn-state-nexts a) (fn-state-articles a)
          (fn-state-pending a) (fn-state-fenced a)
          (fn-node-retention node) (fn-node-stage node) (fn-node-bindings node))))
(defun fn-idrt-store-metadata (s)
  (declare (xargs :guard t))
  (list (fn-idrt-node-frame (fn-sn-node s))
        (fn-sn-groups s) (fn-sn-capacity s) (fn-sn-config-history s)
        (fn-sn-identity-next s) (fn-sn-keyring-snapshots s)
        (fn-sn-keyring s) (fn-sn-keyring-generation s)
        (fn-sn-verdicts s) (fn-sn-index s) (fn-sn-event-index s)
        (fn-sn-consumer s) (fn-sn-topic s)))

(defun fn-idrt-store-frame (s)
  (declare (xargs :guard t))
  (list (fn-sf-records (fn-sn-files s)) (fn-idrt-store-metadata s)))

(local
 (defthm fn-idrt-node-frame-of-advance
   (equal (fn-idrt-node-frame (fn-replay-advance-txid node txid))
          (fn-idrt-node-frame node))
   :hints (("Goal" :in-theory
            (e/d (fn-idrt-node-frame fn-replay-advance-txid)
                 (fn-node-statep))))))

(local
 (defthm fn-idrt-step-keeps-store-metadata
   (equal (fn-idrt-store-metadata (fn-idrt-step s debt))
          (fn-idrt-store-metadata s))
   :hints (("Goal" :in-theory
            (e/d (fn-idrt-step fn-idrt-store-metadata fn-rfh-step
                  fn-sn-refuse-reservation fn-olr-sn-reserve fn-sn-io fn-sn-update)
                 (fn-idrt-node-frame fn-replay-advance-txid
                  fn-sn-refuse-reservation-enabledp fn-sn-statep))))))
(local
 (defthm fn-idrt-step-keeps-full-store-frame
   (equal (fn-idrt-store-frame (fn-idrt-step s debt))
          (fn-idrt-store-frame s))
   :hints (("Goal" :in-theory (e/d (fn-idrt-store-frame)
                                 (fn-idrt-step fn-idrt-store-metadata))))))

(defthm fn-idrt-protected-refusals-keep-full-store-frame
  (equal (fn-idrt-store-frame (fn-idrt-run n s debt))
         (fn-idrt-store-frame s))
  :hints (("Goal" :induct (fn-idrt-run n s debt)
           :in-theory (e/d (fn-idrt-run)
                           (fn-idrt-step fn-idrt-store-frame)))))

(in-theory (disable fn-idrt-step fn-idrt-run fn-idrt-node-frame fn-idrt-store-frame))
