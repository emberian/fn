; Node writer bridge for the W9 projection. These are the node decisions
; reached by the live Store prepare/completion wrappers, not a new machine.
(in-package "ACL2")
(include-book "retention-obligation-view")
(include-book "node-invariants")

(defthm fn-rov-node-prepare-keeps-ledger
  (equal (fn-node-retention
          (fn-node-prepare node generation msgid payload groups id subject evidence charge stamp binding))
         (fn-node-retention node))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare)
                           (fn-node-statep fn-retain-admissiblep fn-retain-admit
                            fn-accept-prepare fn-node-make-stage)))))

(defthm fn-rov-stage-ledger-is-admit
  (implies (fn-node-stagep acceptance ledger stage)
           (equal (fn-node-stage-retention stage)
                  (fn-retain-admit ledger (fn-node-stage-id stage)
                    (fn-node-stage-subject stage) :archive
                    (fn-node-stage-evidence stage) (fn-node-stage-charge stage))))
  :hints (("Goal" :in-theory (e/d (fn-node-stagep) (fn-retain-admit)))))

(defthm fn-rov-valid-node-has-valid-ledger
  (implies (fn-node-statep node) (fn-retain-statep (fn-node-retention node)))
  :hints (("Goal" :in-theory (enable fn-node-statep))))
(defthm fn-rov-valid-node-has-valid-stage
  (implies (and (fn-node-statep node) (consp (fn-node-stage node)))
           (fn-node-stagep (fn-node-acceptance node) (fn-node-retention node)
                           (fn-node-stage node)))
  :hints (("Goal" :in-theory (enable fn-node-statep))))

(defthm fn-rov-node-complete-preserves-correspondence
  (implies (fn-rov-correspondp view (fn-retain-pins (fn-node-retention node)))
           (fn-rov-correspondp
            (fn-rov-update (fn-node-retention node)
              (fn-node-retention (fn-node-complete node txid generation status)) view)
            (fn-retain-pins
             (fn-node-retention (fn-node-complete node txid generation status)))))
  :hints (("Goal" :cases ((fn-node-statep node))
           :in-theory (e/d (fn-node-complete fn-node-pending-matchesp)
                                 (fn-node-statep fn-node-stagep fn-retain-statep
                                  fn-retain-admit fn-rov-update fn-rov-correspondp))
           :use ((:instance fn-rov-valid-node-has-valid-stage)))))

(defthm fn-rov-node-recover-preserves-correspondence
  (implies (fn-rov-correspondp view (fn-retain-pins (fn-node-retention node)))
           (fn-rov-correspondp
            (fn-rov-update (fn-node-retention node)
              (fn-node-retention (fn-node-recover node txid generation result)) view)
            (fn-retain-pins
             (fn-node-retention (fn-node-recover node txid generation result)))))
  :hints (("Goal" :cases ((fn-node-statep node))
           :in-theory (e/d (fn-node-recover)
                                 (fn-node-statep fn-node-stagep fn-retain-statep
                                  fn-retain-admit fn-rov-update fn-rov-correspondp))
           :use ((:instance fn-rov-valid-node-has-valid-stage)))))

(in-theory (disable fn-rov-node-prepare-keeps-ledger))
