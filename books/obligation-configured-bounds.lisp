; W9 configured numeric support, derived from the phase-aware Store relation.
; The relation is proof vocabulary and is never evaluated on a served read.
(in-package "ACL2")
(include-book "config-store-traces")
(include-book "retention-obligation-view-bounds")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-rov-configured-node-capacity-is-uint32
  (implies (fn-cnode-statep cn)
           (unsigned-byte-p 32
            (fn-retain-capacity (fn-node-retention (fn-cnode-node cn)))))
  :hints (("Goal" :in-theory
           (e/d (fn-cnode-statep fn-cfgp fn-cfg-valuep fn-record-uint32p
                  unsigned-byte-p integer-range-p)
                (fn-node-statep fn-cfg-shapep fn-cnode-shapep)))))

(defthm fn-rov-configured-replay-capacity-is-uint32
  (implies (consp (fn-cst-replay-node configs events frontier))
           (unsigned-byte-p 32
            (fn-retain-capacity
             (fn-node-retention (fn-cst-replay-node configs events frontier)))))
  :hints (("Goal" :in-theory
           (e/d (fn-cst-replay-node)
                (fn-cnode-statep fn-replay-advance-txid fn-cpr-replay
                 fn-replay-advance-okp)))))

(defthm fn-rov-store-configured-capacity-is-uint32
  (implies (fn-cst-final-configurationp st)
           (unsigned-byte-p 32 (fn-sn-capacity st)))
  :hints (("Goal" :in-theory
           (e/d (fn-cst-final-configurationp fn-cnode-statep fn-cfgp
                  fn-cfg-valuep fn-record-uint32p unsigned-byte-p integer-range-p)
                (fn-node-statep fn-cpr-replay fn-cfg-shapep fn-cnode-shapep
                 fn-cpr-replay-ok-is-configured)))))

(defthm fn-rov-retain-release-keeps-capacity-by-definition
  (equal (fn-retain-capacity (fn-retain-release retention id subject kind evidence))
         (fn-retain-capacity retention))
  :hints (("Goal" :in-theory (enable fn-retain-release))))
(defthm fn-rov-retain-admit-keeps-capacity-by-definition
  (equal (fn-retain-capacity (fn-retain-admit retention id subject kind evidence charge))
         (fn-retain-capacity retention))
  :hints (("Goal" :in-theory (enable fn-retain-admit))))

(defthm fn-rov-replay-keeps-capacity
  (implies (and (fn-node-statep node)
                (consp (fn-replay-apply-record node record)))
           (equal (fn-retain-capacity
                   (fn-node-retention (fn-replay-apply-record node record)))
                  (fn-retain-capacity (fn-node-retention node))))
  :hints (("Goal" :in-theory
           (e/d (fn-replay-apply-record fn-node-prepare-preserves-state
                  fn-replay-advance-preserves-node-statep
                  fn-cnode-node-complete-keeps-groups-and-capacity
                  fn-cnode-node-prepare-keeps-groups-and-capacity)
                (fn-node-prepare fn-node-complete fn-node-pending-matchesp
                 fn-replay-advance-txid fn-record-record-vocabulary
                 fn-record-shape-vocabulary fn-stxa-p fn-stxe-p fn-stxk-p
                 fn-held-p fn-hstxa-p fn-store-retention-event-p
                 fn-replay-composite-record)))))

(defthm fn-rov-initial-node-capacity-by-definition
  (equal (fn-retain-capacity (fn-node-retention (fn-node-initial-state groups capacity)))
         capacity)
  :hints (("Goal" :in-theory (enable fn-node-initial-state fn-retain-initial-state))))

(defthm fn-rov-configured-store-ledger-capacity-is-uint32
  (implies (fn-cst-relation st)
           (unsigned-byte-p 32
            (fn-retain-capacity (fn-node-retention (fn-sn-node st)))))
  :hints (("Goal"
           :use ((:instance fn-rov-store-configured-capacity-is-uint32)
                 (:instance fn-rov-configured-replay-capacity-is-uint32
                    (configs (fn-sn-config-history st))
                    (events (fn-sf-records (fn-sn-files st)))
                    (frontier (fn-sf-frontier (fn-sn-files st))))
                 (:instance fn-rov-configured-replay-capacity-is-uint32
                    (configs (fn-sn-config-history st))
                    (events (fn-sf-records (fn-sn-files st)))
                    (frontier (1- (fn-sf-frontier (fn-sn-files st))))))
           :in-theory
           (e/d (fn-cst-relation fn-cst-recoverablep fn-cst-pending-linkp
                  fn-cst-deferred-linkp fn-cst-completion-linkp fn-sn-statep
                  fn-cnode-node-complete-keeps-groups-and-capacity)
                (fn-node-initial-state fn-retain-initial-state
                 unsigned-byte-p fn-replay-identity-step
                 fn-rov-store-configured-capacity-is-uint32
                 fn-node-statep fn-cst-final-configurationp fn-cst-replay-node
                 fn-replay-apply-record fn-node-complete fn-sf-statep
                 fn-rov-configured-replay-capacity-is-uint32)))))

(defthm fn-rov-configured-store-view-is-uint64
  (implies (and (fn-cst-relation st)
                (fn-rov-correspondp view
                 (fn-retain-pins (fn-node-retention (fn-sn-node st)))))
           (and (unsigned-byte-p 64 (fn-rov-count view))
                (unsigned-byte-p 64 (car (fn-rov-subject subject view)))
                (unsigned-byte-p 64 (cdr (fn-rov-subject subject view)))))
  :hints (("Goal"
           :use ((:instance fn-rov-count-and-charge-are-uint64
                    (ledger (fn-node-retention (fn-sn-node st))))
                 (:instance fn-rov-configured-store-ledger-capacity-is-uint32))
           :in-theory
           (e/d (fn-cst-relation fn-sn-statep fn-node-statep unsigned-byte-p integer-range-p)
                (fn-rov-correspondp fn-rov-count fn-rov-subject fn-retain-statep
                 fn-cst-final-configurationp fn-cst-replay-node fn-cst-recoverablep
                 fn-cst-pending-linkp fn-cst-deferred-linkp fn-cst-completion-linkp
                 fn-sf-statep fn-rov-configured-store-ledger-capacity-is-uint32
                 fn-rov-count-and-charge-are-uint64)))))
