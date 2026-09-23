; Open a physical image under its ordered configuration and Store histories.
; This runs once at process recovery. It carries no host-derived group table or
; capacity and leaves the existing five recovery barriers to the file kernel.
(in-package "ACL2")
(include-book "config-physical-replay")
(include-book "store-observed")

(defun fn-cpo-install (st cn configs)
  (declare (xargs :guard t))
  (fn-sn-make-v4
   (fn-cnode-domain-of (fn-cnode-config cn))
   (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn)))
   (fn-sn-files st) (fn-cnode-node cn)
   (fn-sn-keyring st) (fn-sn-index st)
   (fn-sn-keyring-generation st) (fn-sn-verdicts st)
   (fn-sn-keyring-snapshots st) (fn-sn-identity-next st)
   configs (fn-sn-consumer st)))

(defun fn-cpo-open-observed (configs frontier events)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (null configs)
          (not (fn-sn-observed-historyp frontier events)))
      (fn-sn-open-error :history)
    (let ((replayed (fn-cpr-replay configs events)))
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-sn-open-error :replay)
        (let* ((cn (fn-replay-result-node replayed))
               (node (fn-cnode-node cn)))
          (if (not (and (fn-cnode-statep cn)
                        (fn-replay-advance-okp node frontier)))
              (fn-sn-open-error :frontier)
            (let* ((advanced (fn-replay-advance-txid node frontier))
                   (config (fn-cnode-config cn))
                   (identity (fn-replay-identity events))
                   (consumer (fn-cpe-projection-replay nil events 0))
                   (files (fn-sf-make :recovering frontier nil events
                                      nil nil nil 0))
                   (seed (fn-sn-observed-seed
                          (fn-cnode-domain-of config)
                          (fn-cfg-capacity (fn-cfg-value config))
                          frontier events))
                   (opened (fn-sn-with-consumer
                            (fn-cpo-install
                             (fn-sn-update-replayed
                              seed files advanced
                              (fn-stx-index-of-store (fn-stx-store advanced) nil)
                              identity)
                             (fn-cnode-make advanced config) configs)
                            (fn-cp-nth 1 consumer))))
              (if (and (equal (fn-stxk-context-kind identity) :ok)
                       (eq (car consumer) :ok)
                       (fn-sn-statep opened))
                  (fn-sn-open-ok opened)
                (fn-sn-open-error :identity)))))))))

(verify-guards fn-cpo-open-observed
  :hints (("Goal"
           :use ((:instance fn-cpr-replay-ok-is-configured
                            (configs configs) (events events)))
           :in-theory (e/d (fn-cnode-statep)
                           (fn-cpr-replay fn-cpr-loop fn-sn-statep
                            fn-cpr-replay-ok-is-configured)))))

; Proof-only relation for the observed recovery boundary. Future live Store
; transitions must carry the configuration history to preserve this relation;
; the current Store record has no such field yet.
(defun fn-cpo-history-relation (st)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((events (fn-sf-records (fn-sn-files st)))
         (frontier (fn-sf-frontier (fn-sn-files st)))
         (replayed (fn-cpr-replay (fn-sn-config-history st) events))
         (cn (fn-replay-result-node replayed)))
    (and (fn-sn-statep st)
         (fn-sn-observed-historyp frontier events)
         (equal (fn-replay-result-kind replayed) :ok)
         (fn-cnode-statep cn)
         (fn-replay-advance-okp (fn-cnode-node cn) frontier)
         (equal (fn-sn-node st)
                (fn-replay-advance-txid (fn-cnode-node cn) frontier))
         (equal (fn-sn-groups st)
                (fn-cnode-domain-of (fn-cnode-config cn)))
         (equal (fn-sn-capacity st)
                (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn)))))))

(verify-guards fn-cpo-history-relation
  :hints (("Goal"
           :use ((:instance fn-cpr-replay-ok-is-configured
                            (configs (fn-sn-config-history st))
                            (events (fn-sf-records (fn-sn-files st)))))
           :in-theory (e/d (fn-cnode-statep)
                           (fn-cpr-replay fn-cpr-loop fn-sn-statep
                            fn-cpr-replay-ok-is-configured)))))

; Durable configuration publication is an administrative transition, never
; a per-command served path. The candidate is replayed against the carried
; physical history at its historical reservation total. An uncertain write
; has no call to this transition; recovery re-observes both directories.
(defun fn-cpo-configure-durable (st record)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((configs (fn-sn-config-history st))
         (events (fn-sf-records (fn-sn-files st)))
         (frontier (fn-sf-frontier (fn-sn-files st))))
    (if (and (fn-cpo-history-relation st)
             (true-listp configs)
             (equal (fn-sf-phase (fn-sn-files st)) :ready)
             (fn-cfg-recordp record)
             (equal (fn-cfg-record-txid record) frontier))
        (let* ((next-configs (append configs (list record)))
               (replayed (fn-cpr-replay next-configs events))
               (cn (fn-replay-result-node replayed)))
          (if (and (equal (fn-replay-result-kind replayed) :ok)
                   (fn-cnode-statep cn)
                   (fn-replay-advance-okp (fn-cnode-node cn) frontier))
              (let* ((advanced (fn-replay-advance-txid
                                (fn-cnode-node cn) frontier))
                     (candidate
                      (fn-cpo-install
                       st (fn-cnode-make advanced (fn-cnode-config cn))
                       next-configs)))
                (if (fn-sn-statep candidate) candidate st))
            st))
      st)))

(verify-guards fn-cpo-configure-durable
  :hints (("Goal"
           :use ((:instance fn-cpr-replay-ok-is-configured
                            (configs (append (fn-sn-config-history st)
                                             (list record)))
                            (events (fn-sf-records (fn-sn-files st)))))
           :in-theory (e/d (fn-cnode-statep)
                           (fn-cpr-replay fn-cpr-loop fn-sn-statep
                            fn-cpr-replay-ok-is-configured)))))

(defthm fn-cpo-configure-durable-keeps-observed-events
  (equal (fn-sf-records (fn-sn-files (fn-cpo-configure-durable st record)))
         (fn-sf-records (fn-sn-files st)))
  :hints (("Goal" :in-theory (enable fn-cpo-configure-durable
                                      fn-cpo-install))))

(defthm fn-cpo-configure-durable-keeps-frontier
  (equal (fn-sf-frontier (fn-sn-files (fn-cpo-configure-durable st record)))
         (fn-sf-frontier (fn-sn-files st)))
  :hints (("Goal" :in-theory (enable fn-cpo-configure-durable
                                      fn-cpo-install))))

(defthm fn-cpo-configure-durable-preserves-history-relation
  (implies (fn-cpo-history-relation st)
           (fn-cpo-history-relation
            (fn-cpo-configure-durable st record)))
  :hints (("Goal" :in-theory (e/d (fn-cpo-configure-durable
                                   fn-cpo-history-relation fn-cpo-install)
                                  (fn-cpr-replay fn-cpr-loop
                                   fn-sn-statep fn-cnode-statep)))))

; The caller sees the complete observed journal and the parameters from the
; final *ordered* configuration. No barrier has been reported at open.
(defthm fn-cpo-open-success-exact-image
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (let* ((st (fn-sn-open-state
                       (fn-cpo-open-observed configs frontier events)))
                  (cn (fn-replay-result-node
                       (fn-cpr-replay configs events))))
             (and (equal (fn-sf-records (fn-sn-files st)) events)
                  (equal (fn-sf-frontier (fn-sn-files st)) frontier)
                  (equal (fn-sf-phase (fn-sn-files st)) :recovering)
                  (equal (fn-sf-barriers (fn-sn-files st)) 0)
                  (equal (fn-sn-config-history st) configs)
                  (equal (fn-sn-groups st) (fn-cnode-domain cn))
                  (equal (fn-sn-capacity st)
                         (fn-cfg-capacity
                          (fn-cfg-value (fn-cnode-config cn)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-open-observed fn-cpo-install
                 fn-sn-update-replayed fn-sn-open-okp fn-cnode-domain)
                (fn-cpr-replay fn-cpr-loop fn-replay-identity
                 fn-replay-identity-loop fn-stx-index-of-store
                 fn-sn-statep fn-cnode-statep fn-sn-observed-seed
                 fn-replay-advance-txid)))))

(defthm fn-cpo-open-success-has-historical-relation
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (fn-cpo-history-relation
            (fn-sn-open-state
             (fn-cpo-open-observed configs frontier events))))
  :hints (("Goal" :in-theory (enable fn-cpo-history-relation
                                      fn-cpo-open-observed fn-sn-open-okp))))

(deftheory fn-cpo-vocabulary '(fn-cpo-install fn-cpo-open-observed
                             fn-cpo-history-relation fn-cpo-configure-durable))
(in-theory (disable fn-cpo-vocabulary))
