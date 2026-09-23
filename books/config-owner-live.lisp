; Atomic logical publication of a durable configuration into the served owner.
; The physical record has already passed the host's immutable publication
; barrier.  This function is administrative, never a per-command served path.
(in-package "ACL2")
(include-book "owner-config")
(include-book "config-store-traces")

(defun fn-ocl-owner-with-store (o st)
  (declare (xargs :guard t))
  (fn-own-refresh
   (fn-own-make st (fn-own-view o) (fn-own-conns o)
                (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger o)
                (fn-own-clock o) (fn-own-facts o)
                (fn-own-config o) (fn-own-queue o)
                (fn-own-inflight o) (fn-own-feeds o))))

(defun fn-ocl-store-config (st)
  (declare (xargs :guard t))
  (fn-cnode-config
   (fn-replay-result-node
    (fn-cpr-replay (fn-sn-config-history st)
                   (fn-sf-records (fn-sn-files st))))))

(defun fn-ocl-complete (oc)
  (declare (xargs :guard (fn-sn-statep
                          (fn-own-store (fn-ocfg-owner oc)))))
  (let ((record (fn-ocfg-staged oc)))
    (if record
        (let* ((o (fn-ocfg-owner oc))
               (old-store (fn-own-store o))
               (new-store (fn-cpo-configure-durable old-store record)))
          ; A durable physical record that cannot be applied to the carried
          ; history is a recovery event.  Keep the stage so the host fences
          ; instead of returning an accepted live configuration.
          (if (equal (fn-sn-config-history new-store)
                     (fn-sn-config-history old-store))
              oc
            (fn-ocfg-make
             (fn-ocl-owner-with-store o new-store)
             (fn-ocl-store-config new-store)
             (fn-ocfg-pins oc) nil)))
      (fn-ocfg-make (fn-own-complete (fn-ocfg-owner oc))
                    (fn-ocfg-config oc) (fn-ocfg-pins oc) nil))))

(defthm fn-ocl-complete-keeps-existing-pins
  (equal (fn-ocfg-pins (fn-ocl-complete oc))
         (fn-ocfg-pins oc))
  :hints (("Goal" :in-theory (enable fn-ocl-complete))))

(defthm fn-ocl-complete-keeps-existing-served-table
  (equal (fn-ocfg-served (fn-ocl-complete oc) id)
         (fn-ocfg-served oc id))
  :hints (("Goal" :in-theory (enable fn-ocfg-served fn-ocfg-conn-config))))

(defthm fn-ocl-complete-success-install-exact-store
  (implies (and (fn-ocfg-staged oc)
                (not (fn-ocfg-staged (fn-ocl-complete oc))))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc)))
                  (fn-cpo-configure-durable
                   (fn-own-store (fn-ocfg-owner oc))
                   (fn-ocfg-staged oc))))
  :hints (("Goal" :in-theory (enable fn-ocl-complete fn-ocl-owner-with-store
                                     fn-own-refresh-keeps-fields))))

(defthm fn-ocl-durable-keeps-file-phase
  (equal (fn-sf-phase (fn-sn-files (fn-cpo-configure-durable st record)))
         (fn-sf-phase (fn-sn-files st)))
  :hints (("Goal" :in-theory (e/d (fn-cpo-configure-durable fn-cpo-install)
                                  (fn-cpo-history-relation fn-cpr-replay)))))

(defthm fn-ocl-durable-keeps-history-proper
  (implies (true-listp (fn-sn-config-history st))
           (true-listp
            (fn-sn-config-history (fn-cpo-configure-durable st record))))
  :hints (("Goal" :in-theory (e/d (fn-cpo-configure-durable fn-cpo-install)
                                  (fn-cpo-history-relation fn-cpr-replay)))))

(defthm fn-ocl-complete-success-preserves-historical-store-relation
  (implies (and (fn-ocfg-staged oc)
                (fn-cpo-history-relation
                 (fn-own-store (fn-ocfg-owner oc)))
                (true-listp (fn-sn-config-history
                             (fn-own-store (fn-ocfg-owner oc))))
                (fn-snt-idle-phasep
                 (fn-sf-phase
                  (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                (not (fn-ocfg-staged (fn-ocl-complete oc))))
           (fn-cst-relation
            (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cpo-configure-durable-preserves-history-relation
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-cst-idle-from-observed-history
                            (st (fn-cpo-configure-durable
                                 (fn-own-store (fn-ocfg-owner oc))
                                 (fn-ocfg-staged oc)))))
           :in-theory (e/d (fn-ocl-complete fn-ocl-owner-with-store
                            fn-own-refresh-keeps-fields)
                           (fn-cpo-configure-durable fn-cpo-history-relation
                            fn-cst-relation)))))

; A reader archive is reconstructed with the configuration generation that
; connection pinned, not today's capacity. The config prefix is identified
; by its dense generation; the Store prefix by the connection's journal
; version. This proof-only comparison runs over neither served command nor
; native open. It also checks the reader's selected group against its pin.
(defun fn-ocl-conn-historyp (oc conn)
  (declare (xargs :guard t))
  (let* ((st (fn-own-store (fn-ocfg-owner oc)))
         (pin (fn-ocfg-conn-config oc (fn-own-conn-id conn)))
         (configs (fn-sn-config-history st))
         (events (fn-sf-records (fn-sn-files st)))
         (generation (fn-cfg-generation pin))
         (version (fn-own-conn-version conn))
         (config-prefix (fn-own-take generation configs))
         (event-prefix (fn-own-take version events))
         (replayed (fn-cpr-replay config-prefix event-prefix))
         (node (fn-cst-replay-node config-prefix event-prefix
                                   (fn-own-conn-frontier conn))))
    (and (fn-own-conn-shapep conn)
         (fn-cfgp pin)
         (natp generation)
         (<= generation (len configs))
         (natp version)
         (<= version (len events))
         (equal (fn-replay-result-kind replayed) :ok)
         (equal (fn-cnode-config (fn-replay-result-node replayed)) pin)
         (fn-node-statep node)
         (equal (fn-own-conn-archive conn) (fn-node-acceptance node))
         (fn-own-conn-boundedp conn (fn-cnode-domain-of pin)))))

(defun fn-ocl-conns-historyp (oc conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (and (fn-ocl-conn-historyp oc (car conns))
           (fn-ocl-conns-historyp oc (cdr conns)))
    (null conns)))

(defthm fn-ocl-take-before-appended-config
  (implies (and (natp n) (<= n (len xs)))
           (equal (fn-own-take n (append xs (list record)))
                  (fn-own-take n xs)))
  :hints (("Goal" :induct (fn-own-take n xs))))

(defthm fn-ocl-length-after-appended-config
  (equal (len (append xs (list record)))
         (+ 1 (len xs)))
  :hints (("Goal" :induct (len xs))))

(defthm fn-ocl-success-appends-exact-config-history
  (implies (and (fn-ocfg-staged oc)
                (not (fn-ocfg-staged (fn-ocl-complete oc))))
           (equal (fn-sn-config-history
                   (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc))))
                  (append (fn-sn-config-history
                           (fn-own-store (fn-ocfg-owner oc)))
                          (list (fn-ocfg-staged oc)))))
  :hints (("Goal" :in-theory
           (e/d (fn-ocl-complete fn-ocl-owner-with-store
                 fn-cpo-configure-durable fn-cpo-install
                 fn-own-refresh-keeps-fields)
                (fn-cpo-history-relation fn-cpr-replay)))))

(defthm fn-ocl-conn-historyp-under-appended-configuration
  (implies
   (and (fn-ocl-conn-historyp oc conn)
        (equal (fn-ocfg-pins next) (fn-ocfg-pins oc))
        (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner next)))
               (append (fn-sn-config-history
                        (fn-own-store (fn-ocfg-owner oc)))
                       (list record)))
        (equal (fn-sf-records (fn-sn-files
                              (fn-own-store (fn-ocfg-owner next))))
               (fn-sf-records (fn-sn-files
                               (fn-own-store (fn-ocfg-owner oc))))))
   (fn-ocl-conn-historyp next conn))
  :hints (("Goal" :in-theory (e/d (fn-ocl-conn-historyp
                                    fn-ocfg-conn-config)
                                   (fn-cpr-replay fn-cst-replay-node)))))

(defthm fn-ocl-conns-historyp-under-appended-configuration
  (implies
   (and (fn-ocl-conns-historyp oc conns)
        (equal (fn-ocfg-pins next) (fn-ocfg-pins oc))
        (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner next)))
               (append (fn-sn-config-history
                        (fn-own-store (fn-ocfg-owner oc)))
                       (list record)))
        (equal (fn-sf-records (fn-sn-files
                              (fn-own-store (fn-ocfg-owner next))))
               (fn-sf-records (fn-sn-files
                               (fn-own-store (fn-ocfg-owner oc))))))
   (fn-ocl-conns-historyp next conns))
  :hints (("Goal" :induct (fn-ocl-conns-historyp oc conns)
           :in-theory (disable fn-ocl-conn-historyp))))

(defthm fn-ocl-staged-complete-keeps-store-events
  (implies (fn-ocfg-staged oc)
           (equal (fn-sf-records
                   (fn-sn-files
                    (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc)))))
                  (fn-sf-records
                   (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
  :hints (("Goal" :in-theory
           (e/d (fn-ocl-complete fn-ocl-owner-with-store
                 fn-own-refresh-keeps-fields)
                (fn-cpo-configure-durable)))))

(defthm fn-ocl-staged-complete-keeps-connections
  (implies (fn-ocfg-staged oc)
           (equal (fn-own-conns (fn-ocfg-owner (fn-ocl-complete oc)))
                  (fn-own-conns (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory
           (e/d (fn-ocl-complete fn-ocl-owner-with-store
                 fn-own-refresh-keeps-fields)
                (fn-cpo-configure-durable)))))

(defthm fn-ocl-staged-but-not-installed-is-unchanged
  (implies (and (fn-ocfg-staged oc)
                (fn-ocfg-staged (fn-ocl-complete oc)))
           (equal (fn-ocl-complete oc) oc))
  :hints (("Goal" :in-theory (enable fn-ocl-complete))))

(defthm fn-ocl-complete-preserves-pinned-connection-histories
  (implies (and (fn-ocfg-staged oc)
                (fn-ocl-conns-historyp oc
                                       (fn-own-conns (fn-ocfg-owner oc))))
           (fn-ocl-conns-historyp
            (fn-ocl-complete oc)
            (fn-own-conns (fn-ocfg-owner (fn-ocl-complete oc)))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((fn-ocfg-staged (fn-ocl-complete oc)))
           :use (fn-ocl-success-appends-exact-config-history
                 fn-ocl-staged-complete-keeps-store-events
                 fn-ocl-staged-complete-keeps-connections
                 fn-ocl-staged-but-not-installed-is-unchanged
                 fn-ocl-complete-keeps-existing-pins
                 (:instance fn-ocl-conns-historyp-under-appended-configuration
                            (next (fn-ocl-complete oc))
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (record (fn-ocfg-staged oc))))
           :in-theory (disable fn-ocl-complete fn-cpo-configure-durable
                               fn-ocl-conns-historyp fn-ocl-conn-historyp))))

; The current owner view is the full configured history at its last refresh.
; During a pending Store transaction that view can be an earlier Store-event
; prefix; the configuration cannot overlap that transaction.
(defun fn-ocl-view-historyp (o)
  (declare (xargs :guard t))
  (let* ((st (fn-own-store o))
         (view (fn-own-view o))
         (events (fn-sf-records (fn-sn-files st)))
         (node (fn-cst-replay-node
                (fn-sn-config-history st)
                (fn-own-take (fn-own-view-version view) events)
                (fn-own-view-frontier view))))
    (and (fn-own-view-shapep view)
         (natp (fn-own-view-version view))
         (<= (fn-own-view-version view) (len events))
         (fn-node-statep node)
         (equal (fn-own-view-archive view) (fn-node-acceptance node)))))

(defun fn-ocl-config-historyp (oc)
  (declare (xargs :guard t))
  (let* ((st (fn-own-store (fn-ocfg-owner oc)))
         (replayed (fn-cpr-replay (fn-sn-config-history st)
                                  (fn-sf-records (fn-sn-files st)))))
    (and (equal (fn-replay-result-kind replayed) :ok)
         (equal (fn-ocfg-config oc)
                (fn-cnode-config (fn-replay-result-node replayed))))))

(defun fn-ocl-view-configp (oc)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (st (fn-own-store o))
         (view (fn-own-view o))
         (configs (fn-sn-config-history st))
         (events (fn-sf-records (fn-sn-files st))))
    (equal (fn-cnode-config
            (fn-replay-result-node
             (fn-cpr-replay configs
                            (fn-own-take (fn-own-view-version view)
                                         events))))
           (fn-ocfg-config oc))))

; The phase-aware replacement for fn-ocfg-statep on a physical-history
; owner. It is proof vocabulary, never an executable guard on a served path.
(defun fn-ocl-relation (oc)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (st (fn-own-store o))
         (conns (fn-own-conns o))
         (events (fn-sf-records (fn-sn-files st))))
    (and (fn-ocfg-shapep oc)
         (fn-own-shapep o)
         (fn-cst-relation st)
         (true-listp (fn-sn-config-history st))
         (fn-cfgp (fn-ocfg-config oc))
         (fn-ocl-config-historyp oc)
         (fn-ocl-view-configp oc)
         (equal (fn-cfg-generation (fn-ocfg-config oc))
                (len (fn-sn-config-history st)))
         (fn-ocl-view-historyp o)
         (fn-ocl-conns-historyp oc conns)
         (fn-ocfg-pins-okp (fn-ocfg-pins oc))
         (fn-ocfg-conns-pinnedp conns (fn-ocfg-pins oc))
         (fn-ocfg-pins-pin-conns-only (fn-ocfg-pins oc) conns)
         (natp (fn-own-max-conns o))
         (<= (len conns) (fn-own-max-conns o))
         (natp (fn-own-next-id o))
         (fn-own-ids-below-next-p conns (fn-own-next-id o))
         (fn-own-ledger-durablep (fn-own-ledger o) events)
         (or (null (fn-own-clock o))
             (fn-clock-observationp (fn-own-clock o)))
         (fn-own-facts-okp (fn-own-facts o))
         (or (null (fn-ocfg-staged oc))
             (and (fn-cfg-recordp (fn-ocfg-staged oc))
                  (equal (fn-cfg-record-generation (fn-ocfg-staged oc))
                         (+ 1 (nfix (fn-cfg-generation
                                     (fn-ocfg-config oc))))))))))

(defthm fn-ocl-view-historyp-of-ready-owner-with-store
  (implies (and (fn-cst-relation st)
                (equal (fn-sf-phase (fn-sn-files st)) :ready)
                (true-listp (fn-sf-records (fn-sn-files st))))
           (fn-ocl-view-historyp (fn-ocl-owner-with-store o st)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-take-of-len
                            (xs (fn-sf-records (fn-sn-files st)))))
           :in-theory (e/d (fn-ocl-view-historyp fn-ocl-owner-with-store
                            fn-own-refresh fn-own-store-idlep fn-cst-relation)
                           (fn-cst-replay-node fn-cpr-replay fn-own-take)))))

(defthm fn-ocl-complete-success-store-ready
  (implies (and (fn-ocfg-staged oc)
                (equal (fn-sf-phase
                        (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) :ready)
                (not (fn-ocfg-staged (fn-ocl-complete oc))))
           (equal (fn-sf-phase
                   (fn-sn-files
                    (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc)))))
                  :ready))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ocl-complete-success-install-exact-store
                 (:instance fn-ocl-durable-keeps-file-phase
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (record (fn-ocfg-staged oc))))
           :in-theory (disable fn-ocl-complete fn-cpo-configure-durable))))

(defthm fn-ocl-refresh-is-shaped
  (implies (fn-own-shapep o)
           (fn-own-shapep (fn-own-refresh o)))
  :hints (("Goal" :in-theory (enable fn-own-refresh))))

(defthm fn-ocl-cst-events-are-proper
  (implies (fn-cst-relation st)
           (true-listp (fn-sf-records (fn-sn-files st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cst-relation
                                    fn-sn-observed-historyp)
                                   (fn-sn-statep fn-sf-statep)))))

(defthm fn-ocl-store-config-is-typed
  (implies (fn-cpo-history-relation st)
           (fn-cfgp (fn-ocl-store-config st)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cpr-replay-ok-is-configured
                            (configs (fn-sn-config-history st))
                            (events (fn-sf-records (fn-sn-files st)))))
           :in-theory (e/d (fn-cpo-history-relation fn-cnode-statep
                            fn-ocl-store-config)
                           (fn-cpr-replay fn-cpr-replay-ok-is-configured)))))

(defthm fn-ocl-store-config-generation-counts-history
  (implies (fn-cpo-history-relation st)
           (equal (fn-cfg-generation (fn-ocl-store-config st))
                  (len (fn-sn-config-history st))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cpr-replay-success-counts-configurations
                            (configs (fn-sn-config-history st))
                            (events (fn-sf-records (fn-sn-files st)))))
           :in-theory (e/d (fn-cpo-history-relation fn-ocl-store-config)
                           (fn-cpr-replay
                            fn-cpr-replay-success-counts-configurations)))))

(defthm fn-ocl-config-historyp-of-history-related-store
  (implies (fn-cpo-history-relation st)
           (fn-ocl-config-historyp
            (fn-ocfg-make (fn-ocl-owner-with-store o st)
                          (fn-ocl-store-config st) pins nil)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-refresh-keeps-fields
                            (o (fn-own-make
                                st (fn-own-view o) (fn-own-conns o)
                                (fn-own-next-id o) (fn-own-max-conns o)
                                (fn-own-pending o) (fn-own-ledger o)
                                (fn-own-clock o) (fn-own-facts o)
                                (fn-own-config o) (fn-own-queue o)
                                (fn-own-inflight o) (fn-own-feeds o)))))
           :in-theory (e/d (fn-ocl-config-historyp fn-ocl-owner-with-store
                            fn-ocl-store-config fn-cpo-history-relation)
                           (fn-own-refresh fn-cpr-replay)))))

(defthm fn-ocl-view-configp-of-ready-owner-with-store
  (implies (and (fn-cpo-history-relation st)
                (equal (fn-sf-phase (fn-sn-files st)) :ready)
                (true-listp (fn-sf-records (fn-sn-files st))))
           (fn-ocl-view-configp
            (fn-ocfg-make (fn-ocl-owner-with-store o st)
                          (fn-ocl-store-config st) pins nil)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-take-of-len
                            (xs (fn-sf-records (fn-sn-files st)))))
           :in-theory (e/d (fn-ocl-view-configp fn-ocl-owner-with-store
                            fn-own-refresh fn-own-store-idlep
                            fn-ocl-store-config)
                           (fn-cpr-replay fn-own-take)))))

(defthm fn-ocl-complete-preserves-full-historical-relation
  (implies
   (and (fn-ocl-relation oc)
        (fn-cpo-history-relation (fn-own-store (fn-ocfg-owner oc)))
        (equal (fn-sf-phase
                (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) :ready)
        (fn-ocfg-staged oc)
        (not (fn-ocfg-staged (fn-ocl-complete oc))))
   (fn-ocl-relation (fn-ocl-complete oc)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ocl-complete-success-preserves-historical-store-relation
                 fn-ocl-complete-success-store-ready
                 fn-ocl-complete-success-install-exact-store
                 (:instance fn-own-refresh-keeps-fields
                            (o (fn-own-make
                                (fn-cpo-configure-durable
                                 (fn-own-store (fn-ocfg-owner oc))
                                 (fn-ocfg-staged oc))
                                (fn-own-view (fn-ocfg-owner oc))
                                (fn-own-conns (fn-ocfg-owner oc))
                                (fn-own-next-id (fn-ocfg-owner oc))
                                (fn-own-max-conns (fn-ocfg-owner oc))
                                (fn-own-pending (fn-ocfg-owner oc))
                                (fn-own-ledger (fn-ocfg-owner oc))
                                (fn-own-clock (fn-ocfg-owner oc))
                                (fn-own-facts (fn-ocfg-owner oc))
                                (fn-own-config (fn-ocfg-owner oc))
                                (fn-own-queue (fn-ocfg-owner oc))
                                (fn-own-inflight (fn-ocfg-owner oc))
                                (fn-own-feeds (fn-ocfg-owner oc)))))
                 (:instance fn-ocl-durable-keeps-history-proper
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-cpo-configure-durable-preserves-history-relation
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-cpo-configure-durable-keeps-observed-events
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-ocl-store-config-generation-counts-history
                            (st (fn-cpo-configure-durable
                                 (fn-own-store (fn-ocfg-owner oc))
                                 (fn-ocfg-staged oc))))
                 (:instance fn-ocl-store-config-is-typed
                            (st (fn-cpo-configure-durable
                                 (fn-own-store (fn-ocfg-owner oc))
                                 (fn-ocfg-staged oc))))
                 (:instance fn-ocl-config-historyp-of-history-related-store
                            (o (fn-ocfg-owner oc))
                            (st (fn-cpo-configure-durable
                                 (fn-own-store (fn-ocfg-owner oc))
                                 (fn-ocfg-staged oc)))
                            (pins (fn-ocfg-pins oc)))
                 (:instance fn-ocl-view-configp-of-ready-owner-with-store
                            (o (fn-ocfg-owner oc))
                            (st (fn-cpo-configure-durable
                                 (fn-own-store (fn-ocfg-owner oc))
                                 (fn-ocfg-staged oc)))
                            (pins (fn-ocfg-pins oc)))
                 fn-ocl-complete-preserves-pinned-connection-histories
                 fn-ocl-staged-complete-keeps-store-events
                 fn-ocl-staged-complete-keeps-connections
                 fn-ocl-complete-keeps-existing-pins
                 (:instance fn-ocl-cst-events-are-proper
                            (st (fn-own-store
                                 (fn-ocfg-owner (fn-ocl-complete oc)))))
                 (:instance fn-ocl-view-historyp-of-ready-owner-with-store
                            (o (fn-ocfg-owner oc))
                            (st (fn-cpo-configure-durable
                                 (fn-own-store (fn-ocfg-owner oc))
                                 (fn-ocfg-staged oc)))))
           :in-theory (e/d (fn-ocl-relation fn-ocl-complete
                            fn-ocl-owner-with-store fn-ocl-store-config)
                           (fn-own-refresh fn-ocl-view-historyp
                            fn-ocl-config-historyp fn-ocl-view-configp
                            fn-cpo-history-relation
                            fn-cpo-configure-durable fn-cst-relation
                            fn-cpr-replay fn-ocl-conns-historyp)))))

(defthm fn-ocl-reader-context-preserves-owner-shape
  (implies (fn-own-shapep o)
           (fn-own-shapep (fn-own-reader-context o id cfg)))
  :hints (("Goal" :in-theory (enable fn-own-reader-context
                                      fn-own-set-conns))))

(local
 (defthm fn-ocl-pin-is-open
   (implies (and (fn-ocfg-pins-pin-conns-only pins conns)
                 (fn-ocfg-pin-find id pins))
            (fn-own-find-conn id conns))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ocfg-pin-find id pins)
            :in-theory (enable fn-ocfg-pin-find
                               fn-ocfg-pins-pin-conns-only)))))

(defthm fn-ocl-open-pins-current-physical-configuration
  (implies (and (fn-ocl-relation oc)
                (fn-own-find-conn
                 (fn-own-next-id (fn-ocfg-owner oc))
                 (fn-own-conns (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))
           (equal (fn-ocfg-conn-config
                   (cdr (fn-ocfg-open oc acfg))
                   (fn-own-next-id (fn-ocfg-owner oc)))
                  (fn-ocfg-config oc)))
  :hints (("Goal"
           :use ((:instance fn-ocl-pin-is-open
                            (id (fn-own-next-id (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc))
                            (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-own-find-conn-id-below-next
                            (id (fn-own-next-id (fn-ocfg-owner oc)))
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-next-id (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocl-relation fn-ocfg-open
                            fn-ocfg-conn-config fn-ocfg-pin-add
                            fn-ocfg-pin-find)
                           (fn-cst-relation fn-ocl-conns-historyp
                            fn-ocl-view-historyp fn-ocl-config-historyp)))))

(defthm fn-ocl-replayed-view-has-successful-physical-prefix
  (implies (fn-node-statep (fn-cst-replay-node configs events frontier))
           (equal (fn-replay-result-kind (fn-cpr-replay configs events))
                  :ok))
  :hints (("Goal" :in-theory (e/d (fn-cst-replay-node)
                                      (fn-cpr-replay fn-node-statep)))))

(defthm fn-ocl-current-view-pins-a-historical-connection
  (implies
   (and (fn-ocl-relation oc)
        (fn-own-conn-shapep conn)
        (equal (fn-ocfg-conn-config oc (fn-own-conn-id conn))
               (fn-ocfg-config oc))
        (equal (fn-own-conn-version conn)
               (fn-own-view-version (fn-own-view (fn-ocfg-owner oc))))
        (equal (fn-own-conn-frontier conn)
               (fn-own-view-frontier (fn-own-view (fn-ocfg-owner oc))))
        (equal (fn-own-conn-archive conn)
               (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))
        (fn-own-conn-boundedp conn
                              (fn-cnode-domain-of (fn-ocfg-config oc))))
   (fn-ocl-conn-historyp oc conn))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-own-take-of-len
                            (xs (fn-sn-config-history
                                 (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-ocl-replayed-view-has-successful-physical-prefix
                            (configs (fn-sn-config-history
                                      (fn-own-store (fn-ocfg-owner oc))))
                            (events (fn-own-take
                                     (fn-own-conn-version conn)
                                     (fn-sf-records
                                      (fn-sn-files
                                       (fn-own-store (fn-ocfg-owner oc))))))
                            (frontier (fn-own-conn-frontier conn))))
           :in-theory (e/d (fn-ocl-relation fn-ocl-conn-historyp
                            fn-ocl-view-historyp fn-ocl-view-configp)
                           (fn-cst-replay-node fn-cpr-replay
                            fn-ocl-conns-historyp fn-own-take)))))

(deftheory fn-ocl-vocabulary
  '(fn-ocl-owner-with-store fn-ocl-store-config fn-ocl-complete fn-ocl-conn-historyp
    fn-ocl-conns-historyp fn-ocl-view-historyp fn-ocl-config-historyp
    fn-ocl-view-configp fn-ocl-relation))
(in-theory (disable fn-ocl-vocabulary))
