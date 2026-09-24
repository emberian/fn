; Atomic logical publication of a durable configuration into the served owner.
; The physical record has already passed the host's immutable publication
; barrier.  This function is administrative, never a per-command served path.
(in-package "ACL2")
(include-book "owner-config")
(include-book "config-store-traces")

; Keep the carried index constructors opaque while proving historical pins.
; Their selector theorems expose each field without expanding 11-field lists.
(in-theory (disable fn-own-conn-make-group-indexed
                    fn-own-view-make-group-indexed))

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

; Proof-only identity invariant.  The owner allocates fresh IDs, and a read,
; close or advance can only replace/remove an existing entry.  In particular,
; a single configuration pin must never describe two distinct open records.
(defun fn-ocl-unique-conn-idsp (conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (and (not (fn-own-find-conn (fn-own-conn-id (car conns))
                                  (cdr conns)))
           (fn-ocl-unique-conn-idsp (cdr conns)))
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
         (fn-ocl-unique-conn-idsp conns)
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
                           (fn-cst-replay-node fn-cpr-replay fn-own-take
                            fn-own-view-make-group-indexed)))))

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
                           (fn-cpr-replay fn-own-take
                            fn-own-view-make-group-indexed)))))

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

(defthm fn-ocl-unchanged-view-new-pin-is-historical
  (implies
   (and (fn-ocl-relation oc)
        (equal (fn-own-store (fn-ocfg-owner next))
               (fn-own-store (fn-ocfg-owner oc)))
        (equal (fn-own-view (fn-ocfg-owner next))
               (fn-own-view (fn-ocfg-owner oc)))
        (fn-own-conn-shapep conn)
        (equal (fn-ocfg-conn-config next (fn-own-conn-id conn))
               (fn-ocfg-config oc))
        (equal (fn-own-conn-version conn)
               (fn-own-view-version (fn-own-view (fn-ocfg-owner oc))))
        (equal (fn-own-conn-frontier conn)
               (fn-own-view-frontier (fn-own-view (fn-ocfg-owner oc))))
        (equal (fn-own-conn-archive conn)
               (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))
        (fn-own-conn-boundedp conn
                              (fn-cnode-domain-of (fn-ocfg-config oc))))
   (fn-ocl-conn-historyp next conn))
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

(defthm fn-ocl-reader-context-keeps-store-and-view
  (and (equal (fn-own-store (fn-own-reader-context o id cfg))
              (fn-own-store o))
       (equal (fn-own-view (fn-own-reader-context o id cfg))
              (fn-own-view o)))
  :hints (("Goal" :in-theory (enable fn-own-reader-context
                                      fn-own-set-conns))))

(defthm fn-ocl-reader-context-keeps-owner-control
  (and (equal (fn-own-max-conns (fn-own-reader-context o id cfg))
              (fn-own-max-conns o))
       (equal (fn-own-next-id (fn-own-reader-context o id cfg))
              (fn-own-next-id o))
       (equal (fn-own-pending (fn-own-reader-context o id cfg))
              (fn-own-pending o))
       (equal (fn-own-ledger (fn-own-reader-context o id cfg))
              (fn-own-ledger o))
       (equal (fn-own-clock (fn-own-reader-context o id cfg))
              (fn-own-clock o))
       (equal (fn-own-facts (fn-own-reader-context o id cfg))
              (fn-own-facts o))
       (equal (fn-own-config (fn-own-reader-context o id cfg))
              (fn-own-config o))
       (equal (fn-own-queue (fn-own-reader-context o id cfg))
              (fn-own-queue o))
       (equal (fn-own-inflight (fn-own-reader-context o id cfg))
              (fn-own-inflight o))
       (equal (fn-own-feeds (fn-own-reader-context o id cfg))
              (fn-own-feeds o)))
  :hints (("Goal" :in-theory (enable fn-own-reader-context
                                      fn-own-set-conns))))

(defthm fn-ocl-related-owner-has-open-bound
  (implies (fn-ocl-relation oc)
           (and (natp (fn-own-max-conns (fn-ocfg-owner oc)))
                (natp (fn-own-next-id (fn-ocfg-owner oc)))
                (fn-own-ids-below-next-p
                 (fn-own-conns (fn-ocfg-owner oc))
                 (fn-own-next-id (fn-ocfg-owner oc)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-ocl-relation))))

(defthm fn-ocl-related-configuration-is-valid
  (implies (fn-ocl-relation oc)
           (fn-cfgp (fn-ocfg-config oc)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-ocl-relation))))

(defthm fn-ocl-related-next-id-is-fresh
  (implies (fn-ocl-relation oc)
           (not (fn-own-find-conn
                 (fn-own-next-id (fn-ocfg-owner oc))
                 (fn-own-conns (fn-ocfg-owner oc)))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-id-below-next
                            (id (fn-own-next-id (fn-ocfg-owner oc)))
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-next-id (fn-ocfg-owner oc)))))
           :in-theory (enable fn-ocl-relation))))

(defthm fn-ocl-related-missing-connection-has-no-pin
  (implies (and (fn-ocl-relation oc)
                (not (fn-own-find-conn
                      id (fn-own-conns (fn-ocfg-owner oc)))))
           (not (fn-ocfg-pin-find id (fn-ocfg-pins oc))))
  :hints (("Goal"
           :use ((:instance fn-ocl-pin-is-open
                            (pins (fn-ocfg-pins oc))
                            (conns (fn-own-conns (fn-ocfg-owner oc)))))
           :in-theory (enable fn-ocl-relation))))

(defthm fn-ocl-pins-okp-implies-true-listp
  (implies (fn-ocfg-pins-okp pins)
           (true-listp pins))
  :hints (("Goal" :induct (fn-ocfg-pins-okp pins)
           :in-theory (enable fn-ocfg-pins-okp))))

(defthm fn-ocl-missing-connection-pin-remove-is-unchanged
  (implies (and (fn-ocl-relation oc)
                (not (fn-own-find-conn
                      id (fn-own-conns (fn-ocfg-owner oc)))))
           (equal (fn-ocfg-pin-remove id (fn-ocfg-pins oc))
                  (fn-ocfg-pins oc)))
  :hints (("Goal"
           :use ((:instance fn-ocl-related-missing-connection-has-no-pin)
                 (:instance fn-ocl-pins-okp-implies-true-listp
                            (pins (fn-ocfg-pins oc))))
           :in-theory (enable fn-ocl-relation))))

(defthm fn-ocl-find-after-remove-same
  (not (fn-own-find-conn id (fn-own-remove-conn id conns)))
  :hints (("Goal" :induct (fn-own-remove-conn id conns)
           :in-theory (enable fn-own-remove-conn fn-own-find-conn))))

(defthm fn-ocl-read-removal-uses-requested-id
  (implies (fn-own-find-conn id conns)
           (not (fn-own-find-conn
                 id (fn-own-remove-conn
                     (fn-own-conn-id (fn-own-find-conn id conns))
                     conns))))
  :hints (("Goal" :use ((:instance fn-own-find-conn-id)))))

(local
 (defthm fn-ocl-auth-with-new-reader-base-is-session
   (implies (fn-auth-sessionp as)
            (fn-auth-sessionp
             (fn-auth-with-base as
                                (fn-peer-open-session archive nil node cfg))))
   :hints (("Goal"
            :use ((:instance fn-peer-open-session-is-consistent
                             (peer nil)))
            :in-theory (e/d (fn-auth-sessionp fn-auth-with-base)
                            (fn-peer-open-session
                             fn-peer-open-session-is-consistent
                             fn-peer-sessionp fn-auth-configp))))))

(local
 (defthm fn-ocl-auth-base-of-with-base
   (equal (fn-auth-session-base (fn-auth-with-base as base)) base)
   :hints (("Goal" :in-theory (enable fn-auth-with-base)))))

(local
 (defthm fn-ocl-peer-open-reader-base
   (equal (fn-peer-session-base
           (fn-peer-open-session archive nil node cfg))
          (fn-post-open-session archive))
   :hints (("Goal" :in-theory (enable fn-peer-open-session)))))

(defthm fn-ocl-new-reader-context-session-is-bounded
  (implies (fn-auth-sessionp as)
           (fn-own-conn-boundedp
            (fn-own-conn-make
             id version frontier wire
             (fn-auth-with-base as
                                (fn-peer-open-session archive nil node cfg))
             archive config observation)
            groups))
  :hints (("Goal"
           :in-theory (e/d (fn-own-conn-boundedp
                            fn-post-open-session
                            fn-nntp-open-session fn-nntp-make-session
                            fn-nntp-session-group fn-nntp-session-current)
                           (fn-auth-sessionp fn-peer-sessionp
                            fn-post-sessionp fn-nntp-sessionp
                            fn-auth-with-base fn-peer-open-session)))))

(defthm fn-ocl-served-open-has-auth-session
  (fn-auth-sessionp
   (fn-served-conn-session
    (fn-served-result-conn
     (fn-served-open archive line-limit body-limit config
                     observation injection acfg))))
  :hints (("Goal"
           :use ((:instance fn-own-open-session-boundedp
                            (id nil) (version 0) (frontier 0) (wire nil)
                            (groups nil)))
           :in-theory (e/d (fn-own-conn-boundedp)
                           (fn-served-open fn-auth-sessionp
                            fn-own-open-session-boundedp)))))

(defthm fn-ocl-served-open-indexed-has-auth-session
  (fn-auth-sessionp
   (fn-served-conn-session
    (fn-served-result-conn
     (fn-served-open-indexed
      archive index verdicts line-limit body-limit config
      observation injection acfg))))
  :hints (("Goal"
           :use ((:instance fn-own-open-indexed-session-boundedp
                            (id nil) (version 0) (frontier 0)
                            (wire nil) (groups nil)))
           :in-theory (e/d (fn-own-conn-boundedp)
                           (fn-served-open-indexed fn-auth-sessionp
                            fn-own-open-indexed-session-boundedp)))))

(defthm fn-ocl-reader-context-new-connection
  (implies (and (fn-own-conn-shapep conn)
                (equal (fn-own-conn-id conn) id)
                (fn-cfgp cfg))
           (equal
            (fn-own-find-conn
             id
             (fn-own-conns
              (fn-own-reader-context
               (fn-own-set-conns o (cons conn (fn-own-conns o)))
               id cfg)))
            (fn-own-conn-make-group-indexed
             id (fn-own-conn-version conn)
             (fn-own-conn-frontier conn)
             (fn-own-conn-wire conn)
             (fn-auth-with-base
              (fn-own-conn-session conn)
              (fn-peer-open-session
               (fn-own-conn-archive conn) nil
               (fn-sn-node (fn-own-store o)) cfg))
             (fn-own-conn-archive conn)
             (fn-own-conn-config conn)
             (fn-own-conn-observation conn)
             (fn-own-conn-verdicts conn)
             (fn-own-conn-index conn)
             (fn-own-conn-group-index conn))))
  :hints (("Goal" :in-theory (e/d (fn-own-reader-context
                                    fn-own-set-conns fn-own-find-conn
                                    fn-own-replace-conn)
                                   (fn-own-conn-make-group-indexed)))))

(defthm fn-ocl-reader-context-new-connection-is-bounded
  (implies
   (and (fn-own-conn-shapep conn)
        (equal (fn-own-conn-id conn) id)
        (fn-cfgp cfg)
        (fn-auth-sessionp (fn-own-conn-session conn)))
   (fn-own-conn-boundedp
    (fn-own-find-conn
     id
     (fn-own-conns
      (fn-own-reader-context
       (fn-own-set-conns o (cons conn (fn-own-conns o)))
       id cfg)))
    groups))
  :hints (("Goal"
           :use ((:instance fn-ocl-new-reader-context-session-is-bounded
                            (as (fn-own-conn-session conn))
                            (archive (fn-own-conn-archive conn))
                            (node (fn-sn-node (fn-own-store o)))
                            (config (fn-own-conn-config conn))
                            (observation (fn-own-conn-observation conn))
                            (version (fn-own-conn-version conn))
                            (frontier (fn-own-conn-frontier conn))
                            (wire (fn-own-conn-wire conn))))
           :in-theory (disable fn-own-conn-boundedp
                               fn-peer-open-session fn-auth-with-base
                               fn-own-conn-make-group-indexed))))

(defthm fn-ocl-reader-context-first-connection
  (implies
   (and (fn-own-conn-shapep (car (fn-own-conns o)))
        (equal (fn-own-conn-id (car (fn-own-conns o))) id)
        (fn-cfgp cfg))
   (equal
    (fn-own-find-conn id
                      (fn-own-conns (fn-own-reader-context o id cfg)))
    (fn-own-conn-make-group-indexed
     id
     (fn-own-conn-version (car (fn-own-conns o)))
     (fn-own-conn-frontier (car (fn-own-conns o)))
     (fn-own-conn-wire (car (fn-own-conns o)))
     (fn-auth-with-base
      (fn-own-conn-session (car (fn-own-conns o)))
      (fn-peer-open-session
       (fn-own-conn-archive (car (fn-own-conns o))) nil
       (fn-sn-node (fn-own-store o)) cfg))
     (fn-own-conn-archive (car (fn-own-conns o)))
     (fn-own-conn-config (car (fn-own-conns o)))
     (fn-own-conn-observation (car (fn-own-conns o)))
     (fn-own-conn-verdicts (car (fn-own-conns o)))
     (fn-own-conn-index (car (fn-own-conns o)))
     (fn-own-conn-group-index (car (fn-own-conns o))))))
  :hints (("Goal" :in-theory (e/d (fn-own-reader-context
                                    fn-own-set-conns fn-own-find-conn
                                    fn-own-replace-conn)
                                   (fn-own-conn-make-group-indexed)))))

(defthm fn-ocl-reader-context-first-is-bounded
  (implies
   (and (fn-own-conn-shapep (car (fn-own-conns o)))
        (equal (fn-own-conn-id (car (fn-own-conns o))) id)
        (fn-cfgp cfg)
        (fn-auth-sessionp
         (fn-own-conn-session (car (fn-own-conns o)))))
   (fn-own-conn-boundedp
    (fn-own-find-conn id
                      (fn-own-conns (fn-own-reader-context o id cfg)))
    groups))
  :hints (("Goal"
           :use (fn-ocl-reader-context-first-connection
                 (:instance fn-ocl-new-reader-context-session-is-bounded
                            (as (fn-own-conn-session
                                 (car (fn-own-conns o))))
                            (archive (fn-own-conn-archive
                                      (car (fn-own-conns o))))
                            (node (fn-sn-node (fn-own-store o)))
                            (config (fn-own-conn-config
                                     (car (fn-own-conns o))))
                            (observation (fn-own-conn-observation
                                          (car (fn-own-conns o))))
                            (version (fn-own-conn-version
                                      (car (fn-own-conns o))))
                            (frontier (fn-own-conn-frontier
                                       (car (fn-own-conns o))))
                            (wire (fn-own-conn-wire
                                   (car (fn-own-conns o))))))
           :in-theory (e/d (fn-own-reader-context fn-own-set-conns
                            fn-own-find-conn fn-own-replace-conn)
                           (fn-own-conn-boundedp
                            fn-peer-open-session fn-auth-with-base
                            fn-own-conn-make-group-indexed)))))

(defthm fn-ocl-indexed-open-context-is-bounded
  (fn-own-conn-boundedp
   (fn-own-conn-make-indexed
    id version frontier wire
    (fn-auth-with-base
     (fn-auth-open-session archive nil nil nil acfg nil)
     (fn-peer-open-session archive nil node cfg))
    archive config observation verdicts index)
   groups)
  :hints (("Goal"
           :use ((:instance fn-ocl-new-reader-context-session-is-bounded
                            (as (fn-auth-open-session archive nil nil nil
                                                      acfg nil)))
                 (:instance fn-auth-open-session-is-consistent
                            (peer nil) (node nil) (cfg nil) (tlsp nil)))
           :in-theory (e/d (fn-own-conn-boundedp-of-make-indexed)
                           (fn-auth-open-session fn-auth-sessionp
                            fn-auth-open-session-is-consistent
                            fn-peer-open-session fn-auth-with-base
                            fn-ocl-new-reader-context-session-is-bounded)))))

(defthm fn-ocl-open-new-connection-has-historical-pin
  (implies
   (and (fn-ocl-relation oc)
        (fn-own-find-conn
         (fn-own-next-id (fn-ocfg-owner oc))
         (fn-own-conns (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))
   (fn-ocl-conn-historyp
    (cdr (fn-ocfg-open oc acfg))
    (fn-own-find-conn
     (fn-own-next-id (fn-ocfg-owner oc))
     (fn-own-conns (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg)))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ocl-open-pins-current-physical-configuration
                 (:instance fn-ocl-unchanged-view-new-pin-is-historical
                            (next (cdr (fn-ocfg-open oc acfg)))
                            (conn
                             (fn-own-find-conn
                              (fn-own-next-id (fn-ocfg-owner oc))
                              (fn-own-conns
                               (fn-ocfg-owner
                                (cdr (fn-ocfg-open oc acfg))))))))
           :in-theory (e/d (fn-ocfg-open fn-own-open)
                           (fn-ocl-relation fn-ocl-conn-historyp
                            fn-cpr-replay fn-cst-replay-node
                            fn-own-conn-make-group-indexed
                            fn-own-view-make-group-indexed)))))

(defthm fn-ocl-open-keeps-store-and-view
  (and (equal (fn-own-store
               (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-view
               (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))
              (fn-own-view (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-open fn-own-open))))

(defthm fn-ocl-conn-historyp-under-same-store-and-pin
  (implies
   (and (fn-ocl-conn-historyp oc conn)
        (equal (fn-own-store (fn-ocfg-owner next))
               (fn-own-store (fn-ocfg-owner oc)))
        (equal (fn-ocfg-conn-config next (fn-own-conn-id conn))
               (fn-ocfg-conn-config oc (fn-own-conn-id conn))))
   (fn-ocl-conn-historyp next conn))
  :hints (("Goal" :in-theory (e/d (fn-ocl-conn-historyp)
                                      (fn-cpr-replay fn-cst-replay-node)))))

(defthm fn-ocl-open-preserves-an-existing-connection-history
  (implies
   (and (fn-ocl-conn-historyp oc conn)
        (fn-ocfg-pin-find (fn-own-conn-id conn) (fn-ocfg-pins oc)))
   (fn-ocl-conn-historyp (cdr (fn-ocfg-open oc acfg)) conn))
  :hints (("Goal"
           :use ((:instance fn-ocl-conn-historyp-under-same-store-and-pin
                            (next (cdr (fn-ocfg-open oc acfg)))))
           :in-theory (enable fn-ocfg-conn-config))))

(defthm fn-ocl-open-preserves-existing-connection-histories
  (implies
   (and (fn-ocl-conns-historyp oc conns)
        (fn-ocfg-conns-pinnedp conns (fn-ocfg-pins oc)))
   (fn-ocl-conns-historyp (cdr (fn-ocfg-open oc acfg)) conns))
  :hints (("Goal" :induct (fn-ocl-conns-historyp oc conns)
           :in-theory (e/d (fn-ocfg-conns-pinnedp
                            fn-ocl-conns-historyp)
                           (fn-ocl-conn-historyp)))))

(defthm fn-ocl-reader-context-preserves-other-connections
  (implies (and (fn-own-conn-shapep (car (fn-own-conns o)))
                (equal (fn-own-conn-id (car (fn-own-conns o))) id)
                (fn-cfgp cfg))
           (equal (cdr (fn-own-conns (fn-own-reader-context o id cfg)))
                  (cdr (fn-own-conns o))))
  :hints (("Goal" :in-theory (e/d (fn-own-reader-context
                                    fn-own-set-conns fn-own-replace-conn
                                    fn-own-find-conn)
                                   (fn-own-conn-make-group-indexed)))))

(defthm fn-ocl-reader-context-replaces-first-connection
  (implies
   (and (fn-own-conn-shapep (car (fn-own-conns o)))
        (equal (fn-own-conn-id (car (fn-own-conns o))) id)
        (fn-cfgp cfg))
   (equal
    (fn-own-conns (fn-own-reader-context o id cfg))
    (cons
     (fn-own-conn-make-group-indexed
      id
      (fn-own-conn-version (car (fn-own-conns o)))
      (fn-own-conn-frontier (car (fn-own-conns o)))
      (fn-own-conn-wire (car (fn-own-conns o)))
      (fn-auth-with-base
       (fn-own-conn-session (car (fn-own-conns o)))
       (fn-peer-open-session
        (fn-own-conn-archive (car (fn-own-conns o))) nil
        (fn-sn-node (fn-own-store o)) cfg))
      (fn-own-conn-archive (car (fn-own-conns o)))
      (fn-own-conn-config (car (fn-own-conns o)))
      (fn-own-conn-observation (car (fn-own-conns o)))
      (fn-own-conn-verdicts (car (fn-own-conns o)))
      (fn-own-conn-index (car (fn-own-conns o)))
      (fn-own-conn-group-index (car (fn-own-conns o))))
     (cdr (fn-own-conns o)))))
  :hints (("Goal" :in-theory (e/d (fn-own-reader-context
                                    fn-own-set-conns fn-own-replace-conn
                                    fn-own-find-conn)
                                   (fn-own-conn-make-group-indexed)))))

(defthm fn-ocl-open-preserves-all-connection-histories
  (implies (fn-ocl-relation oc)
           (fn-ocl-conns-historyp
            (cdr (fn-ocfg-open oc acfg))
            (fn-own-conns
             (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ocl-open-new-connection-has-historical-pin
                 (:instance fn-ocl-open-preserves-existing-connection-histories
                            (conns (fn-own-conns (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocl-relation fn-ocfg-open fn-own-open
                            fn-ocl-conns-historyp)
                           (fn-cst-relation fn-ocl-conn-historyp
                            fn-ocl-view-historyp fn-ocl-config-historyp
                            fn-ocl-view-configp fn-cpr-replay
                            fn-cst-replay-node)))))

(defthm fn-ocl-pin-add-preserves-pins-okp
  (implies (and (fn-cfgp cfg)
                (fn-ocfg-pins-okp pins))
           (fn-ocfg-pins-okp (fn-ocfg-pin-add id cfg pins)))
  :hints (("Goal" :in-theory (enable fn-ocfg-pin-add
                                      fn-ocfg-pins-okp))))

(defthm fn-ocl-old-pins-point-into-extended-connections
  (implies (and (fn-own-conn-shapep conn)
                (fn-ocfg-pins-pin-conns-only pins conns))
           (fn-ocfg-pins-pin-conns-only pins (cons conn conns)))
  :hints (("Goal" :induct (fn-ocfg-pins-pin-conns-only pins conns)
           :in-theory (enable fn-ocfg-pins-pin-conns-only
                              fn-own-find-conn))))

(defthm fn-ocl-pin-add-points-into-extended-connections
  (implies (and (fn-own-conn-shapep conn)
                (fn-ocfg-pins-pin-conns-only pins conns)
                (not (fn-own-find-conn id conns))
                (equal (fn-own-conn-id conn) id))
           (fn-ocfg-pins-pin-conns-only
            (fn-ocfg-pin-add id cfg pins)
            (cons conn conns)))
  :hints (("Goal"
           :use ((:instance fn-ocl-pin-is-open
                            (id id) (pins pins) (conns conns)))
           :in-theory (enable fn-ocfg-pin-add
                              fn-ocfg-pins-pin-conns-only
                              fn-own-find-conn))))

(defthm fn-ocl-pin-add-covers-extended-connections
  (implies (and (fn-own-conn-shapep conn)
                (equal (fn-own-conn-id conn) id)
                (fn-ocfg-conns-pinnedp conns pins))
           (fn-ocfg-conns-pinnedp
            (cons conn conns)
            (fn-ocfg-pin-add id cfg pins)))
  :hints (("Goal" :induct (fn-ocfg-conns-pinnedp conns pins)
           :in-theory (enable fn-ocfg-conns-pinnedp
                              fn-ocfg-pin-add fn-ocfg-pin-find))))

(defthm fn-ocl-open-preserves-historical-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (cdr (fn-ocfg-open oc acfg))))
  :hints (("Goal"
           :use (fn-ocl-open-preserves-all-connection-histories
                 (:instance fn-own-ids-below-next-p-of-open
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-next-id (fn-ocfg-owner oc)))
                            (conn
                             (fn-own-find-conn
                              (fn-own-next-id (fn-ocfg-owner oc))
                              (fn-own-conns
                               (fn-ocfg-owner
                                (cdr (fn-ocfg-open oc acfg))))))))
           :in-theory (e/d (fn-ocl-relation fn-ocfg-open fn-own-open
                            fn-ocl-config-historyp
                            fn-ocl-view-historyp fn-ocl-view-configp)
                           (fn-cst-relation fn-cpr-replay
                            fn-cst-replay-node fn-ocl-conns-historyp
                            fn-ocl-conn-historyp)))))

(defthm fn-ocl-close-preserves-surviving-connection-history
  (implies (and (fn-ocl-conn-historyp oc conn)
                (not (equal (fn-own-conn-id conn) id)))
           (fn-ocl-conn-historyp (fn-ocfg-close oc id) conn))
  :hints (("Goal"
           :use ((:instance fn-ocl-conn-historyp-under-same-store-and-pin
                            (next (fn-ocfg-close oc id))))
           :in-theory (enable fn-ocfg-close fn-own-close
                              fn-ocfg-conn-config))))

(defthm fn-ocl-close-preserves-surviving-connection-histories
  (implies (fn-ocl-conns-historyp oc conns)
           (fn-ocl-conns-historyp
            (fn-ocfg-close oc id)
            (fn-own-remove-conn id conns)))
  :hints (("Goal" :induct (fn-own-remove-conn id conns)
           :in-theory (e/d (fn-own-remove-conn
                            fn-ocl-conns-historyp)
                           (fn-ocl-conn-historyp)))))

(defthm fn-ocl-pin-remove-covers-surviving-connections
  (implies (fn-ocfg-conns-pinnedp conns pins)
           (fn-ocfg-conns-pinnedp
            (fn-own-remove-conn id conns)
            (fn-ocfg-pin-remove id pins)))
  :hints (("Goal" :induct (fn-own-remove-conn id conns)
           :in-theory (enable fn-own-remove-conn
                              fn-ocfg-conns-pinnedp))))

(defthm fn-ocl-pin-remove-preserves-pins-okp
  (implies (fn-ocfg-pins-okp pins)
           (fn-ocfg-pins-okp (fn-ocfg-pin-remove id pins)))
  :hints (("Goal" :induct (fn-ocfg-pin-remove id pins)
           :in-theory (enable fn-ocfg-pin-remove
                              fn-ocfg-pins-okp))))

(defthm fn-ocl-pin-remove-points-into-surviving-connections
  (implies (fn-ocfg-pins-pin-conns-only pins conns)
           (fn-ocfg-pins-pin-conns-only
            (fn-ocfg-pin-remove id pins)
            (fn-own-remove-conn id conns)))
  :hints (("Goal" :induct (fn-ocfg-pin-remove id pins)
           :in-theory (enable fn-ocfg-pin-remove
                              fn-ocfg-pins-pin-conns-only
                              fn-own-find-conn-of-remove-conn-other))))

(defthm fn-ocl-remove-cannot-create-found-id
  (implies (not (fn-own-find-conn selected conns))
           (not (fn-own-find-conn selected
                                  (fn-own-remove-conn id conns))))
  :hints (("Goal" :induct (fn-own-remove-conn id conns)
           :in-theory (enable fn-own-remove-conn fn-own-find-conn))))

(defthm fn-ocl-unique-ids-of-remove
  (implies (fn-ocl-unique-conn-idsp conns)
           (fn-ocl-unique-conn-idsp
            (fn-own-remove-conn id conns)))
  :hints (("Goal" :induct (fn-own-remove-conn id conns)
           :in-theory (enable fn-own-remove-conn
                              fn-ocl-unique-conn-idsp))))

(defthm fn-ocl-close-preserves-historical-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-close oc id)))
  :hints (("Goal"
           :use ((:instance
                  fn-ocl-close-preserves-surviving-connection-histories
                  (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-own-remove-conn-len
                            (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-own-remove-conn-ids-below-next
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-next-id (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocl-relation fn-ocfg-close fn-own-close
                            fn-ocl-config-historyp fn-ocl-view-historyp
                            fn-ocl-view-configp
                            fn-own-remove-conn-ids-below-next)
                           (fn-cst-relation fn-cpr-replay fn-cst-replay-node
                            fn-ocl-conns-historyp fn-ocl-conn-historyp)))))

(defthm fn-ocl-conns-historyp-under-same-store-and-pins
  (implies
   (and (fn-ocl-conns-historyp oc conns)
        (equal (fn-own-store (fn-ocfg-owner next))
               (fn-own-store (fn-ocfg-owner oc)))
        (equal (fn-ocfg-pins next) (fn-ocfg-pins oc)))
   (fn-ocl-conns-historyp next conns))
  :hints (("Goal" :induct (fn-ocl-conns-historyp oc conns)
           :in-theory (e/d (fn-ocl-conns-historyp
                            fn-ocfg-conn-config)
                           (fn-ocl-conn-historyp)))))

(defthm fn-ocl-owner-shape-of-set-conns
  (fn-own-shapep (fn-own-set-conns o conns))
  :hints (("Goal" :in-theory (enable fn-own-set-conns))))

(defthm fn-ocl-set-conns-keeps-owner-control
  (and (equal (fn-own-store (fn-own-set-conns o conns))
              (fn-own-store o))
       (equal (fn-own-view (fn-own-set-conns o conns))
              (fn-own-view o))
       (equal (fn-own-next-id (fn-own-set-conns o conns))
              (fn-own-next-id o))
       (equal (fn-own-max-conns (fn-own-set-conns o conns))
              (fn-own-max-conns o))
       (equal (fn-own-pending (fn-own-set-conns o conns))
              (fn-own-pending o))
       (equal (fn-own-ledger (fn-own-set-conns o conns))
              (fn-own-ledger o))
       (equal (fn-own-clock (fn-own-set-conns o conns))
              (fn-own-clock o))
       (equal (fn-own-facts (fn-own-set-conns o conns))
              (fn-own-facts o))
       (equal (fn-own-config (fn-own-set-conns o conns))
              (fn-own-config o)))
  :hints (("Goal" :in-theory (enable fn-own-set-conns))))

(defthm fn-ocl-read-removal-preserves-surviving-histories
  (implies (fn-ocl-conns-historyp oc conns)
           (fn-ocl-conns-historyp
            (fn-ocfg-make
             (fn-own-set-conns (fn-ocfg-owner oc)
                               (fn-own-remove-conn id conns))
             (fn-ocfg-config oc)
             (fn-ocfg-pin-remove id (fn-ocfg-pins oc))
             (fn-ocfg-staged oc))
            (fn-own-remove-conn id conns)))
  :hints (("Goal"
           :use ((:instance
                  fn-ocl-close-preserves-surviving-connection-histories)
                 (:instance fn-ocl-conns-historyp-under-same-store-and-pins
                            (next
                             (fn-ocfg-make
                              (fn-own-set-conns (fn-ocfg-owner oc)
                                                (fn-own-remove-conn id conns))
                              (fn-ocfg-config oc)
                              (fn-ocfg-pin-remove id (fn-ocfg-pins oc))
                              (fn-ocfg-staged oc)))
                            (oc (fn-ocfg-close oc id))
                            (conns (fn-own-remove-conn id conns))))
           :in-theory (e/d (fn-ocfg-close fn-own-close
                            fn-own-set-conns)
                           (fn-ocl-conns-historyp)))))

(defthm fn-ocl-read-removal-preserves-historical-connections
  (implies
   (fn-ocl-relation oc)
   (let* ((o (fn-ocfg-owner oc))
          (conns (fn-own-conns o))
          (owner (fn-own-set-conns o (fn-own-remove-conn id conns)))
          (next (fn-ocfg-with-read-owner oc id owner)))
     (fn-ocl-conns-historyp next (fn-own-conns (fn-ocfg-owner next)))))
  :hints (("Goal"
           :use ((:instance fn-ocl-read-removal-preserves-surviving-histories
                            (conns (fn-own-conns (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocl-relation fn-ocfg-with-read-owner
                            fn-own-set-conns)
                           (fn-ocl-conns-historyp)))))

(defthm fn-ocl-replay-advance-keeps-groups
  (equal (fn-state-groups
          (fn-node-acceptance (fn-replay-advance-txid node frontier)))
         (fn-state-groups (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-ocl-connection-archive-has-pinned-domain
  (implies (fn-ocl-conn-historyp oc conn)
           (equal (fn-state-groups (fn-own-conn-archive conn))
                  (fn-cnode-domain-of
                   (fn-ocfg-conn-config oc (fn-own-conn-id conn)))))
  :hints (("Goal"
           :use ((:instance fn-cpr-replay-ok-is-configured
                            (configs (fn-own-take
                                      (fn-cfg-generation
                                       (fn-ocfg-conn-config
                                        oc (fn-own-conn-id conn)))
                                      (fn-sn-config-history
                                       (fn-own-store (fn-ocfg-owner oc)))))
                            (events (fn-own-take
                                     (fn-own-conn-version conn)
                                     (fn-sf-records
                                      (fn-sn-files
                                       (fn-own-store (fn-ocfg-owner oc))))))))
           :in-theory (e/d (fn-ocl-conn-historyp fn-cst-replay-node
                            fn-cnode-statep fn-cnode-domain
                            fn-ocfg-conn-config)
                           (fn-cpr-replay fn-own-take)))))

(defthm fn-ocl-connection-history-keeps-replaced-session
  (implies
   (and (fn-ocl-conn-historyp oc old)
        (equal (fn-own-conn-id next) (fn-own-conn-id old))
        (equal (fn-own-conn-version next) (fn-own-conn-version old))
        (equal (fn-own-conn-frontier next) (fn-own-conn-frontier old))
        (equal (fn-own-conn-archive next) (fn-own-conn-archive old))
        (fn-own-conn-shapep next)
        (fn-own-conn-boundedp
         next (fn-state-groups (fn-own-conn-archive old))))
   (fn-ocl-conn-historyp oc next))
  :hints (("Goal"
           :use ((:instance fn-ocl-connection-archive-has-pinned-domain
                            (conn old)))
           :in-theory (e/d (fn-ocl-conn-historyp)
                           (fn-cpr-replay fn-cst-replay-node)))))

(defthm fn-ocl-replace-connection-preserves-histories
  (implies (and (fn-ocl-conns-historyp oc conns)
                (fn-ocl-conn-historyp oc next))
           (fn-ocl-conns-historyp
            oc (fn-own-replace-conn next conns)))
  :hints (("Goal" :induct (fn-own-replace-conn next conns)
           :in-theory (e/d (fn-own-replace-conn
                            fn-ocl-conns-historyp)
                           (fn-ocl-conn-historyp)))))

(defthm fn-ocl-replace-preserves-conns-pinned
  (implies (fn-ocfg-conns-pinnedp conns pins)
           (fn-ocfg-conns-pinnedp
            (fn-own-replace-conn next conns) pins))
  :hints (("Goal" :induct (fn-own-replace-conn next conns)
           :in-theory (enable fn-own-replace-conn
                              fn-ocfg-conns-pinnedp))))

(defthm fn-ocl-find-survives-connection-replacement
  (implies (and (fn-own-conn-shapep next)
                (fn-own-find-conn id conns))
           (fn-own-find-conn id (fn-own-replace-conn next conns)))
  :hints (("Goal" :induct (fn-own-replace-conn next conns)
           :in-theory (enable fn-own-replace-conn fn-own-find-conn))))

(defthm fn-ocl-replace-preserves-pins-point-to-conns
  (implies (and (fn-own-conn-shapep next)
                (fn-ocfg-pins-pin-conns-only pins conns))
           (fn-ocfg-pins-pin-conns-only
            pins (fn-own-replace-conn next conns)))
  :hints (("Goal" :induct (fn-ocfg-pins-pin-conns-only pins conns)
           :in-theory (e/d (fn-ocfg-pins-pin-conns-only)
                           (fn-own-replace-conn fn-own-find-conn)))))

(defthm fn-ocl-found-connection-has-history
  (implies (and (fn-ocl-conns-historyp oc conns)
                (fn-own-find-conn id conns))
           (fn-ocl-conn-historyp oc (fn-own-find-conn id conns)))
  :hints (("Goal" :induct (fn-own-find-conn id conns)
           :in-theory (e/d (fn-own-find-conn fn-ocl-conns-historyp)
                           (fn-ocl-conn-historyp)))))

(defthm fn-ocl-replacing-found-connection-is-idempotent
  (implies
   (fn-own-find-conn (fn-own-conn-id conn) conns)
   (equal
    (fn-own-replace-conn
     (fn-own-find-conn
      (fn-own-conn-id conn) (fn-own-replace-conn conn conns))
     conns)
    (fn-own-replace-conn conn conns)))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-of-replace-conn-same)))))

(defthm fn-ocl-replacing-found-id-is-idempotent
  (implies (and (fn-own-find-conn id conns)
                (equal (fn-own-conn-id conn) id))
           (equal
            (fn-own-replace-conn
             (fn-own-find-conn id (fn-own-replace-conn conn conns))
             conns)
            (fn-own-replace-conn conn conns)))
  :hints (("Goal" :use ((:instance
                           fn-ocl-replacing-found-connection-is-idempotent)))))

(defthm fn-ocl-own-read-survivor-is-replacement
  (implies
   (and (fn-own-find-conn id (fn-own-conns o))
        (fn-own-find-conn
         id (fn-own-conns (cdr (fn-own-read o id octets)))))
   (equal
    (fn-own-conns (cdr (fn-own-read o id octets)))
    (fn-own-replace-conn
     (fn-own-find-conn
      id (fn-own-conns (cdr (fn-own-read o id octets))))
     (fn-own-conns o))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-id
                            (conns (fn-own-conns o))))
           :in-theory (e/d (fn-own-read fn-own-finish-read
                            fn-own-set-conns fn-own-enqueue)
                           (fn-served-step fn-own-conn-boundedp)))))

(defthm fn-ocl-own-read-nonsurvivor-is-removal
  (implies
   (and (fn-own-find-conn id (fn-own-conns o))
        (not (fn-own-find-conn
              id (fn-own-conns (cdr (fn-own-read o id octets))))))
   (equal (fn-own-conns (cdr (fn-own-read o id octets)))
          (fn-own-remove-conn id (fn-own-conns o))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-id
                            (conns (fn-own-conns o)))
                 (:instance fn-own-read-remove-leaves-no-selected-id
                            (conns (fn-own-conns o))))
           :in-theory (e/d (fn-own-read fn-own-finish-read
                            fn-own-set-conns fn-own-enqueue)
                           (fn-served-step fn-own-conn-boundedp)))))

(defthm fn-ocl-own-read-keeps-store
  (equal (fn-own-store (cdr (fn-own-read o id octets)))
         (fn-own-store o))
  :hints (("Goal" :in-theory (e/d (fn-own-read fn-own-finish-read
                                    fn-own-set-conns fn-own-enqueue)
                                   (fn-served-step fn-own-conn-boundedp)))))

(defthm fn-ocl-own-read-preserves-owner-shape
  (implies (fn-own-shapep o)
           (fn-own-shapep (cdr (fn-own-read o id octets))))
  :hints (("Goal" :in-theory (e/d (fn-own-read fn-own-finish-read
                                    fn-own-set-conns fn-own-enqueue
                                    fn-own-shapep fn-own-make)
                                   (fn-served-step fn-own-conn-boundedp)))))

(defthm fn-ocl-own-read-keeps-owner-control
  (let ((next (cdr (fn-own-read o id octets))))
    (and (equal (fn-own-view next) (fn-own-view o))
         (equal (fn-own-next-id next) (fn-own-next-id o))
         (equal (fn-own-max-conns next) (fn-own-max-conns o))
         (equal (fn-own-pending next) (fn-own-pending o))
         (equal (fn-own-ledger next) (fn-own-ledger o))
         (equal (fn-own-clock next) (fn-own-clock o))
         (equal (fn-own-facts next) (fn-own-facts o))
         (equal (fn-own-config next) (fn-own-config o))))
  :hints (("Goal" :in-theory (e/d (fn-own-read fn-own-finish-read
                                    fn-own-set-conns fn-own-enqueue)
                                   (fn-served-step fn-own-conn-boundedp)))))

(defthm fn-ocl-own-read-does-not-increase-connections
  (<= (len (fn-own-conns (cdr (fn-own-read o id octets))))
      (len (fn-own-conns o)))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-id
                            (conns (fn-own-conns o)))
                 (:instance fn-own-remove-conn-len
                            (conns (fn-own-conns o))))
           :in-theory (e/d (fn-own-read fn-own-finish-read
                            fn-own-set-conns fn-own-enqueue
                            fn-own-replace-conn-len fn-own-remove-conn-len)
                           (fn-own-replace-conn fn-own-remove-conn
                            fn-served-step fn-own-conn-boundedp)))))

(defthm fn-ocl-related-found-connection-has-history
  (implies (and (fn-ocl-relation oc)
                (fn-own-find-conn
                 id (fn-own-conns (fn-ocfg-owner oc))))
           (fn-ocl-conn-historyp
            oc (fn-own-find-conn
                id (fn-own-conns (fn-ocfg-owner oc)))))
  :hints (("Goal"
           :use ((:instance fn-ocl-found-connection-has-history
                            (conns (fn-own-conns (fn-ocfg-owner oc)))))
           :in-theory (enable fn-ocl-relation))))

(defthm fn-ocl-observe-preserves-historical-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation
            (fn-ocfg-pass oc (list :observe observation))))
  :hints (("Goal"
           :use ((:instance fn-ocl-conns-historyp-under-same-store-and-pins
                            (next (fn-ocfg-pass oc
                                                (list :observe observation)))
                            (conns (fn-own-conns (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocl-relation fn-ocfg-pass
                            fn-ocfg-with-owner fn-own-step
                            fn-own-observe fn-own-observe-outcome
                            fn-ocl-view-historyp fn-ocl-config-historyp
                           fn-ocl-view-configp)
                           (fn-cst-relation fn-cpr-replay fn-cst-replay-node
                            fn-ocl-conns-historyp fn-ocl-conn-historyp)))))

(defthm fn-ocl-own-read-survivor-had-original
  (implies
   (fn-own-find-conn id
                     (fn-own-conns (cdr (fn-own-read o id octets))))
   (fn-own-find-conn id (fn-own-conns o)))
  :hints (("Goal" :in-theory (enable fn-own-read))))

(defthm fn-ocl-config-shape-reconstructs
  (implies (fn-ocfg-shapep oc)
           (equal (fn-ocfg-make (fn-ocfg-owner oc)
                                (fn-ocfg-config oc)
                                (fn-ocfg-pins oc)
                                (fn-ocfg-staged oc))
                  oc))
  :hints (("Goal" :induct (len oc)
           :in-theory (enable fn-ocfg-shapep fn-ocfg-make
                                      fn-ocfg-owner fn-ocfg-config
                                      fn-ocfg-pins fn-ocfg-staged))))

(defthm fn-ocl-related-config-shaped
  (implies (fn-ocl-relation oc) (fn-ocfg-shapep oc))
  :hints (("Goal" :in-theory (enable fn-ocl-relation))))

(defthm fn-ocl-missing-read-keeps-configured-owner
  (implies
   (and (fn-ocl-relation oc)
        (not (fn-own-find-conn
              id (fn-own-conns (fn-ocfg-owner oc)))))
   (equal (cdr (fn-ocfg-read oc id octets)) oc))
  :hints (("Goal"
           :use (fn-ocl-missing-connection-pin-remove-is-unchanged
                 fn-ocl-config-shape-reconstructs
                 fn-ocl-related-config-shaped)
           :in-theory (e/d (fn-ocfg-read fn-ocfg-with-read-owner
                            fn-own-read)
                           (fn-ocl-relation fn-cst-relation fn-cpr-replay
                            fn-cst-replay-node)))))

(defthm fn-ocl-own-read-survivor-has-old-history
  (implies
   (and (fn-ocl-relation oc)
        (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))
        (fn-own-find-conn
         id (fn-own-conns
             (cdr (fn-own-read (fn-ocfg-owner oc) id octets)))))
   (fn-ocl-conn-historyp
    oc
    (fn-own-find-conn
     id (fn-own-conns
         (cdr (fn-own-read (fn-ocfg-owner oc) id octets))))))
  :hints (("Goal"
           :use ((:instance fn-ocl-related-found-connection-has-history)
                 (:instance fn-own-read-survivor-is-archive-bounded
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-own-read-survivor-keeps-historical-fields
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-connection-history-keeps-replaced-session
                            (old (fn-own-find-conn
                                  id (fn-own-conns (fn-ocfg-owner oc))))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets)))))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-ocl-replace-cannot-create-other-found-id
  (implies (and (not (equal selected (fn-own-conn-id next)))
                (not (fn-own-find-conn selected conns)))
           (not (fn-own-find-conn selected
                                  (fn-own-replace-conn next conns))))
  :hints (("Goal" :induct (fn-own-replace-conn next conns)
           :in-theory (enable fn-own-replace-conn fn-own-find-conn))))

(defthm fn-ocl-unique-ids-of-replace
  (implies (fn-ocl-unique-conn-idsp conns)
           (fn-ocl-unique-conn-idsp
            (fn-own-replace-conn next conns)))
  :hints (("Goal" :induct (fn-own-replace-conn next conns)
           :in-theory (enable fn-own-replace-conn
                              fn-ocl-unique-conn-idsp))))

; Reassemble the historical relation from its changed connection and pin
; clauses.  The Store, refreshed view, configuration and owner control fields
; are unchanged by a reader command, so no physical replay is redone here.
(defthm fn-ocl-relation-under-same-control-and-valid-connections
  (implies
   (and (fn-ocl-relation oc)
        (fn-ocfg-shapep next)
        (fn-own-shapep (fn-ocfg-owner next))
        (equal (fn-own-store (fn-ocfg-owner next))
               (fn-own-store (fn-ocfg-owner oc)))
        (equal (fn-own-view (fn-ocfg-owner next))
               (fn-own-view (fn-ocfg-owner oc)))
        (equal (fn-ocfg-config next) (fn-ocfg-config oc))
        (equal (fn-ocfg-staged next) (fn-ocfg-staged oc))
        (equal (fn-own-next-id (fn-ocfg-owner next))
               (fn-own-next-id (fn-ocfg-owner oc)))
        (equal (fn-own-max-conns (fn-ocfg-owner next))
               (fn-own-max-conns (fn-ocfg-owner oc)))
        (equal (fn-own-ledger (fn-ocfg-owner next))
               (fn-own-ledger (fn-ocfg-owner oc)))
        (equal (fn-own-clock (fn-ocfg-owner next))
               (fn-own-clock (fn-ocfg-owner oc)))
        (equal (fn-own-facts (fn-ocfg-owner next))
               (fn-own-facts (fn-ocfg-owner oc)))
        (fn-ocl-conns-historyp next
                               (fn-own-conns (fn-ocfg-owner next)))
        (fn-ocl-unique-conn-idsp (fn-own-conns (fn-ocfg-owner next)))
        (fn-ocfg-pins-okp (fn-ocfg-pins next))
        (fn-ocfg-conns-pinnedp (fn-own-conns (fn-ocfg-owner next))
                               (fn-ocfg-pins next))
        (fn-ocfg-pins-pin-conns-only (fn-ocfg-pins next)
                                      (fn-own-conns (fn-ocfg-owner next)))
        (<= (len (fn-own-conns (fn-ocfg-owner next)))
            (fn-own-max-conns (fn-ocfg-owner next)))
        (fn-own-ids-below-next-p (fn-own-conns (fn-ocfg-owner next))
                                  (fn-own-next-id (fn-ocfg-owner next))))
   (fn-ocl-relation next))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation)
                                   (fn-cst-relation fn-cpr-replay
                                    fn-cst-replay-node fn-ocl-conns-historyp
                                    fn-ocl-conn-historyp)))))

(defthm fn-ocl-relation-read-input-facts
  (implies
   (fn-ocl-relation oc)
   (let* ((o (fn-ocfg-owner oc))
          (conns (fn-own-conns o))
          (pins (fn-ocfg-pins oc)))
     (and (fn-ocfg-shapep oc)
          (fn-own-shapep o)
          (fn-ocl-conns-historyp oc conns)
          (fn-ocl-unique-conn-idsp conns)
          (fn-ocfg-pins-okp pins)
          (fn-ocfg-conns-pinnedp conns pins)
          (fn-ocfg-pins-pin-conns-only pins conns)
          (<= (len conns) (fn-own-max-conns o))
          (fn-own-ids-below-next-p conns (fn-own-next-id o)))))
  :hints (("Goal" :in-theory (enable fn-ocl-relation))))

(defthm fn-ocl-read-preserves-capacity-bound
  (implies
   (fn-ocl-relation oc)
   (<= (len (fn-own-conns
             (cdr (fn-own-read (fn-ocfg-owner oc) id octets))))
       (fn-own-max-conns (fn-ocfg-owner oc))))
  :hints (("Goal"
           :use (fn-ocl-relation-read-input-facts
                 (:instance fn-ocl-own-read-does-not-increase-connections
                            (o (fn-ocfg-owner oc))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-ocl-read-preserves-historical-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (cdr (fn-ocfg-read oc id octets))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((fn-own-find-conn
                    id (fn-own-conns (fn-ocfg-owner oc)))
                   (fn-own-find-conn
                    id (fn-own-conns
                        (cdr (fn-own-read (fn-ocfg-owner oc) id octets)))))
           :use ((:instance fn-ocl-relation-under-same-control-and-valid-connections
                            (next (cdr (fn-ocfg-read oc id octets))))
                 fn-ocl-relation-read-input-facts
                 fn-ocl-read-preserves-capacity-bound
                 fn-ocl-missing-read-keeps-configured-owner
                 fn-ocl-read-removal-preserves-historical-connections
                 (:instance fn-ocl-own-read-keeps-store
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-preserves-owner-shape
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-keeps-owner-control
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-does-not-increase-connections
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-survivor-is-replacement
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-nonsurvivor-is-removal
                            (o (fn-ocfg-owner oc)))
                 fn-ocl-own-read-survivor-has-old-history
                 (:instance fn-ocl-own-read-survivor-had-original
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-replace-connection-preserves-histories
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets))))))
                 (:instance fn-ocl-replace-preserves-conns-pinned
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets))))))
                 (:instance fn-ocl-replace-preserves-pins-point-to-conns
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets))))))
                 (:instance fn-own-find-conn-id
                            (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-own-read-survivor-keeps-historical-fields
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-own-find-conn-id-below-next
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-next-id (fn-ocfg-owner oc))))
                 (:instance fn-own-replace-conn-ids-below-next
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets)))))
                            (n (fn-own-next-id (fn-ocfg-owner oc))))
                 (:instance fn-own-replace-conn-len
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets))))))
                 (:instance fn-ocl-pin-remove-covers-surviving-connections
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc)))
                 (:instance fn-ocl-pin-remove-points-into-surviving-connections
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc)))
                 (:instance fn-own-remove-conn-len
                            (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-own-remove-conn-ids-below-next
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-next-id (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocfg-read
                            fn-ocfg-with-read-owner
                            fn-own-set-conns fn-own-enqueue)
                           (fn-ocl-relation fn-ocl-view-historyp
                            fn-ocl-config-historyp fn-ocl-view-configp
                            fn-own-read fn-own-finish-read
                            fn-cst-relation fn-cpr-replay fn-cst-replay-node
                            fn-served-step fn-ocl-conns-historyp
                            fn-ocl-conn-historyp
                            fn-ocl-relation-under-same-control-and-valid-connections
                            fn-ocl-read-preserves-capacity-bound
                            fn-ocl-read-removal-preserves-historical-connections
                            fn-ocl-missing-read-keeps-configured-owner
                            fn-ocl-own-read-keeps-store
                            fn-ocl-own-read-preserves-owner-shape
                            fn-ocl-own-read-keeps-owner-control
                            fn-ocl-own-read-does-not-increase-connections
                            fn-ocl-own-read-survivor-is-replacement
                            fn-ocl-own-read-nonsurvivor-is-removal
                            fn-ocl-own-read-survivor-has-old-history
                            fn-ocl-own-read-survivor-had-original
                            fn-ocl-replace-connection-preserves-histories
                            fn-ocl-replace-preserves-conns-pinned
                            fn-ocl-replace-preserves-pins-point-to-conns
                            fn-own-find-conn-id
                            fn-own-read-survivor-keeps-historical-fields
                            fn-own-replace-conn-ids-below-next
                            fn-own-replace-conn-len
                            fn-ocl-pin-remove-covers-surviving-connections
                            fn-ocl-pin-remove-points-into-surviving-connections
                            fn-own-remove-conn-len
                            fn-own-remove-conn-ids-below-next)))))

(deftheory fn-ocl-vocabulary
  '(fn-ocl-owner-with-store fn-ocl-store-config fn-ocl-complete fn-ocl-conn-historyp
    fn-ocl-conns-historyp fn-ocl-view-historyp fn-ocl-config-historyp
    fn-ocl-view-configp fn-ocl-relation))
(in-theory (disable fn-ocl-vocabulary))

; These large read-composition facts are applied explicitly by the historical
; reader proof.  Leaving them as global rewrite rules makes unrelated TLS and
; pin proofs expand a second read path while simplifying their own one.
(deftheory fn-ocl-read-proof-lemmas
  '(fn-ocl-replace-preserves-conns-pinned
    fn-ocl-find-survives-connection-replacement
    fn-ocl-replace-preserves-pins-point-to-conns
    fn-ocl-own-read-survivor-is-replacement
    fn-ocl-own-read-nonsurvivor-is-removal
    fn-ocl-own-read-keeps-store
    fn-ocl-own-read-preserves-owner-shape
    fn-ocl-own-read-keeps-owner-control
    fn-ocl-own-read-does-not-increase-connections
    fn-ocl-related-found-connection-has-history
    fn-ocl-own-read-survivor-had-original
    fn-ocl-config-shape-reconstructs
    fn-ocl-related-config-shaped
    fn-ocl-missing-read-keeps-configured-owner
    fn-ocl-own-read-survivor-has-old-history
    fn-ocl-relation-under-same-control-and-valid-connections
    fn-ocl-relation-read-input-facts
    fn-ocl-read-preserves-capacity-bound))
(in-theory (disable fn-ocl-read-proof-lemmas))
