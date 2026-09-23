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
             (fn-ocfg-published-config (fn-ocfg-config oc) record)
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

(deftheory fn-ocl-vocabulary '(fn-ocl-owner-with-store fn-ocl-complete))
(in-theory (disable fn-ocl-vocabulary))
