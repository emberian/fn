; Actual configured-owner ADVANCE over a physical configuration history.
; The owner reports whether its rebuilt connection was admitted, and only an
; admitted rebuild moves the configuration pin.  This book proves the host-
; called transition against the carried historical relation, including the
; immutable archives of other connections.
(in-package "ACL2")
(include-book "config-owner-live")

(defthm fn-ocl-advance-result-keeps-owner-control
  (implies (fn-own-shapep (fn-ocfg-owner oc))
   (let* ((o (fn-ocfg-owner oc))
         (after (cdr (fn-own-advance-result o id))))
    (and (fn-own-shapep after)
         (equal (fn-own-store after) (fn-own-store o))
         (equal (fn-own-view after) (fn-own-view o))
         (equal (fn-own-next-id after) (fn-own-next-id o))
         (equal (fn-own-max-conns after) (fn-own-max-conns o))
         (equal (fn-own-ledger after) (fn-own-ledger o))
         (equal (fn-own-clock after) (fn-own-clock o))
         (equal (fn-own-facts after) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-advance-result fn-own-set-conns))))
(defthm fn-ocl-advance-result-pins-view
  (implies
   (equal (car (fn-own-advance-result o id)) :advanced)
   (let* ((next (cdr (fn-own-advance-result o id)))
          (conn (fn-own-find-conn id (fn-own-conns next))))
     (and conn
          (fn-own-conn-shapep conn)
          (equal (fn-own-conn-version conn)
                 (fn-own-view-version (fn-own-view o)))
          (equal (fn-own-conn-frontier conn)
                 (fn-own-view-frontier (fn-own-view o)))
          (equal (fn-own-conn-archive conn)
                 (fn-own-view-archive (fn-own-view o)))
          (fn-own-conn-boundedp conn
                                (fn-sn-groups (fn-own-store o))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-own-find-conn-id
                              (conns (fn-own-conns o))))
           :in-theory (e/d (fn-own-advance-result fn-own-set-conns)
                           (fn-own-conn-boundedp
                            fn-own-conn-make-group-indexed)))))
(defthm fn-ocl-current-config-is-store-domain
  (implies (fn-ocl-relation oc)
           (equal (fn-sn-groups (fn-own-store (fn-ocfg-owner oc)))
                  (fn-cnode-domain-of (fn-ocfg-config oc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation
                                    fn-cst-relation
                                    fn-cst-final-configurationp
                                    fn-ocl-config-historyp)
                                   (fn-cpr-replay fn-cst-replay-node
                                    fn-ocl-conns-historyp
                                    fn-ocl-view-historyp
                                    fn-ocl-view-configp)))))
(defthm fn-ocl-found-connection-has-pin
  (implies (and (fn-ocfg-conns-pinnedp conns pins)
                (fn-own-find-conn id conns))
           (fn-ocfg-pin-find id pins))
  :rule-classes nil
  :hints (("Goal" :induct (fn-own-find-conn id conns)
           :in-theory (enable fn-own-find-conn fn-ocfg-conns-pinnedp))))
(defthm fn-ocl-advanced-had-connection
  (implies (equal (car (fn-own-advance-result o id)) :advanced)
           (fn-own-find-conn id (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-own-advance-result))))
(defthm fn-ocl-advanced-connection-gets-current-pin
  (implies
   (and (fn-ocl-relation oc)
        (equal (car (fn-own-advance-result (fn-ocfg-owner oc) id))
               :advanced))
   (equal (fn-ocfg-conn-config (fn-ocfg-advance oc id) id)
          (fn-ocfg-config oc)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ocl-relation-read-input-facts
                 (:instance fn-ocl-advanced-had-connection
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-found-connection-has-pin
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc))))
           :in-theory (e/d (fn-ocfg-advance fn-ocfg-conn-config)
                           (fn-ocl-relation fn-own-advance-result
                            fn-ocfg-pin-set)))))
(defthm fn-ocl-advanced-connection-has-current-history
  (implies
   (and (fn-ocl-relation oc)
        (equal (car (fn-own-advance-result (fn-ocfg-owner oc) id))
               :advanced))
   (let* ((next (fn-ocfg-advance oc id))
          (conn (fn-own-find-conn id
                  (fn-own-conns (fn-ocfg-owner next)))))
     (fn-ocl-conn-historyp next conn)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ocl-relation-read-input-facts
                 (:instance fn-ocl-advance-result-keeps-owner-control)
                 (:instance fn-ocl-advance-result-pins-view
                            (o (fn-ocfg-owner oc)))
                 fn-ocl-current-config-is-store-domain
                 (:instance fn-own-find-conn-id
                            (conns (fn-own-conns
                                    (cdr (fn-own-advance-result
                                          (fn-ocfg-owner oc) id)))))
                 fn-ocl-advanced-connection-gets-current-pin
                 (:instance fn-ocl-unchanged-view-new-pin-is-historical
                            (next (fn-ocfg-advance oc id))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (fn-ocfg-owner
                                        (fn-ocfg-advance oc id)))))))
           :in-theory (e/d (fn-ocfg-advance)
                           (fn-ocl-relation fn-ocl-conn-historyp
                            fn-own-advance-result fn-cpr-replay
                            fn-cst-replay-node)))))
(defthm fn-ocl-advanced-connection-replaces-exact-id
  (implies
   (equal (car (fn-own-advance-result o id)) :advanced)
   (equal (fn-own-conns (cdr (fn-own-advance-result o id)))
          (fn-own-replace-conn
           (fn-own-find-conn
            id (fn-own-conns (cdr (fn-own-advance-result o id))))
           (fn-own-conns o))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-id
                            (conns (fn-own-conns o)))
                 (:instance fn-ocl-replacing-found-id-is-idempotent
                            (conns (fn-own-conns o))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-advance-result o id)))))))
           :in-theory (e/d (fn-own-advance-result fn-own-set-conns)
                           (fn-own-replace-conn
                            fn-own-conn-boundedp
                            fn-own-conn-make-group-indexed)))))
(defthm fn-ocl-other-connection-keeps-history-after-pin-set
  (implies
   (and (fn-ocl-conn-historyp oc conn)
        (not (equal (fn-own-conn-id conn) id))
        (equal (fn-own-store (fn-ocfg-owner next))
               (fn-own-store (fn-ocfg-owner oc)))
        (equal (fn-ocfg-pins next)
               (fn-ocfg-pin-set id cfg (fn-ocfg-pins oc))))
   (fn-ocl-conn-historyp next conn))
  :hints (("Goal"
           :use ((:instance fn-ocl-conn-historyp-under-same-store-and-pin))
           :in-theory (e/d (fn-ocfg-conn-config)
                           (fn-ocl-conn-historyp fn-cpr-replay
                            fn-cst-replay-node)))))
(defthm fn-ocl-connection-history-implies-consp
  (implies (fn-ocl-conn-historyp oc conn)
           (consp conn))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-ocl-conn-historyp))))
(defthm fn-ocl-others-keep-history-after-pin-set
  (implies
   (and (fn-ocl-conns-historyp oc conns)
        (not (fn-own-find-conn id conns))
        (equal (fn-own-store (fn-ocfg-owner next))
               (fn-own-store (fn-ocfg-owner oc)))
        (equal (fn-ocfg-pins next)
               (fn-ocfg-pin-set id cfg (fn-ocfg-pins oc))))
   (fn-ocl-conns-historyp next conns))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ocl-conns-historyp oc conns)
           :in-theory (e/d (fn-ocl-conns-historyp fn-own-find-conn)
                           (fn-ocl-conn-historyp)))))
(defthm fn-ocl-advance-replacement-preserves-connection-histories
  (implies
   (and (fn-ocl-conns-historyp oc conns)
        (fn-ocl-unique-conn-idsp conns)
        (fn-ocl-conn-historyp next advanced)
        (equal (fn-own-store (fn-ocfg-owner next))
               (fn-own-store (fn-ocfg-owner oc)))
        (equal (fn-ocfg-pins next)
               (fn-ocfg-pin-set id cfg (fn-ocfg-pins oc)))
        (equal (fn-own-conn-id advanced) id))
   (fn-ocl-conns-historyp
    next (fn-own-replace-conn advanced conns)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-own-replace-conn advanced conns)
           :in-theory (e/d (fn-own-replace-conn fn-ocl-conns-historyp
                            fn-ocl-unique-conn-idsp)
                           (fn-ocl-conn-historyp
                            fn-ocfg-pin-set
                            fn-cpr-replay fn-cst-replay-node)))))
(defthm fn-ocl-pin-set-preserves-pins-okp
  (implies (and (fn-cfgp cfg) (fn-ocfg-pins-okp pins))
           (fn-ocfg-pins-okp (fn-ocfg-pin-set id cfg pins)))
  :hints (("Goal" :induct (fn-ocfg-pin-set id cfg pins)
           :in-theory (enable fn-ocfg-pin-set fn-ocfg-pins-okp))))
(defthm fn-ocl-pin-set-keeps-existing-pin-domain
  (implies (fn-ocfg-pin-find selected pins)
           (fn-ocfg-pin-find selected (fn-ocfg-pin-set id cfg pins)))
  :hints (("Goal" :cases ((equal selected id)))))
(defthm fn-ocl-pin-set-preserves-connection-coverage
  (implies (fn-ocfg-conns-pinnedp conns pins)
           (fn-ocfg-conns-pinnedp conns
                                  (fn-ocfg-pin-set id cfg pins)))
  :hints (("Goal" :induct (fn-ocfg-conns-pinnedp conns pins)
           :in-theory (enable fn-ocfg-conns-pinnedp))))
(defthm fn-ocl-pin-set-preserves-pin-domain
  (implies (fn-ocfg-pins-pin-conns-only pins conns)
           (fn-ocfg-pins-pin-conns-only
            (fn-ocfg-pin-set id cfg pins) conns))
  :hints (("Goal" :induct (fn-ocfg-pin-set id cfg pins)
           :in-theory (enable fn-ocfg-pin-set
                              fn-ocfg-pins-pin-conns-only))))
(defthm fn-ocl-advanced-preserves-all-connection-histories
  (implies
   (and (fn-ocl-relation oc)
        (equal (car (fn-own-advance-result (fn-ocfg-owner oc) id))
               :advanced))
   (fn-ocl-conns-historyp
    (fn-ocfg-advance oc id)
    (fn-own-conns (fn-ocfg-owner (fn-ocfg-advance oc id)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ocl-relation-read-input-facts
                 fn-ocl-advanced-connection-has-current-history
                 (:instance fn-ocl-advanced-connection-replaces-exact-id
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-own-find-conn-id
                            (conns (fn-own-conns
                                    (cdr (fn-own-advance-result
                                          (fn-ocfg-owner oc) id)))))
                 (:instance fn-ocl-advance-result-keeps-owner-control)
                 (:instance fn-ocl-advance-replacement-preserves-connection-histories
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (next (fn-ocfg-advance oc id))
                            (advanced (fn-own-find-conn
                                       id (fn-own-conns
                                           (fn-ocfg-owner
                                            (fn-ocfg-advance oc id)))))
                            (cfg (fn-ocfg-config oc))))
           :in-theory (e/d (fn-ocfg-advance)
                           (fn-ocl-relation fn-ocl-conns-historyp
                            fn-own-advance-result
                            fn-own-replace-conn)))))
(defthm fn-ocl-advanced-preserves-connection-and-pin-clauses
  (implies
   (and (fn-ocl-relation oc)
        (equal (car (fn-own-advance-result (fn-ocfg-owner oc) id))
               :advanced))
   (let* ((next (fn-ocfg-advance oc id))
          (owner (fn-ocfg-owner next))
          (conns (fn-own-conns owner))
          (pins (fn-ocfg-pins next)))
     (and (fn-ocl-unique-conn-idsp conns)
          (fn-ocfg-pins-okp pins)
          (fn-ocfg-conns-pinnedp conns pins)
          (fn-ocfg-pins-pin-conns-only pins conns)
          (<= (len conns) (fn-own-max-conns owner))
          (fn-own-ids-below-next-p conns (fn-own-next-id owner)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ocl-relation-read-input-facts
                 (:instance fn-ocl-advanced-had-connection
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-advanced-connection-replaces-exact-id
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-advance-result-keeps-owner-control)
                 (:instance fn-ocl-advance-result-pins-view
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-own-find-conn-id
                            (conns (fn-own-conns
                                    (cdr (fn-own-advance-result
                                          (fn-ocfg-owner oc) id)))))
                 (:instance fn-ocl-pin-set-preserves-pins-okp
                            (cfg (fn-ocfg-config oc))
                            (pins (fn-ocfg-pins oc)))
                 (:instance fn-ocl-pin-set-preserves-connection-coverage
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc)))
                 (:instance fn-ocl-pin-set-preserves-pin-domain
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc)))
                 (:instance fn-ocl-replace-preserves-conns-pinned
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pin-set id (fn-ocfg-config oc)
                                                   (fn-ocfg-pins oc)))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (fn-ocfg-owner
                                        (fn-ocfg-advance oc id))))))
                 (:instance fn-ocl-replace-preserves-pins-point-to-conns
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pin-set id (fn-ocfg-config oc)
                                                   (fn-ocfg-pins oc)))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (fn-ocfg-owner
                                        (fn-ocfg-advance oc id))))))
                 (:instance fn-ocl-unique-ids-of-replace
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (fn-ocfg-owner
                                        (fn-ocfg-advance oc id))))))
                 (:instance fn-own-replace-conn-len
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (fn-ocfg-owner
                                        (fn-ocfg-advance oc id))))))
                 (:instance fn-own-replace-conn-ids-below-next
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (fn-ocfg-owner
                                        (fn-ocfg-advance oc id)))))
                            (n (fn-own-next-id (fn-ocfg-owner oc))))
                 (:instance fn-own-find-conn-id-below-next
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-next-id (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocfg-advance)
                           (fn-ocl-relation fn-own-advance-result
                            fn-own-replace-conn fn-ocfg-pin-set
                            fn-ocfg-pins-okp fn-ocfg-conns-pinnedp
                            fn-ocfg-pins-pin-conns-only
                            fn-ocl-unique-conn-idsp)))))
(defthm fn-ocl-nonadvanced-keeps-configured-owner
  (implies
   (and (fn-ocl-relation oc)
        (not (equal (car (fn-own-advance-result
                         (fn-ocfg-owner oc) id)) :advanced)))
   (equal (fn-ocfg-advance oc id) oc))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ocl-related-config-shaped
                 fn-ocl-config-shape-reconstructs)
           :in-theory (e/d (fn-ocfg-advance fn-own-advance-result)
                           (fn-ocl-relation fn-own-conn-boundedp
                            fn-own-conn-make-group-indexed)))))
(defthm fn-ocl-advance-preserves-historical-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-advance oc id)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((equal (car (fn-own-advance-result
                                (fn-ocfg-owner oc) id)) :advanced))
           :use (fn-ocl-nonadvanced-keeps-configured-owner
                 fn-ocl-relation-read-input-facts
                 (:instance fn-ocl-advance-result-keeps-owner-control)
                 fn-ocl-advanced-preserves-all-connection-histories
                 fn-ocl-advanced-preserves-connection-and-pin-clauses
                 (:instance
                  fn-ocl-relation-under-same-control-and-valid-connections
                  (next (fn-ocfg-advance oc id))))
           :in-theory (e/d (fn-ocfg-advance)
                           (fn-ocl-relation fn-own-advance-result
                            fn-ocl-conns-historyp fn-cst-relation
                            fn-cpr-replay fn-cst-replay-node
                            fn-ocl-relation-under-same-control-and-valid-connections)))))

; Keep the inductive pin helper from searching unrelated reader proofs.
(in-theory (disable fn-ocl-other-connection-keeps-history-after-pin-set
                    fn-ocl-advance-result-keeps-owner-control))
