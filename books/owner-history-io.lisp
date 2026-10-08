; Owner view preservation for the resident refresh, without assuming its content relation.
(in-package "ACL2")
(include-book "owner-refresh-indexed")
(include-book "history-served-sync")
(include-book "owner-prepare-served-ocl")
(include-book "history-served-control-invariants")

(local
 (defthm fn-hsv-record-count-is-length
  (equal (fn-sf-records-count files) (len (fn-sf-records files)))
  :hints (("Goal" :in-theory (union-theories '(fn-sf-records-count) (theory 'minimal-theory))))))

(defun fn-ocl-owner-with-store-ix (o st fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (fn-own-refresh-ix (fn-own-make st
                                  (fn-own-view o)
                                  (fn-own-conns o)
                                  (fn-own-next-id o)
                                  (fn-own-max-conns o)
                                  (fn-own-pending o)
                                  (fn-own-ledger-field o)
                                  (fn-own-clock o)
                                  (fn-own-facts o)
                                  (fn-own-config o)
                                  (fn-own-queue o)
                                  (fn-own-inflight o)
                                  (fn-own-feeds o)
                                  (fn-own-node-secret o)
                                  (fn-own-refused o))
                     fn-hist))

(defthm fn-own-refresh-keeps-fields-ix
  (and (equal (fn-own-store (fn-own-refresh-ix o fn-hist)) (fn-own-store o))
       (equal (fn-own-conns (fn-own-refresh-ix o fn-hist)) (fn-own-conns o))
       (equal (fn-own-next-id (fn-own-refresh-ix o fn-hist)) (fn-own-next-id o))
       (equal (fn-own-max-conns (fn-own-refresh-ix o fn-hist)) (fn-own-max-conns o))
       (equal (fn-own-pending (fn-own-refresh-ix o fn-hist)) (fn-own-pending o))
       (equal (fn-own-ledger (fn-own-refresh-ix o fn-hist)) (fn-own-ledger o))
       (equal (fn-own-clock (fn-own-refresh-ix o fn-hist)) (fn-own-clock o))
       (equal (fn-own-facts (fn-own-refresh-ix o fn-hist)) (fn-own-facts o))
       (equal (fn-own-config (fn-own-refresh-ix o fn-hist)) (fn-own-config o))
       (equal (fn-own-queue (fn-own-refresh-ix o fn-hist)) (fn-own-queue o))
       (equal (fn-own-inflight (fn-own-refresh-ix o fn-hist)) (fn-own-inflight o))
       (equal (fn-own-refused (fn-own-refresh-ix o fn-hist)) (fn-own-refused o)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-own-refresh-ix) (fn-own-store-idlep fn-own-refresh-ix-is-own-refresh)))))

(defthm fn-lgoc-refresh-not-idle-ix
  (implies (not (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files (fn-own-store o)))))
           (equal (fn-own-refresh-ix o fn-hist) o))
  :hints (("Goal" :in-theory (quote (fn-own-refresh-ix fn-own-store-idlep)))))

(defthm fn-lgoc-refreshed-idle-view-config-ix
  (implies (and (fn-ocl-config-historyp (fn-ocfg-make (fn-own-refresh-ix (fn-own-make st
                                                                                      view
                                                                                      conns
                                                                                      next-id
                                                                                      max-conns
                                                                                      pending
                                                                                      ledger
                                                                                      clock
                                                                                      facts
                                                                                      config
                                                                                      queue
                                                                                      inflight
                                                                                      feeds
                                                                                      node-secret
                                                                                      refused)
                                                                         fn-hist)
                                                      cfg
                                                      pins
                                                      staged))
                (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files st)))
                (true-listp (fn-sf-records (fn-sn-files st))))
           (fn-ocl-view-configp (fn-ocfg-make (fn-own-refresh-ix (fn-own-make st
                                                                              view
                                                                              conns
                                                                              next-id
                                                                              max-conns
                                                                              pending
                                                                              ledger
                                                                              clock
                                                                              facts
                                                                              config
                                                                              queue
                                                                              inflight
                                                                              feeds
                                                                              node-secret
                                                                              refused)
                                                                 fn-hist)
                                              cfg
                                              pins
                                              staged)))
  :rule-classes nil
  :hints (("Goal"
           :use
           ((:instance fn-own-take-of-len (xs (fn-sf-records (fn-sn-files st)))))
           :in-theory
           (e/d (fn-ocl-view-configp fn-ocl-config-historyp fn-own-refresh-ix fn-own-store-idlep)
                (fn-cpr-replay fn-own-take
                               fn-snt-idle-phasep
                               fn-own-view-make-group-indexed
                               fn-ctl-served-refresh-visible-is-visible
                               fn-ctl-visible-articles
                               fn-ctl-visible-filter
                               fn-ctl-withdrawn-by-p
                               fn-ctl-withdrawal-effect
                               fn-ctl-withdrawalp)))))

(defthm fn-ocl-refreshed-idle-view-history-ix
  (implies (and (fn-ocl-view-visiblep view)
                (fn-cst-relation st)
                (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files st)))
                (true-listp (fn-sf-records (fn-sn-files st))))
           (fn-ocl-view-historyp (fn-own-refresh-ix (fn-own-make st
                                                                 view
                                                                 conns
                                                                 next-id
                                                                 max-conns
                                                                 pending
                                                                 ledger
                                                                 clock
                                                                 facts
                                                                 config
                                                                 queue
                                                                 inflight
                                                                 feeds
                                                                 node-secret
                                                                 refused)
                                                    fn-hist)))
  :rule-classes nil
  :hints (("Goal"
           :use
           ((:instance fn-own-take-of-len (xs (fn-sf-records (fn-sn-files st))))
            (:instance fn-own-node-statep-acceptance-articles (node (fn-sn-node st)))
            (:instance fn-ctl-article-listp-msgids-distinct
                       (configured (fn-state-groups (fn-node-acceptance (fn-sn-node st))))
                       (xs (fn-state-articles (fn-node-acceptance (fn-sn-node st)))))
            (:instance fn-ctl-served-refresh-visible-is-visible
                       (new (fn-state-articles (fn-node-acceptance (fn-sn-node st))))
                       (old (fn-own-view-raw view))
                       (old-visible (fn-state-articles (fn-own-view-archive view)))
                       (ws (fn-own-view-withdrawals view))
                       (old-verdicts (fn-own-view-verdicts view))
                       (verdicts (fn-sn-verdicts st))
                       (files (fn-sn-files st))
                       (hist fn-hist)
                       (configs (fn-sn-config-history st))))
           :in-theory
           (e/d (fn-ocl-view-historyp fn-ocl-view-visiblep
                                      fn-own-refresh-ix
                                      fn-own-store-idlep
                                      fn-cst-relation
                                      fn-ctl-visible-state)
                (fn-cst-replay-node fn-cpr-replay
                                    fn-own-take
                                    fn-own-view-make-group-indexed
                                    fn-ctl-served-refresh-visible-is-visible
                                    fn-ctl-refresh-visible
                                    fn-ctl-refresh-withdrawals-served
                                    fn-ctl-visible-articles
                                    fn-ctl-visible-state-of
                                    fn-own-node-statep-acceptance-articles
                                    fn-ctl-article-listp-msgids-distinct
                                    fn-node-statep
                                    fn-article-listp
                                    fn-snt-idle-phasep)))))

(defthm fn-own-refresh-ix-preserves-shape
 (implies (fn-own-shapep o) (fn-own-shapep (fn-own-refresh-ix o hist)))
 :hints (("Goal" :in-theory (e/d (fn-own-refresh-ix)
 (fn-own-refresh-ix-is-own-refresh fn-own-make fn-own-view-make-visible fn-own-shapep)))))

(defthm fn-lgoc-ocl-relation-of-owner-with-store-ix
  (implies (and (fn-ocl-relation oc)
                (fn-cst-relation st)
                (equal (fn-sn-config-history st)
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                               (fn-sf-records (fn-sn-files st))))
           (fn-ocl-relation (fn-ocfg-with-owner oc
                                                (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                                            st
                                                                            fn-hist))))
  :hints (("Goal"
           :cases
           ((fn-snt-idle-phasep (fn-sf-phase (fn-sn-files st))))
           :use
           ((:instance fn-lgoc-cst-relation-replay-ok)
            (:instance fn-lgoc-config-historyp-of-longer-history
                       (oc2 (fn-ocfg-with-owner oc
                                                (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                                            st
                                                                            fn-hist))))
            (:instance fn-lgoc-conns-historyp-of-longer-history
                       (conns (fn-own-conns (fn-ocfg-owner oc)))
                       (oc2 (fn-ocfg-with-owner oc
                                                (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                                            st
                                                                            fn-hist))))
            (:instance fn-lgoc-ledger-durablep-of-longer-history
                       (ledger (fn-own-ledger (fn-ocfg-owner oc)))
                       (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                       (ys (fn-sf-records (fn-sn-files st))))
            (:instance fn-ocl-view-historyp-is-visible (o (fn-ocfg-owner oc)))
            (:instance fn-lgoc-view-historyp-of-longer-history
                       (o (fn-ocfg-owner oc))
                       (o2 (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc) st fn-hist)))
            (:instance fn-lgoc-view-configp-of-longer-history
                       (oc2 (fn-ocfg-with-owner oc
                                                (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                                            st
                                                                            fn-hist))))
            (:instance fn-cstp-relation-is-statep)
            (:instance fn-cstp-sn-statep-files (st s))
            (:instance fn-sf-state-records-are-true-list (s (fn-sn-files st)))
            (:instance fn-ocl-refreshed-idle-view-history-ix
                       (view (fn-own-view (fn-ocfg-owner oc)))
                       (conns (fn-own-conns (fn-ocfg-owner oc)))
                       (next-id (fn-own-next-id (fn-ocfg-owner oc)))
                       (max-conns (fn-own-max-conns (fn-ocfg-owner oc)))
                       (pending (fn-own-pending (fn-ocfg-owner oc)))
                       (ledger (fn-own-ledger-field (fn-ocfg-owner oc)))
                       (clock (fn-own-clock (fn-ocfg-owner oc)))
                       (facts (fn-own-facts (fn-ocfg-owner oc)))
                       (config (fn-own-config (fn-ocfg-owner oc)))
                       (queue (fn-own-queue (fn-ocfg-owner oc)))
                       (inflight (fn-own-inflight (fn-ocfg-owner oc)))
                       (feeds (fn-own-feeds (fn-ocfg-owner oc)))
                       (node-secret (fn-own-node-secret (fn-ocfg-owner oc)))
                       (refused (fn-own-refused (fn-ocfg-owner oc))))
            (:instance fn-lgoc-refreshed-idle-view-config-ix
                       (view (fn-own-view (fn-ocfg-owner oc)))
                       (conns (fn-own-conns (fn-ocfg-owner oc)))
                       (next-id (fn-own-next-id (fn-ocfg-owner oc)))
                       (max-conns (fn-own-max-conns (fn-ocfg-owner oc)))
                       (pending (fn-own-pending (fn-ocfg-owner oc)))
                       (ledger (fn-own-ledger-field (fn-ocfg-owner oc)))
                       (clock (fn-own-clock (fn-ocfg-owner oc)))
                       (facts (fn-own-facts (fn-ocfg-owner oc)))
                       (config (fn-own-config (fn-ocfg-owner oc)))
                       (queue (fn-own-queue (fn-ocfg-owner oc)))
                       (inflight (fn-own-inflight (fn-ocfg-owner oc)))
                       (feeds (fn-own-feeds (fn-ocfg-owner oc)))
                       (node-secret (fn-own-node-secret (fn-ocfg-owner oc)))
                       (refused (fn-own-refused (fn-ocfg-owner oc)))
                       (cfg (fn-ocfg-config oc))
                       (pins (fn-ocfg-pins oc))
                       (staged (fn-ocfg-staged oc))))
           :in-theory
           (e/d (fn-ocl-relation fn-ocfg-with-owner
                                 fn-ocl-owner-with-store-ix
                                 fn-own-refresh-keeps-fields-ix
                                 fn-lgoc-refresh-not-idle-ix)
                (fn-own-refresh-ix fn-cst-relation
                                   fn-snt-idle-phasep
                                   fn-ocl-conns-historyp
                                   fn-ocl-config-historyp
                                   fn-ocl-view-configp
                                   fn-ocl-view-historyp
                                   fn-ocl-view-visiblep
                                   fn-ocl-view-historyp-is-visible
                                   fn-ocl-unique-conn-idsp
                                   fn-ocfg-pins-okp
                                   fn-ocfg-conns-pinnedp
                                   fn-ocfg-pins-pin-conns-only
                                   fn-own-ids-below-next-p
                                   fn-own-facts-okp
                                   fn-clock-observationp
                                   fn-cfgp
                                   fn-cpr-replay
                                   fn-own-ledger-durablep
                                   fn-sf-prefixp
                                   fn-sn-statep
                                   fn-sf-statep
                                   fn-lgoc-config-historyp-of-longer-history
                                   fn-lgoc-conns-historyp-of-longer-history
                                   fn-lgoc-ledger-durablep-of-longer-history
                                   fn-lgoc-view-historyp-of-longer-history
                                   fn-lgoc-view-configp-of-longer-history
                                   fn-lgoc-cst-relation-replay-ok
                                   fn-nntp-response-text-true-listp
                                   fn-oct-bufp-true-listp
                                   fn-nntp-response-textp
                                   fn-cbor-octet-listp
                                   fn-scc-octet-listp
                                   (:definition true-listp))))))

(defun fn-rcon-ocfg-io-ix (oc operation result fn-hist)
 (declare (xargs :stobjs fn-hist
                 :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
 (fn-ocfg-with-owner oc
  (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
   (fn-rcon-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result) fn-hist)))

(defthm fn-ocl-owner-with-store-ix-is-reference
 (implies (and (fn-sn-statep st) (fn-hist-of-storep hist st))
  (equal (fn-ocl-owner-with-store-ix o st hist) (fn-ocl-owner-with-store o st)))
 :hints (("Goal" :in-theory '(fn-ocl-owner-with-store-ix fn-ocl-owner-with-store
 fn-own-refresh-ix-is-own-refresh fn-own-store-of-fn-own-make))))

(defthm fn-rcon-ocfg-io-ix-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist
                 (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result)))
  (equal (fn-rcon-ocfg-io-ix oc operation result hist) (fn-rcon-ocfg-io oc operation result)))
 :hints (("Goal" :in-theory '(fn-rcon-ocfg-io-ix fn-lgoc-rcon-io-is-owner-with-store
 fn-ocl-owner-with-store-ix-is-reference fn-rcon-sn-io-is-sn-io fn-sn-io-preserves-state))))

(defthm fn-hsv-store-of-owner-with-store
 (equal (fn-own-store (fn-ocfg-owner
         (fn-ocfg-with-owner oc (fn-ocl-owner-with-store-ix o st hist)))) st)
 :hints (("Goal" :in-theory '(fn-ocfg-with-owner fn-ocl-owner-with-store-ix
 fn-own-refresh-keeps-fields-ix fn-ocfg-owner-of-fn-ocfg-make fn-own-store-of-fn-own-make))))

(defthm fn-hsv-rcon-io-preserves-invariant
 (implies (and (fn-lgoc-invariantp oc)
               (fn-lgoc-io-safep (fn-own-store (fn-ocfg-owner oc)) operation result))
  (fn-lgoc-invariantp (fn-rcon-ocfg-io-ix oc operation result hist)))
 :hints (("Goal"
 :use ((:instance fn-lgoc-io-store-preserves (st (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-lgoc-ocl-relation-of-owner-with-store-ix
          (st (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result)) (fn-hist hist))
       (:instance fn-cstp-io-fields (s (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-snt-io-records-prefix (s (fn-own-store (fn-ocfg-owner oc))))
       fn-lgoc-ocl-relation-cst)
 :in-theory '(fn-lgoc-invariantp fn-rcon-ocfg-io-ix fn-rcon-sn-io-is-sn-io
 fn-hsv-store-of-owner-with-store fn-cstp-relation-is-statep))))

(defthm fn-hsv-deferred-dir-preserves-invariant
 (implies (and (fn-lgoc-invariantp oc)
               (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) :record-attempted)
               (not (fn-held-p (fn-sf-record-candidate (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))))
  (fn-lgoc-invariantp (fn-rcon-ocfg-io-ix oc :record-directory :ok hist)))
 :hints (("Goal"
 :use ((:instance fn-psrv-deferred-record-dir-preserves-relation (s (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-cstp-record-dir-preserves-carriedp (s (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-lgoc-ocl-relation-of-owner-with-store-ix
        (st (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) :record-directory :ok)) (fn-hist hist))
       (:instance fn-cstp-io-fields (s (fn-own-store (fn-ocfg-owner oc))) (operation :record-directory) (result :ok))
       (:instance fn-snt-io-records-prefix (s (fn-own-store (fn-ocfg-owner oc))) (operation :record-directory) (result :ok))
       fn-lgoc-invariant-statep fn-lgoc-ocl-relation-cst)
 :in-theory '(fn-lgoc-invariantp fn-rcon-ocfg-io-ix fn-rcon-sn-io-is-sn-io
 fn-hsv-store-of-owner-with-store))))

(defthm fn-hsv-served-io-preserves-invariant
 (implies (and (fn-lgoc-invariantp oc) (fn-psrv-io-safep operation))
  (fn-lgoc-invariantp (fn-rcon-ocfg-io-ix oc operation result hist)))
 :hints (("Goal"
 :cases ((and (equal operation :record-directory) (equal result :ok)
              (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) :record-attempted)
              (not (fn-held-p (fn-sf-record-candidate (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))))
 :use (fn-hsv-rcon-io-preserves-invariant fn-hsv-deferred-dir-preserves-invariant)
 :in-theory '(fn-psrv-io-safep fn-lgoc-io-safep member-equal
 (:executable-counterpart equal) (:executable-counterpart member-equal)))))

(defthm fn-hsv-base-of-kept-field
 (equal (fn-hist-served-base
         (fn-sf-make-fields phase frontier candidate (fn-sf-records-field files)
                            record completion successes barriers))
        (fn-hist-served-base files))
 :hints (("Goal" :in-theory '(fn-hist-served-base fn-sf-records-field-of-fn-sf-make-fields))))

(defthm fn-hsv-base-of-appended-field
 (equal (fn-hist-served-base
         (fn-sf-make-fields phase frontier candidate (fn-sfr-snoc (fn-sf-records-field files) event)
                            record completion successes barriers))
        (fn-hist-served-base files))
 :hints (("Goal" :in-theory (e/d (fn-hist-served-base fn-sfr-snoc fn-sfr-based fn-sfr-handle fn-sfr-basedp)
                                (fn-sl-snoc fn-sf-make-fields)))))

(defthm fn-hsv-file-step-keeps-base
 (equal (fn-hist-served-base (fn-sn-file-step files operation result))
        (fn-hist-served-base files))
 :hints (("Goal" :in-theory
 (e/d (fn-sn-file-step fn-sf-start-frontier fn-sf-frontier-file-result
        fn-sf-frontier-replace-result fn-sf-frontier-dir-result fn-sf-record-file-result
        fn-sf-record-link-result fn-sf-record-dir-result fn-sf-recovery-barrier)
      (fn-hist-served-base fn-sf-statep fn-sf-make-fields fn-store-event-p)))))

(defthm fn-hsv-io-keeps-base
 (equal (fn-hist-served-base (fn-sn-files (fn-sn-io s operation result)))
        (fn-hist-served-base (fn-sn-files s)))
 :hints (("Goal" :use ((:instance fn-cstp-io-fields))
 :in-theory '(fn-hsv-file-step-keeps-base))))

(defun fn-hsv-observe (oc operation result fn-hist)
 (declare (xargs :stobjs fn-hist
                 :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
 (let* ((s (fn-rcon-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result))
        (fn-hist (fn-hist-served-sync (fn-sn-files s) fn-hist)))
  (mv (fn-ocfg-with-owner oc (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc) s fn-hist))
      fn-hist)))

(defthm fn-hsv-observe-value-is-indexed-io
 (equal (mv-nth 0 (fn-hsv-observe oc operation result hist))
        (fn-rcon-ocfg-io-ix oc operation result (mv-nth 1 (fn-hsv-observe oc operation result hist))))
 :hints (("Goal" :in-theory '(fn-hsv-observe fn-rcon-ocfg-io-ix))))

(defthm fn-hsv-observe-store
 (equal (fn-own-store (fn-ocfg-owner (mv-nth 0 (fn-hsv-observe oc operation result hist))))
        (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result))
 :hints (("Goal" :in-theory '(fn-hsv-observe fn-rcon-sn-io-is-sn-io fn-hsv-store-of-owner-with-store))))

(defthm fn-hsv-observe-preserves-state
 (implies (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
  (fn-sn-statep (fn-own-store (fn-ocfg-owner (mv-nth 0 (fn-hsv-observe oc operation result hist))))))
 :hints (("Goal" :in-theory '(fn-hsv-observe-store fn-sn-io-preserves-state))))

(defthm fn-hsv-observe-preserves-invariant
 (implies (and (fn-lgoc-invariantp oc) (fn-psrv-io-safep operation))
  (fn-lgoc-invariantp (mv-nth 0 (fn-hsv-observe oc operation result hist))))
 :hints (("Goal" :in-theory '(fn-hsv-observe-value-is-indexed-io fn-hsv-served-io-preserves-invariant))))

(defthm fn-hsv-state-has-history-list
 (implies (fn-sn-statep s) (true-listp (fn-sf-records (fn-sn-files s))))
 :hints (("Goal" :use ((:instance fn-cstp-sn-statep-files (st s))
                       (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s))))
                 :in-theory (theory 'minimal-theory))))

(defthm fn-hsv-observe-history-is-store
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (fn-hist-of-storep
   (mv-nth 1 (fn-hsv-observe oc operation result hist))
   (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result)))
 :hints (("Goal"
 :use ((:instance fn-hist-served-base-is-within-record-count
          (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
       (:instance fn-hsv-io-keeps-base (s (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-snt-io-records-prefix (s (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-sn-io-preserves-state (s (fn-own-store (fn-ocfg-owner oc)))))
 :in-theory '(fn-hsv-observe fn-rcon-sn-io-is-sn-io fn-hist-of-storep
 fn-hist-served-sync-is-sync fn-hist-sync-of-prefix-is-the-history
 fn-hist-count-is-len fn-sf-records-count fn-hsv-state-has-history-list))))

(defthm fn-hsv-observe-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (mv-nth 0 (fn-hsv-observe oc operation result hist))
         (fn-rcon-ocfg-io oc operation result)))
 :hints (("Goal" :use (fn-hsv-observe-history-is-store)
 :in-theory '(fn-hsv-observe-value-is-indexed-io fn-rcon-ocfg-io-ix-is-reference))))

(defthm fn-hsv-observe-preserves-history
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (fn-hist-of-storep
   (mv-nth 1 (fn-hsv-observe oc operation result hist))
   (fn-own-store (fn-ocfg-owner (mv-nth 0 (fn-hsv-observe oc operation result hist))))))
 :hints (("Goal" :in-theory '(fn-hsv-observe-store fn-hsv-observe-history-is-store))))

(in-theory (disable fn-hsv-observe fn-rcon-ocfg-io-ix fn-ocl-owner-with-store-ix))

(defthm fn-hsv-observe-car-preserves-state
 (implies (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
  (fn-sn-statep (fn-own-store (fn-ocfg-owner (car (fn-hsv-observe oc operation result hist))))))
 :hints (("Goal" :use fn-hsv-observe-preserves-state :in-theory (union-theories '(mv-nth zp) (theory 'ground-zero)))))
(defthm fn-hsv-observe-car-preserves-history
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (fn-hist-of-storep (mv-nth 1 (fn-hsv-observe oc operation result hist))
   (fn-own-store (fn-ocfg-owner (car (fn-hsv-observe oc operation result hist))))))
 :hints (("Goal" :use fn-hsv-observe-preserves-history :in-theory (union-theories '(mv-nth zp) (theory 'ground-zero)))))
(defthm fn-hsv-observe-car-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (car (fn-hsv-observe oc operation result hist)) (fn-rcon-ocfg-io oc operation result)))
 :hints (("Goal" :use fn-hsv-observe-is-reference :in-theory (union-theories '(mv-nth zp) (theory 'ground-zero)))))
(defthm fn-hsv-observe-car-preserves-invariant
 (implies (and (fn-lgoc-invariantp oc) (fn-psrv-io-safep operation))
  (fn-lgoc-invariantp (car (fn-hsv-observe oc operation result hist))))
 :hints (("Goal" :use fn-hsv-observe-preserves-invariant :in-theory (union-theories '(mv-nth zp) (theory 'ground-zero)))))

(defthm fn-hsv-observe-history-of-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (fn-hist-of-storep (mv-nth 1 (fn-hsv-observe oc operation result hist))
                    (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc operation result)))))
 :hints (("Goal" :use (fn-hsv-observe-preserves-history fn-hsv-observe-is-reference)
 :in-theory (theory 'minimal-theory))))
