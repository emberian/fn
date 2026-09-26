;; fn: the configured owner the host installs at recovery satisfies the
;; configured owner's relation and the view-trie premise.
;
; host/owner-host.lisp fn-owner-recover builds the owner it installs from
; ACL2 functions only: fn-cpr-replay over the decoded configuration and Store
; journals, fn-cpo-open-observed over the same journals, then fn-own-start,
; fn-own-configure (with fn-oag-post-config, through the host wrapper
; fn-owner-post-config) and fn-ocfg-make.  The keystones of the carried
; served path (owner-served-carried, owner-commit-ocl, owner-advance-carried)
; take fn-ocl-relation and fn-scar-view-indexedp of the configured owner.
; This book proves both of the owner that recovery installs, over that exact
; composition, under the checks the host makes before it installs.

(in-package "ACL2")
(include-book "owner-offer-indexed")
;
; The hypotheses are exactly two of the host's checks before it installs:
; (natp max-conns) at owner-host.lisp:184 and the open's kind :ok at :192.
; Its other checks -- decoded journals not :bad (:183), a non-empty
; configuration journal (:184), the replay's kind :ok (:187) and the
; :recovering phase (:193) -- are implied by the open's kind :ok
; (fn-orec-open-ok-replays-ok, fn-cpo-open-success-exact-image), and the
; decoded configuration journal is a proper list because a successful replay
; ends on (null configs) (fn-orec-replay-ok-has-proper-configs).  Nothing is
; evaluated at open beyond what the host already computes.

; -----------------------------------------------------------------------------
; The open's typed result.

; The host dispatches on (fn-sn-open-kind opened) (owner-host.lisp:192), not on
; fn-sn-open-okp.  For the function it calls, fn-cpo-open-observed, kind :ok
; is fn-sn-open-okp: the only :ok arm is taken after (fn-sn-statep opened).
(defthm fn-orec-open-kind-ok-is-okp
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events))
                  :ok)
           (fn-sn-open-okp (fn-cpo-open-observed configs frontier events)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed fn-sn-open-okp
                                   fn-sn-open-shapep fn-sn-open-ok
                                   fn-sn-open-error fn-sn-open-kind
                                   fn-sn-open-state)
                                  (fn-cpr-replay fn-sn-statep fn-cpo-install
                                   fn-sn-with-event-index fn-sn-with-topic
                                   fn-sn-with-consumer fn-sn-update-replayed
                                   fn-sn-observed-seed fn-replay-identity
                                   fn-cpe-projection-replay fn-th-prefix-project
                                   fn-replay-advance-txid fn-cei-build
                                   fn-cnode-statep fn-replay-advance-okp
                                   fn-sn-observed-historyp
                                   fn-stx-index-of-store)))))

; The open replays the same two journals the host replayed at :186, so its
; kind :ok carries the replay's.
(defthm fn-orec-open-ok-replays-ok
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events))
                  :ok)
           (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed fn-sn-open-ok
                                   fn-sn-open-error fn-sn-open-kind)
                                  (fn-cpr-replay fn-sn-statep fn-cpo-install
                                   fn-sn-with-event-index fn-sn-with-topic
                                   fn-sn-with-consumer fn-sn-update-replayed
                                   fn-sn-observed-seed fn-replay-identity
                                   fn-cpe-projection-replay fn-th-prefix-project
                                   fn-replay-advance-txid fn-cei-build
                                   fn-cnode-statep fn-replay-advance-okp
                                   fn-sn-observed-historyp
                                   fn-stx-index-of-store)))))

; A successful configuration replay consumed a proper list: its only :ok arm
; is (and (null configs) (null events)).
(defthm fn-orec-cpr-loop-ok-has-proper-configs
  (implies (equal (fn-replay-result-kind
                   (fn-cpr-loop cn configs events config-sequence event-sequence))
                  :ok)
           (true-listp configs))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cpr-loop cn configs events config-sequence
                                       event-sequence)
           :in-theory (e/d (fn-cpr-loop)
                           (fn-cnode-statep fn-cnode-apply-config
                            fn-cpr-apply-event fn-cnode-record-acceptablep
                            fn-store-event-p fn-cfg-recordp
                            fn-replay-advance-okp fn-replay-advance-txid)))))

(defthm fn-orec-replay-ok-has-proper-configs
  (implies (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
           (true-listp configs))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-orec-cpr-loop-ok-has-proper-configs
                                   (cn (fn-cnode-initial (fn-cfg-initial)))
                                   (config-sequence 0) (event-sequence 0)))
           :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop)))))

; The configuration the host reads off its own replay (:189-190) is the one
; the relation reads off the opened store's carried history.
(defthm fn-orec-recovered-config-is-store-config
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (equal (fn-ocl-store-config
                   (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))
                  (fn-cnode-config (fn-replay-result-node
                                    (fn-cpr-replay configs events)))))
  :rule-classes nil
  :hints (("Goal" :use fn-cpo-open-success-exact-image
           :in-theory (e/d (fn-ocl-store-config)
                           (fn-cpo-open-observed fn-cpr-replay)))))

; -----------------------------------------------------------------------------
; The started, configured owner over a history-related idle store.

(defthm fn-orec-started-owner-fields-unfold
  (let ((o (fn-own-configure (fn-own-start st max-conns) post)))
    (and (fn-own-shapep o)
         (equal (fn-own-store o) st)
         (equal (fn-own-conns o) nil)
         (equal (fn-own-next-id o) 0)
         (equal (fn-own-max-conns o) max-conns)
         (equal (fn-own-ledger o) nil)
         (equal (fn-own-clock o) nil)
         (equal (fn-own-facts o) nil)))
  :hints (("Goal" :in-theory (e/d (fn-own-configure fn-own-start
                                   fn-own-refresh-keeps-fields)
                                  (fn-own-refresh)))))

(defthm fn-orec-view-historyp-of-configure
  (equal (fn-ocl-view-historyp (fn-own-configure o config))
         (fn-ocl-view-historyp o))
  :hints (("Goal" :in-theory (e/d (fn-ocl-view-historyp fn-own-configure)
                                  (fn-cst-replay-node fn-own-take)))))

; fn-own-start refreshes at every idle phase, :recovering among them, so the
; view is the whole journal's replay at the store's frontier: the store node,
; served as its visible state (the start view is consistent by construction:
; no records, no verdicts, the visible list of the empty prefix).
(defthm fn-orec-start-view-historyp
  (implies (and (fn-cst-relation st)
                (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files st))))
           (fn-ocl-view-historyp
            (fn-own-configure (fn-own-start st max-conns) post)))
  :hints (("Goal"
           :use (fn-ocl-cst-events-are-proper
                 (:instance fn-ocl-refreshed-idle-view-history
                  (view (let* ((prefix (fn-own-prefix-archive
                                        (fn-sn-groups st) (fn-sn-capacity st)
                                        (fn-sf-records (fn-sn-files st)) 0 0))
                               (archive (fn-ctl-visible-state prefix nil nil)))
                          (fn-own-view-make-visible
                           0 0 archive nil
                           (fn-midx-build (fn-state-articles archive))
                           (fn-gidx-build (fn-state-articles archive))
                           nil (fn-state-articles prefix)
                           (fn-ctl-subseq-diff (fn-state-articles prefix)
                                               (fn-state-articles archive))
                           nil)))
                  (conns nil) (next-id 0) (max-conns max-conns) (pending nil) (ledger nil)
                  (clock nil) (facts nil) (config nil) (queue nil) (inflight nil) (feeds nil)))
           :in-theory (e/d (fn-own-start fn-ocl-view-visiblep
                            fn-ctl-visible-state fn-own-refresh-keeps-fields)
                           (fn-own-refresh fn-ocl-view-historyp fn-cst-relation fn-own-configure
                            fn-cst-replay-node fn-cpr-replay fn-own-take
                            fn-snt-idle-phasep fn-ctl-visible-articles
                            fn-own-prefix-archive fn-midx-build fn-gidx-build)))))

(defthm fn-orec-start-view-configp
  (implies (and (fn-cst-relation st)
                (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files st))))
           (fn-ocl-view-configp
            (fn-ocfg-make (fn-own-configure (fn-own-start st max-conns) post)
                          (fn-ocl-store-config st) pins staged)))
  :hints (("Goal"
           :use ((:instance fn-own-take-of-len
                            (xs (fn-sf-records (fn-sn-files st))))
                 fn-ocl-cst-events-are-proper)
           :in-theory (e/d (fn-ocl-view-configp fn-own-start fn-own-configure
                            fn-own-refresh fn-own-store-idlep
                            fn-ocl-store-config)
                           (fn-cst-relation fn-cpr-replay fn-own-take
                            fn-own-view-make-group-indexed fn-snt-idle-phasep
                            fn-own-prefix-archive fn-midx-build fn-gidx-build
                            fn-midx-refresh)))))

(defthm fn-orec-start-config-historyp
  (implies (fn-cpo-history-relation st)
           (fn-ocl-config-historyp
            (fn-ocfg-make (fn-own-configure (fn-own-start st max-conns) post)
                          (fn-ocl-store-config st) pins staged)))
  :hints (("Goal"
           :in-theory (e/d (fn-ocl-config-historyp fn-own-start fn-own-configure
                            fn-own-refresh-keeps-fields
                            fn-ocl-store-config fn-cpo-history-relation)
                           (fn-own-refresh fn-cpr-replay)))))

(defthm fn-orec-started-owner-ocl-relation
  (implies (and (fn-cpo-history-relation st)
                (true-listp (fn-sn-config-history st))
                (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files st)))
                (natp max-conns))
           (fn-ocl-relation
            (fn-ocfg-make (fn-own-configure (fn-own-start st max-conns) post)
                          (fn-ocl-store-config st) nil nil)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-cst-idle-from-observed-history
                 fn-ocl-store-config-is-typed
                 fn-ocl-store-config-generation-counts-history
                 fn-orec-start-view-historyp
                 (:instance fn-orec-start-view-configp (pins nil) (staged nil))
                 (:instance fn-orec-start-config-historyp (pins nil) (staged nil)))
           :in-theory (e/d (fn-ocl-relation fn-ocl-conns-historyp)
                           (fn-own-start fn-own-configure
                            fn-own-refresh fn-cst-relation fn-cpo-history-relation
                            fn-ocl-store-config fn-ocl-view-historyp
                            fn-ocl-view-configp fn-ocl-config-historyp
                            fn-snt-idle-phasep fn-cfgp)))))

; -----------------------------------------------------------------------------
; The keystone: the owner fn-owner-recover installs.
;
; host/owner-host.lisp fn-owner-recover, in the order it calls them:
;   :186      replayed = (fn-cpr-replay config-records records)
;   :187      checks (fn-replay-result-kind replayed) = :ok
;   :189-190  cfg = (fn-cnode-config (fn-replay-result-node replayed))
;   :191      opened = (fn-cpo-open-observed config-records frontier records)
;   :192-194  checks (fn-sn-open-kind opened) = :ok and the :recovering phase
;   :195-201  installs (fn-ocfg-make (fn-own-configure
;                                     (fn-own-start (fn-sn-open-state opened)
;                                                   max-conns)
;                                     (fn-owner-post-config cfg))
;                                    cfg nil nil)
; where fn-owner-post-config (owner-host.lisp:80) is
; (fn-oag-post-config cfg *fn-record-max-payload*).  The conclusion carries
; both premises the carried served keystones take (fn-ocl-relation and
; fn-scar-view-indexedp of the owner).
(defthm fn-orec-recover-installs-ocl-relation
  (implies (and (natp max-conns)
                (equal (fn-sn-open-kind
                        (fn-cpo-open-observed configs frontier events))
                       :ok))
           (let* ((replayed (fn-cpr-replay configs events))
                  (cfg (fn-cnode-config (fn-replay-result-node replayed)))
                  (opened (fn-cpo-open-observed configs frontier events))
                  (oc (fn-ocfg-make
                       (fn-own-configure
                        (fn-own-start (fn-sn-open-state opened) max-conns)
                        (fn-oag-post-config cfg *fn-record-max-payload*))
                       cfg nil nil)))
             (and (fn-ocl-relation oc)
                  (fn-scar-view-indexedp (fn-ocfg-owner oc)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-orec-open-kind-ok-is-okp
                 fn-orec-open-ok-replays-ok
                 fn-orec-replay-ok-has-proper-configs
                 fn-orec-recovered-config-is-store-config
                 fn-cpo-open-success-exact-image
                 fn-cpo-open-success-has-historical-relation
                 (:instance fn-orec-started-owner-ocl-relation
                            (st (fn-sn-open-state
                                 (fn-cpo-open-observed configs frontier events)))
                            (post (fn-oag-post-config
                                   (fn-cnode-config
                                    (fn-replay-result-node
                                     (fn-cpr-replay configs events)))
                                   *fn-record-max-payload*))))
           :in-theory (e/d (fn-snt-idle-phasep)
                           (fn-cpo-open-observed fn-cpr-replay fn-ocl-relation
                            fn-own-start fn-own-configure fn-oag-post-config
                            fn-cpo-history-relation fn-ocl-store-config
                            fn-scar-view-indexedp fn-sn-open-okp)))))

; The native live administration opens a private logical connection before
; staging (host/native/admin.lisp:159, fnn-owner-core 'fn-owner-open), and
; fn-owner-open calls (fn-ocfg-open (fn-owner-ocfg state) (fn-owner-auth
; state)) at owner-host.lisp:1337.  The preservation is the keystones
; fn-ocl-open-preserves-historical-relation (config-owner-live) and
; fn-oix-ocfg-open-keeps-view-indexed (owner-offer-indexed), which hold for
; every related owner and every acfg; this corollary composes them with the
; recovery keystone for the first open after recovery.
(defthm fn-orec-admin-open-after-recover-keeps-premises
  (implies (and (natp max-conns)
                (equal (fn-sn-open-kind
                        (fn-cpo-open-observed configs frontier events))
                       :ok))
           (let* ((replayed (fn-cpr-replay configs events))
                  (cfg (fn-cnode-config (fn-replay-result-node replayed)))
                  (opened (fn-cpo-open-observed configs frontier events))
                  (oc (fn-ocfg-make
                       (fn-own-configure
                        (fn-own-start (fn-sn-open-state opened) max-conns)
                        (fn-oag-post-config cfg *fn-record-max-payload*))
                       cfg nil nil))
                  (admin (cdr (fn-ocfg-open oc acfg))))
             (and (fn-ocl-relation admin)
                  (fn-scar-view-indexedp (fn-ocfg-owner admin)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-orec-recover-installs-ocl-relation
                 (:instance fn-ocl-open-preserves-historical-relation
                            (oc (fn-ocfg-make
                                 (fn-own-configure
                                  (fn-own-start
                                   (fn-sn-open-state
                                    (fn-cpo-open-observed configs frontier events))
                                   max-conns)
                                  (fn-oag-post-config
                                   (fn-cnode-config
                                    (fn-replay-result-node
                                     (fn-cpr-replay configs events)))
                                   *fn-record-max-payload*))
                                 (fn-cnode-config
                                  (fn-replay-result-node
                                   (fn-cpr-replay configs events)))
                                 nil nil)))
                 (:instance fn-oix-ocfg-open-keeps-view-indexed
                            (oc (fn-ocfg-make
                                 (fn-own-configure
                                  (fn-own-start
                                   (fn-sn-open-state
                                    (fn-cpo-open-observed configs frontier events))
                                   max-conns)
                                  (fn-oag-post-config
                                   (fn-cnode-config
                                    (fn-replay-result-node
                                     (fn-cpr-replay configs events)))
                                   *fn-record-max-payload*))
                                 (fn-cnode-config
                                  (fn-replay-result-node
                                   (fn-cpr-replay configs events)))
                                 nil nil))))
           :in-theory '())))
