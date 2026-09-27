; fn: the configured owner's invariant across the format-9 commit
; (lane control-quanta-2, 2026-09-27; PKT-827 (c)).
;
; This book shares the prefix `fn-lgoc-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "config-store-steps")
(include-book "owner-commit-ocl")
(include-book "owner-log-route")
(include-book "post-identity-index")
(include-book "owner-checkpoint-open")
(include-book "config-owner-carried")
(defthm fn-lgoc-conn-historyp-of-longer-history
  (implies (and (fn-ocl-conn-historyp oc conn)
                (equal (fn-ocfg-pins oc2) (fn-ocfg-pins oc))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc2)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                               (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2))))))
           (fn-ocl-conn-historyp oc2 conn))
  :hints (("Goal" :use ((:instance fn-own-prefixp-len
                                   (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                                   (ys (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2))))))
                        (:instance fn-own-take-of-prefix
                                   (n (fn-own-conn-version conn))
                                   (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                                   (ys (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2)))))))
           :in-theory (e/d (fn-ocl-conn-historyp fn-ocfg-conn-config)
                           (fn-cpr-replay fn-cst-replay-node fn-own-take fn-own-take-of-prefix
                            fn-own-conn-boundedp fn-ctl-projectionp fn-node-statep
                            fn-cfgp fn-own-conn-shapep)))))

(defthm fn-lgoc-conns-historyp-of-longer-history
  (implies (and (fn-ocl-conns-historyp oc conns)
                (equal (fn-ocfg-pins oc2) (fn-ocfg-pins oc))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc2)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                               (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2))))))
           (fn-ocl-conns-historyp oc2 conns))
  :hints (("Goal" :induct (fn-ocl-conns-historyp oc conns)
           :in-theory (e/d (fn-ocl-conns-historyp) (fn-ocl-conn-historyp)))))

(defthm fn-lgoc-ledger-durablep-of-longer-history
  (implies (and (fn-own-ledger-durablep ledger xs)
                (fn-sf-prefixp xs ys))
           (fn-own-ledger-durablep ledger ys))
  :hints (("Goal" :induct (fn-own-ledger-durablep ledger xs)
           :in-theory (e/d (fn-own-ledger-durablep) (fn-sf-record-has-pairp)))))
(defthm fn-lgoc-refresh-not-idle
  (implies (not (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files (fn-own-store o)))))
           (equal (fn-own-refresh o) o))
  :hints (("Goal" :in-theory '(fn-own-refresh fn-own-store-idlep))))

(defthm fn-lgoc-refreshed-idle-view-config
  (implies (and (fn-ocl-config-historyp
                 (fn-ocfg-make
                  (fn-own-refresh
                   (fn-own-make st view conns next-id max-conns pending ledger
                                clock facts config queue inflight feeds node-secret refused))
                  cfg pins staged))
                (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files st)))
                (true-listp (fn-sf-records (fn-sn-files st))))
           (fn-ocl-view-configp
            (fn-ocfg-make
             (fn-own-refresh
              (fn-own-make st view conns next-id max-conns pending ledger
                           clock facts config queue inflight feeds node-secret refused))
             cfg pins staged)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-take-of-len
                            (xs (fn-sf-records (fn-sn-files st)))))
           :in-theory (e/d (fn-ocl-view-configp fn-ocl-config-historyp
                            fn-own-refresh fn-own-store-idlep)
                           (fn-cpr-replay fn-own-take fn-snt-idle-phasep
                            fn-own-view-make-group-indexed
                            fn-ctl-refresh-visible-is-visible fn-ctl-visible-articles
                            fn-ctl-visible-filter fn-ctl-withdrawn-by-p
                            fn-ctl-withdrawal-effect fn-ctl-withdrawalp)))))
(defthm fn-lgoc-view-historyp-of-longer-history
  (implies (and (fn-ocl-view-historyp o)
                (equal (fn-own-view o2) (fn-own-view o))
                (equal (fn-sn-config-history (fn-own-store o2))
                       (fn-sn-config-history (fn-own-store o)))
                (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store o)))
                               (fn-sf-records (fn-sn-files (fn-own-store o2)))))
           (fn-ocl-view-historyp o2))
  :hints (("Goal" :use ((:instance fn-own-prefixp-len
                                   (xs (fn-sf-records (fn-sn-files (fn-own-store o))))
                                   (ys (fn-sf-records (fn-sn-files (fn-own-store o2)))))
                        (:instance fn-own-take-of-prefix
                                   (n (fn-own-view-version (fn-own-view o)))
                                   (xs (fn-sf-records (fn-sn-files (fn-own-store o))))
                                   (ys (fn-sf-records (fn-sn-files (fn-own-store o2))))))
           :in-theory (e/d (fn-ocl-view-historyp)
                           (fn-cst-replay-node fn-own-take fn-own-take-of-prefix
                            fn-own-prefixp-len fn-node-statep fn-ctl-visible-state
                            fn-own-view-shapep)))))

(defthm fn-lgoc-view-configp-of-longer-history
  (implies (and (fn-ocl-view-configp oc)
                (fn-ocl-view-historyp (fn-ocfg-owner oc))
                (equal (fn-ocfg-config oc2) (fn-ocfg-config oc))
                (equal (fn-own-view (fn-ocfg-owner oc2)) (fn-own-view (fn-ocfg-owner oc)))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc2)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                               (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2))))))
           (fn-ocl-view-configp oc2))
  :hints (("Goal" :use ((:instance fn-own-take-of-prefix
                                   (n (fn-own-view-version (fn-own-view (fn-ocfg-owner oc))))
                                   (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                                   (ys (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2)))))))
           :in-theory (e/d (fn-ocl-view-configp fn-ocl-view-historyp)
                           (fn-cpr-replay fn-cst-replay-node fn-own-take fn-own-take-of-prefix
                            fn-node-statep fn-ctl-visible-state fn-own-view-shapep)))))
(defthm fn-lgoc-config-historyp-of-longer-history
  (implies (and (fn-ocl-config-historyp oc)
                (equal (fn-ocfg-config oc2) (fn-ocfg-config oc))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc2)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (equal (fn-replay-result-kind
                        (fn-cpr-replay (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                                       (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2))))))
                       :ok))
           (fn-ocl-config-historyp oc2))
  :hints (("Goal" :use ((:instance fn-cstp-fold-config-independent-of-events
                                   (configs (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                                   (events (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                                   (events2 (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2)))))))
           :in-theory (e/d (fn-ocl-config-historyp fn-cstp-fold) (fn-cpr-replay)))))

(defthm fn-lgoc-cst-relation-replay-ok
  (implies (fn-cst-relation st)
           (equal (fn-replay-result-kind
                   (fn-cpr-replay (fn-sn-config-history st) (fn-sf-records (fn-sn-files st))))
                  :ok))
  :hints (("Goal" :in-theory '(fn-cst-relation fn-cst-final-configurationp))))

; The owner over a Store related to the same configuration history and a
; history extending its own: every conjunct of fn-ocl-relation but the Store's
; is read off the owner, the history and the view, and the refresh that
; follows an idle Store rebuilds the view from the history.
(defthm fn-lgoc-ocl-relation-of-owner-with-store
  (implies (and (fn-ocl-relation oc)
                (fn-cst-relation st)
                (equal (fn-sn-config-history st)
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                               (fn-sf-records (fn-sn-files st))))
           (fn-ocl-relation
            (fn-ocfg-with-owner oc (fn-ocl-owner-with-store (fn-ocfg-owner oc) st))))
  :hints (("Goal"
           :cases ((fn-snt-idle-phasep (fn-sf-phase (fn-sn-files st))))
           :use ((:instance fn-lgoc-cst-relation-replay-ok)
                 (:instance fn-lgoc-config-historyp-of-longer-history
                            (oc2 (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                                         (fn-ocfg-owner oc) st))))
                 (:instance fn-lgoc-conns-historyp-of-longer-history
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (oc2 (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                                         (fn-ocfg-owner oc) st))))
                 (:instance fn-lgoc-ledger-durablep-of-longer-history
                            (ledger (fn-own-ledger (fn-ocfg-owner oc)))
                            (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                            (ys (fn-sf-records (fn-sn-files st))))
                 (:instance fn-ocl-view-historyp-is-visible (o (fn-ocfg-owner oc)))
                 (:instance fn-lgoc-view-historyp-of-longer-history
                            (o (fn-ocfg-owner oc))
                            (o2 (fn-ocl-owner-with-store (fn-ocfg-owner oc) st)))
                 (:instance fn-lgoc-view-configp-of-longer-history
                            (oc2 (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                                         (fn-ocfg-owner oc) st))))
                 (:instance fn-cstp-relation-is-statep)
                 (:instance fn-cstp-sn-statep-files)
                 (:instance fn-sf-state-records-are-true-list (s (fn-sn-files st)))
                 (:instance fn-ocl-refreshed-idle-view-history
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
                 (:instance fn-lgoc-refreshed-idle-view-config
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
                            (cfg (fn-ocfg-config oc)) (pins (fn-ocfg-pins oc))
                            (staged (fn-ocfg-staged oc))))
           :in-theory (e/d (fn-ocl-relation fn-ocfg-with-owner fn-ocl-owner-with-store
                            fn-own-refresh-keeps-fields fn-lgoc-refresh-not-idle)
                           (fn-own-refresh fn-cst-relation fn-snt-idle-phasep
                            fn-ocl-conns-historyp fn-ocl-config-historyp
                            fn-ocl-view-configp fn-ocl-view-historyp
                            fn-ocl-view-visiblep fn-ocl-view-historyp-is-visible
                            fn-ocl-unique-conn-idsp fn-ocfg-pins-okp
                            fn-ocfg-conns-pinnedp fn-ocfg-pins-pin-conns-only
                            fn-own-ids-below-next-p fn-own-facts-okp
                            fn-clock-observationp fn-cfgp fn-cpr-replay
                            fn-own-ledger-durablep fn-sf-prefixp fn-sn-statep fn-sf-statep
                            fn-lgoc-config-historyp-of-longer-history
                            fn-lgoc-conns-historyp-of-longer-history
                            fn-lgoc-ledger-durablep-of-longer-history
                            fn-lgoc-view-historyp-of-longer-history
                            fn-lgoc-view-configp-of-longer-history
                            fn-lgoc-cst-relation-replay-ok
                            fn-nntp-response-text-true-listp fn-oct-bufp-true-listp
                            fn-nntp-response-textp fn-cbor-octet-listp fn-scc-octet-listp
                            (:definition true-listp))))))
; -----------------------------------------------------------------------------
; The carried owner invariant: fn-ocl-relation and the Store's carried
; companion (books/config-store-steps.lisp fn-cstp-carriedp).
(defun fn-lgoc-invariantp (oc)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-ocl-relation oc)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner oc)))))

(defthm fn-lgoc-store-of-owner-with-store
  (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-with-owner oc (fn-ocl-owner-with-store o st))))
         st)
  :hints (("Goal" :in-theory '(fn-ocfg-with-owner fn-ocl-owner-with-store
                               fn-own-refresh-keeps-fields fn-ocfg-owner-of-fn-ocfg-make
                               fn-own-store-of-fn-own-make))))

(defthm fn-lgoc-rcon-io-is-owner-with-store
  (equal (fn-rcon-ocfg-io oc operation result)
         (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                 (fn-ocfg-owner oc)
                                 (fn-sn-io (fn-own-store (fn-ocfg-owner oc))
                                           operation result))))
  :hints (("Goal" :in-theory '(fn-rcon-ocfg-io fn-rcon-own-store-io fn-ocl-owner-with-store
                               fn-rcon-sn-io-is-sn-io))))

(defun fn-lgoc-io-safep (st operation result)
  ; The file steps this book carries the invariant across: the reservation's,
  ; the recovery barriers', and the record steps -- the directory's publishing
  ; observation of an article candidate.
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-cstp-reserve-opp operation)
      (member-equal operation '(:record-file :record-link))
      (and (equal operation :record-directory)
           (or (not (equal result :ok))
               (not (equal (fn-sf-phase (fn-sn-files st)) :record-attempted))
               (fn-held-p (fn-sf-record-candidate (fn-sn-files st)))))))

(defthm fn-lgoc-io-store-preserves
  (implies (and (fn-cst-relation st) (fn-cstp-carriedp st)
                (fn-lgoc-io-safep st operation result))
           (and (fn-cst-relation (fn-sn-io st operation result))
                (fn-cstp-carriedp (fn-sn-io st operation result))))
  :hints (("Goal"
           :cases ((and (equal operation :record-directory) (equal result :ok)
                        (equal (fn-sf-phase (fn-sn-files st)) :record-attempted)))
           :use ((:instance fn-cstp-reserve-io-preserves-relation (s st))
                 (:instance fn-cstp-reserve-io-preserves-carriedp (s st))
                 (:instance fn-cstp-record-io-preserves-relation (s st))
                 (:instance fn-cstp-record-io-preserves-carriedp (s st))
                 (:instance fn-cstp-held-record-dir-preserves-relation (s st))
                 (:instance fn-cstp-record-dir-preserves-carriedp (s st)))
           :in-theory '(fn-lgoc-io-safep fn-cstp-relation-is-statep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)))))

(defthm fn-lgoc-ocl-relation-cst
  (implies (fn-ocl-relation oc)
           (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory '(fn-ocl-relation))))

; KEYSTONE (owner).  Every file observation fn-owner-io feeds the owner
; (host/owner-host.lisp: fn-rcon-ocfg-io) that the safe set names keeps the
; carried invariant.
(defthm fn-lgoc-rcon-io-preserves-invariant
  (implies (and (fn-lgoc-invariantp oc)
                (fn-lgoc-io-safep (fn-own-store (fn-ocfg-owner oc)) operation result))
           (fn-lgoc-invariantp (fn-rcon-ocfg-io oc operation result)))
  :hints (("Goal"
           :use ((:instance fn-lgoc-io-store-preserves
                            (st (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-lgoc-ocl-relation-of-owner-with-store
                            (st (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result)))
                 (:instance fn-cstp-io-fields (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-snt-io-records-prefix (s (fn-own-store (fn-ocfg-owner oc))))
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-lgoc-invariantp fn-lgoc-rcon-io-is-owner-with-store
                        fn-lgoc-store-of-owner-with-store fn-cstp-relation-is-statep))))
(defthm fn-lgoc-log-reserve-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-olr-ocfg-reserve oc)))
  :hints (("Goal" :in-theory '(fn-olr-ocfg-reserve fn-lgoc-rcon-io-preserves-invariant
                               fn-lgoc-io-safep fn-cstp-reserve-opp member-equal
                               (:executable-counterpart member-equal)
                               (:executable-counterpart fn-cstp-reserve-opp)))))

(defun fn-lgoc-article-stagedp (st)
  ; A record phase's candidate is an article (the article commit's order).
  (declare (xargs :guard t :verify-guards nil))
  (or (not (fn-sf-record-phasep (fn-sf-phase (fn-sn-files st))))
      (fn-held-p (fn-sf-record-candidate (fn-sn-files st)))))

(defthm fn-lgoc-record-io-keeps-article-stagedp
  (implies (and (fn-sn-statep st)
                (fn-lgoc-article-stagedp st)
                (member-equal operation '(:record-file :record-link)))
           (fn-lgoc-article-stagedp (fn-sn-io st operation result)))
  :hints (("Goal" :use ((:instance fn-cstp-record-file-step-cases (files (fn-sn-files st)))
                        (:instance fn-cstp-io-fields (s st))
                        (:instance fn-cstp-sn-statep-files))
           :in-theory '(fn-lgoc-article-stagedp member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)))))

(defthm fn-lgoc-store-of-rcon-io
  (equal (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc operation result)))
         (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result))
  :hints (("Goal" :in-theory '(fn-lgoc-rcon-io-is-owner-with-store
                               fn-lgoc-store-of-owner-with-store))))

(defthm fn-lgoc-invariant-statep
  (implies (fn-lgoc-invariantp oc)
           (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :use ((:instance fn-cstp-relation-is-statep
                                   (st (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-lgoc-invariantp fn-lgoc-ocl-relation-cst))))

; KEYSTONE (owner).  The log route's ORDER step (host/owner-host.lisp
; fn-owner-io :log-order) keeps the carried invariant when what is staged is
; an article (the article commit: fn-owner-prepare-buffer stages a held row).
(defthm fn-lgoc-log-order-preserves-invariant
  (implies (and (fn-lgoc-invariantp oc)
                (fn-lgoc-article-stagedp (fn-own-store (fn-ocfg-owner oc))))
           (fn-lgoc-invariantp (fn-olr-ocfg-order oc)))
  :hints (("Goal"
           :use ((:instance fn-lgoc-rcon-io-preserves-invariant
                            (operation :record-file) (result :ok))
                 (:instance fn-lgoc-rcon-io-preserves-invariant
                            (oc (fn-rcon-ocfg-io oc :record-file :ok))
                            (operation :record-link) (result :ok))
                 (:instance fn-lgoc-rcon-io-preserves-invariant
                            (oc (fn-rcon-ocfg-io (fn-rcon-ocfg-io oc :record-file :ok)
                                                 :record-link :ok))
                            (operation :record-directory) (result :ok))
                 (:instance fn-lgoc-record-io-keeps-article-stagedp
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (operation :record-file) (result :ok))
                 (:instance fn-lgoc-record-io-keeps-article-stagedp
                            (st (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc :record-file :ok))))
                            (operation :record-link) (result :ok))
                 (:instance fn-lgoc-invariant-statep)
                 (:instance fn-lgoc-invariant-statep (oc (fn-rcon-ocfg-io oc :record-file :ok))))
           :in-theory '(fn-olr-ocfg-order fn-lgoc-io-safep fn-lgoc-article-stagedp
                        fn-lgoc-store-of-rcon-io fn-sf-record-phasep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-cstp-reserve-opp)))))
(defthm fn-lgoc-opc-prepare-is-owner-with-store
  (equal (fn-opc-prepare oc record)
         (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                 (fn-ocfg-owner oc)
                                 (fn-spc-prepare (fn-own-store (fn-ocfg-owner oc)) record))))
  :hints (("Goal" :in-theory '(fn-opc-prepare fn-opc-owner-prepare fn-ocl-owner-with-store))))

(defthm fn-lgoc-spc-prepare-of-non-article
  (implies (not (fn-held-p record))
           (equal (fn-spc-prepare s record) s))
  :hints (("Goal" :in-theory '(fn-spc-prepare))))

(defthm fn-lgoc-spc-prepare-store-preserves
  (implies (and (fn-cst-relation st) (fn-cstp-carriedp st)
                (equal (fn-cnode-config (fn-cstp-fold (fn-sn-config-history st)
                                                      (fn-sf-records (fn-sn-files st))))
                       cfg)
                (implies (fn-held-p record)
                         (fn-cnode-selection-servedp cfg (fn-record-groups record))))
           (and (fn-cst-relation (fn-spc-prepare st record))
                (fn-cstp-carriedp (fn-spc-prepare st record))
                (equal (fn-sn-config-history (fn-spc-prepare st record))
                       (fn-sn-config-history st))
                (fn-sf-prefixp (fn-sf-records (fn-sn-files st))
                               (fn-sf-records (fn-sn-files (fn-spc-prepare st record))))))
  :hints (("Goal"
           :cases ((fn-held-p record))
           :use ((:instance fn-cstp-spc-prepare-preserves-relation (s st))
                 (:instance fn-cstp-spc-prepare-preserves-carriedp (s st))
                 (:instance fn-cstp-spc-prepare-cases (s st))
                 (:instance fn-cstp-relation-is-statep)
                 (:instance fn-cstp-sn-statep-files)
                 (:instance fn-sf-state-records-are-true-list (s (fn-sn-files st)))
                 (:instance fn-sf-prefixp-reflexive (xs (fn-sf-records (fn-sn-files st)))))
           :in-theory '(fn-cpr-event-servedp fn-lgoc-spc-prepare-of-non-article))))

(defthm fn-lgoc-ocl-relation-config-fold
  (implies (fn-ocl-relation oc)
           (equal (fn-cnode-config
                   (fn-cstp-fold (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                                 (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                  (fn-ocfg-config oc)))
  :hints (("Goal" :in-theory '(fn-ocl-relation fn-ocl-config-historyp fn-cstp-fold))))

; KEYSTONE (owner).  The configured prepare below the budget gate
; (books/owner-store-budget.lisp fn-sbud-prepare, which
; fn-pidx-sbud-prepare-is-pcar-sbud-prepare and
; fn-pcar-sbud-prepare-is-sbud-prepare equate with the host's
; fn-pidx-sbud-prepare) keeps the carried invariant when an article's groups
; are served by the live configuration.  The served test is ACL2's, not the
; host's: the prepare the host calls is books/owner-prepare-served.lisp
; fn-psrv-prepare, which tests it (fn-psrv-event-servedp) and calls this
; prepare only when it holds; its KEYSTONE
; fn-psrv-prepare-preserves-invariant discharges the served hypothesis below
; for every record.
(defthm fn-lgoc-sbud-prepare-preserves-invariant
  (implies (and (fn-lgoc-invariantp oc)
                (implies (fn-held-p record)
                         (fn-cnode-selection-servedp (fn-ocfg-config oc)
                                                     (fn-record-groups record))))
           (fn-lgoc-invariantp (fn-sbud-prepare oc record budget)))
  :hints (("Goal"
           :use ((:instance fn-lgoc-spc-prepare-store-preserves
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (cfg (fn-ocfg-config oc)))
                 (:instance fn-lgoc-ocl-relation-of-owner-with-store
                            (st (fn-spc-prepare (fn-own-store (fn-ocfg-owner oc)) record))))
           :in-theory '(fn-lgoc-invariantp fn-sbud-prepare fn-lgoc-opc-prepare-is-owner-with-store
                        fn-lgoc-store-of-owner-with-store fn-lgoc-ocl-relation-cst
                        fn-lgoc-ocl-relation-config-fold))))
; fn-pidx-sbud-prepare under the two carried index premises its bridge to
; fn-sbud-prepare takes.  The host does not call it directly: host/owner-host.lisp
; fn-owner-prepare-buffer installs fn-psrv-prepare (books/owner-prepare-served.lisp),
; which reaches this prepare through fn-prc-sbud-prepare only when ACL2's own
; served test holds.
(defthm fn-lgoc-pidx-sbud-prepare-preserves-invariant
  (implies (and (fn-lgoc-invariantp oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (implies (fn-held-p record)
                         (fn-cnode-selection-servedp (fn-ocfg-config oc)
                                                     (fn-record-groups record))))
           (fn-lgoc-invariantp (fn-pidx-sbud-prepare oc record budget)))
  :hints (("Goal"
           :use (fn-lgoc-sbud-prepare-preserves-invariant
                 fn-pidx-sbud-prepare-is-pcar-sbud-prepare
                 fn-pcar-sbud-prepare-is-sbud-prepare
                 (:instance fn-ocl-view-historyp-is-visible (o (fn-ocfg-owner oc))))
           :in-theory '(fn-lgoc-invariantp fn-ocl-relation))))

(defthm fn-lgoc-own-complete-store
  (equal (fn-own-store (fn-own-complete o))
         (if (fn-sn-completion-enabledp (fn-own-store o))
             (fn-sn-finish (fn-own-store o))
           (fn-own-store o)))
  :hints (("Goal" :in-theory (e/d (fn-own-complete fn-own-refresh-keeps-fields)
                                  (fn-own-refresh fn-sn-finish fn-sn-completion-enabledp)))))

; KEYSTONE (owner).  The commit's finish the host installs
; (host/owner-host.lisp fn-owner-finish-submission) keeps the carried
; invariant: fn-ocl-relation by fn-ocmt-post-commit-preserves-ocl-relation,
; the companion by fn-cstp-finish-preserves-carriedp.
(defthm fn-lgoc-finish-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp
            (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
  :hints (("Goal"
           :cases ((fn-sn-completion-enabledp (fn-own-store (fn-ocfg-owner oc))))
           :use (fn-ocmt-post-commit-preserves-ocl-relation
                 (:instance fn-cstp-finish-preserves-carriedp
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-ocmt-enabled-completion-is-completing
                            (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-lgoc-invariantp fn-ccar-own-finish-is-own-finish fn-own-finish
                        cdr-cons fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make
                        fn-lgoc-own-complete-store))))
(defthm fn-lgoc-store-of-started-owner
  (equal (fn-own-store (fn-own-configure (fn-own-start st max-conns) post)) st)
  :hints (("Goal" :in-theory (e/d (fn-own-configure fn-own-start fn-own-refresh-keeps-fields)
                                  (fn-own-refresh)))))

; KEYSTONE (owner).  The owner the host installs at recovery, on either path
; (host/owner-host.lisp fn-owner-recover-from-store-open and
; fn-owner-recover-extended: fn-ock-recover-extended of the capture extended
; over the rest of the history), carries the invariant.
(defthm fn-lgoc-recover-installs-invariant
  (let ((oc (fn-ock-recover-extended
             (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
             configs frontier max-conns)))
    (implies (not (equal oc :fault))
             (fn-lgoc-invariantp oc)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-ock-recover-installs-ocl-relation
                 fn-owner-recover-from-checkpoint-equals-full-recover
                 (:instance fn-cstp-open-establishes-carriedp
                            (events (append prefix suffix))))
           :in-theory '(fn-lgoc-invariantp fn-ock-recover-full fn-ock-install
                        fn-ocfg-owner-of-fn-ocfg-make fn-lgoc-store-of-started-owner))))
(defthm fn-lgoc-ocl-complete-store
  (implies (fn-ocfg-staged oc)
           (equal (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc)))
                  (if (not (equal (fn-sn-config-history
                                   (fn-cpo-configure-durable (fn-own-store (fn-ocfg-owner oc))
                                                             (fn-ocfg-staged oc)))
                                  (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))))
                      (fn-cpo-configure-durable (fn-own-store (fn-ocfg-owner oc))
                                                (fn-ocfg-staged oc))
                    (fn-own-store (fn-ocfg-owner oc)))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-complete fn-ocl-owner-with-store
                                   fn-own-refresh-keeps-fields)
                                  (fn-cpo-configure-durable fn-own-refresh
                                   fn-ocl-store-config)))))

(defthm fn-lgoc-ocl-publish-store
  (equal (fn-own-store (fn-ocfg-owner (mv-nth 1 (fn-ocl-publish oc generation max-octets))))
         (if (and (fn-ocfg-staged oc)
                  (equal (mv-nth 0 (fn-ocl-publish oc generation max-octets)) :durable))
             (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc)))
           (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-publish fn-ocfg-with-owner fn-own-configure)
                                  (fn-ocl-complete fn-oag-post-config)))))

; KEYSTONE (owner).  The live configuration completion the host calls
; (host/owner-host.lisp fn-owner-reconfigure-complete: fn-oclc-publish) keeps
; the carried invariant, every verdict.
(defthm fn-lgoc-publish-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (mv-nth 1 (fn-oclc-publish oc generation max-octets))))
  :hints (("Goal"
           :use (fn-oclc-publish-carries-ocl-relation fn-oclc-publish-is-publish
                 (:instance fn-cstp-configure-durable-preserves-carriedp
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (record (fn-ocfg-staged oc))))
           :in-theory '(fn-lgoc-invariantp fn-lgoc-ocl-publish-store fn-lgoc-ocl-complete-store))))
(defthm fn-lgoc-refuse-reservation-is-owner-with-store
  (equal (fn-ocfg-step oc (list :store (list :refuse-reservation txid)) fn-arena)
         (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                 (fn-ocfg-owner oc)
                                 (fn-sn-refuse-reservation (fn-own-store (fn-ocfg-owner oc))
                                                           txid))))
  :hints (("Goal" :in-theory '(fn-ocfg-step fn-ocfg-pass fn-own-step fn-own-store-step
                               fn-snrt-step fn-ocl-owner-with-store car-cons cdr-cons
                               (:executable-counterpart equal)))))

; KEYSTONE (owner).  The refused reservation the host feeds when a prepare is
; refused (host/owner-host.lisp fn-owner-refuse-reservation) keeps the
; carried invariant.
(defthm fn-lgoc-refuse-reservation-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :store (list :refuse-reservation txid)) fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-cstp-refuse-reservation-preserves
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-cstp-refuse-reservation-cases
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-lgoc-ocl-relation-of-owner-with-store
                            (st (fn-sn-refuse-reservation (fn-own-store (fn-ocfg-owner oc)) txid)))
                 (:instance fn-sf-prefixp-reflexive
                            (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                 (:instance fn-sf-state-records-are-true-list
                            (s (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-cstp-sn-statep-files (st (fn-own-store (fn-ocfg-owner oc))))
                 fn-lgoc-invariant-statep)
           :in-theory '(fn-lgoc-invariantp fn-lgoc-refuse-reservation-is-owner-with-store
                        fn-lgoc-store-of-owner-with-store fn-lgoc-ocl-relation-cst))))

; Accessor equalities used above as rewrite rules; withdrawn at export.
(in-theory (disable fn-lgoc-ocl-relation-config-fold))
