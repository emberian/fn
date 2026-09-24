;; fn: the configured owner's relation survives an ordinary POST commit.
;
; fn-ocl-relation (books/config-owner-live.lisp) is the configured owner's
; invariant; the open, close, observe, read and advance transitions keep it
; and the configuration completion keeps it
; (fn-ocl-complete-preserves-full-historical-relation), but nothing said the
; ordinary commit the host runs for every POST keeps it: host/owner-host.lisp
; fn-owner-finish-submission installs (cdr (fn-ccar-own-finish o cfg)).  Nor did anything say its store conjunct,
; fn-cst-relation (books/config-store-traces.lisp), survives fn-sn-finish:
; that book proves only that open establishes it.
;
; The store step is the one piece of content.  In the :completing phase
; fn-cst-relation carries fn-cst-completion-linkp: the node completed by the
; completion record (article arm) or with the record applied (every other
; arm) IS the replay of the history, and fn-sn-finish installs exactly that
; node, keeps the records, the frontier, the groups, the capacity and the
; configuration journal, and returns to :ready.  The owner step then only
; refreshes the view to the whole history, whose replay the store relation
; now names, and appends the committed pair to the ledger.

(in-package "ACL2")
(include-book "owner-commit-carried")

(local (in-theory (disable fn-node-statep fn-sn-statep fn-sf-statep)))

; -----------------------------------------------------------------------------
; The store step.

(defthm fn-ocmt-sn-finish-keeps-config-history
  (equal (fn-sn-config-history (fn-sn-finish s))
         (fn-sn-config-history s))
  :hints (("Goal" :in-theory (e/d (fn-sn-finish)
                                  (fn-sn-completion-enabledp
                                   fn-sn-completion-record
                                   fn-record-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-cpe-eventp fn-th-topic-eventp
                                   fn-replay-apply-record
                                   fn-replay-apply-retention-event
                                   fn-node-complete fn-sf-core-completion
                                   fn-sf-emit-success
                                   fn-cpe-projection-step fn-th-prefix-step)))))

(defthm fn-ocmt-enabled-completion-is-completing
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sf-phase (fn-sn-files s)) :completing))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory '(fn-sn-completion-enabledp
                               fn-sn-completion-core-enabledp))))
(defthm fn-ocmt-sn-finish-keeps-final-configuration
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-cst-final-configurationp (fn-sn-finish s))
                  (fn-cst-final-configurationp s)))
  :hints (("Goal" :use (fn-snt-finish-image
                        fn-ocmt-sn-finish-keeps-config-history)
           :in-theory (e/d (fn-cst-final-configurationp)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-cpr-replay fn-cnode-statep
                            fn-snt-finish-image
                            fn-ocmt-sn-finish-keeps-config-history)))))
; KEYSTONE (store).  fn-cst-relation survives fn-sn-finish, on every arm:
; the completing arm's link is the equation between the node fn-sn-finish
; installs and the replay of the unchanged history.
(defthm fn-ocmt-sn-finish-preserves-cst-relation
  (implies (fn-cst-relation s)
           (fn-cst-relation (fn-sn-finish s)))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-preserves-state fn-snt-finish-image
                 fn-sn-finish-is-actual-durable-completion
                 fn-snt-finish-is-the-applied-event
                 fn-sn-finish-disabled-is-no-op
                 fn-ocmt-sn-finish-keeps-config-history
                 fn-ocmt-sn-finish-keeps-final-configuration
                 (:instance fn-snt-an-article-record-is-no-other-store-event
                   (record (fn-sn-completion-record s))))
           :in-theory (e/d (fn-cst-relation fn-cst-completion-linkp)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-sn-completion-record
                            fn-cst-final-configurationp fn-sn-observed-historyp
                            fn-cst-recoverablep fn-cst-replay-node
                            fn-cst-pending-linkp fn-cst-deferred-linkp
                            fn-node-complete fn-replay-apply-record
                            fn-record-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-cpe-eventp fn-th-topic-eventp
                            fn-snt-idle-phasep fn-sf-record-phasep
                            fn-node-initial-state fn-record-txid
                            fn-record-generation)))))

; -----------------------------------------------------------------------------
; What the owner relation reads off the store, the pins and the view.

(defthm fn-ocmt-conns-historyp-of-same-history
  (implies (and (equal (fn-ocfg-pins oc2) (fn-ocfg-pins oc))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc2)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2))))
                       (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
           (equal (fn-ocl-conns-historyp oc2 conns)
                  (fn-ocl-conns-historyp oc conns)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ocl-conns-historyp oc conns)
           :in-theory (e/d (fn-ocl-conns-historyp fn-ocl-conn-historyp
                            fn-ocfg-conn-config)
                           (fn-cpr-replay fn-cst-replay-node fn-own-take
                            fn-own-conn-boundedp)))))
(defthm fn-ocmt-config-historyp-of-same-history
  (implies (and (equal (fn-ocfg-config oc2) (fn-ocfg-config oc))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc2)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc2))))
                       (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
           (equal (fn-ocl-config-historyp oc2)
                  (fn-ocl-config-historyp oc)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocl-config-historyp)
                                  (fn-cpr-replay)))))
(defthm fn-ocmt-refreshed-ready-view-history
  (implies (and (fn-cst-relation st)
                (equal (fn-sf-phase (fn-sn-files st)) :ready)
                (true-listp (fn-sf-records (fn-sn-files st))))
           (fn-ocl-view-historyp
            (fn-own-refresh
             (fn-own-make st view conns next-id max-conns pending ledger
                          clock facts config queue inflight feeds))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-take-of-len
                            (xs (fn-sf-records (fn-sn-files st)))))
           :in-theory (e/d (fn-ocl-view-historyp
                            fn-own-refresh fn-own-store-idlep fn-cst-relation)
                           (fn-cst-replay-node fn-cpr-replay fn-own-take
                            fn-own-view-make-group-indexed)))))
(defthm fn-ocmt-refreshed-ready-view-config
  (implies (and (fn-ocl-config-historyp
                 (fn-ocfg-make
                  (fn-own-refresh
                   (fn-own-make st view conns next-id max-conns pending ledger
                                clock facts config queue inflight feeds))
                  cfg pins staged))
                (equal (fn-sf-phase (fn-sn-files st)) :ready)
                (true-listp (fn-sf-records (fn-sn-files st))))
           (fn-ocl-view-configp
            (fn-ocfg-make
             (fn-own-refresh
              (fn-own-make st view conns next-id max-conns pending ledger
                           clock facts config queue inflight feeds))
             cfg pins staged)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-take-of-len
                            (xs (fn-sf-records (fn-sn-files st)))))
           :in-theory (e/d (fn-ocl-view-configp fn-ocl-config-historyp
                            fn-own-refresh fn-own-store-idlep)
                           (fn-cpr-replay fn-own-take
                            fn-own-view-make-group-indexed)))))

(defthm fn-ocmt-completing-pair-is-recorded
  (implies (and (fn-sf-statep f)
                (equal (fn-sf-phase f) :completing))
           (fn-sf-record-has-pairp (fn-sf-completion f) (fn-sf-records f)))
  :hints (("Goal" :in-theory (e/d (fn-sf-statep fn-sf-phase-shapep)
                                  (fn-sf-record-has-pairp fn-sf-record-listp
                                   fn-sf-success-listp fn-sf-candidatep)))))
(defthm fn-ocmt-view-configp-of-same-owner
  (equal (fn-ocl-view-configp
          (fn-ocfg-make (fn-ocfg-owner oc) (fn-ocfg-config oc) pins staged))
         (fn-ocl-view-configp oc))
  :hints (("Goal" :in-theory (e/d (fn-ocl-view-configp) (fn-cpr-replay fn-own-take)))))
(defthm fn-ocmt-config-historyp-of-same-owner
  (equal (fn-ocl-config-historyp
          (fn-ocfg-make (fn-ocfg-owner oc) (fn-ocfg-config oc) pins staged))
         (fn-ocl-config-historyp oc))
  :hints (("Goal" :in-theory (e/d (fn-ocl-config-historyp) (fn-cpr-replay)))))
; -----------------------------------------------------------------------------
; The owner step.

; The owner's completion keeps the configured owner's relation.  A staged
; configuration record is carried through unchanged: the relation's staged
; conjunct reads only the live configuration, which this step keeps.
(defthm fn-ocmt-own-complete-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation
            (fn-ocfg-make (fn-own-complete (fn-ocfg-owner oc))
                          (fn-ocfg-config oc) (fn-ocfg-pins oc)
                          (fn-ocfg-staged oc))))
  :hints (("Goal"
           :cases ((fn-sn-completion-enabledp (fn-own-store (fn-ocfg-owner oc))))
           :use ((:instance fn-ocmt-sn-finish-preserves-cst-relation
                  (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-snt-finish-image
                  (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-ocmt-sn-finish-keeps-config-history
                  (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-sf-state-records-are-true-list
                  (s (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-ocmt-completing-pair-is-recorded
                  (f (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-ocmt-conns-historyp-of-same-history
                  (oc2 (fn-ocfg-make (fn-own-complete (fn-ocfg-owner oc))
                                     (fn-ocfg-config oc) (fn-ocfg-pins oc)
                                     (fn-ocfg-staged oc)))
                  (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-ocmt-config-historyp-of-same-history
                  (oc2 (fn-ocfg-make (fn-own-complete (fn-ocfg-owner oc))
                                     (fn-ocfg-config oc) (fn-ocfg-pins oc)
                                     (fn-ocfg-staged oc))))
                 (:instance fn-ocmt-refreshed-ready-view-history
                  (st (fn-sn-finish (fn-own-store (fn-ocfg-owner oc))))
                  (view (fn-own-view (fn-ocfg-owner oc)))
                  (conns (fn-own-conns (fn-ocfg-owner oc)))
                  (next-id (fn-own-next-id (fn-ocfg-owner oc)))
                  (max-conns (fn-own-max-conns (fn-ocfg-owner oc)))
                  (pending nil)
                  (ledger (fn-ag-append (fn-own-ledger (fn-ocfg-owner oc))
                                        (list (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))))
                  (clock (fn-own-clock (fn-ocfg-owner oc)))
                  (facts (fn-own-facts (fn-ocfg-owner oc)))
                  (config (fn-own-config (fn-ocfg-owner oc)))
                  (queue (fn-own-queue (fn-ocfg-owner oc)))
                  (inflight (fn-own-inflight (fn-ocfg-owner oc)))
                  (feeds (fn-own-feeds (fn-ocfg-owner oc))))
                 (:instance fn-ocmt-refreshed-ready-view-config
                  (st (fn-sn-finish (fn-own-store (fn-ocfg-owner oc))))
                  (view (fn-own-view (fn-ocfg-owner oc)))
                  (conns (fn-own-conns (fn-ocfg-owner oc)))
                  (next-id (fn-own-next-id (fn-ocfg-owner oc)))
                  (max-conns (fn-own-max-conns (fn-ocfg-owner oc)))
                  (pending nil)
                  (ledger (fn-ag-append (fn-own-ledger (fn-ocfg-owner oc))
                                        (list (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))))
                  (clock (fn-own-clock (fn-ocfg-owner oc)))
                  (facts (fn-own-facts (fn-ocfg-owner oc)))
                  (config (fn-own-config (fn-ocfg-owner oc)))
                  (queue (fn-own-queue (fn-ocfg-owner oc)))
                  (inflight (fn-own-inflight (fn-ocfg-owner oc)))
                  (feeds (fn-own-feeds (fn-ocfg-owner oc)))
                  (cfg (fn-ocfg-config oc)) (pins (fn-ocfg-pins oc))
                  (staged (fn-ocfg-staged oc))))
           :in-theory (e/d (fn-ocl-relation fn-own-complete
                            fn-own-refresh-keeps-fields
                            fn-own-ledger-durablep-append)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-own-refresh fn-cst-relation
                            fn-ocl-conns-historyp fn-ocl-config-historyp
                            fn-ocl-view-configp fn-ocl-view-historyp
                            fn-ocl-unique-conn-idsp fn-ocfg-pins-okp
                            fn-ocfg-conns-pinnedp fn-ocfg-pins-pin-conns-only
                            fn-own-ids-below-next-p fn-own-facts-okp
                            fn-clock-observationp fn-cfgp
                            fn-sf-record-has-pairp fn-own-ledger-durablep
                            fn-snt-finish-image
                            fn-ocmt-sn-finish-keeps-config-history)))))

; KEYSTONE for host/owner-host.lisp fn-owner-finish-submission: the
; configured owner the commit installs satisfies fn-ocl-relation again, for
; every configuration passed.  No other hypothesis (the host additionally
; refuses the commit while a configuration record is staged).
(defthm fn-ocmt-post-commit-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation
            (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg)))))
  :hints (("Goal" :use fn-ocmt-own-complete-preserves-ocl-relation
           :in-theory '(fn-ocfg-with-owner fn-ccar-own-finish-is-own-finish
                        fn-own-finish cdr-cons))))
