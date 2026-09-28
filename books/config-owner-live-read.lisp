; fn: fn-ocl-relation preserved by the served read (fn-own-read under the
; configured owner: missing, removed, kept and repinned) and by observe.
; Part 3 of 3 of books/config-owner-live.lisp.

(in-package "ACL2")
(include-book "config-owner-live-open")
; Withdrawn on export by part 1; this part reasons about them, as it did
; when the withdrawal was the umbrella book's.
(local (in-theory (enable fn-ocl-vocabulary)))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; The local prelude of config-owner-live-complete, replayed (local events do not
; cross include-book).
; Configuration updates retain the file state through the exported selector
; theorem.  Expanding the updater first hides that match inside UPDATE-NTH.
(local (in-theory (disable fn-sn-with-configuration)))
; Shape rules of the NNTP and content-identity clusters that are tried on
; every true-listp and consp test here and backchain by opening their
; recognizers; nothing below needs them.
(local (in-theory (disable fn-nntp-response-text-true-listp fn-cp-idp-true-listp
                           fn-nntp-article-idp-is-consp fn-cp-id-length-bound)))
; Rules and vocabulary of the resolution, wire, control, feed and index
; clusters that are tried or opened here and never apply (accumulated
; persistence over the book, 2026-09-27): consp and car conclusions with
; free-variable hypotheses, and the group and message-id index builders.
(local (in-theory (disable fn-snrt-new-success-is-actual-matching-durable-completion
                           fn-wire-next-loop-event-needs-input
                           fn-wire-next-event-needs-input
                           fn-ctl-authorize-execute-is-nonempty
                           fn-cpr-config-firstp-has-config
                           fn-own-feed-never-offers-a-loop
                           fn-digest-octetsp-implies-octet-listp
                           fn-prov-structured-is-not-a-string
                           fn-ctl-refresh-visible-is-visible fn-gidx-refresh-is-build
                           fn-gidx-put fn-gidx-put-all fn-gidx-build-entries
                           fn-gnix-add fn-gnix-set fn-midx-branch-put
                           fn-ctl-visible-articles fn-ctl-withdrawal-effect
                           fn-sf-record-has-pairp)))

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
           :in-theory (e/d (fn-ocl-projectionp-of-a-visible-state
                            fn-ocl-projection-keeps-state-fields
                            fn-ocl-conn-historyp fn-cst-replay-node
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
         id (fn-own-conns (cdr (fn-own-read o id octets fn-arena)))))
   (equal
    (fn-own-conns (cdr (fn-own-read o id octets fn-arena)))
    (fn-own-replace-conn
     (fn-own-find-conn
      id (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
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
              id (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))))
   (equal (fn-own-conns (cdr (fn-own-read o id octets fn-arena)))
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
  (equal (fn-own-store (cdr (fn-own-read o id octets fn-arena)))
         (fn-own-store o))
  :hints (("Goal" :in-theory (e/d (fn-own-read fn-own-finish-read
                                    fn-own-set-conns fn-own-enqueue)
                                   (fn-served-step fn-own-conn-boundedp)))))

; fn-own-finish-read ends in fn-own-set-conns or fn-own-enqueue, both an
; fn-own-make that copies every control field; the two read theorems below
; cite these instead of opening the served step's result three ways.
(local
 (defthm fn-ocl-finish-read-owner-shape
   (fn-own-shapep (cdr (fn-own-finish-read o conn result)))
   :hints (("Goal" :in-theory (e/d (fn-own-finish-read fn-own-set-conns
                                    fn-own-enqueue)
                                   (fn-own-shapep fn-own-make
                                    fn-own-conn-boundedp fn-own-replace-conn
                                    fn-own-remove-conn))))))

(local
 (defthm fn-ocl-finish-read-keeps-owner-control
   (let ((next (cdr (fn-own-finish-read o conn result))))
     (and (equal (fn-own-view next) (fn-own-view o))
          (equal (fn-own-next-id next) (fn-own-next-id o))
          (equal (fn-own-max-conns next) (fn-own-max-conns o))
          (equal (fn-own-pending next) (fn-own-pending o))
          (equal (fn-own-ledger next) (fn-own-ledger o))
          (equal (fn-own-clock next) (fn-own-clock o))
          (equal (fn-own-facts next) (fn-own-facts o))
          (equal (fn-own-config next) (fn-own-config o))))
   :hints (("Goal" :in-theory (e/d (fn-own-finish-read fn-own-set-conns
                                    fn-own-enqueue)
                                   (fn-own-make
                                    fn-own-conn-boundedp fn-own-replace-conn
                                    fn-own-remove-conn))))))

(defthm fn-ocl-own-read-preserves-owner-shape
  (implies (fn-own-shapep o)
           (fn-own-shapep (cdr (fn-own-read o id octets fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-own-read fn-own-read-full)
                                  (fn-own-finish-read fn-own-shapep
                                   fn-served-step fn-own-conn-boundedp)))))

(defthm fn-ocl-own-read-keeps-owner-control
  (let ((next (cdr (fn-own-read o id octets fn-arena))))
    (and (equal (fn-own-view next) (fn-own-view o))
         (equal (fn-own-next-id next) (fn-own-next-id o))
         (equal (fn-own-max-conns next) (fn-own-max-conns o))
         (equal (fn-own-pending next) (fn-own-pending o))
         (equal (fn-own-ledger next) (fn-own-ledger o))
         (equal (fn-own-clock next) (fn-own-clock o))
         (equal (fn-own-facts next) (fn-own-facts o))
         (equal (fn-own-config next) (fn-own-config o))))
  :hints (("Goal" :in-theory (e/d (fn-own-read fn-own-read-full)
                                  (fn-own-finish-read
                                   fn-served-step fn-own-conn-boundedp)))))

(defthm fn-ocl-own-read-does-not-increase-connections
  (<= (len (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
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
            (fn-ocfg-pass oc (list :observe observation) fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-ocl-conns-historyp-under-same-store-and-pins
                            (next (fn-ocfg-pass oc
                                                (list :observe observation) fn-arena))
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
                     (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
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
   (equal (cdr (fn-ocfg-read oc id octets fn-arena)) oc))
  :hints (("Goal"
           :use (fn-ocl-missing-connection-pin-remove-is-unchanged
                 fn-ocl-config-shape-reconstructs
                 fn-ocl-related-config-shaped)
           :in-theory (e/d (fn-ocfg-read fn-ocfg-with-read-owner
                            fn-own-read)
                           (fn-ocl-relation fn-cst-relation fn-cpr-replay
                            fn-cst-replay-node)))))

; NNT-042: a read whose GROUP or LISTGROUP advanced the connection pins it to
; the current configuration (fn-ocfg-with-read-owner: fn-ocfg-pin-set).  The
; pin table's three invariants survive a pin-set.
(defthm fn-ocl-pin-set-keeps-conns-pinned
  (implies (fn-ocfg-conns-pinnedp conns pins)
           (fn-ocfg-conns-pinnedp conns (fn-ocfg-pin-set id cfg pins)))
  :hints (("Goal" :induct (fn-ocfg-conns-pinnedp conns pins)
           :in-theory (e/d (fn-ocfg-conns-pinnedp) (fn-ocfg-pin-set fn-ocfg-pin-find)))
          ("Subgoal *1/1" :cases ((equal (fn-own-conn-id (car conns)) id)))))

(defthm fn-ocl-pin-set-keeps-pins-pin-conns-only
  (implies (fn-ocfg-pins-pin-conns-only pins conns)
           (fn-ocfg-pins-pin-conns-only (fn-ocfg-pin-set id cfg pins) conns))
  :hints (("Goal" :induct (fn-ocfg-pin-set id cfg pins)
           :in-theory (enable fn-ocfg-pin-set fn-ocfg-pins-pin-conns-only))))

(defthm fn-ocl-pin-set-keeps-pins-okp
  (implies (and (fn-ocfg-pins-okp pins) (fn-cfgp cfg))
           (fn-ocfg-pins-okp (fn-ocfg-pin-set id cfg pins)))
  :hints (("Goal" :induct (fn-ocfg-pin-set id cfg pins)
           :in-theory (e/d (fn-ocfg-pin-set fn-ocfg-pins-okp) (fn-cfgp)))))

; The configured read in the owner's vocabulary: the owner read, the flag,
; and the pin table moved with it.
(defthm fn-ocl-ocfg-read-unfolds
  (and (equal (car (fn-ocfg-read oc id octets fn-arena))
              (car (fn-own-read (fn-ocfg-owner oc) id octets fn-arena)))
       (equal (cdr (fn-ocfg-read oc id octets fn-arena))
              (fn-ocfg-with-read-owner oc id
                                       (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))
                                       (fn-own-read-repinned (fn-ocfg-owner oc) id octets fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-read fn-own-read fn-own-read-repinned)
                                  (fn-own-read-full fn-ocfg-with-read-owner)))))

; The committed view's archive has the current configuration's domain: the
; view is replayed under the whole configuration history (fn-ocl-view-historyp)
; and that replay's node carries the current configuration
; (fn-ocl-view-configp); the mirror of fn-ocl-connection-archive-has-pinned-domain,
; in two steps because the view's archive is EQUAL to a visible state (the
; connection's is a projection): first the replayed node's domain, then the
; view archive's through the projection.
(local
 (defthm fn-ocl-view-node-has-current-domain
   (implies (fn-ocl-relation oc)
            (equal (fn-state-groups
                    (fn-node-acceptance
                     (fn-cst-replay-node
                      (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                      (fn-own-take (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))
                                   (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                      (fn-own-view-frontier (fn-own-view (fn-ocfg-owner oc))))))
                   (fn-cnode-domain-of (fn-ocfg-config oc))))
   :hints (("Goal"
            :use ((:instance fn-cpr-replay-ok-is-configured
                             (configs (fn-sn-config-history
                                       (fn-own-store (fn-ocfg-owner oc))))
                             (events (fn-own-take
                                      (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))
                                      (fn-sf-records
                                       (fn-sn-files
                                        (fn-own-store (fn-ocfg-owner oc)))))))
                  (:instance fn-ocl-replayed-view-has-successful-physical-prefix
                             (configs (fn-sn-config-history
                                       (fn-own-store (fn-ocfg-owner oc))))
                             (events (fn-own-take
                                      (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))
                                      (fn-sf-records
                                       (fn-sn-files
                                        (fn-own-store (fn-ocfg-owner oc))))))
                             (frontier (fn-own-view-frontier (fn-own-view (fn-ocfg-owner oc))))))
            :in-theory (e/d (fn-ocl-relation fn-ocl-view-historyp fn-ocl-view-configp
                             fn-cst-replay-node fn-cnode-statep fn-cnode-domain)
                            (fn-cpr-replay fn-own-take fn-ocl-conns-historyp
                             fn-ocl-conn-historyp fn-ocl-config-historyp
                             fn-cst-relation fn-ctl-visible-state))))))

(defthm fn-ocl-view-archive-has-current-domain
  (implies (fn-ocl-relation oc)
           (equal (fn-state-groups (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))
                  (fn-cnode-domain-of (fn-ocfg-config oc))))
  :hints (("Goal"
           :use ((:instance fn-ocl-view-node-has-current-domain)
                 (:instance fn-ocl-projectionp-of-a-visible-state
                            (a (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))
                            (p (fn-node-acceptance
                                (fn-cst-replay-node
                                 (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                                 (fn-own-take (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))
                                              (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                                 (fn-own-view-frontier (fn-own-view (fn-ocfg-owner oc))))))
                            (ws (fn-own-view-withdrawals (fn-own-view (fn-ocfg-owner oc))))
                            (verdicts (fn-own-view-verdicts (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-ocl-projection-keeps-state-fields
                            (a (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))
                            (p (fn-node-acceptance
                                (fn-cst-replay-node
                                 (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                                 (fn-own-take (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))
                                              (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                                 (fn-own-view-frontier (fn-own-view (fn-ocfg-owner oc))))))))
           :in-theory (e/d (fn-ocl-relation fn-ocl-view-historyp)
                           (fn-cst-replay-node fn-cpr-replay fn-own-take
                            fn-ocl-conns-historyp fn-ocl-conn-historyp
                            fn-ocl-config-historyp fn-ocl-view-configp fn-cst-relation
                            fn-ctl-visible-state fn-ctl-projectionp fn-node-statep
                            fn-ocl-view-node-has-current-domain
                            fn-ocl-projectionp-of-a-visible-state
                            fn-ocl-projection-keeps-state-fields)))))

; A connection the table pins has a pin (fn-ocfg-conns-pinnedp, read at the
; found connection).
(local
 (defthm fn-ocl-found-connection-has-a-pin
   (implies (and (fn-ocfg-conns-pinnedp conns pins)
                 (fn-own-find-conn id conns))
            (fn-ocfg-pin-find (fn-own-conn-id (fn-own-find-conn id conns)) pins))
   :hints (("Goal" :induct (fn-own-find-conn id conns)
            :in-theory (e/d (fn-own-find-conn fn-ocfg-conns-pinnedp)
                            (fn-ocfg-pin-find))))))

; The read wrapper's owner and its connection's configuration, by cases on
; the flag (books/owner-config.lisp fn-ocfg-with-read-owner).
(local
 (defthm fn-ocl-with-read-owner-fields
   (and (equal (fn-ocfg-owner (fn-ocfg-with-read-owner oc id owner repinned)) owner)
        (equal (fn-ocfg-config (fn-ocfg-with-read-owner oc id owner repinned))
               (fn-ocfg-config oc))
        (equal (fn-ocfg-staged (fn-ocfg-with-read-owner oc id owner repinned))
               (fn-ocfg-staged oc))
        (equal (fn-ocfg-pins (fn-ocfg-with-read-owner oc id owner repinned))
               (if (fn-own-find-conn id (fn-own-conns owner))
                   (if repinned
                       (fn-ocfg-pin-set id (fn-ocfg-config oc) (fn-ocfg-pins oc))
                     (fn-ocfg-pins oc))
                 (fn-ocfg-pin-remove id (fn-ocfg-pins oc))))
        (implies (and (fn-own-find-conn id (fn-own-conns owner))
                      (fn-ocfg-pin-find id (fn-ocfg-pins oc)))
                 (equal (fn-ocfg-conn-config (fn-ocfg-with-read-owner oc id owner repinned) id)
                        (if repinned (fn-ocfg-config oc) (fn-ocfg-conn-config oc id)))))
   :hints (("Goal" :in-theory (e/d (fn-ocfg-with-read-owner fn-ocfg-conn-config)
                                   (fn-ocfg-pin-find fn-ocfg-pin-set fn-ocfg-pin-remove
                                    fn-own-find-conn))))))

; A connection whose identifier is not the moved pin's keeps its history when
; the store is the same and only that other pin moved.
(local
 (defthm fn-ocl-conn-historyp-under-same-store-and-other-pin-set
   (implies (and (fn-ocl-conn-historyp oc conn)
                 (equal (fn-own-store (fn-ocfg-owner next))
                        (fn-own-store (fn-ocfg-owner oc)))
                 (equal (fn-ocfg-pins next)
                        (fn-ocfg-pin-set id cfg (fn-ocfg-pins oc)))
                 (not (equal (fn-own-conn-id conn) id)))
            (fn-ocl-conn-historyp next conn))
   :hints (("Goal"
            :use ((:instance fn-ocl-conn-historyp-under-same-store-and-pin))
            :in-theory (e/d (fn-ocfg-conn-config)
                            (fn-ocl-conn-historyp fn-ocfg-pin-set fn-ocfg-pin-find
                             fn-ocl-conn-historyp-under-same-store-and-pin))))))

; A connection with a history is a connection (a twelve-list), hence a cons.
(local
 (defthm fn-ocl-conn-historyp-is-a-cons
   (implies (fn-ocl-conn-historyp oc conn)
            (consp conn))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (fn-ocl-conn-historyp fn-own-conn-shapep)
                                   (fn-cpr-replay fn-cst-replay-node fn-own-take
                                    fn-ctl-projectionp fn-own-conn-boundedp))))))

; A list with no connection of the moved pin's identifier keeps every history.
(local
 (defthm fn-ocl-conns-historyp-under-same-store-and-other-pin-set
   (implies (and (fn-ocl-conns-historyp oc conns)
                 (equal (fn-own-store (fn-ocfg-owner next))
                        (fn-own-store (fn-ocfg-owner oc)))
                 (equal (fn-ocfg-pins next)
                        (fn-ocfg-pin-set id cfg (fn-ocfg-pins oc)))
                 (not (fn-own-find-conn id conns)))
            (fn-ocl-conns-historyp next conns))
   :hints (("Goal" :induct (fn-ocl-conns-historyp oc conns)
            :in-theory (e/d (fn-ocl-conns-historyp fn-own-find-conn)
                            (fn-ocl-conn-historyp fn-ocfg-pin-set fn-ocfg-pin-find))))))

; The replacement of the connection whose pin moved keeps every history when
; the identifiers are unique (fn-ocl-relation carries fn-ocl-unique-conn-idsp):
; the replaced connection has one in the new owner by hypothesis, the rest by
; the lemmas above.
(local
 (defthm fn-ocl-replace-connection-preserves-histories-under-pin-set
   (implies (and (fn-ocl-conns-historyp oc conns)
                 (fn-ocl-unique-conn-idsp conns)
                 (equal (fn-own-store (fn-ocfg-owner next-oc))
                        (fn-own-store (fn-ocfg-owner oc)))
                 (equal (fn-ocfg-pins next-oc)
                        (fn-ocfg-pin-set (fn-own-conn-id next) cfg (fn-ocfg-pins oc)))
                 (fn-ocl-conn-historyp next-oc next))
            (fn-ocl-conns-historyp next-oc (fn-own-replace-conn next conns)))
   :hints (("Goal" :induct (fn-own-replace-conn next conns)
            :in-theory (e/d (fn-own-replace-conn fn-ocl-conns-historyp
                             fn-ocl-unique-conn-idsp)
                            (fn-ocl-conn-historyp fn-ocfg-pin-set fn-ocfg-pin-find
                             fn-own-find-conn))))))

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

; NNT-042: the surviving connection has a history in the configured owner
; AFTER the read: with its old pin and fields when the read moved nothing
; (fn-own-read-survivor-keeps-historical-fields, first case), or at the
; committed view under the current configuration, to which
; fn-ocfg-with-read-owner pinned it (second case;
; fn-ocl-unchanged-view-new-pin-is-historical is the :advance shape).  Proved
; in the minimal theory from the named facts: an open theory looped the
; rewriter on the read's owner.
(defthm fn-ocl-own-read-survivor-has-history
  (implies
   (and (fn-ocl-relation oc)
        (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))
        (fn-own-find-conn
         id (fn-own-conns
             (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena)))))
   (fn-ocl-conn-historyp
    (cdr (fn-ocfg-read oc id octets fn-arena))
    (fn-own-find-conn
     id (fn-own-conns
         (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))))))
  :hints (("Goal"
           :use ((:instance fn-ocl-relation-read-input-facts)
                 (:instance fn-ocl-related-found-connection-has-history)
                 (:instance fn-ocl-found-connection-has-a-pin
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc)))
                 (:instance fn-own-find-conn-id (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-own-read-survivor-is-archive-bounded
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-own-read-survivor-keeps-historical-fields
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-ocfg-read-unfolds)
                 (:instance fn-ocl-with-read-owner-fields
                            (owner (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena)))
                            (repinned (fn-own-read-repinned (fn-ocfg-owner oc) id octets fn-arena)))
                 (:instance fn-ocl-own-read-keeps-store (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-keeps-owner-control (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-view-archive-has-current-domain)
                 (:instance fn-ocl-connection-history-keeps-replaced-session
                            (old (fn-own-find-conn
                                  id (fn-own-conns (fn-ocfg-owner oc))))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena))))))
                 (:instance fn-ocl-conn-historyp-under-same-store-and-pin
                            (next (cdr (fn-ocfg-read oc id octets fn-arena)))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena))))))
                 (:instance fn-ocl-unchanged-view-new-pin-is-historical
                            (next (cdr (fn-ocfg-read oc id octets fn-arena)))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena)))))))
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

(defthm fn-ocl-read-preserves-capacity-bound
  (implies
   (fn-ocl-relation oc)
   (<= (len (fn-own-conns
             (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))))
       (fn-own-max-conns (fn-ocfg-owner oc))))
  :hints (("Goal"
           :use (fn-ocl-relation-read-input-facts
                 (:instance fn-ocl-own-read-does-not-increase-connections
                            (o (fn-ocfg-owner oc))))
           :in-theory (theory 'minimal-theory))))

; The read theorem, one lemma per case of the read (D26: the single :cases
; proof re-simplified the whole :use list eight times, 58 s in the REPL).
; No connection ID: the read returns the configured owner unchanged.
(defthm fn-ocl-read-preserves-historical-relation-missing
  (implies (and (fn-ocl-relation oc)
                (not (fn-own-find-conn
                    id (fn-own-conns (fn-ocfg-owner oc)))))
           (fn-ocl-relation (cdr (fn-ocfg-read oc id octets fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-ocl-relation-under-same-control-and-valid-connections
                            (next (cdr (fn-ocfg-read oc id octets fn-arena))))
                 fn-ocl-relation-read-input-facts
                 fn-ocl-read-preserves-capacity-bound
                 fn-ocl-missing-read-keeps-configured-owner
                 (:instance fn-ocl-own-read-keeps-store
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-preserves-owner-shape
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-keeps-owner-control
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-does-not-increase-connections
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-ocfg-read-unfolds)
                 (:instance fn-ocl-with-read-owner-fields
                            (owner (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena)))
                            (repinned (fn-own-read-repinned (fn-ocfg-owner oc) id octets fn-arena)))
                 (:instance fn-own-find-conn-id
                            (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-own-find-conn-id-below-next
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-next-id (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocfg-with-read-owner
                            fn-own-set-conns fn-own-enqueue
                            ; the read wrapper opens to the owner read and
                            ; the pin table's move (fn-ocfg-read stays closed)
                            fn-ocl-ocfg-read-unfolds)
                           (fn-ocfg-read fn-own-read-full fn-own-read-repinned
                            fn-ocl-pin-set-keeps-conns-pinned
                            fn-ocl-pin-set-keeps-pins-pin-conns-only
                            fn-ocl-pin-set-keeps-pins-okp
                            fn-ocl-relation fn-ocl-view-historyp
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
                            fn-ocl-own-read-survivor-has-history
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

; The connection was found and the read closed it: the pin table loses its entry.
(defthm fn-ocl-read-preserves-historical-relation-removed
  (implies (and (fn-ocl-relation oc)
                (fn-own-find-conn
                    id (fn-own-conns (fn-ocfg-owner oc)))
                (not (fn-own-find-conn
                    id (fn-own-conns
                        (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))))))
           (fn-ocl-relation (cdr (fn-ocfg-read oc id octets fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-ocl-relation-under-same-control-and-valid-connections
                            (next (cdr (fn-ocfg-read oc id octets fn-arena))))
                 fn-ocl-relation-read-input-facts
                 fn-ocl-read-preserves-capacity-bound
                 fn-ocl-read-removal-preserves-historical-connections
                 (:instance fn-ocl-own-read-keeps-store
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-preserves-owner-shape
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-keeps-owner-control
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-does-not-increase-connections
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-own-read-nonsurvivor-is-removal
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-ocfg-read-unfolds)
                 (:instance fn-ocl-with-read-owner-fields
                            (owner (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena)))
                            (repinned (fn-own-read-repinned (fn-ocfg-owner oc) id octets fn-arena)))
                 (:instance fn-own-find-conn-id
                            (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-own-find-conn-id-below-next
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-next-id (fn-ocfg-owner oc))))
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
           :in-theory (e/d (fn-ocfg-with-read-owner
                            fn-own-set-conns fn-own-enqueue
                            ; the read wrapper opens to the owner read and
                            ; the pin table's move (fn-ocfg-read stays closed)
                            fn-ocl-ocfg-read-unfolds)
                           (fn-ocfg-read fn-own-read-full fn-own-read-repinned
                            fn-ocl-pin-set-keeps-conns-pinned
                            fn-ocl-pin-set-keeps-pins-pin-conns-only
                            fn-ocl-pin-set-keeps-pins-okp
                            fn-ocl-relation fn-ocl-view-historyp
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
                            fn-ocl-own-read-survivor-has-history
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

; The connection survives at its old pin: its history and pin entry are kept.
(defthm fn-ocl-read-preserves-historical-relation-kept
  (implies (and (fn-ocl-relation oc)
                (fn-own-find-conn
                    id (fn-own-conns (fn-ocfg-owner oc)))
                (fn-own-find-conn
                    id (fn-own-conns
                        (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))))
                (not (fn-own-read-repinned (fn-ocfg-owner oc) id octets fn-arena)))
           (fn-ocl-relation (cdr (fn-ocfg-read oc id octets fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-ocl-relation-under-same-control-and-valid-connections
                            (next (cdr (fn-ocfg-read oc id octets fn-arena))))
                 fn-ocl-relation-read-input-facts
                 fn-ocl-read-preserves-capacity-bound
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
                 fn-ocl-own-read-survivor-has-history
                 (:instance fn-ocl-ocfg-read-unfolds)
                 (:instance fn-ocl-with-read-owner-fields
                            (owner (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena)))
                            (repinned (fn-own-read-repinned (fn-ocfg-owner oc) id octets fn-arena)))
                 (:instance fn-ocl-own-read-survivor-had-original
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-replace-connection-preserves-histories
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena))))))
                 (:instance fn-ocl-replace-preserves-conns-pinned
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena))))))
                 (:instance fn-ocl-replace-preserves-pins-point-to-conns
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena))))))
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
                                             (fn-ocfg-owner oc) id octets fn-arena)))))
                            (n (fn-own-next-id (fn-ocfg-owner oc))))
                 (:instance fn-own-replace-conn-len
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena)))))))
           :in-theory (e/d (fn-ocfg-with-read-owner
                            fn-own-set-conns fn-own-enqueue
                            ; the read wrapper opens to the owner read and
                            ; the pin table's move (fn-ocfg-read stays closed)
                            fn-ocl-ocfg-read-unfolds)
                           (fn-ocfg-read fn-own-read-full fn-own-read-repinned
                            fn-ocl-pin-set-keeps-conns-pinned
                            fn-ocl-pin-set-keeps-pins-pin-conns-only
                            fn-ocl-pin-set-keeps-pins-okp
                            fn-ocl-relation fn-ocl-view-historyp
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
                            fn-ocl-own-read-survivor-has-history
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

; The connection survives re-pinned at the committed view (NNT-042): its pin
; entry moves to the current configuration and every other history is kept.
(defthm fn-ocl-read-preserves-historical-relation-repinned
  (implies (and (fn-ocl-relation oc)
                (fn-own-find-conn
                    id (fn-own-conns (fn-ocfg-owner oc)))
                (fn-own-find-conn
                    id (fn-own-conns
                        (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))))
                (fn-own-read-repinned (fn-ocfg-owner oc) id octets fn-arena))
           (fn-ocl-relation (cdr (fn-ocfg-read oc id octets fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-ocl-relation-under-same-control-and-valid-connections
                            (next (cdr (fn-ocfg-read oc id octets fn-arena))))
                 fn-ocl-relation-read-input-facts
                 fn-ocl-read-preserves-capacity-bound
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
                 fn-ocl-own-read-survivor-has-history
                 (:instance fn-ocl-ocfg-read-unfolds)
                 (:instance fn-ocl-with-read-owner-fields
                            (owner (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena)))
                            (repinned (fn-own-read-repinned (fn-ocfg-owner oc) id octets fn-arena)))
                 (:instance fn-ocl-replace-connection-preserves-histories-under-pin-set
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (next-oc (cdr (fn-ocfg-read oc id octets fn-arena)))
                            (cfg (fn-ocfg-config oc))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))))))
                 (:instance fn-ocl-pin-set-keeps-conns-pinned
                            (conns (fn-own-replace-conn
                                    (fn-own-find-conn
                                     id (fn-own-conns
                                         (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))))
                                    (fn-own-conns (fn-ocfg-owner oc))))
                            (pins (fn-ocfg-pins oc)) (cfg (fn-ocfg-config oc)))
                 (:instance fn-ocl-pin-set-keeps-pins-pin-conns-only
                            (conns (fn-own-replace-conn
                                    (fn-own-find-conn
                                     id (fn-own-conns
                                         (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))))
                                    (fn-own-conns (fn-ocfg-owner oc))))
                            (pins (fn-ocfg-pins oc)) (cfg (fn-ocfg-config oc)))
                 (:instance fn-ocl-pin-set-keeps-pins-okp
                            (pins (fn-ocfg-pins oc)) (cfg (fn-ocfg-config oc)))
                 (:instance fn-ocl-own-read-survivor-had-original
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocl-replace-connection-preserves-histories
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena))))))
                 (:instance fn-ocl-replace-preserves-conns-pinned
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena))))))
                 (:instance fn-ocl-replace-preserves-pins-point-to-conns
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc))
                            (next (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena))))))
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
                                             (fn-ocfg-owner oc) id octets fn-arena)))))
                            (n (fn-own-next-id (fn-ocfg-owner oc))))
                 (:instance fn-own-replace-conn-len
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (conn (fn-own-find-conn
                                   id (fn-own-conns
                                       (cdr (fn-own-read
                                             (fn-ocfg-owner oc) id octets fn-arena)))))))
           :in-theory (e/d (fn-ocfg-with-read-owner
                            fn-own-set-conns fn-own-enqueue
                            ; the read wrapper opens to the owner read and
                            ; the pin table's move (fn-ocfg-read stays closed)
                            fn-ocl-ocfg-read-unfolds)
                           (fn-ocfg-read fn-own-read-full fn-own-read-repinned
                            fn-ocl-pin-set-keeps-conns-pinned
                            fn-ocl-pin-set-keeps-pins-pin-conns-only
                            fn-ocl-pin-set-keeps-pins-okp
                            fn-ocl-relation fn-ocl-view-historyp
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
                            fn-ocl-own-read-survivor-has-history
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

(defthm fn-ocl-read-preserves-historical-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (cdr (fn-ocfg-read oc id octets fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((fn-own-find-conn
                    id (fn-own-conns (fn-ocfg-owner oc)))
                   (fn-own-find-conn
                    id (fn-own-conns
                        (cdr (fn-own-read (fn-ocfg-owner oc) id octets fn-arena))))
                   (fn-own-read-repinned (fn-ocfg-owner oc) id octets fn-arena))
           :use (fn-ocl-read-preserves-historical-relation-missing
                 fn-ocl-read-preserves-historical-relation-removed
                 fn-ocl-read-preserves-historical-relation-kept
                 fn-ocl-read-preserves-historical-relation-repinned)
           :in-theory (theory 'minimal-theory))))
