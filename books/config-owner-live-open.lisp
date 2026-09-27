; fn: fn-ocl-relation preserved by the reader context, open and close, and
; the read's removal of a connection.  Part 2 of 3 of
; books/config-owner-live.lisp.

(in-package "ACL2")
(include-book "config-owner-live-complete")

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
                            (frontier (fn-own-conn-frontier conn)))
                 (:instance fn-ctl-visible-state-is-a-projection
                            (p (fn-node-acceptance
                                (fn-cst-replay-node
                                 (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                                 (fn-own-take (fn-own-conn-version conn)
                                              (fn-sf-records
                                               (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                                 (fn-own-conn-frontier conn))))
                            (ws (fn-own-view-withdrawals (fn-own-view (fn-ocfg-owner oc))))
                            (verdicts (fn-own-view-verdicts (fn-own-view (fn-ocfg-owner oc))))))
           :in-theory (e/d (fn-ocl-relation fn-ocl-conn-historyp
                            fn-ocl-view-historyp fn-ocl-view-configp)
                           (fn-cst-replay-node fn-cpr-replay
                            fn-ocl-conns-historyp fn-own-take
                            fn-ctl-visible-state fn-ctl-projectionp
                            fn-ctl-visible-state-is-a-projection)))))

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
           :in-theory (e/d (fn-ocl-projectionp-of-a-visible-state
                            fn-ocl-projection-keeps-state-fields
                            fn-ocl-relation fn-ocl-conn-historyp
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
             (fn-own-conn-group-index conn) (fn-own-conn-control conn))))
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
     (fn-own-conn-group-index (car (fn-own-conns o))) (fn-own-conn-control (car (fn-own-conns o))))))
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
      (fn-own-conn-group-index (car (fn-own-conns o))) (fn-own-conn-control (car (fn-own-conns o))))
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
          (next (fn-ocfg-with-read-owner oc id owner repinned)))
     (fn-ocl-conns-historyp next (fn-own-conns (fn-ocfg-owner next)))))
  :hints (("Goal"
           :use ((:instance fn-ocl-read-removal-preserves-surviving-histories
                            (conns (fn-own-conns (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocl-relation fn-ocfg-with-read-owner
                            fn-own-set-conns)
                           (fn-ocl-conns-historyp)))))
