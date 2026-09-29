; fn: fn-own-relation preserved by every owner event -- read and read-step,
; advance, close, begin, store-step, complete, reopen, observe (the clock
; seam), declare-group, configure, the submissions and outcomes -- and so by
; fn-own-step and fn-own-run (K6).  Part 2 of 4 of books/owner-invariants.lisp.

(in-package "ACL2")
(include-book "owner-invariants-relation")

; The local prelude of owner-invariants-relation, replayed (local events do not
; cross include-book).
(local (include-book "arithmetic/top" :dir :system))
; fn-inj-injected-article-is-a-reinjection-of-its-source and
; fn-inj-injection-requires-posting-allowed: the operator keystones below.
(local (include-book "injection-invariants"))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

(local (in-theory (enable fn-own-vocabulary fn-ag-append fn-ag-member)))

; List-recursive vocabulary of other clusters that must stay closed here so
; the proofs below see it only through the cited keystones.
(local (in-theory (disable fn-sf-record-has-pairp fn-sf-prefixp
                           fn-served-reply-octets fn-served-submission
                           fn-served-closingp fn-served-chunk-listp
                           fn-served-concat fn-nntp-session-consistentp
                           fn-nntp-projectionp)))

; The index correspondences inside fn-own-conn-okp and fn-own-view-okp build
; a message-id trie and a group-bucket index from the archive when opened;
; only the proofs that establish one for a fresh or rebuilt index open them.
; fn-nntp-article-idp-is-consp and the true-list shape rules of the NNTP and
; content-identity clusters are tried on every consp and true-listp test and
; backchain by opening their recognizers; nothing here needs them.
(local (in-theory (disable fn-midx-correspondencep fn-gidx-build
                           fn-nntp-article-idp-is-consp
                           fn-nntp-response-text-true-listp fn-cp-idp-true-listp
                           fn-cp-id-length-bound)))
; Rules whose conclusion is a consp or car test on a variable, with a
; free-variable hypothesis, from the resolution, wire, control and feed
; clusters: each is tried on every such test here and none applies.
(local (in-theory (disable fn-snrt-new-success-is-actual-matching-durable-completion
                           fn-wire-next-loop-event-needs-input
                           fn-wire-next-event-needs-input
                           fn-ctl-authorize-execute-is-nonempty
                           fn-own-feed-never-offers-a-loop)))
; Vocabulary of the article parser, the control projection, the replay
; identity and the group indexes that the owner theorems reach only through
; the served step and the store: opened here, none of it ever applied
; (accumulated persistence over the book, 2026-09-27).
(local (in-theory (disable fn-article-parse fn-ctl-visible-articles
                           fn-ctl-withdrawal-effect fn-ctl-locks-octets
                           fn-ctl-received-fields fn-ctl-covers-every-p
                           fn-sn-observed-identity-okp fn-replay-identity
                           fn-snt-idle-phasep fn-gidx-put fn-gidx-put-all
                           fn-gnix-add fn-own-feed-inflight-msgid
                           fn-feed-state-inflightp
                           fn-ctl-refresh-visible-is-visible
                           fn-prov-structured-is-not-a-string
                           fn-digest-octetsp-implies-octet-listp
                           fn-inj-generated-identity-is-the-clock-identity
                           fn-inj-supplied-message-id-is-retained-exactly)))

; The connection `fn-own-advance' re-pins at the view carries the view's
; control pin, and that pin is okp against the connection's own prefix
; (the view's): the conn-okp conjunct control-c3e added.
(defthm fn-own-conn-okp-of-view-pin
  (implies (and (fn-own-view-okp view groups capacity records)
                (natp id)
                (fn-own-conn-boundedp
                 (fn-own-conn-make-group-indexed
                  id (fn-own-view-version view) (fn-own-view-frontier view)
                  wire session (fn-own-view-archive view) config obs
                  (fn-own-view-verdicts view) (fn-own-view-index view)
                  (fn-own-view-group-index view) (fn-own-view-control view))
                 groups))
           (fn-own-conn-okp
            (fn-own-conn-make-group-indexed
             id (fn-own-view-version view) (fn-own-view-frontier view)
             wire session (fn-own-view-archive view) config obs
             (fn-own-view-verdicts view) (fn-own-view-index view)
             (fn-own-view-group-index view) (fn-own-view-control view))
            groups capacity records))
  :hints (("Goal" :in-theory (disable fn-own-conn-make-group-indexed
                                      fn-own-conn-boundedp))))

; NNT-042: the read hands the served connection the owner's committed view as
; its live pin and takes the pin back (fn-own-finish-read).  What comes back
; is the connection's own pin or the view's (fn-served-step-pin-is-old-or-live,
; books/served.lisp), so the rebuilt connection is okp either as the found
; connection was (its pin) or as an advanced connection is
; (fn-own-conn-okp-of-view-pin, the :advance argument); its boundedness is
; the runtime check fn-own-finish-read makes.

; The two cases of a served result's pin against the owner connection it
; was built from, in the owner's vocabulary.
(local
 (defthm fn-own-served-conn-pin-cases
   (implies (fn-served-pin-old-or-live-p (fn-own-served-conn o conn session) sconn)
            (or (and (equal (fn-served-conn-archive sconn) (fn-own-conn-archive conn))
                     (equal (fn-served-conn-verdicts sconn) (fn-own-conn-verdicts conn))
                     (equal (fn-served-conn-index sconn) (fn-own-conn-index conn))
                     (equal (fn-served-conn-group-index sconn) (fn-own-conn-group-index conn))
                     (equal (fn-served-conn-control sconn) (fn-own-conn-control conn))
                     (equal (fn-served-conn-pinned sconn)
                            (fn-served-pinned-make (fn-own-conn-version conn)
                                                   (fn-own-conn-frontier conn) nil)))
                (and (equal (fn-served-conn-archive sconn) (fn-own-view-archive (fn-own-view o)))
                     (equal (fn-served-conn-verdicts sconn) (fn-own-view-verdicts (fn-own-view o)))
                     (equal (fn-served-conn-index sconn) (fn-own-view-index (fn-own-view o)))
                     (equal (fn-served-conn-group-index sconn) (fn-own-view-group-index (fn-own-view o)))
                     (equal (fn-served-conn-control sconn) (fn-own-view-control (fn-own-view o)))
                     (equal (fn-served-conn-pinned sconn)
                            (fn-served-pinned-make (fn-own-view-version (fn-own-view o))
                                                   (fn-own-view-frontier (fn-own-view o)) t)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-served-pin-old-or-live-p-cases
                             (c0 (fn-own-served-conn o conn session)) (c sconn))
                  (:instance fn-served-conn-pin-fields
                             (a sconn) (b (fn-own-served-conn o conn session)))
                  (:instance fn-served-live-pin-fields
                             (a sconn) (live (fn-own-view-live (fn-own-view o)))))
            :in-theory (e/d (fn-own-served-conn)
                            (fn-served-pin-old-or-live-p fn-served-conn-pin
                             fn-served-live-pin fn-own-view-live))))))

; The rebuilt connection of fn-own-finish-read is okp in either case: with
; the found connection's pin it is okp as that connection was (field by
; field, fn-own-conn-okp opened once with the pin equalities in hand); with
; the view's pin it is fn-own-conn-okp-of-view-pin (the :advance argument).
; Two lemmas, then the disjunction, so fn-own-conn-okp is never opened under
; a disjunctive hypothesis (D26: the one-lemma form took 43 s).
(local
 (defthm fn-own-finish-read-conn-okp-old-pin
   (implies (and (fn-own-conn-okp conn groups capacity records)
                 (equal archive (fn-own-conn-archive conn))
                 (equal verdicts (fn-own-conn-verdicts conn))
                 (equal index (fn-own-conn-index conn))
                 (equal buckets (fn-own-conn-group-index conn))
                 (equal control (fn-own-conn-control conn))
                 (fn-own-conn-boundedp
                  (fn-own-conn-make-group-indexed
                   (fn-own-conn-id conn) (fn-own-conn-version conn) (fn-own-conn-frontier conn)
                   wire session2 archive
                   (fn-own-conn-config conn) (fn-own-conn-observation conn)
                   verdicts index buckets control)
                  groups))
            (fn-own-conn-okp
             (fn-own-conn-make-group-indexed
              (fn-own-conn-id conn) (fn-own-conn-version conn) (fn-own-conn-frontier conn)
              wire session2 archive
              (fn-own-conn-config conn) (fn-own-conn-observation conn)
              verdicts index buckets control)
             groups capacity records))
   :hints (("Goal" :in-theory (e/d (fn-own-conn-okp)
                                   (fn-own-conn-make-group-indexed fn-own-conn-boundedp
                                    fn-ctl-projectionp fn-midx-correspondencep fn-gidx-build
                                    fn-own-control-okp fn-own-prefix-archive))))))

(local
 (defthm fn-own-conn-okp-has-a-natural-id
   (implies (fn-own-conn-okp conn groups capacity records)
            (natp (fn-own-conn-id conn)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-own-conn-okp)
                                   (fn-ctl-projectionp fn-midx-correspondencep fn-gidx-build
                                    fn-own-control-okp fn-own-prefix-archive
                                    fn-own-conn-boundedp))))))

(local
 (defthm fn-own-finish-read-conn-okp
   (implies (and (fn-own-conn-okp conn groups capacity records)
                 (fn-own-view-okp (fn-own-view o) groups capacity records)
                 (fn-served-pin-old-or-live-p (fn-own-served-conn o conn session) sconn)
                 (fn-own-conn-boundedp
                  (fn-own-conn-make-group-indexed
                   (fn-own-conn-id conn)
                   (fn-served-pinned-version (fn-served-conn-pinned sconn))
                   (fn-served-pinned-frontier (fn-served-conn-pinned sconn))
                   wire session2
                   (fn-served-conn-archive sconn)
                   (fn-own-conn-config conn) (fn-own-conn-observation conn)
                   (fn-served-conn-verdicts sconn) (fn-served-conn-index sconn)
                   (fn-served-conn-group-index sconn) (fn-served-conn-control sconn))
                  groups))
            (fn-own-conn-okp
             (fn-own-conn-make-group-indexed
              (fn-own-conn-id conn)
              (fn-served-pinned-version (fn-served-conn-pinned sconn))
              (fn-served-pinned-frontier (fn-served-conn-pinned sconn))
              wire session2
              (fn-served-conn-archive sconn)
              (fn-own-conn-config conn) (fn-own-conn-observation conn)
              (fn-served-conn-verdicts sconn) (fn-served-conn-index sconn)
              (fn-served-conn-group-index sconn) (fn-served-conn-control sconn))
             groups capacity records))
   :hints (("Goal"
            :use ((:instance fn-own-served-conn-pin-cases)
                  (:instance fn-own-conn-okp-has-a-natural-id)
                  (:instance fn-own-finish-read-conn-okp-old-pin
                             (archive (fn-served-conn-archive sconn))
                             (verdicts (fn-served-conn-verdicts sconn))
                             (index (fn-served-conn-index sconn))
                             (buckets (fn-served-conn-group-index sconn))
                             (control (fn-served-conn-control sconn)))
                  (:instance fn-own-conn-okp-of-view-pin
                             (view (fn-own-view o)) (id (fn-own-conn-id conn))
                             (wire wire) (session session2)
                             (config (fn-own-conn-config conn))
                             (obs (fn-own-conn-observation conn))))
            ; the two pin cases and the two okp lemmas close it by
            ; propositional reasoning and the pin's field selectors alone
            :in-theory (union-theories '(fn-served-pinned-fields)
                                       (theory 'minimal-theory))))))

(defthm fn-own-read-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-read o id octets fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 ; the rebuilt connection keeps the found connection's
                 ; identifier, so it keeps its bound below `next-id' too
                 (:instance fn-own-find-conn-id-below-next
                            (conns (fn-own-conns o))
                            (n (fn-own-next-id o)))
                 (:instance fn-served-step-pin-is-old-or-live
                            (conn (fn-own-served-conn
                                   o (fn-own-find-conn id (fn-own-conns o))
                                   (fn-own-conn-live-session
                                    o (fn-own-find-conn id (fn-own-conns o))))))
                 (:instance fn-own-finish-read-conn-okp
                            (conn (fn-own-find-conn id (fn-own-conns o)))
                            (session (fn-own-conn-live-session
                                      o (fn-own-find-conn id (fn-own-conns o))))
                            (sconn (fn-served-result-conn
                                    (fn-served-step
                                     (fn-own-served-conn
                                      o (fn-own-find-conn id (fn-own-conns o))
                                      (fn-own-conn-live-session
                                       o (fn-own-find-conn id (fn-own-conns o))))
                                     octets fn-arena)))
                            (wire (fn-served-conn-wire
                                   (fn-served-result-conn
                                    (fn-served-step
                                     (fn-own-served-conn
                                      o (fn-own-find-conn id (fn-own-conns o))
                                      (fn-own-conn-live-session
                                       o (fn-own-find-conn id (fn-own-conns o))))
                                     octets fn-arena))))
                            (session2 (fn-served-conn-session
                                       (fn-served-result-conn
                                        (fn-served-step
                                         (fn-own-served-conn
                                          o (fn-own-find-conn id (fn-own-conns o))
                                          (fn-own-conn-live-session
                                           o (fn-own-find-conn id (fn-own-conns o))))
                                         octets fn-arena))))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-relation fn-own-read fn-own-read-full fn-own-finish-read)
                           (fn-own-conns-okp fn-own-view-okp fn-own-conn-make-group-indexed
                            fn-own-conn-boundedp fn-own-find-conn-okp fn-own-conn-okp
                            fn-served-step fn-own-served-conn fn-served-pin-old-or-live-p
                            fn-own-conn-live-session)))))

(defthm fn-own-read-step-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-read-step o id event fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-own-find-conn-id-below-next
                            (conns (fn-own-conns o))
                            (n (fn-own-next-id o)))
                 (:instance fn-served-dispatch-pin
                            (conn (fn-own-served-conn
                                   o (fn-own-find-conn id (fn-own-conns o))
                                   (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))))))
                 (:instance fn-own-finish-read-conn-okp
                            (conn (fn-own-find-conn id (fn-own-conns o)))
                            (session (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))))
                            (sconn (fn-served-result-conn
                                    (fn-served-dispatch
                                     (fn-own-served-conn
                                      o (fn-own-find-conn id (fn-own-conns o))
                                      (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))))
                                     event fn-arena)))
                            (wire (fn-served-conn-wire
                                   (fn-served-result-conn
                                    (fn-served-dispatch
                                     (fn-own-served-conn
                                      o (fn-own-find-conn id (fn-own-conns o))
                                      (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))))
                                     event fn-arena))))
                            (session2 (fn-served-conn-session
                                       (fn-served-result-conn
                                        (fn-served-dispatch
                                         (fn-own-served-conn
                                          o (fn-own-find-conn id (fn-own-conns o))
                                          (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))))
                                         event fn-arena))))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-relation fn-own-read-step fn-own-read-step-full)
                           (fn-own-conns-okp fn-own-view-okp fn-own-conn-make-group-indexed
                            fn-own-conn-boundedp fn-own-find-conn-okp fn-own-conn-okp
                            fn-served-dispatch fn-own-served-conn fn-served-pin-old-or-live-p)))))

(defthm fn-own-advance-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-advance o id)))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 ; the rebuilt connection keeps the found connection's
                 ; identifier, so it keeps its bound below `next-id' too
                 (:instance fn-own-find-conn-id-below-next
                            (conns (fn-own-conns o))
                            (n (fn-own-next-id o))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-conn-make-group-indexed
                            fn-own-conn-boundedp fn-own-find-conn-okp
                            fn-own-view-okp fn-own-view-group-index)))))

; `fn-own-advance' returns `o' unchanged when there is no connection at `id',
; and otherwise either re-pins it in place (`fn-own-replace-conn', which keeps
; the identifier) or leaves `o' alone; it never ADDS one.  So a connection
; present after the advance was present before it.  books/owner-config spends
; this to reach `fn-ocfg-conns-pinnedp' on the pre-state pin table, where the
; pin it is about to replace lives.  :rule-classes nil -- the conclusion is a
; recognizer call, not a rewrite target -- so it is reached by :use and needs
; no place in the export theory.
(defthm fn-own-advance-finds-only-what-it-had
  (implies (fn-own-find-conn id (fn-own-conns (fn-own-advance o id)))
           (fn-own-find-conn id (fn-own-conns o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-advance fn-own-set-conns)
                                  (fn-own-conn-boundedp fn-own-replace-conn
                                   fn-own-conn-make)))))

(defthm fn-own-close-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-close o id)))
  :hints (("Goal" :in-theory (e/d (fn-own-relation) (fn-own-conns-okp fn-own-view-okp fn-own-conn-okp)))))

(defthm fn-own-begin-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-begin o id)))
  :hints (("Goal" :in-theory (e/d (fn-own-relation) (fn-own-conns-okp fn-own-view-okp fn-own-conn-okp)))))

(defthm fn-own-store-step-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-store-step o event)))
  :hints (("Goal"
           :use ((:instance fn-own-refresh-preserves-relation
                            (o (fn-own-make (fn-snrt-step (fn-own-store o) event)
                                            (fn-own-view o) (fn-own-conns o)
                                            (fn-own-next-id o) (fn-own-max-conns o)
                                            (fn-own-pending o) (fn-own-ledger-field o)
                                            (fn-own-clock o) (fn-own-facts o)
                                            ; `feeds' is `fn-own-make's THIRTEENTH
                                            ; field (w10/owner-feed).  Six `:use'
                                            ; instances in this book were left at
                                            ; twelve, and `certify-book' stops at
                                            ; the first, so only one was ever seen.
                                            (fn-own-config o) (fn-own-queue o)
                                            (fn-own-inflight o)
                                            (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))
                 (:instance fn-own-snrt-step-records-prefix (s (fn-own-store o))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-conns-okp fn-own-view-okp fn-own-conn-okp fn-own-refresh-preserves-relation fn-own-refresh
                            fn-own-snrt-step-records-prefix)))))

(defthm fn-own-complete-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-complete o)))
  :hints (("Goal"
           :use ((:instance fn-own-refresh-preserves-relation
                            (o (fn-own-make (fn-sn-finish (fn-own-store o))
                                            (fn-own-view o) (fn-own-conns o)
                                            (fn-own-next-id o) (fn-own-max-conns o)
                                            nil
                                            (fn-sl-snoc (fn-own-ledger-field o) (fn-sf-completion
                                                           (fn-sn-files (fn-own-store o))))
                                            (fn-own-clock o) (fn-own-facts o)
                                            (fn-own-config o) (fn-own-queue o)
                                            (fn-own-inflight o)
                                            (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))
                 (:instance fn-snt-finish-preserves-relation (s (fn-own-store o)))
                 (:instance fn-snt-finish-image (s (fn-own-store o)))
                 (:instance fn-snt-finish-keeps-records (s (fn-own-store o)))
                 (:instance fn-own-completion-pair-has-record (s (fn-own-store o)))
                 (:instance fn-snt-relation-implies-structural-state (s (fn-own-store o))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-conns-okp fn-own-view-okp fn-own-conn-okp fn-own-refresh-preserves-relation fn-own-refresh
                            fn-snt-finish-preserves-relation fn-snt-finish-image
                            fn-snt-finish-keeps-records
                            fn-own-completion-pair-has-record
                            fn-snt-relation-implies-structural-state)))))

(defthm fn-own-reopen-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-reopen o frontier records)))
  :hints (("Goal"
           :use ((:instance fn-own-refresh-preserves-relation
                            (o (fn-own-make
                                (fn-sn-open-state
                                 (fn-sn-open-observed (fn-sn-groups (fn-own-store o))
                                                      (fn-sn-capacity (fn-own-store o))
                                                      frontier records))
                                (fn-own-view o) nil (fn-own-next-id o)
                                (fn-own-max-conns o) nil (fn-own-ledger-field o) nil
                                (fn-own-facts o) (fn-own-config o) nil nil
                                (fn-own-feed-restart-all (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))
                 (:instance fn-sn-open-observed-success-has-live-history-relation
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o))))
                 (:instance fn-sn-open-observed-success-exact-history
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o))))
                 (:instance fn-sn-open-observed-success-configuration
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o))))
                 (:instance fn-own-crash-image-extends-records
                            (files (fn-sn-files (fn-own-store o))))
                 (:instance fn-own-related-records-true-list (s (fn-own-store o))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-view-okp fn-own-refresh-preserves-relation fn-own-refresh
                            fn-sn-open-observed-success-has-live-history-relation
                            fn-sn-open-observed-success-exact-history
                            fn-sn-open-observed-success-configuration
                            fn-own-crash-image-extends-records
                            fn-own-related-records-true-list)))))

(defthm fn-own-observe-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-observe o obs)))
  :hints (("Goal" :in-theory (enable fn-own-relation))))

; -----------------------------------------------------------------------------
; The clock seam (decision D10-a).  The owner answers a reading with one of
; three words and a refusal costs it the clock it held.

; Definitional, cited by :use and never a registry event: which word leaves
; which state.  Named for what it is.
(defthm fn-own-observe-outcome-decides-the-clock-by-definition
  (and (implies (equal (fn-own-observe-outcome o obs) :observed)
                (equal (fn-own-clock (fn-own-observe o obs)) obs))
       (implies (equal (fn-own-observe-outcome o obs) :refused)
                (equal (fn-own-clock (fn-own-observe o obs)) nil))
       (implies (equal (fn-own-observe-outcome o obs) :invalid)
                (equal (fn-own-observe o obs) o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-own-observe fn-own-observe-outcome))))

; The outcome is exactly one of three, and it is the word the host reports
; (host/owner-host.lisp fn-owner-observe).  The host used to compute the
; word by comparing the owner before and after the event, which spelled an
; ADMITTED reading equal to the one held with the same `rejected' as a
; contradicted clock; the three-outcome rule says that distinction matters.
(defthm fn-own-observe-outcome-is-one-of-three
  (member-equal (fn-own-observe-outcome o obs) '(:observed :refused :invalid))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-own-observe-outcome))))

; KEYSTONE.  A refusal NAMES a host contradiction: on a related owner that
; holds a clock, `:refused' says the monotonic counter went backwards, or
; `has-wall' changed, or a widened error bound moved the earliest admissible
; true time back (specs/time.md: that is not a later observation of the same
; clock).  It is never merely a reading that did not move -- an admitted
; reading EQUAL to the one held is `:observed', which is the case the host
; used to spell as a refusal.  What the refusal then costs is the clock
; itself: fn-own-observe leaves none, so the injection reading fn-own-read
; supplies is not an observation (the sixth field of the served connection
; in fn-own-reader-sees-pinned-prefix-replay is (fn-own-clock o)),
; fn-nntp-post-step answers the CLOCK line and emits no submission
; (fn-post-without-a-clock-refuses-with-the-clock-line, books/nntp-post.lisp),
; fn-own-declare-group refuses and DATE answers 503.
(defthm fn-own-observe-refusal-names-a-contradiction
  (implies (and (fn-own-relation o)
                (fn-own-clock o)
                (equal (fn-own-observe-outcome o obs) :refused))
           (or (< (fn-clock-monotonic obs) (fn-clock-monotonic (fn-own-clock o)))
               (not (equal (fn-clock-has-wall obs)
                           (fn-clock-has-wall (fn-own-clock o))))
               (< (fn-clock-earliest-true obs)
                  (fn-clock-earliest-true (fn-own-clock o)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-relation fn-own-observe-outcome
                                   fn-clock-later-observationp)
                                  (fn-own-conn-boundedp)))))

(defthm fn-own-group-fact-make-is-fact
  (implies (and (stringp name) (fn-clock-observationp obs))
           (fn-own-group-factp (fn-own-group-fact-make name obs))))

(defthm fn-own-declare-group-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-declare-group o name)))
  :hints (("Goal" :in-theory (e/d (fn-own-relation)
                                  (fn-own-facts-okp fn-own-group-factp)))))

; The served POST events touch the configuration, the queue, the submission
; in flight and the pending transaction only; the relation reads none of
; them.
(defthm fn-own-configure-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-configure o config)))
  :hints (("Goal" :in-theory (e/d (fn-own-relation) (fn-own-conns-okp fn-own-view-okp fn-own-conn-okp)))))

(defthm fn-own-take-submission-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-take-submission o)))
  :hints (("Goal" :in-theory (e/d (fn-own-relation) (fn-own-conns-okp fn-own-view-okp fn-own-conn-okp)))))

(defthm fn-own-control-submit-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-control-submit o msgid groups octets)))
  :hints (("Goal" :in-theory (e/d (fn-own-control-submit-result
                                   fn-own-control-submit
                                   fn-own-enqueue fn-own-relation)
                                  (fn-own-control-decision fn-own-conns-okp
                                   fn-own-view-okp fn-midx-correspondencep
                                   fn-gidx-build)))))

(defthm fn-own-operator-submit-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-operator-submit o msgid groups octets stored)))
  :hints (("Goal" :in-theory (e/d (fn-own-operator-submit-result
                                   fn-own-operator-submit
                                   fn-own-enqueue fn-own-relation)
                                  (fn-own-conns-okp fn-own-view-okp fn-own-operator-decision-of)))))

(defthm fn-own-bp-transit-submit-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation
            (fn-own-bp-transit-submit o cfg peer msgid octets id subject)))
  :hints (("Goal" :in-theory (e/d (fn-own-bp-transit-submit
                                     fn-own-bp-transit-submit-result
                                     fn-own-enqueue fn-own-relation) (fn-own-conns-okp fn-own-view-okp fn-own-conn-okp)))))

; -----------------------------------------------------------------------------
; The operator's submission injects (books/owner.lisp fn-own-operator-submit,
; the (:operator-submit ...) event; host/owner-host.lisp fn-owner-operator-
; submit calls fn-own-operator-submit-result and steps the event, and
; host/native/owner.lisp fnn-owner-control-submit-serialized calls that for
; `fn operator CONFIG post').  Found by the INN lab of 2026-09-22: the verb
; stored its payload with no Path and INN refused it 437.
;
; 1. What is queued is an injection of the submitted octets by this node's
;    injecting agent: its Path line, an Injection-Date, its Injection-Info,
;    then the octets as submitted (fn-inj-reinjectionp), under the Message-ID
;    and newsgroups the command named (the decision as queued, unpacked:
;    fn-own-sub-queued-decision, what the take installs).
; 2. With no usable clock nothing is queued and the answer is a refusal
;    (D10-a).
; 3. A retry of the same octets after the first became durable is the stored
;    article, whatever the clock now reads, so the store answers duplicate.

(defthm fn-own-operator-decision-is-an-injection-of-the-payload
  (implies (fn-inj-injectedp (fn-own-operator-decision cfg clock stored msgid groups octets))
           (let ((d (fn-own-operator-decision cfg clock stored msgid groups octets)))
             (and (equal (fn-inj-decision-msgid d) msgid)
                  (equal (fn-inj-decision-groups d) groups)
                  (fn-inj-reinjectionp (fn-inj-decision-octets d) octets
                                       (fn-inj-config-agent cfg) msgid))))
  :hints (("Goal" :in-theory (e/d (fn-own-operator-decision)
                                  (fn-inj-decide fn-inj-reinjectionp
                                   fn-own-clock-usablep))
           :use ((:instance fn-inj-injected-article-is-a-reinjection-of-its-source
                            (source octets) (config cfg) (observation clock))))))

(defthm fn-own-operator-submission-is-an-injection-of-the-payload
  (implies (equal (fn-own-operator-submit-result o msgid groups octets stored) :submitted)
           (let* ((q (fn-own-queue (fn-own-operator-submit o msgid groups octets stored)))
                  (d (fn-own-sub-queued-decision (car q))))
             (and (equal (len q) 1)
                  (fn-own-control-submissionp (car q))
                  (fn-inj-injectedp d)
                  (equal (fn-inj-decision-msgid d) msgid)
                  (equal (fn-inj-decision-groups d) groups)
                  (fn-inj-reinjectionp (fn-inj-decision-octets d) octets
                                       (fn-inj-config-agent (fn-own-config o))
                                       msgid))))
  :hints (("Goal" :in-theory (e/d (fn-own-operator-submit-result
                                   fn-own-operator-submit fn-own-enqueue
                                   fn-own-operator-decision-of)
                                  (fn-own-operator-decision fn-inj-reinjectionp))
           :use ((:instance fn-own-operator-decision-is-an-injection-of-the-payload
                            (cfg (fn-own-config o)) (clock (fn-own-clock o))
                            (stored stored))))))

(defthm fn-own-operator-submit-without-a-clock-refuses-and-changes-nothing
  (implies (not (and (fn-clock-observationp (fn-own-clock o))
                     (fn-clock-has-wall (fn-own-clock o))))
           (and (equal (fn-own-operator-submit-result o msgid groups octets stored)
                       :refused)
                (equal (fn-own-operator-submit o msgid groups octets stored) o)))
  :hints (("Goal" :in-theory (e/d (fn-own-operator-submit-result
                                   fn-own-operator-submit
                                   fn-own-operator-decision-of
                                   fn-own-operator-decision
                                   fn-own-clock-usablep)
                                  (fn-inj-decide)))))

(defthm fn-own-a-reinjection-is-not-absent
  (implies (fn-inj-reinjectionp stored source agent msgid)
           (not (equal stored :absent)))
  :hints (("Goal" :in-theory (enable fn-inj-reinjectionp)
           :use ((:instance fn-inj-source-of-an-atom-is-nil
                            (stored :absent))))))

(defthm fn-own-operator-retry-resubmits-the-stored-injection
  (implies (and (fn-inj-injectedp (fn-inj-decide octets cfg first))
                (equal (fn-inj-decision-msgid (fn-inj-decide octets cfg first))
                       msgid)
                (equal stored
                       (fn-inj-decision-octets (fn-inj-decide octets cfg first)))
                (fn-clock-observationp later)
                (fn-clock-has-wall later))
           (equal (fn-own-operator-decision cfg later stored msgid groups octets)
                  (fn-inj-make-decision
                   :injected nil msgid groups
                   (fn-inj-decision-octets (fn-inj-decide octets cfg first)))))
  :hints (("Goal" :in-theory (e/d (fn-own-operator-decision fn-own-clock-usablep)
                                  (fn-inj-decide fn-inj-reinjectionp
                                   fn-inj-injected-article-is-a-reinjection-of-its-source
                                   fn-inj-injection-requires-posting-allowed))
           :use ((:instance fn-inj-injected-article-is-a-reinjection-of-its-source
                            (source octets) (config cfg) (observation first))
                 (:instance fn-inj-injection-requires-posting-allowed
                            (source octets) (config cfg) (observation first))
                 (:instance fn-own-a-reinjection-is-not-absent
                            (stored (fn-inj-decision-octets (fn-inj-decide octets cfg first)))
                            (source octets) (agent (fn-inj-config-agent cfg))
                            (msgid msgid)))))
  :rule-classes nil)

; The outcome releases the transaction and empties `inflight'; neither is
; read by the relation, nor is the refused-offer memory (PRF-235), which a
; transit outcome records into.  Both served and control outcomes use this body.
(local
 (defthm fn-own-outcome-body-preserves-relation
   (implies (fn-own-relation o)
            (fn-own-relation
             (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                          (fn-own-next-id o) (fn-own-max-conns o) p
                          (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                          (fn-own-config o) (fn-own-queue o) nil fds (fn-own-node-secret o) rf)))
   :hints (("Goal" :in-theory (enable fn-own-relation)))))

(defthm fn-own-control-outcome-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-control-outcome o word)))
  :hints (("Goal"
           :use ((:instance fn-own-outcome-body-preserves-relation
                            (rf (fn-own-refused o))
                            (p (if (equal (fn-own-pending o)
                                          *fn-own-control-id*)
                                   nil (fn-own-pending o)))
                            (fds (if (equal (fn-own-outcome-completion o word)
                                            :durable)
                                     (fn-own-feed-durable o (fn-own-inflight o))
                                   (fn-own-feeds o)))))
           :in-theory (e/d (fn-own-control-outcome)
                           (fn-own-relation fn-own-outcome-completion
                            fn-own-outcome-body-preserves-relation)))))

(defthm fn-own-bp-transit-outcome-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-bp-transit-outcome o word)))
  :hints (("Goal" :in-theory (disable fn-own-relation
                                      fn-own-control-outcome))))

; The host calls fn-owner-control-outcome (host/owner-host.lisp), whose state
; transition is this function.  It gates acceptance on the same completion
; predicate as served fn-own-outcome.  The host calls
; fn-owner-submission-intent before the store and
; fn-owner-submission-resolution before this state transition.
(defthm fn-own-control-accepted-uses-owner-completion
  (implies (equal (fn-own-control-outcome-result o word) :accepted)
           (equal (fn-own-outcome-completion o word) :durable))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-own-control-outcome-result))))

(defthm fn-own-control-durable-feeds-the-owner-targets
  (implies (and (fn-own-control-submissionp (fn-own-inflight o))
                (equal (fn-own-outcome-completion o word) :durable))
           (equal (fn-own-feeds (fn-own-control-outcome o word))
                  (fn-own-feed-durable o (fn-own-inflight o))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-own-control-outcome))))

; KEYSTONE.  The durable resolution the actual host wrapper writes is a
; commit, and it repeats the exact values of the intent written before the
; store began.  Thus the acceptance-time targets, object identity,
; provenance, configuration generation, transaction id and tick cross both
; crash cuts without Python reconstructing any field.
(local
 (defthm fn-own-feed-resolution-first-matches-intent-first
   (implies (consp names)
            (and (consp (fn-own-feed-resolution-records
                         :feed-commit names msgid identity evidence
                         generation txid tick))
                 (equal
                  (fn-feed-journal-kind
                   (car (fn-own-feed-resolution-records
                         :feed-commit names msgid identity evidence
                         generation txid tick)))
                  :feed-commit)
                 (equal
                  (fn-feed-journal-values
                   (car (fn-own-feed-resolution-records
                         :feed-commit names msgid identity evidence
                         generation txid tick)))
                  (fn-feed-journal-values
                   (car (fn-own-feed-intent-records
                         names msgid identity evidence generation txid
                         tick))))))
   :hints (("Goal" :in-theory (enable fn-own-feed-resolution-records
                                      fn-own-feed-intent-records)))))

(defthm fn-own-control-accepted-resolves-the-exact-intent
  (implies (and (equal (fn-own-outcome-completion o word) :durable)
                (equal (fn-own-submission-intent-result
                        o evidence generation txid) :ready)
                (consp (fn-own-submission-targets o)))
           (let ((intent (fn-own-submission-intent-records
                          o evidence generation txid))
                 (resolution (fn-own-submission-resolution-records
                              o word evidence generation txid)))
             (and (consp resolution)
                  (equal (fn-feed-journal-kind (car resolution)) :feed-commit)
                  (equal (fn-feed-journal-values (car resolution))
                         (fn-feed-journal-values (car intent))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  fn-own-feed-resolution-first-matches-intent-first
                  (names (fn-own-submission-targets o))
                  (msgid (fn-own-sub-msgid (fn-own-inflight o)))
                  (identity
                   (fn-own-feed-intent-id
                    (fn-own-sub-msgid (fn-own-inflight o))
                    (fn-own-sub-octets (fn-own-inflight o))))
                  (tick (fn-own-feed-stamp o))))
           :in-theory (enable fn-own-submission-intent-result
                              fn-own-submission-intent-records
                              fn-own-submission-resolution-records))))

(defthm fn-own-outcome-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-outcome o id word))))
  :hints (("Goal"
           :use ((:instance fn-own-outcome-body-preserves-relation
                            (rf (fn-own-refused o))
                            (p (if (equal (fn-own-pending o) id)
                                   nil (fn-own-pending o)))
                            (fds (if (equal (fn-own-outcome-completion o word)
                                            :durable)
                                     (fn-own-feed-durable o (fn-own-inflight o))
                                     (fn-own-feeds o)))))
           :in-theory (e/d (fn-own-outcome)
                           (fn-own-relation fn-own-outcome-completion
                            fn-served-post-outcome fn-own-advance
                            fn-own-outcome-body-preserves-relation)))))

; -----------------------------------------------------------------------------
; K6: every step, and every finite trace, preserves the relation; the store
; inside keeps fn-snt-relation.

; The five feed arms of `fn-own-step' (`:feeds', `:feed-conn',
; `:feed-replay', `:tick-peer', `:feed-octets') rebuild the owner through
; `fn-own-with-feeds', changing the THIRTEENTH slot and nothing else, and
; `fn-own-relation' above does not read that slot.  One lemma over an
; arbitrary `fds' closes every one of them; without it each arm is its own
; key checkpoint (`Subgoal 47' and its siblings, measured 2026-09-20).
(local
 (defthm fn-own-relation-of-any-feeds
   (implies (fn-own-relation o)
            (fn-own-relation
             (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                          (fn-own-next-id o) (fn-own-max-conns o)
                          (fn-own-pending o) (fn-own-ledger-field o) (fn-own-clock o)
                          (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
                          (fn-own-inflight o) fds (fn-own-node-secret o) rf)))
   :hints (("Goal" :in-theory (enable fn-own-relation)))))

(defthm fn-own-step-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-step o event fn-arena)))
  :hints (("Goal" :in-theory (disable fn-own-relation fn-own-open
                                      fn-own-open-peer fn-own-read
                                      fn-own-read-step fn-own-advance fn-own-close
                                      fn-own-begin fn-own-store-step fn-own-complete
                                      fn-own-reopen fn-own-observe
                                      fn-own-declare-group fn-own-configure
                                      fn-own-take-submission fn-own-outcome
                                      fn-own-control-submit
                                      fn-own-bp-transit-submit
                                      fn-own-bp-transit-outcome
                                      fn-own-operator-submit
                                      fn-own-control-outcome))))

(defthm fn-own-run-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-run o events fn-arena)))
  :hints (("Goal" :induct (fn-own-run o events fn-arena)
           :in-theory (disable fn-own-step))))

(defthm fn-own-run-preserves-store-relation
  (implies (fn-own-relation o)
           (fn-snt-relation (fn-own-store (fn-own-run o events fn-arena))))
  :hints (("Goal" :use fn-own-run-preserves-relation
           :in-theory (e/d (fn-own-relation)
                           (fn-own-run fn-own-run-preserves-relation)))))
