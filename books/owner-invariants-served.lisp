; fn: the root relation (fn-own-start-relation, fn-own-open-observed-start-
; relation) and the served-port keystones: K1 (the pinned prefix), K2 (a
; completion consumed once), K3 (the pinned prefix survives), the reclaim
; floor, K4 (connections bounded) and K5 (a completed POST survives).
; Part 3 of 4 of books/owner-invariants.lisp.

(in-package "ACL2")
(include-book "owner-invariants-step")

; The local prelude of owner-invariants-relation, replayed (local events do not
; cross include-book).
(local (include-book "arithmetic/top" :dir :system))
; fn-inj-injected-article-is-a-reinjection-of-its-source and
; fn-inj-injection-requires-posting-allowed: the operator keystones below.
(local (include-book "injection-invariants"))

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

; Local copy (from owner-invariants-relation; cited by :use below).
; The two conjuncts of the relation that the connection and ledger proofs
; read, so those proofs keep the relation closed (fn-own-durable-reply-names-
; a-durable-record: 1.6 s to 0.6 s with it).
(local
 (defthm fn-own-relation-conns-and-ledger
   (implies (fn-own-relation o)
            (and (fn-own-conns-okp (fn-own-conns o)
                                   (fn-sn-groups (fn-own-store o))
                                   (fn-sn-capacity (fn-own-store o))
                                   (fn-sf-records (fn-sn-files (fn-own-store o))))
                 (fn-own-ledger-durablep (fn-own-ledger o)
                                         (fn-sf-records (fn-sn-files (fn-own-store o))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-own-relation) (theory 'minimal-theory))))))

; -----------------------------------------------------------------------------
; Root: the owner the host starts over the observed reopen satisfies it.

(defthm fn-own-start-relation
  (implies (and (fn-snt-relation store)
                (natp max-conns))
           (fn-own-relation (fn-own-start store max-conns)))
  :hints (("Goal"
           :use ((:instance fn-own-refresh-preserves-relation
                            (o (fn-own-make store
                                            (let* ((prefix
                                                    (fn-own-prefix-archive
                                                     (fn-sn-groups store)
                                                     (fn-sn-capacity store)
                                                     (fn-sf-records
                                                      (fn-sn-files store))
                                                     0 0))
                                                   (archive (fn-ctl-visible-state
                                                             prefix nil nil)))
                                              (fn-own-view-make-visible
                                               0 0 archive nil
                                               (fn-midx-build
                                                (fn-state-articles archive))
                                               (fn-gidx-build
                                                (fn-state-articles archive))
                                               nil (fn-state-articles prefix)
                                               (fn-ctl-subseq-diff
                                                (fn-state-articles prefix)
                                                (fn-state-articles archive))
                                               nil))
                                            nil 0 max-conns nil nil nil nil
                                            nil nil nil nil nil nil))))
           :in-theory (e/d (fn-own-relation fn-midx-correspondencep
                            fn-gidx-build)
                           (fn-own-view-make-group-indexed
                            fn-own-refresh-preserves-relation fn-own-refresh
                            fn-own-prefix-archive)))))

; The owner started over the state fn-sn-open-observed returned for the
; image on disk.  host/owner-host.lisp fn-owner-recover starts it over
; fn-cpo-open-observed's state instead, which this theorem does not name
; (fn-orec-recover-installs-ocl-relation, books/owner-recover-ocl.lisp, is
; over the called open).
(defthm fn-own-open-observed-start-relation
  (implies (and (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
                (natp max-conns))
           (fn-own-relation
            (fn-own-start
             (fn-sn-open-state (fn-sn-open-observed groups capacity frontier records))
             max-conns)))
  :hints (("Goal" :use (fn-sn-open-observed-success-has-live-history-relation
                        (:instance fn-own-start-relation
                                   (store (fn-sn-open-state
                                           (fn-sn-open-observed groups capacity
                                                                frontier records)))))
           :in-theory (disable fn-own-start fn-own-start-relation))))

; -----------------------------------------------------------------------------
; K1, served port: one socket read of a connection is one fn-served-step over
; the connection's wire and session and the acceptance projection of
; fn-sf-replay-node over the first `version` durable records, advanced to the
; pinned frontier, with the connection's article list in place of the
; projection's (C3: the visible list of the view it pinned, which withdrew
; targets; fn-own-conn-serves-a-projection below says that list is a
; subsequence of the prefix's and nothing else of the state differs).  The
; effects the host writes are exactly this call's.

; KEYSTONE (C3, K1 restated).  A connection serves a withdrawal projection
; of its pinned prefix: the prefix's acceptance state with a subsequence of
; its articles (nothing added, nothing reordered, every number and
; watermark the prefix's own).  The view it pinned is exactly the visible
; state of that prefix under the records it carried (fn-own-view-okp).
(defthm fn-own-conn-serves-a-projection
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o)))
           (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
                  (s (fn-own-store o))
                  (p (fn-node-acceptance
                      (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                         (fn-own-take (fn-own-conn-version conn)
                                                      (fn-sf-records (fn-sn-files s)))
                                         (fn-own-conn-frontier conn)))))
             (and (equal (fn-own-conn-archive conn)
                         (fn-ctl-visible-state-of
                          p (fn-state-articles (fn-own-conn-archive conn))))
                  (fn-ctl-subseqp (fn-state-articles (fn-own-conn-archive conn))
                                  (fn-state-articles p)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-relation fn-ctl-projectionp)
                           (fn-own-conn-boundedp fn-own-find-conn-okp)))))

(defthm fn-own-read-is-served-step-on-pinned-prefix
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o)))
           (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
                  (s (fn-own-store o)))
             (equal (car (fn-own-read o id octets))
                    (fn-served-result-effects
                     (fn-served-step
                      (fn-served-make-conn-live
                       (fn-own-conn-wire conn)
                       (fn-own-conn-live-session o conn)
                       (fn-ctl-visible-state-of
                        (fn-node-acceptance
                         (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                           (fn-own-take (fn-own-conn-version conn)
                                                        (fn-sf-records (fn-sn-files s)))
                                           (fn-own-conn-frontier conn)))
                        (fn-state-articles (fn-own-conn-archive conn)))
                       (fn-own-conn-config conn)
                       (fn-own-conn-observation conn)
                       (fn-own-clock o)
                       (fn-own-conn-verdicts conn)
                       (fn-own-conn-index conn)
                       (fn-own-conn-group-index conn) (fn-own-conn-control conn)
                       (fn-served-pinned-make (fn-own-conn-version conn)
                                              (fn-own-conn-frontier conn) nil)
                       (fn-own-view-live (fn-own-view o)))
                      octets)))))
  :hints (("Goal"
           :use (fn-own-conn-serves-a-projection
                 fn-own-relation-conns-and-ledger
                 (:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d ()
                           (fn-own-relation fn-own-conns-okp fn-own-find-conn
                            fn-own-conn-boundedp fn-own-find-conn-okp)))))

(defthm fn-own-read-is-served-step-on-pinned-prefix-after-any-trace
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns (fn-own-run o events))))
           (let* ((final (fn-own-run o events))
                  (conn (fn-own-find-conn id (fn-own-conns final)))
                  (s (fn-own-store final)))
             (equal (car (fn-own-read final id octets))
                    (fn-served-result-effects
                     (fn-served-step
                      (fn-served-make-conn-live
                       (fn-own-conn-wire conn)
                       (fn-own-conn-live-session final conn)
                       (fn-ctl-visible-state-of
                        (fn-node-acceptance
                         (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                           (fn-own-take (fn-own-conn-version conn)
                                                        (fn-sf-records (fn-sn-files s)))
                                           (fn-own-conn-frontier conn)))
                        (fn-state-articles (fn-own-conn-archive conn)))
                       (fn-own-conn-config conn)
                       (fn-own-conn-observation conn)
                       (fn-own-clock final)
                       (fn-own-conn-verdicts conn)
                       (fn-own-conn-index conn)
                       (fn-own-conn-group-index conn) (fn-own-conn-control conn)
                       (fn-served-pinned-make (fn-own-conn-version conn)
                                              (fn-own-conn-frontier conn) nil)
                       (fn-own-view-live (fn-own-view final)))
                      octets)))))
  :hints (("Goal" :use (fn-own-run-preserves-relation
                        (:instance fn-own-read-is-served-step-on-pinned-prefix
                                   (o (fn-own-run o events))))
           :in-theory (disable fn-own-run fn-own-read fn-own-relation
                               fn-own-run-preserves-relation
                               fn-own-read-is-served-step-on-pinned-prefix))))

; -----------------------------------------------------------------------------
; K1, per event: every reader sees exactly the replay of the record prefix at
; its pinned version.  The effects of one framed event are those of
; fn-served-dispatch (the byte fold's step: fn-nntp-post-step with the
; article-mode switch) over the connection's wire, session, config and
; observation and the acceptance projection of fn-sf-replay-node over the
; first `version` durable records, advanced to the pinned frontier, with the
; connection's (visible) article list in place of the projection's.

(defthm fn-own-reader-sees-pinned-prefix-replay
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o)))
           (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
                  (s (fn-own-store o)))
             (equal (car (fn-own-read-step o id event))
                    (fn-served-result-effects
                     (fn-served-dispatch
                      (fn-served-make-conn-live
                       (fn-own-conn-wire conn)
                       (fn-own-conn-session conn)
                       (fn-ctl-visible-state-of
                        (fn-node-acceptance
                         (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                           (fn-own-take (fn-own-conn-version conn)
                                                        (fn-sf-records (fn-sn-files s)))
                                           (fn-own-conn-frontier conn)))
                        (fn-state-articles (fn-own-conn-archive conn)))
                       (fn-own-conn-config conn)
                       (fn-own-conn-observation conn)
                       (fn-own-clock o)
                       (fn-own-conn-verdicts conn)
                       (fn-own-conn-index conn)
                       (fn-own-conn-group-index conn) (fn-own-conn-control conn)
                       (fn-served-pinned-make (fn-own-conn-version conn)
                                              (fn-own-conn-frontier conn) nil)
                       (fn-own-view-live (fn-own-view o)))
                      event)))))
  :hints (("Goal"
           :use (fn-own-conn-serves-a-projection
                 fn-own-relation-conns-and-ledger
                 (:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d ()
                           (fn-own-relation fn-own-conns-okp
                            fn-own-conn-boundedp fn-own-find-conn-okp)))))

(defthm fn-own-reader-sees-pinned-prefix-replay-after-any-trace
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns (fn-own-run o events))))
           (let* ((final (fn-own-run o events))
                  (conn (fn-own-find-conn id (fn-own-conns final)))
                  (s (fn-own-store final)))
             (equal (car (fn-own-read-step final id event))
                    (fn-served-result-effects
                     (fn-served-dispatch
                      (fn-served-make-conn-live
                       (fn-own-conn-wire conn)
                       (fn-own-conn-session conn)
                       (fn-ctl-visible-state-of
                        (fn-node-acceptance
                         (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                           (fn-own-take (fn-own-conn-version conn)
                                                        (fn-sf-records (fn-sn-files s)))
                                           (fn-own-conn-frontier conn)))
                        (fn-state-articles (fn-own-conn-archive conn)))
                       (fn-own-conn-config conn)
                       (fn-own-conn-observation conn)
                       (fn-own-clock final)
                       (fn-own-conn-verdicts conn)
                       (fn-own-conn-index conn)
                       (fn-own-conn-group-index conn) (fn-own-conn-control conn)
                       (fn-served-pinned-make (fn-own-conn-version conn)
                                              (fn-own-conn-frontier conn) nil)
                       (fn-own-view-live (fn-own-view final)))
                      event)))))
  :hints (("Goal" :use (fn-own-run-preserves-relation
                        (:instance fn-own-reader-sees-pinned-prefix-replay
                                   (o (fn-own-run o events))))
           :in-theory (disable fn-own-run fn-own-read-step fn-own-relation
                               fn-own-run-preserves-relation
                               fn-own-reader-sees-pinned-prefix-replay))))

; -----------------------------------------------------------------------------
; K2: a completion is consumed once.  The second application of the owner's
; completion is the identity on the whole owner: the consumed generation is
; gone from the kernel (fn-snt-finish-image puts it at :ready), so the ledger
; cannot grow twice for one durable record.  No hypothesis is needed.

(defthm fn-own-complete-ledger-is-exact-pair
  (and (implies (fn-sn-completion-enabledp (fn-own-store o))
                (and (equal (fn-own-ledger (fn-own-complete o))
                            (append (fn-own-ledger o)
                                    (list (fn-sf-completion (fn-sn-files (fn-own-store o))))))
                     (equal (fn-own-store (fn-own-complete o))
                            (fn-sn-finish (fn-own-store o)))
                     (null (fn-own-pending (fn-own-complete o)))))
       (implies (not (fn-sn-completion-enabledp (fn-own-store o)))
                (equal (fn-own-complete o) o)))
  :hints (("Goal" :in-theory (disable fn-own-refresh))))

(defthm fn-own-completion-consumed-once
  (equal (fn-own-complete (fn-own-complete o))
         (fn-own-complete o))
  :hints (("Goal"
           :use ((:instance fn-snt-finish-image (s (fn-own-store o)))
                 (:instance fn-own-completion-needs-completing-phase
                            (s (fn-sn-finish (fn-own-store o))))
                 fn-own-complete-ledger-is-exact-pair
                 (:instance fn-own-complete-ledger-is-exact-pair
                            (o (fn-own-complete o))))
           :in-theory (disable fn-own-complete fn-snt-finish-image
                               fn-own-completion-needs-completing-phase
                               fn-own-complete-ledger-is-exact-pair))))

; -----------------------------------------------------------------------------
; K3: a pinned version is never reclaimed while pinned.  Durable records only
; grow along owner traces, so the prefix a connection pinned is exactly
; present after any finite trace.  The reclaim floor is the lowest pin.

; The connection and POST events never touch the store, the bound or the
; ledger; the trace lemmas below read this instead of opening the served
; step, the dispatcher and the outcome renderer inside each event.
; A read finishes, and an outcome advances, through these two; each keeps
; the three fields, so the event theorem below keeps both closed.
(local
 (defthm fn-own-finish-read-keeps-store-bound-and-ledger
   (let ((next (cdr (fn-own-finish-read o conn result))))
     (and (equal (fn-own-store next) (fn-own-store o))
          (equal (fn-own-max-conns next) (fn-own-max-conns o))
          (equal (fn-own-ledger next) (fn-own-ledger o))))
   :hints (("Goal" :in-theory (e/d (fn-own-finish-read fn-own-set-conns
                                    fn-own-enqueue)
                                   (fn-own-make fn-own-conn-boundedp
                                    fn-own-replace-conn fn-own-remove-conn))))))

(local
 (defthm fn-own-advance-keeps-store-bound-and-ledger
   (and (equal (fn-own-store (fn-own-advance o id)) (fn-own-store o))
        (equal (fn-own-max-conns (fn-own-advance o id)) (fn-own-max-conns o))
        (equal (fn-own-ledger (fn-own-advance o id)) (fn-own-ledger o)))
   :hints (("Goal" :in-theory (disable fn-served-step fn-served-dispatch
                                       fn-own-conn-boundedp fn-own-find-conn
                                       fn-own-replace-conn fn-own-feed-enqueue-all
                                       fn-own-feed-targets)))))

(defthm fn-own-connection-events-keep-store-bound-and-ledger
  (and (equal (fn-own-store (cdr (fn-own-open o acfg))) (fn-own-store o))
       (equal (fn-own-max-conns (cdr (fn-own-open o acfg))) (fn-own-max-conns o))
       (equal (fn-own-ledger (cdr (fn-own-open o acfg))) (fn-own-ledger o))
       (equal (fn-own-store (cdr (fn-own-read o id octets))) (fn-own-store o))
       (equal (fn-own-max-conns (cdr (fn-own-read o id octets))) (fn-own-max-conns o))
       (equal (fn-own-ledger (cdr (fn-own-read o id octets))) (fn-own-ledger o))
       (equal (fn-own-store (cdr (fn-own-read-step o id event))) (fn-own-store o))
       (equal (fn-own-max-conns (cdr (fn-own-read-step o id event))) (fn-own-max-conns o))
       (equal (fn-own-ledger (cdr (fn-own-read-step o id event))) (fn-own-ledger o))
       (equal (fn-own-store (fn-own-advance o id)) (fn-own-store o))
       (equal (fn-own-max-conns (fn-own-advance o id)) (fn-own-max-conns o))
       (equal (fn-own-ledger (fn-own-advance o id)) (fn-own-ledger o))
       (equal (fn-own-store (fn-own-close o id)) (fn-own-store o))
       (equal (fn-own-max-conns (fn-own-close o id)) (fn-own-max-conns o))
       (equal (fn-own-ledger (fn-own-close o id)) (fn-own-ledger o))
       (equal (fn-own-store (fn-own-begin o id)) (fn-own-store o))
       (equal (fn-own-max-conns (fn-own-begin o id)) (fn-own-max-conns o))
       (equal (fn-own-ledger (fn-own-begin o id)) (fn-own-ledger o))
       (equal (fn-own-store (fn-own-observe o obs)) (fn-own-store o))
       (equal (fn-own-max-conns (fn-own-observe o obs)) (fn-own-max-conns o))
       (equal (fn-own-ledger (fn-own-observe o obs)) (fn-own-ledger o))
       (equal (fn-own-store (fn-own-declare-group o name)) (fn-own-store o))
       (equal (fn-own-max-conns (fn-own-declare-group o name)) (fn-own-max-conns o))
       (equal (fn-own-ledger (fn-own-declare-group o name)) (fn-own-ledger o))
       (equal (fn-own-store (fn-own-configure o config)) (fn-own-store o))
       (equal (fn-own-max-conns (fn-own-configure o config)) (fn-own-max-conns o))
       (equal (fn-own-ledger (fn-own-configure o config)) (fn-own-ledger o))
       (equal (fn-own-store (fn-own-take-submission o)) (fn-own-store o))
       (equal (fn-own-max-conns (fn-own-take-submission o)) (fn-own-max-conns o))
       (equal (fn-own-ledger (fn-own-take-submission o)) (fn-own-ledger o))
       (equal (fn-own-store (cdr (fn-own-outcome o id word))) (fn-own-store o))
       (equal (fn-own-max-conns (cdr (fn-own-outcome o id word))) (fn-own-max-conns o))
       (equal (fn-own-ledger (cdr (fn-own-outcome o id word))) (fn-own-ledger o)))
  ; which connection a read finds, and the feed queues an advance fills,
  ; never reach the store, the capacity or the ledger
  :hints (("Goal" :in-theory (disable fn-served-step fn-served-dispatch
                                      fn-served-post-outcome fn-served-open
                                      fn-own-conn-boundedp fn-own-outcome-completion
                                      fn-own-find-conn-id fn-own-find-conn
                                      fn-own-replace-conn fn-own-feed-enqueue-all
                                      fn-own-finish-read fn-own-advance))))

; Only the :store, :complete and :reopen events move the store; every other
; event leaves it as it was, so the prefix is reflexive there and the
; store-changing lemmas are needed only for those three kinds.
(local
 (defthm fn-own-step-store-of-other-events
   (implies (not (member-equal (car event) '(:store :complete :reopen)))
            (equal (fn-own-store (fn-own-step o event)) (fn-own-store o)))
   :hints (("Goal" :in-theory (e/d (fn-own-step)
                                   (fn-served-step fn-served-dispatch
                                    fn-served-post-outcome fn-served-open
                                    fn-own-conn-boundedp fn-own-outcome-completion
                                    fn-own-find-conn-id fn-own-find-conn
                                    ; the connection events: their own theorem above
                                    fn-own-open fn-own-read fn-own-read-step
                                    fn-own-advance fn-own-close fn-own-begin
                                    fn-own-observe fn-own-declare-group
                                    fn-own-configure fn-own-take-submission
                                    fn-own-outcome
                                    fn-own-feed-enqueue-all fn-article-parse
                                    fn-own-feed-inflight-msgid fn-feed-state-inflightp
                                    fn-inj-generated-identity-is-the-clock-identity
                                    fn-inj-supplied-message-id-is-retained-exactly))))))

(local
 (defthm fn-own-step-of-store-changing-events
   (and (implies (equal (car event) :store)
                 (equal (fn-own-step o event) (fn-own-store-step o (cadr event))))
        (implies (equal (car event) :complete)
                 (equal (fn-own-step o event) (fn-own-complete o)))
        (implies (equal (car event) :reopen)
                 (equal (fn-own-step o event)
                        (fn-own-reopen o (cadr event) (caddr event)))))
   :hints (("Goal" :in-theory '(fn-own-step)))))

(defthm fn-own-step-records-prefix
  (implies (fn-own-relation o)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store o)))
                          (fn-sf-records (fn-sn-files (fn-own-store (fn-own-step o event))))))
  :hints (("Goal"
           :cases ((equal (car event) :store) (equal (car event) :complete)
                   (equal (car event) :reopen))
           :use ((:instance fn-own-snrt-step-records-prefix
                            (s (fn-own-store o)) (event (cadr event)))
                 (:instance fn-snt-finish-keeps-records (s (fn-own-store o)))
                 (:instance fn-own-related-records-true-list (s (fn-own-store o)))
                 (:instance fn-sf-prefixp-reflexive
                            (xs (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-own-crash-image-extends-records
                            (files (fn-sn-files (fn-own-store o)))
                            (frontier (cadr event)) (records (caddr event)))
                 (:instance fn-sn-open-observed-success-exact-history
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (frontier (cadr event)) (records (caddr event))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-step fn-own-snrt-step-records-prefix fn-snt-finish-keeps-records
                            fn-own-related-records-true-list fn-sf-prefixp-reflexive
                            fn-own-crash-image-extends-records
                            fn-sn-open-observed-success-exact-history
                            fn-own-refresh fn-own-conn-boundedp
                            fn-own-open fn-own-read fn-own-read-step fn-own-advance
                            fn-own-close fn-own-begin fn-own-observe
                            fn-own-declare-group fn-own-configure
                            fn-own-take-submission fn-own-outcome
                            ;; the reflexive prefix in the hypotheses would
                            ;; make each of these rewrite a term to itself
                            fn-own-take-of-prefix fn-own-prefix-archive-of-prefix
                            fn-own-conns-okp-of-prefix fn-own-view-okp-of-prefix
                            fn-own-ledger-durablep-of-prefix
                            fn-own-conn-okp fn-own-view-okp
                            ;; the operator's and the feeds' admission tests
                            ;; parse the article; the store is the same on
                            ;; both of their branches
                            fn-own-operator-decision fn-own-operator-decision-of
                            fn-own-feed-inflight-msgid fn-feed-state-inflightp
                            fn-article-parse fn-cp-idp
                            fn-own-ledger-durablep fn-own-facts-okp
                            fn-cbor-octet-listp
                            fn-wire-next-loop-event-needs-input
                            fn-wire-next-event-needs-input)))))

(defthm fn-own-run-records-prefix
  (implies (fn-own-relation o)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store o)))
                          (fn-sf-records (fn-sn-files (fn-own-store (fn-own-run o events))))))
  :hints (("Goal" :induct (fn-own-run o events)
           :in-theory (e/d (fn-sf-prefixp-reflexive) (fn-own-step fn-own-relation)))
          ("Subgoal *1/1"
           :use (fn-own-step-preserves-relation
                 (:instance fn-own-step-records-prefix (event (car events)))
                 (:instance fn-own-related-records-true-list (s (fn-own-store o)))
                 (:instance fn-sf-prefixp-transitive
                            (xs (fn-sf-records (fn-sn-files (fn-own-store o))))
                            (ys (fn-sf-records (fn-sn-files (fn-own-store
                                                             (fn-own-step o (car events))))))
                            (zs (fn-sf-records (fn-sn-files (fn-own-store
                                                             (fn-own-run (fn-own-step o (car events))
                                                                         (cdr events)))))))))))

(defthm fn-own-pinned-prefix-survives-any-trace
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o)))
           (let ((version (fn-own-conn-version (fn-own-find-conn id (fn-own-conns o)))))
             (equal (fn-own-take version
                                 (fn-sf-records (fn-sn-files (fn-own-store (fn-own-run o events)))))
                    (fn-own-take version
                                 (fn-sf-records (fn-sn-files (fn-own-store o)))))))
  :hints (("Goal"
           :use (fn-own-run-records-prefix
                 (:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-run fn-own-run-records-prefix fn-own-find-conn-okp
                            fn-own-conn-boundedp)))))

(defthm fn-own-min-pinned-below-floor
  (<= (fn-own-min-pinned conns floor) (nfix floor))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-own-min-pinned conns floor))))

(defthm fn-own-min-pinned-below-found
  (implies (and (fn-own-conns-okp conns groups capacity records)
                (fn-own-find-conn id conns))
           (<= (fn-own-min-pinned conns floor)
               (fn-own-conn-version (fn-own-find-conn id conns))))
  :hints (("Goal" :induct (fn-own-min-pinned conns floor)
           :in-theory (disable fn-own-conn-boundedp fn-own-prefix-archive))))

(defthm fn-own-reclaim-floor-below-every-pin
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o)))
           (<= (fn-own-reclaim-floor o)
               (fn-own-conn-version (fn-own-find-conn id (fn-own-conns o)))))
  :hints (("Goal" :in-theory (e/d (fn-own-relation)
                                  (fn-own-conn-boundedp fn-own-min-pinned
                                   fn-own-prefix-archive)))))

; -----------------------------------------------------------------------------
; K4: the number of connections and each connection's retained state are
; bounded by configuration after any finite trace.

(defun fn-own-conns-boundedp (conns groups)
  (if (consp conns)
      (and (fn-own-conn-boundedp (car conns) groups)
           (fn-own-conns-boundedp (cdr conns) groups))
    (null conns)))

(defthm fn-own-conns-okp-are-bounded
  (implies (fn-own-conns-okp conns groups capacity records)
           (fn-own-conns-boundedp conns groups))
  :hints (("Goal" :induct (fn-own-conns-okp conns groups capacity records)
           :in-theory (disable fn-own-conn-boundedp))))

(defthm fn-own-step-keeps-max-conns
  (equal (fn-own-max-conns (fn-own-step o event)) (fn-own-max-conns o))
  :hints (("Goal" :in-theory (disable fn-own-refresh fn-own-conn-boundedp
                                      fn-own-open fn-own-read fn-own-read-step
                                      fn-own-advance fn-own-close fn-own-begin
                                      fn-own-observe fn-own-declare-group
                                      fn-own-configure fn-own-take-submission
                                      fn-own-outcome))))

(defthm fn-own-run-keeps-max-conns
  (equal (fn-own-max-conns (fn-own-run o events)) (fn-own-max-conns o))
  :hints (("Goal" :induct (fn-own-run o events)
           :in-theory (disable fn-own-step))))

(defthm fn-own-connections-bounded-after-any-trace
  (implies (fn-own-relation o)
           (let ((final (fn-own-run o events)))
             (and (<= (len (fn-own-conns final)) (fn-own-max-conns o))
                  (fn-own-conns-boundedp (fn-own-conns final)
                                         (fn-sn-groups (fn-own-store final))))))
  :hints (("Goal" :use (fn-own-run-preserves-relation fn-own-run-keeps-max-conns)
           :in-theory (e/d (fn-own-relation)
                           (fn-own-run fn-own-run-preserves-relation
                            fn-own-run-keeps-max-conns fn-own-conn-boundedp)))))

; -----------------------------------------------------------------------------
; K5: post-then-disconnect durability.  A pair the owner consumed as a
; completion has a record in the durable history after any finite trace,
; whatever happened to the connection that posted it: close, crash,
; reopen through fn-sn-open-observed, more posts.

(defthm fn-own-step-ledger-grows
  (implies (member-equal pair (fn-own-ledger o))
           (member-equal pair (fn-own-ledger (fn-own-step o event))))
  :hints (("Goal" :in-theory (disable fn-own-refresh fn-own-conn-boundedp
                                      fn-own-open fn-own-read fn-own-read-step
                                      fn-own-advance fn-own-close fn-own-begin
                                      fn-own-observe fn-own-declare-group
                                      fn-own-configure fn-own-take-submission
                                      fn-own-outcome))))

(defthm fn-own-run-ledger-grows
  (implies (member-equal pair (fn-own-ledger o))
           (member-equal pair (fn-own-ledger (fn-own-run o events))))
  :hints (("Goal" :induct (fn-own-run o events)
           :in-theory (disable fn-own-step))))

(defthm fn-own-completed-post-survives-close-and-any-trace
  (implies (and (fn-own-relation o)
                (member-equal pair (fn-own-ledger o)))
           (fn-sf-record-has-pairp
            pair (fn-sf-records (fn-sn-files (fn-own-store (fn-own-run o events))))))
  :hints (("Goal" :use (fn-own-run-preserves-relation fn-own-run-ledger-grows
                        (:instance fn-own-ledger-durablep-member
                                   (ledger (fn-own-ledger (fn-own-run o events)))
                                   (records (fn-sf-records
                                             (fn-sn-files (fn-own-store (fn-own-run o events)))))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-run fn-own-run-preserves-relation
                            fn-own-run-ledger-grows fn-own-ledger-durablep-member
                            fn-own-conn-boundedp)))))
