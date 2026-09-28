; fn: the owner relation fn-own-relation, its list vocabulary, the store
; transitions it rests on, and its preservation by refresh, open and
; open-peer.  Part 1 of 4 of books/owner-invariants.lisp (the umbrella names
; the keystones).

(in-package "ACL2")
(include-book "owner")
(local (include-book "arithmetic/top" :dir :system))
; fn-inj-injected-article-is-a-reinjection-of-its-source and
; fn-inj-injection-requires-posting-allowed: the operator keystones below.
(local (include-book "injection-invariants"))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-gidx-refresh-is-build))))

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

; -----------------------------------------------------------------------------
; Prefixes of the durable history

(defthm fn-own-take-of-len
  (implies (true-listp xs)
           (equal (fn-own-take (len xs) xs) xs))
  :hints (("Goal" :induct (true-listp xs))))

(defthm fn-own-prefixp-len
  (implies (fn-sf-prefixp xs ys)
           (<= (len xs) (len ys)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-sf-prefixp xs ys)
           :in-theory (enable fn-sf-prefixp))))

(defun fn-own-take-prefix-induct (n xs ys)
  (if (and (posp n) (consp xs) (consp ys))
      (fn-own-take-prefix-induct (1- n) (cdr xs) (cdr ys))
    (list n xs ys)))

(defthm fn-own-take-of-prefix
  (implies (and (fn-sf-prefixp xs ys)
                (<= n (len xs)))
           (equal (fn-own-take n ys) (fn-own-take n xs)))
  :hints (("Goal" :induct (fn-own-take-prefix-induct n xs ys)
           :in-theory (enable fn-sf-prefixp))))

(defthm fn-own-prefix-archive-of-prefix
  (implies (and (fn-sf-prefixp xs ys)
                (<= v (len xs)))
           (equal (fn-own-prefix-archive groups capacity ys v frontier)
                  (fn-own-prefix-archive groups capacity xs v frontier))))

(defthm fn-own-has-pairp-of-prefix
  (implies (and (fn-sf-prefixp xs ys)
                (fn-sf-record-has-pairp pair xs))
           (fn-sf-record-has-pairp pair ys))
  :hints (("Goal" :induct (fn-sf-prefixp xs ys)
           :in-theory (enable fn-sf-prefixp fn-sf-record-has-pairp))))

(defthm fn-own-member-of-append-last
  (member-equal x (append l (list x))))

(defthm fn-own-member-of-append-left
  (implies (member-equal x l)
           (member-equal x (append l m)))
  :hints (("Goal" :induct (member-equal x l))))

; -----------------------------------------------------------------------------
; The owner relation (proof vocabulary; never executed)

; A connection's control pin (control-c3e) is its view's: the pinned archive
; serves RAW's visible list under the pinned records, and W is the rest of
; RAW (`fn-ctl-subseq-diff', which is `fn-ctl-withdrawn-articles' by
; `fn-ctl-subseq-diff-of-filter').  RAW is the connection's pinned prefix.
(defun fn-own-control-okp (control archive verdicts raw)
  (declare (xargs :guard t))
  (or (null control)
      (and (equal (fn-state-articles archive)
                  (fn-ctl-visible-articles raw (fn-ctl-pin-ws control) verdicts))
           (equal (fn-ctl-pin-withdrawn control)
                  (fn-ctl-subseq-diff raw (fn-state-articles archive))))))

(defun fn-own-conn-okp (conn groups capacity records)
  (declare (xargs :guard t))
  (and (fn-own-conn-shapep conn)
       (natp (fn-own-conn-id conn))
       (natp (fn-own-conn-version conn))
       (<= (fn-own-conn-version conn) (len records))
       (natp (fn-own-conn-frontier conn))
       (fn-ctl-projectionp (fn-own-conn-archive conn)
                           (fn-own-prefix-archive groups capacity records
                                                  (fn-own-conn-version conn)
                                                  (fn-own-conn-frontier conn)))
       (fn-midx-correspondencep
        (fn-own-conn-index conn)
        (fn-state-articles (fn-own-conn-archive conn)))
       (implies (fn-own-conn-group-index conn)
                (equal (fn-own-conn-group-index conn)
                       (fn-gidx-build
                        (fn-state-articles (fn-own-conn-archive conn)))))
       (fn-own-control-okp (fn-own-conn-control conn)
                           (fn-own-conn-archive conn)
                           (fn-own-conn-verdicts conn)
                           (fn-state-articles
                            (fn-own-prefix-archive groups capacity records
                                                   (fn-own-conn-version conn)
                                                   (fn-own-conn-frontier conn))))
       (fn-own-conn-boundedp conn groups)))

(defun fn-own-conns-okp (conns groups capacity records)
  (declare (xargs :guard t))
  (if (consp conns)
      (and (fn-own-conn-okp (car conns) groups capacity records)
           (fn-own-conns-okp (cdr conns) groups capacity records))
    (null conns)))

(defun fn-own-view-okp (view groups capacity records)
  (declare (xargs :guard t))
  (and (fn-own-view-shapep view)
       (natp (fn-own-view-version view))
       (<= (fn-own-view-version view) (len records))
       (natp (fn-own-view-frontier view))
       (equal (fn-own-view-archive view)
              (fn-ctl-visible-state
               (fn-own-prefix-archive groups capacity records
                                      (fn-own-view-version view)
                                      (fn-own-view-frontier view))
               (fn-own-view-withdrawals view)
               (fn-own-view-verdicts view)))
       (equal (fn-own-view-raw view)
              (fn-state-articles
               (fn-own-prefix-archive groups capacity records
                                      (fn-own-view-version view)
                                      (fn-own-view-frontier view))))
       (fn-midx-correspondencep
        (fn-own-view-index view)
        (fn-state-articles (fn-own-view-archive view)))
       (implies (fn-own-view-group-index view)
                (equal (fn-own-view-group-index view)
                       (fn-gidx-build
                        (fn-state-articles (fn-own-view-archive view)))))
       (equal (fn-own-view-withdrawn view)
              (fn-ctl-subseq-diff (fn-own-view-raw view)
                                  (fn-state-articles (fn-own-view-archive view))))))

; The control pin a connection takes from its view at open or advance.
(defthm fn-own-view-control-okp
  (implies (fn-own-view-okp view groups capacity records)
           (fn-own-control-okp (fn-own-view-control view)
                               (fn-own-view-archive view)
                               (fn-own-view-verdicts view)
                               (fn-state-articles
                                (fn-own-prefix-archive
                                 groups capacity records
                                 (fn-own-view-version view)
                                 (fn-own-view-frontier view)))))
  :hints (("Goal" :in-theory (e/d (fn-ctl-visible-state fn-own-control-okp)
                                  (fn-own-prefix-archive fn-ctl-visible-articles
                                   fn-ctl-subseq-diff)))))

(defthm fn-own-view-control-okp-raw
  (implies (fn-own-view-okp view groups capacity records)
           (fn-own-control-okp (fn-own-view-control view)
                               (fn-own-view-archive view)
                               (fn-own-view-verdicts view)
                               (fn-own-view-raw view)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-visible-state fn-own-control-okp)
                                  (fn-own-prefix-archive fn-ctl-visible-articles
                                   fn-ctl-subseq-diff)))))

; The same, stated over the view-okp conjuncts themselves (no free
; variables outside them), which is the shape a relation proof sees once
; fn-own-view-okp has opened.  P is bound by the first hypothesis.
(defthm fn-own-view-control-okp-of-conjuncts
  (implies (and (equal (fn-own-view-archive view)
                       (fn-ctl-visible-state p (fn-own-view-withdrawals view)
                                             (fn-own-view-verdicts view)))
                (equal (fn-own-view-raw view) (fn-state-articles p))
                (equal (fn-own-view-withdrawn view)
                       (fn-ctl-subseq-diff (fn-own-view-raw view)
                                           (fn-state-articles
                                            (fn-own-view-archive view)))))
           (fn-own-control-okp (fn-own-view-control view)
                               (fn-own-view-archive view)
                               (fn-own-view-verdicts view)
                               (fn-own-view-raw view)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-visible-state fn-own-control-okp)
                                  (fn-ctl-visible-articles fn-ctl-subseq-diff)))))

(in-theory (disable fn-own-control-okp))

(defun fn-own-ledger-durablep (ledger records)
  (declare (xargs :guard t))
  (if (consp ledger)
      (and (fn-sf-record-has-pairp (car ledger) records)
           (fn-own-ledger-durablep (cdr ledger) records))
    (null ledger)))

; Connection identifiers are allocated from fn-own-next-id and it only ever
; moves up: fn-own-open and fn-own-open-peer (books/owner.lisp:650, :697) take
; id = (fn-own-next-id o) for the new connection and write (1+ (nfix id)) back.
; So no OPEN connection carries the identifier the next open will take, which
; is what books/owner-config spends: a pin at (fn-own-next-id o) would have to
; be a pin of an open connection at that identifier (fn-ocfg-pins-pin-conns-only)
; and there is none.  The bound was true of every reachable state before this
; conjunct existed -- fn-own-replace-conn rebuilds at (fn-own-conn-id conn),
; fn-own-remove-conn only drops, fn-own-start and fn-own-reopen give conns = nil
; -- it was simply not stated, so nothing about identifier allocation changed.
; The (natp next-id) guard is discharged at the one call site by the
; (natp (fn-own-next-id o)) conjunct that precedes it in the same `and'.
(defun fn-own-ids-below-next-p (conns next-id)
  (declare (xargs :guard (natp next-id)))
  (if (consp conns)
      (and (natp (fn-own-conn-id (car conns)))
           (< (fn-own-conn-id (car conns)) next-id)
           (fn-own-ids-below-next-p (cdr conns) next-id))
    t))

; Guard verified, with fn-snt-relation below it (books/store-node-traces.lisp):
; fn-ocfg-statep (books/owner-config.lisp:191) declares :guard t and calls
; this, so the whole chain owes its guards.  Nothing here runs per operation:
; the relation is proof vocabulary, no transition is guarded by it, and
; fn-served-dispatch does not reach it.
(defun fn-own-relation (o)
  (declare (xargs :guard t))
  (let* ((s (fn-own-store o))
         (groups (fn-sn-groups s))
         (capacity (fn-sn-capacity s))
         (records (fn-sf-records (fn-sn-files s))))
    (and (fn-own-shapep o)
         (fn-snt-relation s)
         (fn-own-view-okp (fn-own-view o) groups capacity records)
         (fn-own-conns-okp (fn-own-conns o) groups capacity records)
         (natp (fn-own-max-conns o))
         (<= (len (fn-own-conns o)) (fn-own-max-conns o))
         (natp (fn-own-next-id o))
         (fn-own-ids-below-next-p (fn-own-conns o) (fn-own-next-id o))
         (fn-own-ledger-durablep (fn-own-ledger o) records)
         (or (null (fn-own-clock o))
             (fn-clock-observationp (fn-own-clock o)))
         (fn-own-facts-okp (fn-own-facts o)))))

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
; Growth of the durable history keeps every pin, the view and the ledger.

(defthm fn-own-conns-okp-of-prefix
  (implies (and (fn-own-conns-okp conns groups capacity xs)
                (fn-sf-prefixp xs ys))
           (fn-own-conns-okp conns groups capacity ys))
  :hints (("Goal" :induct (fn-own-conns-okp conns groups capacity xs))))

(defthm fn-own-view-okp-of-prefix
  (implies (and (fn-own-view-okp view groups capacity xs)
                (fn-sf-prefixp xs ys))
           (fn-own-view-okp view groups capacity ys)))

(defthm fn-own-ledger-durablep-of-prefix
  (implies (and (fn-own-ledger-durablep ledger xs)
                (fn-sf-prefixp xs ys))
           (fn-own-ledger-durablep ledger ys))
  :hints (("Goal" :induct (fn-own-ledger-durablep ledger xs))))

(defthm fn-own-ledger-durablep-append
  (implies (and (fn-own-ledger-durablep ledger records)
                (fn-sf-record-has-pairp pair records))
           (fn-own-ledger-durablep (append ledger (list pair)) records))
  :hints (("Goal" :induct (fn-own-ledger-durablep ledger records))))

(defthm fn-own-ledger-durablep-member
  (implies (and (fn-own-ledger-durablep ledger records)
                (member-equal pair ledger))
           (fn-sf-record-has-pairp pair records))
  :hints (("Goal" :induct (fn-own-ledger-durablep ledger records))))

(defthm fn-own-facts-okp-append
  (implies (and (fn-own-facts-okp facts)
                (fn-own-group-factp fact))
           (fn-own-facts-okp (append facts (list fact))))
  :hints (("Goal" :induct (fn-own-facts-okp facts))))

; -----------------------------------------------------------------------------
; Connection list lemmas

(defthm fn-own-find-conn-okp
  (implies (and (fn-own-conns-okp conns groups capacity records)
                (fn-own-find-conn id conns))
           (fn-own-conn-okp (fn-own-find-conn id conns) groups capacity records))
  :hints (("Goal" :induct (fn-own-find-conn id conns))))

(defthm fn-own-find-conn-id
  (implies (fn-own-find-conn id conns)
           (equal (fn-own-conn-id (fn-own-find-conn id conns)) id))
  :hints (("Goal" :induct (fn-own-find-conn id conns))))

(defthm fn-own-replace-conn-okp
  (implies (and (fn-own-conns-okp conns groups capacity records)
                (fn-own-conn-okp conn groups capacity records))
           (fn-own-conns-okp (fn-own-replace-conn conn conns) groups capacity records))
  ;; Each connection's own okp is a hypothesis or the table's; opening it
  ;; cost 125,000 steps.
  :hints (("Goal" :induct (fn-own-replace-conn conn conns)
           :in-theory (disable fn-own-conn-okp))))

(defthm fn-own-replace-conn-len
  (equal (len (fn-own-replace-conn conn conns)) (len conns))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns))))

(defthm fn-own-remove-conn-okp
  (implies (fn-own-conns-okp conns groups capacity records)
           (fn-own-conns-okp (fn-own-remove-conn id conns) groups capacity records))
  :hints (("Goal" :induct (fn-own-remove-conn id conns))))

(defthm fn-own-remove-conn-len
  (<= (len (fn-own-remove-conn id conns)) (len conns))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-own-remove-conn id conns))))

; The identifier bound over the three list operations.  `-monotone' is the
; only one of the four that is not stated at a fixed bound: it is what the
; two open arms need, where the bound moves from `next-id' to `1+ next-id'
; while the list gains the connection at `next-id'.  It is :rule-classes nil
; and reached by :use, because as a rewrite rule its `n' is free.
(defthm fn-own-ids-below-next-p-monotone
  (implies (and (fn-own-ids-below-next-p conns n)
                (<= n m))
           (fn-own-ids-below-next-p conns m))
  :rule-classes nil
  :hints (("Goal" :induct (fn-own-ids-below-next-p conns n))))

(defthm fn-own-find-conn-id-below-next
  (implies (and (fn-own-ids-below-next-p conns n)
                (fn-own-find-conn id conns))
           (and (natp id) (< id n)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-own-find-conn id conns))))

(defthm fn-own-replace-conn-ids-below-next
  (implies (and (fn-own-ids-below-next-p conns n)
                (natp (fn-own-conn-id conn))
                (< (fn-own-conn-id conn) n))
           (fn-own-ids-below-next-p (fn-own-replace-conn conn conns) n))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns))))

(defthm fn-own-remove-conn-ids-below-next
  (implies (fn-own-ids-below-next-p conns n)
           (fn-own-ids-below-next-p (fn-own-remove-conn id conns) n))
  :hints (("Goal" :induct (fn-own-remove-conn id conns))))

; The open arms: the new connection sits at the old `next-id' and the bound
; becomes one above it.
(defthm fn-own-ids-below-next-p-of-open
  (implies (and (fn-own-ids-below-next-p conns n)
                (natp n)
                (equal (fn-own-conn-id conn) n))
           (fn-own-ids-below-next-p (cons conn conns) (+ 1 n)))
  :hints (("Goal" :use ((:instance fn-own-ids-below-next-p-monotone
                                   (m (+ 1 n)))))))

; -----------------------------------------------------------------------------
; Facts about the embedded store the events need

(defthm fn-own-idle-node-is-replay
  (implies (and (fn-snt-relation s)
                (fn-own-store-idlep s))
           (equal (fn-sn-node s)
                  (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                     (fn-sf-records (fn-sn-files s))
                                     (fn-sf-frontier (fn-sn-files s)))))
  ; This is the idle arm of the relation.  Keep every other arm and its
  ; growing Store recognizers opaque, as in the Store exact-replay lemma.
  :hints (("Goal" :in-theory '(fn-snt-relation fn-own-store-idlep))))

(defthm fn-own-related-records-true-list
  (implies (fn-snt-relation s)
           (true-listp (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :use fn-snt-related-records-true-list)))

(defthm fn-own-related-frontier-natural
  (implies (fn-snt-relation s)
           (natp (fn-sf-frontier (fn-sn-files s))))
  :hints (("Goal" :use (fn-snt-relation-implies-structural-state
                        fn-snt-typed-store-components
                        (:instance fn-snt-typed-frontier-natural
                                   (files (fn-sn-files s)))))))

(defthm fn-own-relation-records-true-list
  (implies (fn-own-relation o)
           (true-listp (fn-sf-records (fn-sn-files (fn-own-store o)))))
  :hints (("Goal" :in-theory (e/d (fn-own-relation) (fn-own-conn-boundedp))
           :use ((:instance fn-own-related-records-true-list (s (fn-own-store o)))))))

; The bridge books/owner-config spends.  A related owner has no OPEN
; connection at the identifier its next open will allocate, so a pin table
; whose domain is exactly the open connections has no pin there either, and
; `fn-ocfg-pin-add' -- which never overwrites -- therefore installs the live
; configuration rather than leaving a stale one.  Exported (it is not in the
; withdrawal below): its left-hand side is the single term
; `(fn-own-find-conn (fn-own-next-id o) (fn-own-conns o))', which no includer
; states by accident.
(defthm fn-own-relation-has-no-connection-at-next-id
  (implies (fn-own-relation o)
           (not (fn-own-find-conn (fn-own-next-id o) (fn-own-conns o))))
  :hints (("Goal" :in-theory (e/d (fn-own-relation) (fn-own-conn-boundedp))
           :use ((:instance fn-own-find-conn-id-below-next
                            (conns (fn-own-conns o))
                            (id (fn-own-next-id o))
                            (n (fn-own-next-id o)))))))

; Every store transition keeps the fixed configuration.
;
; Each transition rebuilds the state through `fn-sn-make-v4' with the old
; state's groups and capacity, or returns the state itself, so the fact is
; one lemma per transition, each opening that transition alone in the
; minimal theory: constructor group and capacity projections for v2/v3/v4
; answer every branch without looking at a test.  The step then dispatches
; with every transition closed.  Stated over the whole step with the
; transitions and `fn-sn-finish' open together, the tests of the finish arms
; (the store-transaction recognizers, the identity step, the retention
; applier) split the goal 734 ways and then again inside each case: 19 122
; subgoals and 35.3 s on the seam run of 2026-09-23
; (planning/evidence/chain-remainder-cost-2026-09-23.md).
(local
 (defthm fn-own-sn-constructors-keep-configuration
   (and (equal (fn-sn-groups (fn-sn-update s files node)) (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-update s files node)) (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-update-indexed s files node index))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-update-indexed s files node index))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-update-accepted s files node index msgid verdict))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-update-accepted s files node index msgid verdict))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-update-replayed s files node index ctx))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-update-replayed s files node index ctx))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-with-consumer s consumer))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-with-consumer s consumer))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-with-topic s topic))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-with-topic s topic))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-with-event-index s event-index))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-with-event-index s event-index))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-advance-identity-next s)) (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-advance-identity-next s)) (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-finish-identity s files record node))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-finish-identity s files record node))
               (fn-sn-capacity s)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-sn-update fn-sn-update-indexed
                              fn-sn-update-accepted fn-sn-update-replayed
                              fn-sn-with-consumer fn-sn-with-topic
                              fn-sn-with-event-index
                              fn-sn-advance-identity-next fn-sn-finish-identity
                              fn-sn-groups-of-fn-sn-make-v2
                              fn-sn-capacity-of-fn-sn-make-v2
                              fn-sn-groups-of-fn-sn-make-v3
                              fn-sn-capacity-of-fn-sn-make-v3
                              fn-sn-groups-of-fn-sn-make-v4
                              fn-sn-capacity-of-fn-sn-make-v4
                              fn-sn-fields-of-fn-sn-make-v6)
                            (theory 'minimal-theory))))))

(local
 (defthm fn-own-sn-transitions-keep-configuration
   (and (equal (fn-sn-groups (fn-sn-prepare s record)) (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-prepare s record)) (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-io s operation result)) (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-io s operation result)) (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-finish s)) (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-finish s)) (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-crash s frontier-choice record-choice))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-crash s frontier-choice record-choice))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-recover s)) (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-recover s)) (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-prepare-retention s event)) (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-prepare-retention s event))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-prepare-identity s event)) (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-prepare-identity s event))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-prepare-consumer s event))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-prepare-consumer s event))
               (fn-sn-capacity s))
        (equal (fn-sn-groups (fn-sn-prepare-topic s event))
               (fn-sn-groups s))
        (equal (fn-sn-capacity (fn-sn-prepare-topic s event))
               (fn-sn-capacity s)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-sn-prepare fn-sn-io fn-sn-finish fn-sn-crash
                              fn-sn-recover fn-sn-prepare-retention
                              fn-sn-prepare-identity fn-sn-prepare-consumer
                              fn-sn-prepare-topic
                              fn-own-sn-constructors-keep-configuration)
                            (theory 'minimal-theory))))))

(defthm fn-own-snrt-step-keeps-configuration
  (and (equal (fn-sn-groups (fn-snrt-step s event)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-snrt-step s event)) (fn-sn-capacity s)))
  :hints (("Goal" :in-theory
           (union-theories '(fn-snrt-step fn-snt-step
                             fn-own-sn-transitions-keep-configuration
                             fn-sn-refuse-reservation-preserves-configuration
                             fn-sn-known-abort-preserves-configuration)
                           (theory 'minimal-theory)))))

(defthm fn-own-snrt-step-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-snrt-step s event)))
  :hints (("Goal" :use fn-snrt-step-preserves-relation)))

(defthm fn-own-snrt-step-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snrt-step s event)))))
  :hints (("Goal" :use fn-snrt-step-records-prefix)))

; The consumed completion names a record of the durable history: after the
; actual fn-sn-finish it is an acknowledged pair, and every acknowledged pair
; has a record (fn-sf-state-success-member-has-record).
(defthm fn-own-completion-pair-has-record
  (implies (and (fn-sn-statep s)
                (fn-sn-completion-enabledp s))
           (fn-sf-record-has-pairp (fn-sf-completion (fn-sn-files s))
                                   (fn-sf-records (fn-sn-files s))))
  :hints (("Goal"
           :use (fn-sn-finish-acknowledges-exact-pair
                 fn-sn-finish-preserves-state
                 fn-snt-finish-keeps-records
                 (:instance fn-snt-typed-store-components (s (fn-sn-finish s)))
                 (:instance fn-sf-state-success-member-has-record
                            (s (fn-sn-files (fn-sn-finish s)))
                            (pair (fn-sf-completion (fn-sn-files s))))
                 (:instance fn-own-member-of-append-last
                            (x (fn-sf-completion (fn-sn-files s)))
                            (l (fn-sf-successes (fn-sn-files s)))))
           :in-theory (disable fn-sf-successes fn-own-member-of-append-last))))

(defthm fn-own-completion-needs-completing-phase
  (implies (not (equal (fn-sf-phase (fn-sn-files s)) :completing))
           (not (fn-sn-completion-enabledp s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp)
                                  (fn-sn-record-bindsp)))))

; An admissible image extends the durable records of the live state.
(defthm fn-own-crash-image-extends-records
  (implies (and (fn-sf-crash-imagep files frontier records)
                (true-listp (fn-sf-records files)))
           (fn-sf-prefixp (fn-sf-records files) records))
  :hints (("Goal" :in-theory (e/d (fn-sf-crash-imagep)
                                  (fn-sf-frontier-new-visiblep
                                   fn-sf-record-present-visiblep
                                   fn-sf-frontier-candidate fn-sf-record-candidate))
           :use ((:instance fn-sf-prefixp-reflexive (xs (fn-sf-records files)))
                 (:instance fn-sf-prefixp-append (xs (fn-sf-records files))
                            (ys (list (fn-sf-record-candidate files))))))))

; The host's dispatch on the typed open result (store proposal 2): a result
; whose kind is :ok is fn-sn-open-okp, so fn-owner-recover never runs the
; whole-state recognizer that fn-sn-open-okp carries.  :rule-classes nil, a
; guard-style fact cited by the host comment, not a registry event.
(defthm fn-own-open-kind-ok-is-okp
  (implies (equal (fn-sn-open-kind (fn-sn-open-observed groups capacity frontier records))
                  :ok)
           (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records)))
  :rule-classes nil
  :hints (("Goal" :use fn-sn-open-observed-result-is-typed
           :in-theory (e/d (fn-sn-open-okp fn-sn-open-errorp) (fn-sn-open-observed)))))

; -----------------------------------------------------------------------------
; Refresh

(defthm fn-own-refresh-keeps-fields
  (and (equal (fn-own-store (fn-own-refresh o)) (fn-own-store o))
       (equal (fn-own-conns (fn-own-refresh o)) (fn-own-conns o))
       (equal (fn-own-next-id (fn-own-refresh o)) (fn-own-next-id o))
       (equal (fn-own-max-conns (fn-own-refresh o)) (fn-own-max-conns o))
       (equal (fn-own-pending (fn-own-refresh o)) (fn-own-pending o))
       (equal (fn-own-ledger (fn-own-refresh o)) (fn-own-ledger o))
       (equal (fn-own-clock (fn-own-refresh o)) (fn-own-clock o))
       (equal (fn-own-facts (fn-own-refresh o)) (fn-own-facts o))
       (equal (fn-own-config (fn-own-refresh o)) (fn-own-config o))
       (equal (fn-own-queue (fn-own-refresh o)) (fn-own-queue o))
       (equal (fn-own-inflight (fn-own-refresh o)) (fn-own-inflight o))
       (equal (fn-own-refused (fn-own-refresh o)) (fn-own-refused o)))
  :hints (("Goal" :in-theory (disable fn-own-store-idlep))))

; The refresh keystone's one fact about the archive: distinct Message-IDs,
; from the acceptance state the related Store carries.
(defthm fn-own-related-node-statep
  (implies (fn-snt-relation s)
           (fn-node-statep (fn-sn-node s)))
  :hints (("Goal" :use fn-snt-relation-implies-structural-state
           :in-theory (e/d (fn-sn-statep)
                           (fn-node-statep fn-snt-relation
                            fn-snt-relation-implies-structural-state)))))

(defthm fn-own-node-statep-acceptance-articles
  (implies (fn-node-statep node)
           (fn-article-listp (fn-state-groups (fn-node-acceptance node))
                             (fn-state-articles (fn-node-acceptance node))))
  :hints (("Goal" :in-theory (enable fn-node-statep fn-statep))))

(defthm fn-own-related-acceptance-msgids-distinct
  (implies (fn-snt-relation s)
           (no-duplicatesp-equal
            (fn-article-msgids (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
  :hints (("Goal" :in-theory (disable fn-snt-relation fn-node-statep fn-article-listp)
           :use ((:instance fn-own-related-node-statep)
                 (:instance fn-own-node-statep-acceptance-articles
                            (node (fn-sn-node s)))
                 (:instance fn-ctl-article-listp-msgids-distinct
                            (configured (fn-state-groups (fn-node-acceptance (fn-sn-node s))))
                            (xs (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))))))

; The refresh publishes the visible state: the archive it installs is the
; visible state of the grown prefix under the records it carries
; (fn-ctl-refresh-state-is-visible, books/control-visible.lisp), so the
; restated view conjunct holds after it.
(defthm fn-own-refresh-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-refresh o)))
  :hints (("Goal"
           :use ((:instance fn-own-related-records-true-list (s (fn-own-store o)))
                 (:instance fn-own-related-frontier-natural (s (fn-own-store o)))
                 (:instance fn-own-idle-node-is-replay (s (fn-own-store o)))
                 (:instance fn-own-related-acceptance-msgids-distinct (s (fn-own-store o)))
                 (:instance fn-ctl-refresh-state-is-visible
                            (old-archive (fn-own-view-archive (fn-own-view o)))
                            (old-p (fn-own-prefix-archive
                                    (fn-sn-groups (fn-own-store o))
                                    (fn-sn-capacity (fn-own-store o))
                                    (fn-sf-records (fn-sn-files (fn-own-store o)))
                                    (fn-own-view-version (fn-own-view o))
                                    (fn-own-view-frontier (fn-own-view o))))
                            (ws (fn-own-view-withdrawals (fn-own-view o)))
                            (old-verdicts (fn-own-view-verdicts (fn-own-view o)))
                            (old-raw (fn-own-view-raw (fn-own-view o)))
                            (new-p (fn-node-acceptance (fn-sn-node (fn-own-store o))))
                            (verdicts (fn-sn-verdicts (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))
                            (configs (fn-sn-config-history (fn-own-store o)))))
           ;; The index is carried by fn-midx-refresh-preserves-correspondence
           ;; and the group index by fn-ctl-visible-state-of-fields; opening
           ;; either builder rebuilt the whole trie (3.4 s to 0.4 s).
           :in-theory (e/d (fn-own-relation)
                           (fn-own-conns-okp fn-own-view-make-group-indexed
                            fn-midx-refresh fn-midx-correspondencep fn-gidx-build
                            fn-snt-ready-or-recovered-node-is-exact-replay
                            fn-own-store-idlep fn-own-idle-node-is-replay
                            fn-own-related-records-true-list
                            fn-own-related-frontier-natural
                            fn-own-related-acceptance-msgids-distinct
                            fn-ctl-refresh-state-is-visible
                            fn-ctl-refresh-visible-is-visible))
           :cases ((fn-own-store-idlep (fn-own-store o))))))

; -----------------------------------------------------------------------------
; Each event preserves the relation

; The session a served open installs is bounded: open, no group, no cursor.
; Opens served's fn-served-open and nntp's session record locally.
(defthm fn-own-open-session-boundedp
  (fn-own-conn-boundedp
   (fn-own-conn-make id version frontier wire
                     (fn-served-conn-session
                      (fn-served-result-conn
                       (fn-served-open archive line-limit body-limit config
                                       observation injection acfg)))
                     archive config observation)
   groups)
  ; The four OPEN transitions are enabled and the four RECOGNIZERS under
  ; them are not: the accessor-of-constructor lemmas each record exports
  ; carry the base chain down to the reader session, where the group and
  ; the cursor are read, and `fn-auth-sessionp' -- the one conjunct that
  ; would need the whole cascade -- comes from
  ; fn-auth-open-session-is-consistent through the forward-chaining bridge
  ; fn-auth-consistent-forward instead of being opened here
  ; (docs/proof-style.md, "Never open a recognizer to prove a property of a
  ; transition").
  :hints (("Goal"
           :in-theory (e/d (fn-own-conn-boundedp fn-served-open
                            fn-auth-open-session fn-peer-open-session
                            fn-post-open-session fn-nntp-open-session
                            fn-nntp-make-session fn-nntp-session-openp
                            fn-nntp-session-group fn-nntp-session-current
                            fn-nntp-session-projected)
                           (fn-auth-sessionp fn-auth-configp
                            fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-projectionp
                            ; else the :use hypothesis is rewritten to T by
                            ; this very rule and the forward-chaining bridge
                            ; never sees the consistency it was added for
                            fn-auth-open-session-is-consistent
                            fn-auth-open-config))
           :use ((:instance fn-auth-open-session-is-consistent
                            (peer nil) (node nil) (cfg nil) (tlsp nil))))))

; The peer port's counterpart.  fn-own-step opens BOTH open transitions, so
; both need this; before the served session grew its auth wrapper the peer
; branch fell out of the reader lemma and nobody noticed, because
; books/owner-invariants has not certified since the peer port landed.
(defthm fn-own-open-peer-session-boundedp
  (fn-own-conn-boundedp
   (fn-own-conn-make id version frontier wire
                     (fn-served-conn-session
                      (fn-served-result-conn
                       (fn-served-open-peer archive line-limit body-limit
                                            config observation injection
                                            peer node cfg acfg)))
                     archive config observation)
   groups)
  :hints (("Goal"
           :in-theory (e/d (fn-own-conn-boundedp fn-served-open-peer
                            fn-auth-open-session fn-peer-open-session
                            fn-post-open-session fn-nntp-open-session
                            fn-nntp-make-session fn-nntp-session-openp
                            fn-nntp-session-group fn-nntp-session-current
                            fn-nntp-session-projected)
                           (fn-auth-sessionp fn-auth-configp
                            fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-projectionp
                            fn-node-statep fn-cfgp
                            fn-auth-open-session-is-consistent
                            fn-auth-open-config))
           :use ((:instance fn-auth-open-session-is-consistent
                            (tlsp nil))))))

(defthm fn-own-conn-boundedp-of-make-indexed
  (equal (fn-own-conn-boundedp
          (fn-own-conn-make-indexed id version frontier wire session archive
                                    config observation verdicts index)
          groups)
         (fn-own-conn-boundedp
          (fn-own-conn-make id version frontier wire session archive config
                            observation)
          groups))
  :hints (("Goal" :in-theory (enable fn-own-conn-boundedp))))

(defthm fn-own-conn-boundedp-of-make-group-indexed
  (equal (fn-own-conn-boundedp
          (fn-own-conn-make-group-indexed id version frontier wire session
                                          archive config observation verdicts
                                          index buckets control)
          groups)
         (fn-own-conn-boundedp
          (fn-own-conn-make-indexed id version frontier wire session archive
                                    config observation verdicts index)
          groups))
  :hints (("Goal" :in-theory (e/d (fn-own-conn-boundedp)
                                    (fn-own-conn-make-indexed
                                     fn-own-conn-make-group-indexed)))))

; Owner open now supplies its already-built view trie and verdict projection
; to served open.  The session's initial selected group and cursor are still
; nil, independently of those pins and the archive's historical domain.
(defthm fn-own-open-indexed-session-boundedp
  (fn-own-conn-boundedp
   (fn-own-conn-make-indexed
    id version frontier wire
    (fn-served-conn-session
     (fn-served-result-conn
      (fn-served-open-indexed archive index verdicts line-limit body-limit
                              config observation injection acfg)))
    archive config observation verdicts index)
   groups)
  :hints (("Goal"
           :in-theory (e/d (fn-own-conn-boundedp fn-served-open-indexed
                            fn-auth-open-session fn-peer-open-session
                            fn-post-open-session fn-nntp-open-session
                            fn-nntp-make-session fn-nntp-session-openp
                            fn-nntp-session-group fn-nntp-session-current
                            fn-nntp-session-projected)
                           (fn-auth-sessionp fn-auth-configp
                            fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-projectionp
                            fn-auth-open-session-is-consistent
                            fn-auth-open-config))
           :use ((:instance fn-auth-open-session-is-consistent
                            (peer nil) (node nil) (cfg nil) (tlsp nil))))))

(defthm fn-own-open-peer-indexed-session-boundedp
  (fn-own-conn-boundedp
   (fn-own-conn-make-indexed
    id version frontier wire
    (fn-served-conn-session
     (fn-served-result-conn
      (fn-served-open-peer-indexed
       archive index verdicts line-limit body-limit config observation
       injection peer node cfg acfg)))
    archive config observation verdicts index)
   groups)
  :hints (("Goal"
           :in-theory (e/d (fn-own-conn-boundedp fn-served-open-peer-indexed
                            fn-auth-open-session fn-peer-open-session
                            fn-post-open-session fn-nntp-open-session
                            fn-nntp-make-session fn-nntp-session-openp
                            fn-nntp-session-group fn-nntp-session-current
                            fn-nntp-session-projected)
                           (fn-auth-sessionp fn-auth-configp
                            fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-projectionp
                            fn-node-statep fn-cfgp
                            fn-auth-open-session-is-consistent
                            fn-auth-open-config))
           :use ((:instance fn-auth-open-session-is-consistent
                            (tlsp nil))))))

; An open conses one connection onto the table; the old table's
; fn-own-conns-okp is a hypothesis, so it stays closed (the recursive
; definition otherwise reopened it 30,000 times in the open-peer proof).
(local
 (defthm fn-own-conns-okp-of-cons
   (equal (fn-own-conns-okp (cons conn conns) groups capacity records)
          (and (fn-own-conn-okp conn groups capacity records)
               (fn-own-conns-okp conns groups capacity records)))))
(local (in-theory (disable fn-own-conns-okp-of-cons)))

(defthm fn-own-open-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-open o acfg))))
  :hints (("Goal" :in-theory (e/d (fn-own-relation fn-own-conns-okp-of-cons)
                                  (fn-own-conns-okp fn-own-conn-make-group-indexed
                                   fn-own-conn-boundedp
                                   fn-served-open-indexed)))))

; -----------------------------------------------------------------------------
; The re-pinned node of a peer connection (books/owner.lisp
; fn-own-conn-live-session, called by fn-own-read)
;
; Three facts, and the third is the one the served path's duplicate
; suppression rests on.  First, a reader connection is untouched.  Second,
; the re-pin cannot drop a connection: it leaves the reader session
; identical, so fn-own-conn-boundedp -- the test fn-own-read applies after
; the step, and the test that silently disabled ADVANCE for a whole wave
; when a rebuild lost a wrapper -- answers exactly as before.  Third, the
; node fn-peer-decide-offer is given on a peer connection IS the owner's
; live node.

(local (defthm fn-own-live-auth-base-of-with-base
  (equal (fn-auth-session-base (fn-auth-with-base as base)) base)
  :hints (("Goal" :in-theory (enable (:d fn-auth-with-base))))))

(local (defthm fn-own-live-auth-with-base-is-a-session
  (implies (and (fn-auth-sessionp as) (fn-peer-sessionp base))
           (fn-auth-sessionp (fn-auth-with-base as base)))
  :hints (("Goal" :in-theory (e/d (fn-auth-sessionp fn-auth-with-base)
                                  (fn-peer-sessionp fn-auth-configp
                                   fn-nntp-printable-tokenp fn-prin-idp))))))

(local (defthm fn-own-live-auth-sessionp-forward-peer
  (implies (fn-auth-sessionp as)
           (fn-peer-sessionp (fn-auth-session-base as)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-sessionp)
                                  (fn-peer-sessionp fn-auth-configp
                                   fn-nntp-printable-tokenp fn-prin-idp))))))

(defthm fn-own-conn-live-session-of-an-unconfigured-reader-is-the-session
  (implies (not (fn-peer-session-cfg
                 (fn-auth-session-base (fn-own-conn-session conn))))
           (equal (fn-own-conn-live-session o conn) (fn-own-conn-session conn)))
  :hints (("Goal" :in-theory (enable (:d fn-own-conn-live-session)))))

(defthm fn-own-conn-live-session-is-a-session
  (implies (and (fn-auth-sessionp (fn-own-conn-session conn))
                (fn-node-statep (fn-sn-node (fn-own-store o))))
           (fn-auth-sessionp (fn-own-conn-live-session o conn)))
  :hints (("Goal" :in-theory (e/d ((:d fn-own-conn-live-session))
                                  (fn-auth-sessionp fn-peer-sessionp
                                   fn-auth-with-base fn-peer-with-node
                                   fn-peer-with-refused
                                   fn-node-statep)))))

(defthm fn-own-conn-live-session-keeps-the-reader-session
  (equal (fn-auth-reader-session (fn-own-conn-live-session o conn))
         (fn-auth-reader-session (fn-own-conn-session conn)))
  :hints (("Goal" :in-theory (e/d ((:d fn-own-conn-live-session))
                                  (fn-auth-with-base fn-peer-with-node
                                   fn-peer-with-refused)))))

(defthm fn-own-live-session-boundedp
  (implies (and (fn-own-conn-boundedp conn groups)
                (fn-node-statep (fn-sn-node (fn-own-store o))))
           (fn-own-conn-boundedp
            (fn-own-conn-make cid version frontier wire
                              (fn-own-conn-live-session o conn)
                              archive config observation)
            groups))
  :hints (("Goal" :in-theory (e/d ((:d fn-own-conn-boundedp))
                                  (fn-auth-sessionp fn-peer-sessionp
                                   fn-own-conn-live-session
                                   fn-nntp-session-group fn-nntp-session-current
                                   fn-node-statep)))))

; The subject-equating theorem AGENTS.md's first assurance rule asks for on
; the duplicate-offer row.  K3 (fn-peer-history-is-have-at-offer,
; books/peer-inbound-invariants.lisp) is about fn-peer-decide-offer over a
; node; the two wire theorems beside it say the reply to IHAVE and CHECK is
; that decision; this says which node the served path supplies, and it is
; the owner's own, not the one the connection opened with.  The host line is
; host/owner-host.lisp fn-owner-chunk -> fn-own-read.
; A peer session whose role is bound carries a configuration: `fn-peer-sessionp'
; (books/peer-inbound) demands `fn-cfgp' of it on the peer arm, and `fn-cfgp'
; demands a cons.  `64a80197' bound the inbound peer role to an authenticated
; principal and made that pairing the recognizer's business; before it, a peer
; beside a null configuration was merely unusual.
(local
 (defthm fn-own-bound-peer-session-has-configuration
   (implies (and (fn-peer-sessionp x) (fn-peer-session-peer x))
            (fn-peer-session-cfg x))
   :hints (("Goal" :in-theory (e/d (fn-peer-sessionp fn-cfgp fn-cfg-shapep)
                                   (fn-post-sessionp fn-peer-transferp
                                    fn-node-statep fn-cfg-valuep
                                    fn-peer-session-shapep
                                    fn-record-uint32p))))))

; The recognizer hypothesis is what `64a80197' made this theorem owe.
; `fn-own-conn-live-session' (books/owner.lisp) refreshes the node only under
; `(fn-peer-session-cfg ps)', so on a peer beside a NULL configuration the
; session is handed back untouched and the node equation below is false of
; it.  That object is not a `fn-peer-sessionp' -- the lemma above is what says
; so -- and the served path does not reach it; the other four conjuncts hold
; on both branches and are unrestricted.  books/owner-invariants has not
; certified since 2026-09-21.
(defthm fn-own-read-offers-against-the-live-node
  (implies (and (fn-peer-sessionp
                 (fn-auth-session-base (fn-own-conn-session conn)))
                (fn-peer-session-peer
                 (fn-auth-session-base (fn-own-conn-session conn))))
           (and (equal (fn-peer-session-node
                        (fn-auth-session-base (fn-own-conn-live-session o conn)))
                       (fn-sn-node (fn-own-store o)))
                (equal (fn-peer-session-peer
                        (fn-auth-session-base (fn-own-conn-live-session o conn)))
                       (fn-peer-session-peer
                        (fn-auth-session-base (fn-own-conn-session conn))))
                (equal (fn-peer-session-cfg
                        (fn-auth-session-base (fn-own-conn-live-session o conn)))
                       (fn-peer-session-cfg
                        (fn-auth-session-base (fn-own-conn-session conn))))
                (equal (fn-peer-session-transfer
                        (fn-auth-session-base (fn-own-conn-live-session o conn)))
                       (fn-peer-session-transfer
                        (fn-auth-session-base (fn-own-conn-session conn))))
                (equal (fn-peer-session-inflight
                        (fn-auth-session-base (fn-own-conn-live-session o conn)))
                       (fn-peer-session-inflight
                        (fn-auth-session-base (fn-own-conn-session conn))))))
  :hints (("Goal" :in-theory (e/d ((:d fn-own-conn-live-session))
                                  (fn-auth-with-base fn-peer-with-node)))))


; The peer port's counterpart of the lemma above.  fn-own-step's :open-peer
; arm needs it, and there was none: the transition was added with the peer
; port and this book has not certified since, so nothing asked.
(defthm fn-own-open-peer-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-open-peer o peer cfg acfg))))
  :hints (("Goal" :in-theory (e/d (fn-own-relation fn-own-conns-okp-of-cons)
                                  (fn-own-conns-okp fn-own-conn-make-group-indexed
                                   fn-own-conn-boundedp
                                   fn-served-open-peer-indexed)))))
