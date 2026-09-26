; fn: keystones of the mutable service owner (C1-05).
;
; The subject of every theorem here is a function tools/run_owner.py calls
; through host/owner-host.lisp: fn-own-start (fn-owner-recover), fn-own-read
; (fn-owner-chunk: the served port, one fn-served-step per socket read over
; the pinned archive), fn-own-step through fn-own-open / fn-own-advance /
; fn-own-close / fn-own-begin / fn-own-store-step / fn-own-complete /
; fn-own-observe / fn-own-declare-group, and fn-own-run as the arbitrary
; finite event list the host produces.  fn-own-reopen is the process restart
; the host performs by calling fn-owner-recover again over the image on disk.
; fn-own-read-step is the per-event law under the served port: the byte fold
; inside fn-served-step applies fn-served-dispatch once per framed event
; (books/served.lisp), and fn-own-read-step is that one step with the owner's
; bookkeeping around it.  The served POST path (w5/owner-post) adds
; fn-own-take-submission (the writer step, fn-owner-take) and fn-own-outcome
; (fn-owner-outcome): the only owner entry that renders a POST outcome.
;
; Keystones (each has a reachable witness and one concrete violating value
; per hypothesis in tests/acl2/owner-tests.lisp; statements unchanged from
; the first cut of this lane except where a name is new):
;   fn-own-read-is-served-step-on-pinned-prefix         (K1, served port; new)
;   fn-own-read-is-served-step-on-pinned-prefix-after-any-trace   (new)
;   fn-own-reader-sees-pinned-prefix-replay            (K1, per event)
;   fn-own-reader-sees-pinned-prefix-replay-after-any-trace
;   fn-own-completion-consumed-once                    (K2)
;   fn-own-pinned-prefix-survives-any-trace            (K3)
;   fn-own-reclaim-floor-below-every-pin
;   fn-own-connections-bounded-after-any-trace         (K4)
;   fn-own-completed-post-survives-close-and-any-trace (K5)
;   fn-own-run-preserves-relation, fn-own-run-preserves-store-relation (K6)
;   fn-own-open-observed-start-relation                (root)
;   fn-own-every-fact-is-clock-stamped, fn-own-declare-group-without-clock-
;   is-refused, fn-own-declared-group-is-replayed      (facts)
;   fn-own-outcome-completion-is-one-of-four           (POST outcome; clock refusal)
;   fn-own-durable-reply-names-a-durable-record        (POST outcome; new)
;   fn-own-read-touches-only-its-connection            (POST isolation; new)
;   fn-own-outcome-touches-only-its-connection         (POST isolation; new)
;
; Statements changed by the w4-post-compose byte fold, not by this lane's
; choice: the served connection is six fields, so the two served-port
; keystones thread the connection's pinned config and observation, and the
; owner's current clock observation as the injection clock, into
; fn-served-make-conn; the per-event law is stated over fn-served-dispatch
; (fn-nntp-post-step with the article-mode switch), the step the fold now
; applies, where it was stated over fn-nntp-step before POST existed.
;
; Local vocabulary opened here (named on the deputy board): the owner's own
; fn-own-vocabulary; store's fn-snt-relation (fn-own-idle-node-is-replay),
; fn-snrt-step, fn-snt-step and the fn-sn-* transitions
; (fn-own-snrt-step-keeps-configuration), fn-sn-completion-enabledp
; (fn-own-completion-needs-completing-phase), fn-sf-crash-imagep
; (fn-own-crash-image-extends-records), fn-sn-open-okp and fn-sn-open-errorp
; (fn-own-open-kind-ok-is-okp); nntp's session record
; (fn-own-open-session-boundedp); served's fn-served-open (the same lemma).

(in-package "ACL2")
(include-book "owner")
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
       (equal (fn-own-inflight (fn-own-refresh o)) (fn-own-inflight o)))
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
                                   fn-node-statep)))))

(defthm fn-own-conn-live-session-keeps-the-reader-session
  (equal (fn-auth-reader-session (fn-own-conn-live-session o conn))
         (fn-auth-reader-session (fn-own-conn-session conn)))
  :hints (("Goal" :in-theory (e/d ((:d fn-own-conn-live-session))
                                  (fn-auth-with-base fn-peer-with-node)))))

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

(defthm fn-own-read-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-read o id octets))))
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
                           (fn-own-conns-okp fn-own-view-okp fn-own-conn-make-group-indexed
                            fn-own-conn-boundedp fn-own-find-conn-okp)))))

(defthm fn-own-read-step-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-read-step o id event))))
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
                           (fn-own-conns-okp fn-own-view-okp fn-own-conn-make-group-indexed
                            fn-own-conn-boundedp fn-own-find-conn-okp)))))

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
                                            (fn-own-pending o) (fn-own-ledger o)
                                            (fn-own-clock o) (fn-own-facts o)
                                            ; `feeds' is `fn-own-make's THIRTEENTH
                                            ; field (w10/owner-feed).  Six `:use'
                                            ; instances in this book were left at
                                            ; twelve, and `certify-book' stops at
                                            ; the first, so only one was ever seen.
                                            (fn-own-config o) (fn-own-queue o)
                                            (fn-own-inflight o)
                                            (fn-own-feeds o))))
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
                                            (append (fn-own-ledger o)
                                                    (list (fn-sf-completion
                                                           (fn-sn-files (fn-own-store o)))))
                                            (fn-own-clock o) (fn-own-facts o)
                                            (fn-own-config o) (fn-own-queue o)
                                            (fn-own-inflight o)
                                            (fn-own-feeds o))))
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
                                (fn-own-max-conns o) nil (fn-own-ledger o) nil
                                (fn-own-facts o) (fn-own-config o) nil nil
                                (fn-own-feed-restart-all (fn-own-feeds o)))))
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
           (fn-own-relation (fn-own-operator-submit o msgid groups octets)))
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
;    and newsgroups the command named.
; 2. With no usable clock nothing is queued and the answer is a refusal
;    (D10-a).
; 3. A retry of the same octets after the first became durable is the stored
;    article, whatever the clock now reads, so the store answers duplicate.

(defthm fn-own-operator-decision-is-an-injection-of-the-payload
  (implies (fn-inj-injectedp (fn-own-operator-decision cfg clock node msgid groups octets))
           (let ((d (fn-own-operator-decision cfg clock node msgid groups octets)))
             (and (equal (fn-inj-decision-msgid d) msgid)
                  (equal (fn-inj-decision-groups d) groups)
                  (fn-inj-reinjectionp (fn-inj-decision-octets d) octets
                                       (fn-inj-config-agent cfg) msgid))))
  :hints (("Goal" :in-theory (e/d (fn-own-operator-decision)
                                  (fn-inj-decide fn-inj-reinjectionp
                                   fn-own-stored-octets fn-own-clock-usablep))
           :use ((:instance fn-inj-injected-article-is-a-reinjection-of-its-source
                            (source octets) (config cfg) (observation clock))))))

(defthm fn-own-operator-submission-is-an-injection-of-the-payload
  (implies (equal (fn-own-operator-submit-result o msgid groups octets) :submitted)
           (let* ((q (fn-own-queue (fn-own-operator-submit o msgid groups octets)))
                  (d (fn-own-sub-decision (car q))))
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
                            (node (fn-sn-node (fn-own-store o))))))))

(defthm fn-own-operator-submit-without-a-clock-refuses-and-changes-nothing
  (implies (not (and (fn-clock-observationp (fn-own-clock o))
                     (fn-clock-has-wall (fn-own-clock o))))
           (and (equal (fn-own-operator-submit-result o msgid groups octets)
                       :refused)
                (equal (fn-own-operator-submit o msgid groups octets) o)))
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
                (equal (fn-own-stored-octets node msgid)
                       (fn-inj-decision-octets (fn-inj-decide octets cfg first)))
                (fn-clock-observationp later)
                (fn-clock-has-wall later))
           (equal (fn-own-operator-decision cfg later node msgid groups octets)
                  (fn-inj-make-decision
                   :injected nil msgid groups
                   (fn-inj-decision-octets (fn-inj-decide octets cfg first)))))
  :hints (("Goal" :in-theory (e/d (fn-own-operator-decision fn-own-clock-usablep)
                                  (fn-inj-decide fn-inj-reinjectionp
                                   fn-own-stored-octets
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
; read by the relation.  Both served and control outcomes use this body.
(local
 (defthm fn-own-outcome-body-preserves-relation
   (implies (fn-own-relation o)
            (fn-own-relation
             (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                          (fn-own-next-id o) (fn-own-max-conns o) p
                          (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                          (fn-own-config o) (fn-own-queue o) nil fds)))
   :hints (("Goal" :in-theory (enable fn-own-relation)))))

(defthm fn-own-control-outcome-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-control-outcome o word)))
  :hints (("Goal"
           :use ((:instance fn-own-outcome-body-preserves-relation
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
                          (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
                          (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
                          (fn-own-inflight o) fds)))
   :hints (("Goal" :in-theory (enable fn-own-relation)))))

(defthm fn-own-step-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-step o event)))
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
           (fn-own-relation (fn-own-run o events)))
  :hints (("Goal" :induct (fn-own-run o events)
           :in-theory (disable fn-own-step))))

(defthm fn-own-run-preserves-store-relation
  (implies (fn-own-relation o)
           (fn-snt-relation (fn-own-store (fn-own-run o events))))
  :hints (("Goal" :use fn-own-run-preserves-relation
           :in-theory (e/d (fn-own-relation)
                           (fn-own-run fn-own-run-preserves-relation)))))

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
                                                (fn-state-articles archive))))
                                            nil 0 max-conns nil nil nil nil
                                            nil nil nil nil))))
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
                      (fn-served-make-conn-group-indexed
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
                       (fn-own-conn-group-index conn) (fn-own-conn-control conn))
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
                           (fn-own-relation fn-own-conns-okp
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
                      (fn-served-make-conn-group-indexed
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
                       (fn-own-conn-group-index conn) (fn-own-conn-control conn))
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
                      (fn-served-make-conn-group-indexed
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
                       (fn-own-conn-group-index conn) (fn-own-conn-control conn))
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
                      (fn-served-make-conn-group-indexed
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
                       (fn-own-conn-group-index conn) (fn-own-conn-control conn))
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
  :hints (("Goal" :in-theory (disable fn-served-step fn-served-dispatch
                                      fn-served-post-outcome fn-served-open
                                      fn-own-conn-boundedp fn-own-outcome-completion
                                      fn-own-find-conn-id))))

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
                                    fn-own-find-conn-id))))))

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

; -----------------------------------------------------------------------------
; The served POST outcome.
;
; fn-own-outcome is the only owner entry that renders a POST outcome, and
; fn-own-read the only one that renders a command reply; each renders for
; exactly the connection named and leaves every other connection as it was.

(defthm fn-own-find-conn-of-replace-conn-other
  (implies (not (equal (fn-own-conn-id conn) other))
           (equal (fn-own-find-conn other (fn-own-replace-conn conn conns))
                  (fn-own-find-conn other conns)))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns))))

(defthm fn-own-find-conn-of-replace-conn-same
  (implies (fn-own-find-conn (fn-own-conn-id conn) conns)
           (equal (fn-own-find-conn (fn-own-conn-id conn)
                                    (fn-own-replace-conn conn conns))
                  conn))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns))))

; The historical configured-owner relation needs the bound the actual read
; gate checked against this connection's immutable archive.  A failed gate
; removes every connection with the selected ID; it cannot leave a stale
; selected group in a surviving connection.
(defthm fn-own-replaced-conn-archive-bounded
  (implies (and (fn-own-find-conn id conns)
                (equal (fn-own-conn-id next) id)
                (fn-own-conn-boundedp
                 next (fn-state-groups (fn-own-conn-archive next))))
           (fn-own-conn-boundedp
            (fn-own-find-conn id (fn-own-replace-conn next conns))
            (fn-state-groups
             (fn-own-conn-archive
              (fn-own-find-conn id (fn-own-replace-conn next conns))))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-of-replace-conn-same
                            (conn next)))
           :in-theory (disable fn-own-conn-boundedp))))

(defthm fn-own-read-remove-leaves-no-selected-id
  (equal (fn-own-find-conn id (fn-own-remove-conn id conns))
         nil)
  :hints (("Goal" :induct (fn-own-remove-conn id conns))))

(defthm fn-own-read-survivor-is-archive-bounded
  (implies
   (fn-own-find-conn
    id (fn-own-conns (cdr (fn-own-read o id octets))))
   (fn-own-conn-boundedp
    (fn-own-find-conn
     id (fn-own-conns (cdr (fn-own-read o id octets))))
    (fn-state-groups
     (fn-own-conn-archive
      (fn-own-find-conn
       id (fn-own-conns (cdr (fn-own-read o id octets))))))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-id
                            (conns (fn-own-conns o))))
           :in-theory (e/d (fn-own-read fn-own-finish-read
                            fn-own-set-conns fn-own-enqueue)
                           (fn-served-step fn-own-conn-boundedp
                            fn-own-conn-make-group-indexed
                            fn-served-make-conn-group-indexed)))))

(defthm fn-own-find-conn-of-replace-same-id
  (implies (and (fn-own-find-conn id conns)
                (equal (fn-own-conn-id next) id))
           (equal (fn-own-find-conn id (fn-own-replace-conn next conns))
                  next))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-of-replace-conn-same
                            (conn next))))))

(defthm fn-own-read-survivor-keeps-historical-fields
  (implies
   (fn-own-find-conn
    id (fn-own-conns (cdr (fn-own-read o id octets))))
   (let ((old (fn-own-find-conn id (fn-own-conns o)))
         (next (fn-own-find-conn
                id (fn-own-conns (cdr (fn-own-read o id octets))))))
     (and (fn-own-conn-shapep next)
          (equal (fn-own-conn-id next) (fn-own-conn-id old))
          (equal (fn-own-conn-version next) (fn-own-conn-version old))
          (equal (fn-own-conn-frontier next) (fn-own-conn-frontier old))
          (equal (fn-own-conn-archive next) (fn-own-conn-archive old)))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-id
                            (conns (fn-own-conns o))))
           :in-theory (e/d (fn-own-read fn-own-finish-read
                            fn-own-set-conns fn-own-enqueue)
                           (fn-served-step fn-own-conn-boundedp
                            fn-own-conn-make-group-indexed
                            fn-served-make-conn-group-indexed)))))

(defthm fn-own-find-conn-of-remove-conn-other
  (implies (not (equal id other))
           (equal (fn-own-find-conn other (fn-own-remove-conn id conns))
                  (fn-own-find-conn other conns)))
  :hints (("Goal" :induct (fn-own-remove-conn id conns))))

(defthm fn-own-read-touches-only-its-connection
  (implies (not (equal id other))
           (equal (fn-own-find-conn other (fn-own-conns (cdr (fn-own-read o id octets))))
                  (fn-own-find-conn other (fn-own-conns o))))
  :hints (("Goal" :in-theory (disable fn-served-step fn-own-conn-boundedp
                                      fn-own-conn-make-group-indexed))))

; Statement changed by the read-back follow-up, and only where the new
; behaviour forces it: a :durable outcome re-pins the poster's own
; connection (fn-own-outcome), so the first conjunct is now what the
; theorem's name always said -- every connection other than the one named is
; found exactly as it was.  The second conjunct is unchanged.
(defthm fn-own-outcome-touches-only-its-connection
  (and (implies (not (equal id other))
                (equal (fn-own-find-conn other
                                         (fn-own-conns (cdr (fn-own-outcome o id word))))
                       (fn-own-find-conn other (fn-own-conns o))))
       (implies (not (equal (fn-own-sub-id (fn-own-inflight o)) id))
                (equal (car (fn-own-outcome o id word)) nil)))
  :hints (("Goal" :in-theory (e/d (fn-own-advance fn-own-set-conns)
                                  (fn-served-post-outcome fn-own-outcome-completion
                                   fn-own-conn-boundedp
                                   fn-own-conn-make-group-indexed)))))

; -----------------------------------------------------------------------------
; The transit port (w9/peering-e2e; specs/peering.md 2.2 and the owner port
; proposal on the deputy board).
;
; KEYSTONE.  Transit and POST share one durable path.  The writer step reads
; the head of the one queue and installs it in the one pending slot with the
; ledger mark of the moment: it does not test what the submission carries, so
; a `(:transit peer kind msgid octets)` submission and an injected one take
; the same way and cannot both be in flight.  This is the owner-level half of
; `fn-peer-transfer-is-the-post-path' (books/peer-inbound-invariants): that
; one says the node transition is the post path, this one says the serialised
; durable path around it is the same path.
(defthm fn-own-take-installs-the-queued-submission-whatever-it-carries
  (implies (and (null (fn-own-inflight o))
                (consp (fn-own-queue o))
                (null (fn-own-pending o))
                (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready))
           (and (equal (fn-own-inflight (fn-own-take-submission o))
                       (fn-own-sub-make (fn-own-sub-id (car (fn-own-queue o)))
                                        (fn-own-sub-version (car (fn-own-queue o)))
                                        (len (fn-own-ledger o))
                                        (fn-own-sub-decision (car (fn-own-queue o)))))
                (equal (fn-own-queue (fn-own-take-submission o))
                       (cdr (fn-own-queue o)))
                (equal (fn-own-pending (fn-own-take-submission o))
                       (fn-own-sub-id (car (fn-own-queue o))))
                (equal (fn-own-store (fn-own-take-submission o)) (fn-own-store o))
                (equal (fn-own-conns (fn-own-take-submission o)) (fn-own-conns o))))
  :hints (("Goal" :in-theory (enable fn-own-take-submission))))

; KEYSTONE.  A transit outcome reaches only its connection: no other
; connection's pin, session or wire is touched, and an outcome for a
; connection that is not the one in flight renders no octet at all.
(defthm fn-own-transit-outcome-touches-only-its-connection
  (and (implies (not (equal id other))
                (equal (fn-own-find-conn
                        other (fn-own-conns
                               (cdr (fn-own-transit-outcome o id kind reason word))))
                       (fn-own-find-conn other (fn-own-conns o))))
       (implies (not (equal (fn-own-sub-id (fn-own-inflight o)) id))
                (equal (car (fn-own-transit-outcome o id kind reason word)) nil)))
  :hints (("Goal" :in-theory (e/d (fn-own-advance fn-own-set-conns)
                                  (fn-served-transit-outcome
                                   fn-own-outcome-completion
                                   fn-peer-submissionp
                                   fn-own-conn-boundedp
                                   fn-own-conn-make-group-indexed)))))

; A transit outcome renders a reply only for a transit submission: an
; injected submission in flight is answered by fn-own-outcome and by nothing
; here, so the two reply tables can never be crossed.
(defthm fn-own-transit-outcome-needs-a-transit-submission
  (implies (not (fn-own-transit-subp (fn-own-inflight o)))
           (equal (fn-own-transit-outcome o id kind reason word) (cons nil o)))
  :hints (("Goal" :in-theory (disable fn-served-transit-outcome
                                      fn-own-outcome-completion
                                      fn-peer-submissionp))))

; The completion the reply renders is one of the four words, preserving the
; owner's unusable-clock reason rather than flattening it to article refusal.
(defthm fn-own-outcome-completion-is-one-of-four
  (member-equal (fn-own-outcome-completion o word)
                '(:durable :refused :clock-unusable :uncertain)))

; Renamed from -is-post-session: the connection's session is the SERVED
; session, which is fn-auth-step's.
(defthm fn-own-conn-boundedp-is-auth-session
  (implies (fn-own-conn-boundedp conn groups)
           (fn-auth-sessionp (fn-own-conn-session conn)))
  :hints (("Goal" :in-theory (enable fn-own-conn-boundedp))))

(defthm fn-own-conn-boundedp-is-post-session
  (implies (fn-own-conn-boundedp conn groups)
           (fn-post-sessionp
            (fn-peer-session-base
             (fn-auth-session-base (fn-own-conn-session conn)))))
  :hints (("Goal" :in-theory (e/d (fn-own-conn-boundedp fn-auth-sessionp
                                   fn-peer-sessionp)
                                  (fn-post-sessionp fn-auth-configp
                                   fn-peer-transferp fn-node-statep
                                   fn-cfgp)))))

; -----------------------------------------------------------------------------
; Read-back: a 240 moves the poster's pin, and only the poster's.
;
; fn-own-advance rebuilds the connection's session over the committed view's
; archive, keeping the group and the cursor.  Both are carried by the old
; connection's boundedness, so the advance is never refused for a bounded
; connection: that is what makes the re-pin in fn-own-outcome unconditional
; rather than best-effort.

; Replacing the innermost session keeps the two wrappers well-formed: each
; carries only its own fields across, and the recognizer is opened here and
; nowhere in the re-pin theorem.
(local (defthm fn-own-auth-sessionp-forward-bases
  (implies (fn-auth-sessionp as)
           (and (fn-peer-sessionp (fn-auth-session-base as))
                (fn-post-sessionp
                 (fn-peer-session-base (fn-auth-session-base as)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-sessionp fn-peer-sessionp)
                                  (fn-post-sessionp fn-auth-configp
                                   fn-peer-transferp fn-node-statep
                                   fn-cfgp))))))

(local (defthm fn-own-peer-with-base-is-a-session
  (implies (and (fn-peer-sessionp ps) (fn-post-sessionp base))
           (fn-peer-sessionp (fn-peer-with-base ps base)))
  :hints (("Goal" :in-theory (e/d (fn-peer-sessionp fn-peer-with-base)
                                  (fn-post-sessionp fn-node-statep fn-cfgp
                                   fn-peer-transferp))))))

(local (defthm fn-own-auth-with-base-is-a-session
  (implies (and (fn-auth-sessionp as) (fn-peer-sessionp base))
           (fn-auth-sessionp (fn-auth-with-base as base)))
  :hints (("Goal" :in-theory (e/d (fn-auth-sessionp fn-auth-with-base)
                                  (fn-peer-sessionp fn-auth-configp
                                   fn-nntp-printable-tokenp fn-prin-idp))))))


; `books/nntp-auth.lisp' exports no accessor-of-update lemma for its own
; `fn-auth-with-base' (`books/peer-inbound.lisp:1169' does, for
; `fn-peer-with-base'), and the definition rune is withdrawn at that book's
; export, so nothing reduces the rebuilt session's base here.  Stated
; locally, opening only that one definition; the cross-cluster fix is one
; `defthm' beside `fn-peer-session-base-of-fn-peer-with-base'.
(local (defthm fn-own-auth-base-of-fn-auth-with-base
  (equal (fn-auth-session-base (fn-auth-with-base as base)) base)
  :hints (("Goal" :in-theory (enable (:d fn-auth-with-base))))))
;; The re-pinned session is an auth session and keeps its group and cursor.
;; Stated over a general auth session and cursor so the bounded-connection
;; proof below rewrites with them instead of opening every session
;; recognizer at the served session's full depth.
(local
 (defthm fn-own-repinned-cursor-fields
   (and (equal (fn-nntp-session-group (fn-nntp-set-cursor s g c)) g)
        (equal (fn-nntp-session-current (fn-nntp-set-cursor s g c)) c))
   :hints (("Goal" :in-theory (enable fn-nntp-set-cursor fn-nntp-make-session
                                      fn-nntp-session-group
                                      fn-nntp-session-current)))))
(local
 (defthm fn-own-post-session-awaiting-is-boolean
   (implies (fn-post-sessionp x)
            (booleanp (fn-post-session-awaiting x)))
   :hints (("Goal" :in-theory (enable fn-post-sessionp)))))
(local
 (defthm fn-own-repinned-auth-sessionp
   (implies (and (fn-auth-sessionp as)
                 (or (stringp g) (null g))
                 (or (posp c) (null c)))
            (fn-auth-sessionp
             (fn-auth-with-base
              as
              (fn-peer-with-base
               (fn-auth-session-base as)
               (fn-post-make-session
                (fn-nntp-set-cursor (fn-nntp-open-session archive) g c)
                (fn-post-session-awaiting
                 (fn-peer-session-base (fn-auth-session-base as))))))))
   :hints (("Goal"
            :use (fn-own-auth-sessionp-forward-bases
                  (:instance fn-nntp-consistent-session-is-session
                             (session (fn-nntp-open-session archive))
                             (archive archive))
                  (:instance fn-nntp-open-session-is-consistent (archive archive))
                  (:instance fn-nntp-set-cursor-sessionp
                             (session (fn-nntp-open-session archive))
                             (group g) (current c)))
            :in-theory (e/d (fn-post-sessionp)
                            (fn-auth-sessionp fn-nntp-sessionp
                             fn-own-auth-sessionp-forward-bases
                             (:d fn-peer-sessionp) (:d fn-peer-with-base)
                             fn-nntp-set-cursor fn-nntp-open-session
                             fn-nntp-set-cursor-sessionp
                             fn-nntp-consistent-session-is-session
                             fn-nntp-open-session-is-consistent))))))
(local
 (defthm fn-own-served-group-is-a-string
   (implies (and (fn-auth-sessionp as)
                 (fn-nntp-session-group
                  (fn-post-session-base
                   (fn-peer-session-base (fn-auth-session-base as)))))
            (stringp (fn-nntp-session-group
                      (fn-post-session-base
                       (fn-peer-session-base (fn-auth-session-base as))))))
   :hints (("Goal" :use fn-own-auth-sessionp-forward-bases
                   :in-theory (e/d (fn-post-sessionp fn-nntp-sessionp)
                                   (fn-auth-sessionp
                                    fn-own-auth-sessionp-forward-bases))))))
(local
 (defthm fn-own-advanced-session-is-bounded
   (implies (and (fn-own-conn-boundedp conn groups)
                 (fn-auth-sessionp (fn-own-conn-session conn)))
            (fn-own-conn-boundedp
             (fn-own-conn-make cid version frontier wire
                               (fn-auth-with-base
                                (fn-own-conn-session conn)
                                (fn-peer-with-base
                                 (fn-auth-session-base
                                  (fn-own-conn-session conn))
                                 (fn-post-make-session
                                  (fn-nntp-set-cursor
                                   (fn-nntp-open-session archive)
                                   (fn-nntp-session-group
                                    (fn-post-session-base
                                     (fn-peer-session-base
                                      (fn-auth-session-base
                                       (fn-own-conn-session conn)))))
                                   (fn-nntp-session-current
                                    (fn-post-session-base
                                     (fn-peer-session-base
                                      (fn-auth-session-base
                                       (fn-own-conn-session conn))))))
                                  (fn-post-session-awaiting
                                   (fn-peer-session-base
                                    (fn-auth-session-base
                                     (fn-own-conn-session conn)))))))
                               archive config observation)
             groups))
   :hints (("Goal"
            :cases ((fn-nntp-session-group
                     (fn-post-session-base
                      (fn-peer-session-base
                       (fn-auth-session-base (fn-own-conn-session conn))))))
            :in-theory (e/d (fn-own-conn-boundedp)
                            (fn-auth-sessionp fn-post-sessionp fn-nntp-sessionp
                             (:d fn-peer-sessionp) (:d fn-peer-with-base)
                             fn-nntp-set-cursor fn-nntp-open-session))))))

(local
 (defthm fn-own-advance-repins-the-connection
   (implies (and (fn-own-relation o)
                 (fn-own-find-conn id (fn-own-conns o)))
            (and (equal (fn-own-conn-version
                         (fn-own-find-conn id (fn-own-conns (fn-own-advance o id))))
                        (fn-own-view-version (fn-own-view o)))
                 (equal (fn-own-conn-archive
                         (fn-own-find-conn id (fn-own-conns (fn-own-advance o id))))
                        (fn-own-view-archive (fn-own-view o)))))
   :hints (("Goal"
            :use ((:instance fn-own-find-conn-okp
                             (conns (fn-own-conns o))
                             (groups (fn-sn-groups (fn-own-store o)))
                             (capacity (fn-sn-capacity (fn-own-store o)))
                             (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
                  (:instance fn-own-advanced-session-is-bounded
                             (conn (fn-own-find-conn id (fn-own-conns o)))
                             (groups (fn-sn-groups (fn-own-store o)))
                             (cid id)
                             (version (fn-own-view-version (fn-own-view o)))
                             (frontier (fn-own-view-frontier (fn-own-view o)))
                             (wire (fn-own-conn-wire (fn-own-find-conn id (fn-own-conns o))))
                             (archive (fn-own-view-archive (fn-own-view o)))
                             (config (fn-own-conn-config (fn-own-find-conn id (fn-own-conns o))))
                             (observation (fn-own-conn-observation
                                           (fn-own-find-conn id (fn-own-conns o)))))
                  (:instance fn-own-conn-boundedp-is-post-session
                             (conn (fn-own-find-conn id (fn-own-conns o)))
                             (groups (fn-sn-groups (fn-own-store o))))
                  (:instance fn-own-conn-boundedp-is-auth-session
                             (conn (fn-own-find-conn id (fn-own-conns o)))
                             (groups (fn-sn-groups (fn-own-store o))))
                  ; the re-pinned connection is what the table then holds:
                  ; supplied by :use because the rule's left-hand side is
                  ; keyed on (fn-own-conn-id conn) and the goal has already
                  ; normalised that to id.  The session here is
                  ; `fn-own-advance's own (books/owner.lisp): auth over peer
                  ; over the rebuilt POST base, THREE wrappers.  It stood at
                  ; two until this lane, which is the same merge residue as
                  ; the lemma above.
                  (:instance fn-own-find-conn-of-replace-conn-same
                             (conns (fn-own-conns o))
                             (conn
                              (fn-own-conn-make-group-indexed
                               (fn-own-conn-id (fn-own-find-conn id (fn-own-conns o)))
                               (fn-own-view-version (fn-own-view o))
                               (fn-own-view-frontier (fn-own-view o))
                               (fn-own-conn-wire (fn-own-find-conn id (fn-own-conns o)))
                               (fn-auth-with-base
                                (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o)))
                                (fn-peer-with-base
                                 (fn-auth-session-base
                                  (fn-own-conn-session
                                   (fn-own-find-conn id (fn-own-conns o))))
                                 (fn-post-make-session
                                  (fn-nntp-set-cursor
                                   (fn-nntp-open-session
                                    (fn-own-view-archive (fn-own-view o)))
                                   (fn-nntp-session-group
                                    (fn-post-session-base
                                     (fn-peer-session-base
                                      (fn-auth-session-base
                                       (fn-own-conn-session
                                        (fn-own-find-conn id (fn-own-conns o)))))))
                                   (fn-nntp-session-current
                                    (fn-post-session-base
                                     (fn-peer-session-base
                                      (fn-auth-session-base
                                       (fn-own-conn-session
                                        (fn-own-find-conn id (fn-own-conns o))))))))
                                  (fn-post-session-awaiting
                                   (fn-peer-session-base
                                    (fn-auth-session-base
                                     (fn-own-conn-session
                                      (fn-own-find-conn id (fn-own-conns o)))))))))
                               (fn-own-view-archive (fn-own-view o))
                               (fn-own-conn-config (fn-own-find-conn id (fn-own-conns o)))
                               (fn-own-conn-observation
                                (fn-own-find-conn id (fn-own-conns o)))
                               (fn-own-view-verdicts (fn-own-view o))
                               (fn-own-view-index (fn-own-view o))
                               (fn-own-view-group-index (fn-own-view o)) (fn-own-view-control (fn-own-view o))))))
            :in-theory (e/d (fn-own-relation fn-own-advance fn-own-set-conns)
                            (fn-own-conn-boundedp fn-own-find-conn-okp
                             fn-own-conn-make-group-indexed
                             fn-post-sessionp fn-nntp-open-session
                             fn-own-advanced-session-is-bounded))))))

; K1 read-back.  After a 240 for connection `id', that connection is pinned
; to the committed view, so the served step its next GROUP or ARTICLE runs
; (fn-own-read-is-served-step-on-pinned-prefix) is over the prefix that
; contains its own article.  Every other connection is found exactly as it
; was: fn-own-outcome-touches-only-its-connection above.
(defthm fn-own-durable-outcome-repins-the-poster
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o))
                (fn-own-inflight o)
                (equal (fn-own-sub-id (fn-own-inflight o)) id)
                (equal (fn-own-outcome-completion o word) :durable))
           (and (equal (fn-own-conn-version
                        (fn-own-find-conn id (fn-own-conns (cdr (fn-own-outcome o id word)))))
                       (fn-own-view-version (fn-own-view o)))
                (equal (fn-own-conn-archive
                        (fn-own-find-conn id (fn-own-conns (cdr (fn-own-outcome o id word)))))
                       (fn-own-view-archive (fn-own-view o)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-advance-repins-the-connection
                            (o (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                            (fn-own-next-id o) (fn-own-max-conns o)
                                            (if (equal (fn-own-pending o) id)
                                                nil (fn-own-pending o))
                                            (fn-own-ledger o) (fn-own-clock o)
                                            (fn-own-facts o) (fn-own-config o)
                                            (fn-own-queue o) nil
                                            (if (equal (fn-own-outcome-completion
                                                        o word)
                                                       :durable)
                                                (fn-own-feed-durable
                                                 o (fn-own-inflight o))
                                                (fn-own-feeds o))))))
           :in-theory (e/d (fn-own-relation fn-own-outcome)
                           (fn-own-advance fn-own-conn-boundedp
                            fn-served-post-outcome fn-own-outcome-completion
                            fn-own-advance-repins-the-connection)))))

(local
 (defthm fn-own-post-outcome-answers
   (implies (fn-post-sessionp ps)
            (consp (fn-post-result-effects (fn-nntp-post-outcome ps completion))))
   :hints (("Goal" :in-theory (e/d (fn-nntp-post-outcome fn-post-single fn-nntp-single)
                                   (fn-post-sessionp))))))

(local
 (defthm fn-own-last-member
   (implies (consp l) (member-equal (car (last l)) l))))

; A 240 on the wire names a durable record.  If the outcome rendered for a
; connection is the :durable line, then a submission of that connection is
; in flight, a completion was consumed into the ledger after it was taken
; (fn-own-complete consumes the actual fn-sn-finish, whose acknowledged pair
; has a record: fn-sn-finish-acknowledges-exact-pair through
; fn-own-completion-pair-has-record), and the newest ledger pair has a
; record in the durable history.  240 from any other word, or from a host
; that claims :durable without a consumed completion, is impossible
; (fn-post-outcome-240-only-for-a-durable-observation).
; `(fn-own-find-conn id (fn-own-conns o))' was a hypothesis here and is
; DELETED (docs/proof-style.md section 5: a hypothesis with no violating
; value is unnecessary).  Its teeth used to be an absent connection at which
; the equality still held, because `fn-nntp-post-outcome' answered a
; malformed session with NO effects and `fn-own-outcome' answers an unknown
; connection with none either.  Since `w10/session-depth' a malformed
; session is answered 403, the fourth outcome, so the two sides differ at
; every connection-free state and the equality now carries the connection
; itself.  The separation is asserted in `tests/acl2/owner-tests.lisp'.
(defthm fn-own-durable-reply-names-a-durable-record
  (implies (and (fn-own-relation o)
                (equal (car (fn-own-outcome o id word))
                       (let ((conn (fn-own-find-conn id (fn-own-conns o))))
                         (fn-served-result-effects
                          (fn-served-post-outcome
                           (fn-served-make-conn (fn-own-conn-wire conn)
                                                (fn-own-conn-session conn)
                                                (fn-own-conn-archive conn)
                                                (fn-own-conn-config conn)
                                                (fn-own-conn-observation conn)
                                                (fn-own-clock o))
                           :durable)))))
           (and (fn-own-inflight o)
                (equal (fn-own-sub-id (fn-own-inflight o)) id)
                (equal word :durable)
                (natp (fn-own-sub-mark (fn-own-inflight o)))
                (< (fn-own-sub-mark (fn-own-inflight o)) (len (fn-own-ledger o)))
                (fn-sf-record-has-pairp (car (last (fn-own-ledger o)))
                                        (fn-sf-records (fn-sn-files (fn-own-store o))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-relation-conns-and-ledger)
                 (:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-own-conn-boundedp-is-post-session
                            (conn (fn-own-find-conn id (fn-own-conns o)))
                            (groups (fn-sn-groups (fn-own-store o))))
                 ; The POST session is the peer session's base, and the peer
                 ; session is the AUTH session's base: `fn-served-post-outcome'
                 ; (books/served.lisp) hands `fn-nntp-post-outcome' exactly
                 ; `(fn-peer-session-base (fn-auth-session-base ...))', so
                 ; every `ps' below is that term.  It stood one wrapper short
                 ; from `1019c97' until this lane.  The seven field facts of
                 ; fn-peer-sessionp-forward-fields are not used: an instance
                 ; of them multiplied the case split to 386 goals (5.7 s).
                 (:instance fn-post-outcome-240-only-for-a-durable-observation
                            (ps (fn-peer-session-base
                                 (fn-auth-session-base
                                  (fn-own-conn-session
                                   (fn-own-find-conn id (fn-own-conns o))))))
                            (completion (fn-own-outcome-rendering o word)))
                 (:instance fn-own-ledger-durablep-member
                            (ledger (fn-own-ledger o))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))
                            (pair (car (last (fn-own-ledger o)))))
                 (:instance fn-own-last-member (l (fn-own-ledger o)))
                 (:instance fn-own-post-outcome-answers
                            (ps (fn-peer-session-base
                                 (fn-auth-session-base
                                  (fn-own-conn-session
                                   (fn-own-find-conn id (fn-own-conns o))))))
                            (completion :durable)))
           :in-theory (e/d (fn-served-post-outcome)
                           (fn-own-relation fn-own-conn-boundedp fn-own-find-conn-okp
                            fn-own-conns-okp fn-own-conn-group-index
                            fn-own-find-conn last fn-own-facts-okp
                            fn-own-advance fn-own-feed-durable
                            fn-own-conn-boundedp-is-post-session
                            fn-own-ledger-durablep-member fn-own-last-member
                            fn-nntp-post-outcome fn-post-sessionp
                            fn-own-post-outcome-answers
                            fn-own-prefix-archive fn-own-view-okp
                            fn-own-ledger-durablep
                            fn-midx-correspondencep fn-gidx-build)))))

;
; A consumed completion is never answered as a refusal (P2's wire half;
; campaign W2, 2026-09-24).  Once fn-own-complete has consumed a completion
; into the ledger after this submission was taken, the reply fn-own-outcome
; renders for its connection -- the function the host calls at
; host/owner-host.lisp fn-owner-outcome -- is the 240 when the host's word is
; :durable and the uncertain `441 ... do not repost' for EVERY other word.
; No host word, and in particular no OS error the host classified as a
; refusal, turns a durable record into `441 ... refused'.
(defthm fn-own-consumed-completion-is-240-or-uncertain
  (implies (and (fn-own-find-conn id (fn-own-conns o))
                (equal (fn-own-sub-id (fn-own-inflight o)) id)
                (natp (fn-own-sub-mark (fn-own-inflight o)))
                (< (fn-own-sub-mark (fn-own-inflight o)) (len (fn-own-ledger o))))
           (equal (car (fn-own-outcome o id word))
                  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
                    (fn-served-result-effects
                     (fn-served-post-outcome
                      (fn-served-make-conn-group-indexed
                       (fn-own-conn-wire conn) (fn-own-conn-session conn)
                       (fn-own-conn-archive conn) (fn-own-conn-config conn)
                       (fn-own-conn-observation conn) (fn-own-clock o)
                       (fn-own-conn-verdicts conn) (fn-own-conn-index conn)
                       (fn-own-conn-group-index conn) (fn-own-conn-control conn))
                      (if (equal word :durable) :durable :uncertain))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-outcome fn-own-outcome-completion
                                   fn-own-outcome-rendering
                                   fn-own-completion-consumedp)
                                  (fn-served-post-outcome fn-own-advance
                                   fn-own-feed-durable fn-own-find-conn
                                   fn-served-make-conn-group-indexed
                                   fn-own-refusal-wordp)))))

; -----------------------------------------------------------------------------
; Clock-stamped group facts: no fact without an observation; the live group
; view is the replay of the fact log, and the log only grows.

(defthm fn-own-declare-group-without-clock-is-refused
  (implies (not (fn-clock-observationp (fn-own-clock o)))
           (equal (fn-own-declare-group o name) o)))

(defthm fn-own-facts-okp-member
  (implies (and (fn-own-facts-okp facts)
                (member-equal fact facts))
           (fn-own-group-factp fact))
  :hints (("Goal" :induct (fn-own-facts-okp facts)
           :in-theory (disable fn-own-group-factp))))

(defthm fn-own-every-fact-is-clock-stamped
  (implies (and (fn-own-relation o)
                (member-equal fact (fn-own-facts o)))
           (and (fn-own-group-factp fact)
                (fn-clock-observationp (fn-own-group-fact-stamp fact))))
  :hints (("Goal" :use ((:instance fn-own-facts-okp-member (facts (fn-own-facts o))))
           :in-theory (e/d (fn-own-relation fn-own-group-factp)
                           (fn-own-facts-okp fn-own-facts-okp-member
                            fn-own-conn-boundedp)))))

(defthm fn-own-replay-facts-append
  (equal (fn-own-replay-facts (append a b))
         (append (fn-own-replay-facts a) (fn-own-replay-facts b))))

(defthm fn-own-declared-group-is-replayed
  (implies (and (stringp name)
                (fn-clock-observationp (fn-own-clock o)))
           (member-equal name (fn-own-replay-facts
                               (fn-own-facts (fn-own-declare-group o name)))))
  :hints (("Goal" :in-theory (disable fn-own-group-factp))))

; -----------------------------------------------------------------------------
; Export theory.  Keystones and the relation's list vocabulary stay enabled;
; the relation itself, the per-event preservation lemmas and the store facts
; proved here for the owner's own use are withdrawn under one name.

(deftheory fn-own-invariants-vocabulary
  '(fn-own-take-of-len fn-own-prefixp-len fn-own-take-of-prefix
    fn-own-prefix-archive-of-prefix fn-own-has-pairp-of-prefix
    fn-own-member-of-append-last fn-own-member-of-append-left
    fn-own-conn-okp fn-own-view-okp fn-own-relation
    fn-own-conns-okp-of-prefix fn-own-view-okp-of-prefix
    fn-own-ledger-durablep-of-prefix fn-own-ledger-durablep-append
    fn-own-ledger-durablep-member fn-own-facts-okp-append
    fn-own-find-conn-okp fn-own-find-conn-id fn-own-replace-conn-okp
    fn-own-replace-conn-len fn-own-remove-conn-okp fn-own-remove-conn-len
    fn-own-ids-below-next-p fn-own-replace-conn-ids-below-next
    fn-own-remove-conn-ids-below-next fn-own-ids-below-next-p-of-open
    fn-own-idle-node-is-replay fn-own-related-records-true-list
    fn-own-relation-records-true-list
    fn-own-related-frontier-natural fn-own-snrt-step-keeps-configuration
    fn-own-snrt-step-preserves-relation fn-own-snrt-step-records-prefix
    fn-own-completion-pair-has-record fn-own-completion-needs-completing-phase
    fn-own-crash-image-extends-records
    fn-own-refresh-keeps-fields fn-own-refresh-preserves-relation
    fn-own-open-session-boundedp fn-own-open-preserves-relation
    fn-own-read-preserves-relation fn-own-read-step-preserves-relation
    fn-own-advance-preserves-relation fn-own-close-preserves-relation
    fn-own-begin-preserves-relation fn-own-store-step-preserves-relation
    fn-own-complete-preserves-relation fn-own-reopen-preserves-relation
    fn-own-observe-preserves-relation fn-own-group-fact-make-is-fact
    fn-own-declare-group-preserves-relation fn-own-configure-preserves-relation
    fn-own-take-submission-preserves-relation fn-own-outcome-preserves-relation
    fn-own-find-conn-of-replace-conn-other fn-own-find-conn-of-remove-conn-other
    fn-own-conn-boundedp-is-post-session
    ; free-variable `groups' on its one hypothesis, so as a rewrite rule it
    ; would be tried on every `fn-auth-sessionp' term an includer states,
    ; exactly as its `-is-post-session' sibling would.  Both are withdrawn;
    ; this book reaches them with `:use' and so should an includer.
    fn-own-conn-boundedp-is-auth-session
    fn-own-step-preserves-relation
    fn-own-start-relation fn-own-complete-ledger-is-exact-pair
    fn-own-connection-events-keep-store-bound-and-ledger
    fn-own-step-records-prefix fn-own-run-records-prefix
    fn-own-min-pinned-below-floor fn-own-min-pinned-below-found
    fn-own-conns-okp-are-bounded fn-own-step-keeps-max-conns
    fn-own-run-keeps-max-conns fn-own-step-ledger-grows fn-own-run-ledger-grows
    fn-own-facts-okp-member fn-own-replay-facts-append
    fn-own-take-installs-the-queued-submission-whatever-it-carries
    fn-own-transit-outcome-touches-only-its-connection
    fn-own-transit-outcome-needs-a-transit-submission))

(in-theory (disable fn-own-invariants-vocabulary))
