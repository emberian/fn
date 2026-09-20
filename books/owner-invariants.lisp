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
;   fn-own-outcome-completion-is-one-of-three          (POST outcome; new)
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

(local (in-theory (enable fn-own-vocabulary fn-ag-append fn-ag-member)))

; List-recursive vocabulary of other clusters that must stay closed here so
; the proofs below see it only through the cited keystones.
(local (in-theory (disable fn-sf-record-has-pairp fn-sf-prefixp
                           fn-served-reply-octets fn-served-submission
                           fn-served-closingp fn-served-chunk-listp
                           fn-served-concat fn-nntp-session-consistentp
                           fn-nntp-projectionp)))

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

(defun fn-own-conn-okp (conn groups capacity records)
  (and (fn-own-conn-shapep conn)
       (natp (fn-own-conn-id conn))
       (natp (fn-own-conn-version conn))
       (<= (fn-own-conn-version conn) (len records))
       (natp (fn-own-conn-frontier conn))
       (equal (fn-own-conn-archive conn)
              (fn-own-prefix-archive groups capacity records
                                     (fn-own-conn-version conn)
                                     (fn-own-conn-frontier conn)))
       (fn-own-conn-boundedp conn groups)))

(defun fn-own-conns-okp (conns groups capacity records)
  (if (consp conns)
      (and (fn-own-conn-okp (car conns) groups capacity records)
           (fn-own-conns-okp (cdr conns) groups capacity records))
    (null conns)))

(defun fn-own-view-okp (view groups capacity records)
  (and (fn-own-view-shapep view)
       (natp (fn-own-view-version view))
       (<= (fn-own-view-version view) (len records))
       (natp (fn-own-view-frontier view))
       (equal (fn-own-view-archive view)
              (fn-own-prefix-archive groups capacity records
                                     (fn-own-view-version view)
                                     (fn-own-view-frontier view)))))

(defun fn-own-ledger-durablep (ledger records)
  (if (consp ledger)
      (and (fn-sf-record-has-pairp (car ledger) records)
           (fn-own-ledger-durablep (cdr ledger) records))
    (null ledger)))

(defun fn-own-relation (o)
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
         (fn-own-ledger-durablep (fn-own-ledger o) records)
         (or (null (fn-own-clock o))
             (fn-clock-observationp (fn-own-clock o)))
         (fn-own-facts-okp (fn-own-facts o)))))

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
  :hints (("Goal" :induct (fn-own-replace-conn conn conns))))

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

; -----------------------------------------------------------------------------
; Facts about the embedded store the events need

(defthm fn-own-idle-node-is-replay
  (implies (and (fn-snt-relation s)
                (fn-own-store-idlep s))
           (equal (fn-sn-node s)
                  (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                     (fn-sf-records (fn-sn-files s))
                                     (fn-sf-frontier (fn-sn-files s)))))
  :hints (("Goal" :in-theory (e/d (fn-snt-relation fn-own-store-idlep)
                                  (fn-snt-pending-linkp fn-sf-record-phasep)))))

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

; Every store transition keeps the fixed configuration.
(defthm fn-own-snrt-step-keeps-configuration
  (and (equal (fn-sn-groups (fn-snrt-step s event)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-snrt-step s event)) (fn-sn-capacity s)))
  :hints (("Goal" :in-theory (e/d (fn-snrt-step fn-snt-step fn-sn-prepare fn-sn-io
                                   fn-sn-finish fn-sn-crash fn-sn-recover
                                   fn-sn-refuse-reservation fn-sn-known-abort
                                   fn-sn-update)
                                  (fn-sn-record-bindsp fn-sn-prepare-node
                                   fn-sf-prepare-record fn-sn-file-step
                                   fn-sf-core-completion fn-sf-emit-success
                                   fn-sf-crash fn-sf-crash-choicep fn-sf-recover
                                   fn-sn-refuse-reservation-enabledp
                                   fn-sn-known-abort-enabledp
                                   fn-sn-known-abort-files
                                   fn-sn-fence-node fn-sn-resolve-node
                                   fn-sf-refuse-reservation fn-replay-advance-txid
                                   fn-replay-advance-okp fn-node-complete
                                   fn-sf-record-candidate fn-record-txid
                                   fn-record-generation)))))

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

(defthm fn-own-refresh-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-refresh o)))
  :hints (("Goal"
           :use ((:instance fn-own-related-records-true-list (s (fn-own-store o)))
                 (:instance fn-own-related-frontier-natural (s (fn-own-store o)))
                 (:instance fn-own-idle-node-is-replay (s (fn-own-store o))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-store-idlep fn-own-idle-node-is-replay
                            fn-own-related-records-true-list
                            fn-own-related-frontier-natural))
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
                                       observation injection)))
                     archive config observation)
   groups)
  :hints (("Goal" :in-theory (enable fn-served-open fn-post-open-session
                                     fn-post-sessionp fn-nntp-open-session
                                     fn-nntp-make-session fn-nntp-sessionp
                                     fn-nntp-session-openp fn-nntp-session-group
                                     fn-nntp-session-current
                                     fn-nntp-session-projected))))

(defthm fn-own-open-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-open o))))
  :hints (("Goal" :in-theory (e/d (fn-own-relation) (fn-own-conn-boundedp)))))

(defthm fn-own-read-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-read o id octets))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-conn-boundedp fn-own-find-conn-okp)))))

(defthm fn-own-read-step-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-read-step o id event))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-conn-boundedp fn-own-find-conn-okp)))))

(defthm fn-own-advance-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-advance o id)))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-conn-boundedp fn-own-find-conn-okp)))))

(defthm fn-own-close-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-close o id)))
  :hints (("Goal" :in-theory (enable fn-own-relation))))

(defthm fn-own-begin-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-begin o id)))
  :hints (("Goal" :in-theory (enable fn-own-relation))))

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
                                            (fn-own-config o) (fn-own-queue o)
                                            (fn-own-inflight o))))
                 (:instance fn-own-snrt-step-records-prefix (s (fn-own-store o))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-refresh-preserves-relation fn-own-refresh
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
                                            (fn-own-inflight o))))
                 (:instance fn-snt-finish-preserves-relation (s (fn-own-store o)))
                 (:instance fn-snt-finish-image (s (fn-own-store o)))
                 (:instance fn-snt-finish-keeps-records (s (fn-own-store o)))
                 (:instance fn-own-completion-pair-has-record (s (fn-own-store o)))
                 (:instance fn-snt-relation-implies-structural-state (s (fn-own-store o))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-refresh-preserves-relation fn-own-refresh
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
                                (fn-own-facts o) (fn-own-config o) nil nil)))
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
                           (fn-own-refresh-preserves-relation fn-own-refresh
                            fn-sn-open-observed-success-has-live-history-relation
                            fn-sn-open-observed-success-exact-history
                            fn-sn-open-observed-success-configuration
                            fn-own-crash-image-extends-records
                            fn-own-related-records-true-list)))))

(defthm fn-own-observe-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-observe o obs)))
  :hints (("Goal" :in-theory (enable fn-own-relation))))

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
  :hints (("Goal" :in-theory (enable fn-own-relation))))

(defthm fn-own-take-submission-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-take-submission o)))
  :hints (("Goal" :in-theory (enable fn-own-relation))))

; The outcome releases the transaction and empties `inflight'; neither is
; read by the relation, so the only content is the :durable branch's
; fn-own-advance, which is fn-own-advance-preserves-relation above.
(local
 (defthm fn-own-outcome-body-preserves-relation
   (implies (fn-own-relation o)
            (fn-own-relation
             (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                          (fn-own-next-id o) (fn-own-max-conns o) p
                          (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                          (fn-own-config o) (fn-own-queue o) nil)))
   :hints (("Goal" :in-theory (enable fn-own-relation)))))

(defthm fn-own-outcome-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-own-outcome o id word))))
  :hints (("Goal"
           :use ((:instance fn-own-outcome-body-preserves-relation
                            (p (if (equal (fn-own-pending o) id)
                                   nil (fn-own-pending o)))))
           :in-theory (e/d (fn-own-outcome)
                           (fn-own-relation fn-own-outcome-completion
                            fn-served-post-outcome fn-own-advance
                            fn-own-outcome-body-preserves-relation)))))

; -----------------------------------------------------------------------------
; K6: every step, and every finite trace, preserves the relation; the store
; inside keeps fn-snt-relation.

(defthm fn-own-step-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (fn-own-step o event)))
  :hints (("Goal" :in-theory (disable fn-own-relation fn-own-open fn-own-read
                                      fn-own-read-step fn-own-advance fn-own-close
                                      fn-own-begin fn-own-store-step fn-own-complete
                                      fn-own-reopen fn-own-observe
                                      fn-own-declare-group fn-own-configure
                                      fn-own-take-submission fn-own-outcome))))

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
                                            (fn-own-view-make
                                             0 0 (fn-own-prefix-archive
                                                  (fn-sn-groups store)
                                                  (fn-sn-capacity store)
                                                  (fn-sf-records (fn-sn-files store))
                                                  0 0))
                                            nil 0 max-conns nil nil nil nil
                                            nil nil nil))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-refresh-preserves-relation fn-own-refresh
                            fn-own-prefix-archive)))))

; host/owner-host.lisp, fn-owner-recover: the owner is started over the
; state fn-sn-open-observed returned for the image on disk.
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
; pinned frontier.  The effects the host writes are exactly this call's.

(defthm fn-own-read-is-served-step-on-pinned-prefix
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o)))
           (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
                  (s (fn-own-store o)))
             (equal (car (fn-own-read o id octets))
                    (fn-served-result-effects
                     (fn-served-step
                      (fn-served-make-conn
                       (fn-own-conn-wire conn)
                       (fn-own-conn-session conn)
                       (fn-node-acceptance
                        (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                           (fn-own-take (fn-own-conn-version conn)
                                                        (fn-sf-records (fn-sn-files s)))
                                           (fn-own-conn-frontier conn)))
                       (fn-own-conn-config conn)
                       (fn-own-conn-observation conn)
                       (fn-own-clock o))
                      octets)))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-conn-boundedp fn-own-find-conn-okp)))))

(defthm fn-own-read-is-served-step-on-pinned-prefix-after-any-trace
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns (fn-own-run o events))))
           (let* ((final (fn-own-run o events))
                  (conn (fn-own-find-conn id (fn-own-conns final)))
                  (s (fn-own-store final)))
             (equal (car (fn-own-read final id octets))
                    (fn-served-result-effects
                     (fn-served-step
                      (fn-served-make-conn
                       (fn-own-conn-wire conn)
                       (fn-own-conn-session conn)
                       (fn-node-acceptance
                        (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                           (fn-own-take (fn-own-conn-version conn)
                                                        (fn-sf-records (fn-sn-files s)))
                                           (fn-own-conn-frontier conn)))
                       (fn-own-conn-config conn)
                       (fn-own-conn-observation conn)
                       (fn-own-clock final))
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
; first `version` durable records, advanced to the pinned frontier.

(defthm fn-own-reader-sees-pinned-prefix-replay
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o)))
           (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
                  (s (fn-own-store o)))
             (equal (car (fn-own-read-step o id event))
                    (fn-served-result-effects
                     (fn-served-dispatch
                      (fn-served-make-conn
                       (fn-own-conn-wire conn)
                       (fn-own-conn-session conn)
                       (fn-node-acceptance
                        (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                           (fn-own-take (fn-own-conn-version conn)
                                                        (fn-sf-records (fn-sn-files s)))
                                           (fn-own-conn-frontier conn)))
                       (fn-own-conn-config conn)
                       (fn-own-conn-observation conn)
                       (fn-own-clock o))
                      event)))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-relation)
                           (fn-own-conn-boundedp fn-own-find-conn-okp)))))

(defthm fn-own-reader-sees-pinned-prefix-replay-after-any-trace
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns (fn-own-run o events))))
           (let* ((final (fn-own-run o events))
                  (conn (fn-own-find-conn id (fn-own-conns final)))
                  (s (fn-own-store final)))
             (equal (car (fn-own-read-step final id event))
                    (fn-served-result-effects
                     (fn-served-dispatch
                      (fn-served-make-conn
                       (fn-own-conn-wire conn)
                       (fn-own-conn-session conn)
                       (fn-node-acceptance
                        (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                           (fn-own-take (fn-own-conn-version conn)
                                                        (fn-sf-records (fn-sn-files s)))
                                           (fn-own-conn-frontier conn)))
                       (fn-own-conn-config conn)
                       (fn-own-conn-observation conn)
                       (fn-own-clock final))
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
  (and (equal (fn-own-store (cdr (fn-own-open o))) (fn-own-store o))
       (equal (fn-own-max-conns (cdr (fn-own-open o))) (fn-own-max-conns o))
       (equal (fn-own-ledger (cdr (fn-own-open o))) (fn-own-ledger o))
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

(defthm fn-own-step-records-prefix
  (implies (fn-own-relation o)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store o)))
                          (fn-sf-records (fn-sn-files (fn-own-store (fn-own-step o event))))))
  :hints (("Goal"
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
                           (fn-own-snrt-step-records-prefix fn-snt-finish-keeps-records
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
                            fn-own-ledger-durablep-of-prefix)))))

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

(defthm fn-own-find-conn-of-remove-conn-other
  (implies (not (equal id other))
           (equal (fn-own-find-conn other (fn-own-remove-conn id conns))
                  (fn-own-find-conn other conns)))
  :hints (("Goal" :induct (fn-own-remove-conn id conns))))

(defthm fn-own-read-touches-only-its-connection
  (implies (not (equal id other))
           (equal (fn-own-find-conn other (fn-own-conns (cdr (fn-own-read o id octets))))
                  (fn-own-find-conn other (fn-own-conns o))))
  :hints (("Goal" :in-theory (disable fn-served-step fn-own-conn-boundedp))))

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
                                   fn-own-conn-boundedp)))))

; The completion the reply renders is one of the three words, whatever the
; host said.
(defthm fn-own-outcome-completion-is-one-of-three
  (member-equal (fn-own-outcome-completion o word) '(:durable :refused :uncertain)))

(defthm fn-own-conn-boundedp-is-post-session
  (implies (fn-own-conn-boundedp conn groups)
           (fn-post-sessionp (fn-own-conn-session conn)))
  :hints (("Goal" :in-theory (enable fn-own-conn-boundedp))))

; -----------------------------------------------------------------------------
; Read-back: a 240 moves the poster's pin, and only the poster's.
;
; fn-own-advance rebuilds the connection's session over the committed view's
; archive, keeping the group and the cursor.  Both are carried by the old
; connection's boundedness, so the advance is never refused for a bounded
; connection: that is what makes the re-pin in fn-own-outcome unconditional
; rather than best-effort.

(local
 (defthm fn-own-advanced-session-is-bounded
   (implies (and (fn-own-conn-boundedp conn groups)
                 (fn-post-sessionp (fn-own-conn-session conn)))
            (fn-own-conn-boundedp
             (fn-own-conn-make cid version frontier wire
                               (fn-post-make-session
                                (fn-nntp-set-cursor
                                 (fn-nntp-open-session archive)
                                 (fn-nntp-session-group
                                  (fn-post-session-base (fn-own-conn-session conn)))
                                 (fn-nntp-session-current
                                  (fn-post-session-base (fn-own-conn-session conn))))
                                (fn-post-session-awaiting (fn-own-conn-session conn)))
                               archive config observation)
             groups))
   :hints (("Goal"
            :use ((:instance fn-nntp-consistent-session-is-session
                             (session (fn-nntp-open-session archive))
                             (archive archive))
                  (:instance fn-nntp-open-session-is-consistent (archive archive)))
            :in-theory (e/d (fn-own-conn-boundedp fn-post-sessionp fn-nntp-set-cursor)
                            (fn-nntp-open-session fn-nntp-sessionp
                             fn-nntp-consistent-session-is-session
                             fn-nntp-open-session-is-consistent))))))

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
                             (groups (fn-sn-groups (fn-own-store o)))))
            :in-theory (e/d (fn-own-relation fn-own-advance fn-own-set-conns)
                            (fn-own-conn-boundedp fn-own-find-conn-okp
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
                                            (fn-own-queue o) nil))))
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
(defthm fn-own-durable-reply-names-a-durable-record
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o))
                (equal (car (fn-own-outcome o id word))
                       (let ((conn (fn-own-find-conn id (fn-own-conns o))))
                         (fn-served-result-effects
                          (fn-served-post-outcome
                           (fn-served-make-conn (fn-own-conn-wire conn)
                                                (fn-own-conn-session conn)
                                                (fn-own-conn-archive conn)
                                                (fn-own-conn-config conn)
                                                (fn-own-conn-observation conn))
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
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-own-conn-boundedp-is-post-session
                            (conn (fn-own-find-conn id (fn-own-conns o)))
                            (groups (fn-sn-groups (fn-own-store o))))
                 (:instance fn-post-outcome-240-only-for-a-durable-observation
                            (ps (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))))
                            (completion (fn-own-outcome-completion o word)))
                 (:instance fn-own-ledger-durablep-member
                            (ledger (fn-own-ledger o))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o))))
                            (pair (car (last (fn-own-ledger o)))))
                 (:instance fn-own-last-member (l (fn-own-ledger o)))
                 (:instance fn-own-post-outcome-answers
                            (ps (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))))
                            (completion :durable)))
           :in-theory (e/d (fn-own-relation fn-served-post-outcome)
                           (fn-own-conn-boundedp fn-own-find-conn-okp
                            fn-own-conn-boundedp-is-post-session
                            fn-own-ledger-durablep-member fn-own-last-member
                            fn-nntp-post-outcome fn-post-sessionp
                            fn-own-post-outcome-answers
                            fn-own-prefix-archive)))))

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
    fn-own-step-preserves-relation
    fn-own-start-relation fn-own-complete-ledger-is-exact-pair
    fn-own-connection-events-keep-store-bound-and-ledger
    fn-own-step-records-prefix fn-own-run-records-prefix
    fn-own-min-pinned-below-floor fn-own-min-pinned-below-found
    fn-own-conns-okp-are-bounded fn-own-step-keeps-max-conns
    fn-own-run-keeps-max-conns fn-own-step-ledger-grows fn-own-run-ledger-grows
    fn-own-facts-okp-member fn-own-replay-facts-append))

(in-theory (disable fn-own-invariants-vocabulary))
