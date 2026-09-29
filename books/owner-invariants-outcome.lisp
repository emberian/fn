; fn: the served POST outcome -- read and outcome touch only their
; connection, the read-back re-pin, the durable reply, the consumed
; completion -- and the clock-stamped facts.  Part 4 of 4 of
; books/owner-invariants.lisp.

(in-package "ACL2")
(include-book "owner-invariants-served")

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

; Local copy (from owner-invariants-step; cited by :use below).
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
    id (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
   (fn-own-conn-boundedp
    (fn-own-find-conn
     id (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
    (fn-state-groups
     (fn-own-conn-archive
      (fn-own-find-conn
       id (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))))))
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

; The served connection the owner builds, field by field (proof vocabulary
; for the read-back theorems below; books/owner.lisp fn-own-served-conn).
(local
 (defthm fn-own-served-conn-fields
   (let ((c (fn-own-served-conn o conn session)))
     (and (equal (fn-served-conn-wire c) (fn-own-conn-wire conn))
          (equal (fn-served-conn-session c) session)
          (equal (fn-served-conn-archive c) (fn-own-conn-archive conn))
          (equal (fn-served-conn-config c) (fn-own-conn-config conn))
          (equal (fn-served-conn-observation c) (fn-own-conn-observation conn))
          (equal (fn-served-conn-injection c) (fn-own-clock o))
          (equal (fn-served-conn-verdicts c) (fn-own-conn-verdicts conn))
          (equal (fn-served-conn-index c) (fn-own-conn-index conn))
          (equal (fn-served-conn-group-index c) (fn-own-conn-group-index conn))
          (equal (fn-served-conn-control c) (fn-own-conn-control conn))
          (equal (fn-served-conn-pinned c)
                 (fn-served-pinned-make (fn-own-conn-version conn)
                                        (fn-own-conn-frontier conn) nil))
          (equal (fn-served-conn-live c) (fn-own-view-live (fn-own-view o)))))
   :hints (("Goal" :in-theory (enable fn-own-served-conn)))))

; The surviving connection IS the connection fn-own-finish-read rebuilt from
; the served result (the pin from the served connection, the identifier and
; the pinned configuration and observation from the found connection).
; A read on an unknown identifier changes nothing, so a survivor had an original.
(local
 (defthm fn-own-read-of-unknown-keeps-owner
   (implies (not (fn-own-find-conn id (fn-own-conns o)))
            (equal (cdr (fn-own-read o id octets fn-arena)) o))
   :hints (("Goal" :in-theory (e/d (fn-own-read fn-own-read-full)
                                   (fn-served-step fn-own-finish-read fn-own-served-conn))))))

; The read's third answer, without opening the read.
(local
 (defthm fn-own-read-repinned-is-the-served-flag
   (implies (fn-own-find-conn id (fn-own-conns o))
            (equal (fn-own-read-repinned o id octets fn-arena)
                   (fn-own-result-repinned
                    (fn-served-step
                     (fn-own-served-conn o (fn-own-find-conn id (fn-own-conns o))
                                         (fn-own-conn-live-session
                                          o (fn-own-find-conn id (fn-own-conns o))))
                     octets fn-arena))))
   :hints (("Goal" :in-theory (e/d (fn-own-read-repinned fn-own-read-full)
                                   (fn-served-step fn-own-finish-read fn-own-served-conn
                                    fn-own-result-repinned fn-own-conn-live-session))))))

(local
 (defthm fn-own-read-survivor-is-next
   (implies
    (fn-own-find-conn id (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
    (equal (fn-own-find-conn id (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
           (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
                  (sconn (fn-served-result-conn
                          (fn-served-step
                           (fn-own-served-conn o conn (fn-own-conn-live-session o conn))
                           octets fn-arena)))
                  (pinned (fn-served-conn-pinned sconn)))
             (fn-own-conn-make-group-indexed
              id (fn-served-pinned-version pinned) (fn-served-pinned-frontier pinned)
              (fn-served-conn-wire sconn) (fn-served-conn-session sconn)
              (fn-served-conn-archive sconn)
              (fn-own-conn-config conn) (fn-own-conn-observation conn)
              (fn-served-conn-verdicts sconn) (fn-served-conn-index sconn)
              (fn-served-conn-group-index sconn) (fn-served-conn-control sconn)))))
   :hints (("Goal"
            :use ((:instance fn-own-find-conn-id (conns (fn-own-conns o))))
            :in-theory (e/d (fn-own-read fn-own-read-full fn-own-finish-read
                             fn-own-set-conns fn-own-enqueue)
                            (fn-served-step fn-own-conn-boundedp
                             fn-own-conn-make-group-indexed fn-own-served-conn
                             fn-served-make-conn-group-indexed fn-served-make-conn-live
                             fn-own-conn-live-session))))))

; NNT-042: the survivor keeps its identifier; its pin is the old one or the
; view's (fn-served-step-pin-is-old-or-live), and which one is what
; fn-own-read-repinned says.
(defthm fn-own-read-survivor-keeps-historical-fields
  (implies
   (fn-own-find-conn
    id (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
   (let ((old (fn-own-find-conn id (fn-own-conns o)))
         (next (fn-own-find-conn
                id (fn-own-conns (cdr (fn-own-read o id octets fn-arena)))))
         (view (fn-own-view o)))
     (and (fn-own-conn-shapep next)
          (equal (fn-own-conn-id next) (fn-own-conn-id old))
          (equal (fn-own-conn-config next) (fn-own-conn-config old))
          (equal (fn-own-conn-observation next) (fn-own-conn-observation old))
          (if (fn-own-read-repinned o id octets fn-arena)
              (and (equal (fn-own-conn-version next) (fn-own-view-version view))
                   (equal (fn-own-conn-frontier next) (fn-own-view-frontier view))
                   (equal (fn-own-conn-archive next) (fn-own-view-archive view))
                   (equal (fn-own-conn-verdicts next) (fn-own-view-verdicts view))
                   (equal (fn-own-conn-index next) (fn-own-view-index view))
                   (equal (fn-own-conn-group-index next) (fn-own-view-group-index view))
                   (equal (fn-own-conn-control next) (fn-own-view-control view)))
            (and (equal (fn-own-conn-version next) (fn-own-conn-version old))
                 (equal (fn-own-conn-frontier next) (fn-own-conn-frontier old))
                 (equal (fn-own-conn-archive next) (fn-own-conn-archive old))
                 (equal (fn-own-conn-verdicts next) (fn-own-conn-verdicts old))
                 (equal (fn-own-conn-index next) (fn-own-conn-index old))
                 (equal (fn-own-conn-group-index next) (fn-own-conn-group-index old))
                 (equal (fn-own-conn-control next) (fn-own-conn-control old)))))))
  :hints (("Goal"
           :cases ((fn-own-find-conn id (fn-own-conns o)))
           :use ((:instance fn-own-find-conn-id
                            (conns (fn-own-conns o)))
                 (:instance fn-own-read-of-unknown-keeps-owner)
                 (:instance fn-served-step-pin-is-old-or-live
                            (conn (fn-own-served-conn
                                   o (fn-own-find-conn id (fn-own-conns o))
                                   (fn-own-conn-live-session
                                    o (fn-own-find-conn id (fn-own-conns o))))))
                 (:instance fn-own-served-conn-pin-cases
                            (conn (fn-own-find-conn id (fn-own-conns o)))
                            (session (fn-own-conn-live-session
                                      o (fn-own-find-conn id (fn-own-conns o))))
                            (sconn (fn-served-result-conn
                                    (fn-served-step
                                     (fn-own-served-conn
                                      o (fn-own-find-conn id (fn-own-conns o))
                                      (fn-own-conn-live-session
                                       o (fn-own-find-conn id (fn-own-conns o))))
                                     octets fn-arena))))
                 (:instance fn-served-pin-old-or-live-p-cases
                            (c0 (fn-own-served-conn
                                 o (fn-own-find-conn id (fn-own-conns o))
                                 (fn-own-conn-live-session
                                  o (fn-own-find-conn id (fn-own-conns o)))))
                            (c (fn-served-result-conn
                                (fn-served-step
                                 (fn-own-served-conn
                                  o (fn-own-find-conn id (fn-own-conns o))
                                  (fn-own-conn-live-session
                                   o (fn-own-find-conn id (fn-own-conns o))))
                                 octets fn-arena)))))
           :in-theory (e/d (fn-own-result-repinned
                            fn-own-read-survivor-is-next
                            fn-own-read-repinned-is-the-served-flag)
                           (fn-own-read fn-own-read-full fn-own-finish-read
                            fn-served-step fn-own-conn-boundedp
                            fn-own-conn-make-group-indexed fn-own-served-conn
                            fn-served-make-conn-group-indexed fn-served-make-conn-live
                            fn-served-pin-old-or-live-p fn-own-conn-live-session
                            fn-served-conn-pin fn-served-live-pin
                            fn-served-step-pin-is-old-or-live
                            fn-own-read-repinned fn-own-read-of-unknown-keeps-owner
                            ; the accessors stay closed so the -of-make
                            ; projections fire on the rebuilt connection
                            fn-own-conn-group-index fn-own-conn-control
                            fn-own-conn-id fn-own-conn-version fn-own-conn-frontier
                            fn-own-conn-wire fn-own-conn-session fn-own-conn-archive
                            fn-own-conn-config fn-own-conn-observation
                            fn-own-conn-verdicts fn-own-conn-index
                            fn-own-view-group-index fn-own-view-version
                            fn-own-view-frontier fn-own-view-archive
                            fn-own-view-verdicts fn-own-view-index
                            fn-ag-car fn-ag-cdr)))))

; The survivor's wire framing state is the served step's, and that step
; started from the connection's own wire (books/config-owner-read-invariants).
(defthm fn-own-read-survivor-wire-is-the-steps
  (implies
   (fn-own-find-conn
    id (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
   (let ((old (fn-own-find-conn id (fn-own-conns o))))
     (equal (fn-own-conn-wire
             (fn-own-find-conn id (fn-own-conns (cdr (fn-own-read o id octets fn-arena)))))
            (fn-served-conn-wire
             (fn-served-result-conn
              (fn-served-step (fn-own-served-conn o old (fn-own-conn-live-session o old))
                              octets fn-arena))))))
  :hints (("Goal"
           :use ((:instance fn-own-find-conn-id (conns (fn-own-conns o))))
           :in-theory (e/d (fn-own-read fn-own-read-full fn-own-finish-read
                            fn-own-set-conns fn-own-enqueue)
                           (fn-served-step fn-own-conn-boundedp
                            fn-own-conn-make-group-indexed fn-own-served-conn
                            fn-served-make-conn-group-indexed fn-served-make-conn-live
                            fn-own-conn-live-session)))))

(defthm fn-own-served-conn-wire
  (equal (fn-served-conn-wire (fn-own-served-conn o conn session))
         (fn-own-conn-wire conn))
  :hints (("Goal" :in-theory (enable fn-own-served-conn))))

(defthm fn-own-find-conn-of-remove-conn-other
  (implies (not (equal id other))
           (equal (fn-own-find-conn other (fn-own-remove-conn id conns))
                  (fn-own-find-conn other conns)))
  :hints (("Goal" :induct (fn-own-remove-conn id conns))))

(defthm fn-own-read-touches-only-its-connection
  (implies (not (equal id other))
           (equal (fn-own-find-conn other (fn-own-conns (cdr (fn-own-read o id octets fn-arena))))
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
                       (fn-own-sub-make-author (fn-own-sub-id (car (fn-own-queue o)))
                                               (fn-own-sub-version (car (fn-own-queue o)))
                                               (len (fn-own-ledger o))
                                               (fn-psub-unpack-decision
                                                (fn-own-sub-decision (car (fn-own-queue o))))
                                               (fn-own-sub-login (car (fn-own-queue o)))
                                               (fn-own-sub-account (car (fn-own-queue o)))))
                (equal (fn-own-queue (fn-own-take-submission o))
                       (cdr (fn-own-queue o)))
                (equal (fn-own-pending (fn-own-take-submission o))
                       (fn-own-sub-id (car (fn-own-queue o))))
                (equal (fn-own-store (fn-own-take-submission o)) (fn-own-store o))
                (equal (fn-own-conns (fn-own-take-submission o)) (fn-own-conns o))))
  :hints (("Goal" :in-theory (enable fn-own-take-submission))))

; KEYSTONE (lane chunked-body-2, B6b).  The queue holds a submission packed
; (fn-own-enqueue; books/packed-submission.lisp) and the take unpacks it: what
; the writer installs is exactly the decision the read enqueued -- the
; article's octets, its groups, every field -- whatever it carries.
(defthm fn-own-take-installs-the-enqueued-submission
  (implies (and (null (fn-own-inflight o))
                (null (fn-own-queue o))
                (null (fn-own-pending o))
                (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready))
           (equal (fn-own-inflight (fn-own-take-submission (fn-own-enqueue o sub)))
                  (fn-own-sub-make-author (fn-own-sub-id sub)
                                          (fn-own-sub-version sub)
                                          (len (fn-own-ledger o))
                                          (fn-own-sub-decision sub)
                                          (fn-own-sub-login sub)
                                          (fn-own-sub-account sub))))
  :hints (("Goal" :in-theory (e/d (fn-own-take-submission fn-own-enqueue)
                                  (fn-own-sub-fields-of-pack fn-own-sub-fields-of-unpack))
                  :use ((:instance fn-psub-unpack-of-pack-sub (x sub))))))

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
; fn-own-relation reads none of the pending, config, queue, inflight, feeds,
; node-secret and refused slots; an owner rebuilt with any of them keeps it.
(local
 (defthm fn-own-relation-of-make-with-same-core
   (implies (fn-own-relation o)
            (fn-own-relation
             (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                          (fn-own-next-id o) (fn-own-max-conns o) pending
                          (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                          config queue inflight feeds node-secret refused)))
   :hints (("Goal" :in-theory (e/d (fn-own-relation)
                                   (fn-own-view-okp fn-own-conns-okp
                                    fn-snt-relation fn-own-ids-below-next-p
                                    fn-own-ledger-durablep fn-own-facts-okp
                                    fn-clock-observationp fn-own-make))))))

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
           :use ((:instance fn-own-relation-of-make-with-same-core
                            (pending (if (equal (fn-own-pending o) id)
                                         nil (fn-own-pending o)))
                            (config (fn-own-config o)) (queue (fn-own-queue o))
                            (inflight nil)
                            (feeds (fn-own-feed-durable o (fn-own-inflight o)))
                            (node-secret (fn-own-node-secret o))
                            (refused (fn-own-refused o)))
                 (:instance fn-own-advance-repins-the-connection
                            (o (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                            (fn-own-next-id o) (fn-own-max-conns o)
                                            (if (equal (fn-own-pending o) id)
                                                nil (fn-own-pending o))
                                            (fn-own-ledger-field o) (fn-own-clock o)
                                            (fn-own-facts o) (fn-own-config o)
                                            (fn-own-queue o) nil
                                            (if (equal (fn-own-outcome-completion
                                                        o word)
                                                       :durable)
                                                (fn-own-feed-durable
                                                 o (fn-own-inflight o))
                                                (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o)))))
           :in-theory (e/d (fn-own-outcome)
                           (fn-own-relation fn-own-advance fn-own-conn-boundedp
                            fn-served-post-outcome fn-own-outcome-completion
                            fn-own-advance-repins-the-connection
                            fn-own-feed-durable fn-own-find-conn
                            fn-own-make)))))

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
                            (completion (fn-own-post-rendering o word)))
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
; :durable (the 240 naming a refused key change for
; :durable-key-change-refused) and the uncertain `441 ... do not repost' for EVERY other word.
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
                      (cond ((equal word :durable) :durable)
                            ;; PKT-473 (PRF-184): durable, naming the
                            ;; refused key change.
                            ((equal word :durable-key-change-refused) word)
                            (t :uncertain)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-outcome fn-own-outcome-completion
                                   fn-own-outcome-rendering
                                   fn-own-post-rendering fn-own-durable-wordp
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
