; fn: the mutable service owner over the live fn-sn composition (C1-05).
;
; One owner process serializes mutations of one store while readers observe a
; committed version.  This book is the executable model the host drives
; through host/owner-host.lisp (tools/run_owner.py).  It performs no I/O.
;
; The owner record is
;   (store view conns next-id max-conns pending ledger clock facts
;    config queue inflight feeds node-secret refused)
; where
;   store     the actual fn-sn composition (books/store-node.lisp), stepped
;             only through fn-snrt-step and fn-sn-finish;
;   view      the committed view (version frontier archive): version is the
;             generation, the length of the durable record history; archive
;             is the acceptance projection of the node at that generation;
;   conns     the open connections, each
;             (id version frontier wire session archive config observation
;              verdicts):
;             pinned to one committed view and carrying the wire framing
;             state, the POST session, the posting configuration and the one
;             clock observation of one served connection (books/served.lisp);
;   next-id   the next connection identifier;
;   max-conns the configured bound on open connections;
;   pending   nil or the identifier of the connection that began the one
;             transaction the store admits at a time;
;   ledger    proof-only history: the (sequence . txid) pairs consumed by
;             fn-own-complete, in order.  The host keeps no such list; the
;             durability keystone reads it and the records carry the claim;
;   clock     nil or the latest fn-clock-observationp the host supplied;
;   facts     the group-configuration fact records, each stamped with the
;             clock observation current when it was created;
;   config    the posting configuration (fn-inj-configp, books/injection.lisp)
;             pinned into every connection at open; nil refuses POST with 440;
;   queue     the submissions served reads produced and the writer has not
;             taken, each (id version mark decision [login account]), in
;             arrival order; login is the AUTHINFO name and account the
;             principal id of an authenticated served POST
;             (fn-own-finish-read), both absent otherwise;
;   node-secret nil, or the node's key ring (books/node-secret.lisp
;             fn-ns-ringp: the current key epoch first, every retained
;             older one after it) the host read from STORE/keys/ and
;             installed with fn-own-with-node-secret after every open and
;             recovery; every owner step carries it unchanged.  The stored
;             octets of a served POST under an account carry the RFC 8315
;             Cancel-Lock keyed by it (books/owner-served-invariants.lisp
;             fn-own-sub-stored-octets);
;   refused   the refused-offer memory (books/refused-offers.lisp, PRF-235):
;             in memory only, recorded by fn-own-transit-outcome and
;             re-pinned into every peer session by fn-own-conn-live-session;
;   feeds     the outbound feed table (books/owner-feed.lisp): one
;             (name record feed) per configured peer with an outbound half.
;             Built from the configuration by the (:feeds cfg) arm, enqueued
;             on by the DURABLE branch of fn-own-outcome and
;             fn-own-transit-outcome, stepped by (:tick obs) and
;             (:feed-octets peer octets obs), and fenced by fn-own-reopen;
;   inflight  nil or the one submission in the durable path: taken from the
;             queue by fn-own-take-submission when nothing is in flight, the store is
;             :ready and no transaction is pending; answered by
;             fn-own-outcome, which is the only owner entry that produces a
;             POST outcome reply, and produces it for that connection only.
;
; A served read that injects an article (the :submit effect of
; fn-served-step) records a submission against the connection and its pinned
; version.  The writer step is fn-own-take followed by the store events the
; host observes (the same :store / :complete events tools/run_store.py `post`
; reports: fn-node-prepare through fn-sn-finish) and then fn-own-outcome,
; which turns the host's observed word into the completion
; fn-served-post-outcome renders: :durable only when a completion was
; consumed into the ledger after the take (the ledger mark), :refused for a
; refusal, :uncertain for everything else including a host that claims
; :durable without a consumed completion.
;
; The served port is fn-own-read: one socket read of one connection is one
; fn-served-step (books/served.lisp) over the connection's wire, session and
; PINNED archive, never over the live node.  The READER's view is what is
; pinned there.  A PEER connection's OFFER decision is not a reader view: it
; is the transit history question, and it reads the owner's live node, which
; fn-own-conn-live-session re-pins into the session once per read.  Those two
; are not in tension -- what a reader may see is the prefix its connection
; pinned, and what a peer is told about a Message-ID is what the node holds
; now.  fn-own-read-step is the per-event law underneath the read (one
; fn-served-dispatch, the byte fold's step, against the pinned archive).
; The committed view is refreshed only when the store is at an idle phase,
; where fn-snt-relation says the live node is the exact replay of the durable
; records (books/store-node-traces.lisp).
;
; Guards.  Every record accessor, every list function, the served port and
; the connection events (open, read, advance, close, begin) are guard t and
; verified: no recognizer of any kind runs on a served read.  The store events
; carry (fn-sn-statep (fn-own-store o)) because their callees do (store
; CHANGE, 2026-09-19); fn-own-complete is verified, fn-own-store-step and
; fn-own-step are declared but not verified because fn-snrt-step (store)
; is not guard verified.  That is recorded open in the handoff.

(in-package "ACL2")
(include-book "store-observed")
(include-book "snoc-list")
(include-book "served")
(include-book "clock")
(include-book "owner-feed")
(include-book "msgid-index")
(include-book "control-visible")
(include-book "packed-submission")

; store's idle-phase predicate has no explicit guard; it is guard t and its
; body is one member-equal over a constant, so verify it here so that
; fn-own-refresh can be.  Redundant once store carries the event itself.
(verify-guards fn-snt-idle-phasep)

; -----------------------------------------------------------------------------
; The connection record:
;   (id version frontier wire session archive config observation verdicts index
;    buckets control)
; CONTROL is the control pin of the view the connection is pinned to
; (`fn-own-view-control': its withdrawn list and withdrawal records), set at
; open and advance with the archive (control-c3e).

(defun fn-own-conn-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 12)))
(defun fn-own-conn-id (c)
  (declare (xargs :guard t))
  (mbe :logic (car c) :exec (fn-ag-car c)))
(defun fn-own-conn-version (c)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr c)) :exec (fn-ag-car (fn-ag-cdr c))))
(defun fn-own-conn-frontier (c)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr c)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr c)))))
(defun fn-own-conn-wire (c)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr c))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr c))))))
(defun fn-own-conn-session (c)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr c)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr c)))))))
(defun fn-own-conn-archive (c)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr c))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr c))))))))
(defun fn-own-conn-config (c)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr c)))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr c)))))))))
(defun fn-own-conn-observation (c)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr c))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr c))))))))))
(defun fn-own-conn-verdicts (c)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr c)))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr c)))))))))))
(defun fn-own-conn-index (c)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr c))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr c))))))))))))
(defun fn-own-conn-group-index (c)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr c))))))))))))
(defun fn-own-conn-control (c)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
   (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr c)))))))))))))
(defun fn-own-conn-make-group-indexed
    (id version frontier wire session archive config observation verdicts
        index buckets control)
  (declare (xargs :guard t))
  (list id version frontier wire session archive config observation verdicts
        index buckets control))
(defun fn-own-conn-make-indexed
    (id version frontier wire session archive config observation verdicts index)
  (declare (xargs :guard t))
  (fn-own-conn-make-group-indexed
   id version frontier wire session archive config observation verdicts index nil nil))
(defthm fn-own-conn-group-index-of-make
  (equal (fn-own-conn-group-index
          (fn-own-conn-make-group-indexed
           id version frontier wire session archive config observation
           verdicts index buckets control))
         buckets))
(defthm fn-own-conn-control-of-make
  (equal (fn-own-conn-control
          (fn-own-conn-make-group-indexed
           id version frontier wire session archive config observation
           verdicts index buckets control))
         control))
(defthm fn-own-conn-shapep-of-group-indexed
  (fn-own-conn-shapep
   (fn-own-conn-make-group-indexed
    id version frontier wire session archive config observation verdicts
    index buckets control)))

(defthm fn-own-conn-id-of-make-group-indexed
  (equal (fn-own-conn-id
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         id))

(defthm fn-own-conn-version-of-make-group-indexed
  (equal (fn-own-conn-version
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         version))

(defthm fn-own-conn-frontier-of-make-group-indexed
  (equal (fn-own-conn-frontier
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         frontier))

(defthm fn-own-conn-wire-of-make-group-indexed
  (equal (fn-own-conn-wire
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         wire))

(defthm fn-own-conn-session-of-make-group-indexed
  (equal (fn-own-conn-session
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         session))

(defthm fn-own-conn-archive-of-make-group-indexed
  (equal (fn-own-conn-archive
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         archive))

(defthm fn-own-conn-config-of-make-group-indexed
  (equal (fn-own-conn-config
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         config))

(defthm fn-own-conn-observation-of-make-group-indexed
  (equal (fn-own-conn-observation
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         observation))

(defthm fn-own-conn-verdicts-of-make-group-indexed
  (equal (fn-own-conn-verdicts
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         verdicts))

(defthm fn-own-conn-index-of-make-group-indexed
  (equal (fn-own-conn-index
          (fn-own-conn-make-group-indexed id version frontier wire session archive config observation verdicts index buckets control))
         index))
(defthm fn-own-conn-shapep-of-fn-own-conn-make-indexed
  (fn-own-conn-shapep
   (fn-own-conn-make-indexed id version frontier wire session archive config
                              observation verdicts index)))

(defthm fn-own-conn-fields-of-fn-own-conn-make-indexed
  (and (equal (fn-own-conn-id
               (fn-own-conn-make-indexed id version frontier wire session
                                         archive config observation verdicts
                                         index)) id)
       (equal (fn-own-conn-version
               (fn-own-conn-make-indexed id version frontier wire session
                                         archive config observation verdicts
                                         index)) version)
       (equal (fn-own-conn-frontier
               (fn-own-conn-make-indexed id version frontier wire session
                                         archive config observation verdicts
                                         index)) frontier)
       (equal (fn-own-conn-wire
               (fn-own-conn-make-indexed id version frontier wire session
                                         archive config observation verdicts
                                         index)) wire)
       (equal (fn-own-conn-session
               (fn-own-conn-make-indexed id version frontier wire session
                                         archive config observation verdicts
                                         index)) session)
       (equal (fn-own-conn-archive
               (fn-own-conn-make-indexed id version frontier wire session
                                         archive config observation verdicts
                                         index)) archive)
       (equal (fn-own-conn-config
               (fn-own-conn-make-indexed id version frontier wire session
                                         archive config observation verdicts
                                         index)) config)
       (equal (fn-own-conn-observation
               (fn-own-conn-make-indexed id version frontier wire session
                                         archive config observation verdicts
                                         index)) observation)
       (equal (fn-own-conn-verdicts
               (fn-own-conn-make-indexed id version frontier wire session
                                         archive config observation verdicts
                                         index)) verdicts)))
(defun fn-own-conn-make-pinned
    (id version frontier wire session archive config observation verdicts)
  (declare (xargs :guard t))
  (fn-own-conn-make-indexed id version frontier wire session archive config
                             observation verdicts nil))

(defthm fn-own-conn-index-of-fn-own-conn-make-indexed
  (equal (fn-own-conn-index
          (fn-own-conn-make-indexed id version frontier wire session archive
                                     config observation verdicts index))
         index))

(defthm fn-own-conn-index-of-fn-own-conn-make-pinned
  (equal (fn-own-conn-index
          (fn-own-conn-make-pinned id version frontier wire session archive
                                    config observation verdicts))
         nil))
(defun fn-own-conn-make (id version frontier wire session archive config observation)
  (declare (xargs :guard t))
  (fn-own-conn-make-pinned id version frontier wire session archive config
                            observation nil))

(defthm fn-own-conn-shapep-of-fn-own-conn-make-pinned
  (fn-own-conn-shapep
   (fn-own-conn-make-pinned id version frontier wire session archive config
                             observation verdicts)))
(defthm fn-own-conn-old-fields-of-fn-own-conn-make-pinned
  (and (equal (fn-own-conn-id
               (fn-own-conn-make-pinned id version frontier wire session archive
                                         config observation verdicts)) id)
       (equal (fn-own-conn-version
               (fn-own-conn-make-pinned id version frontier wire session archive
                                         config observation verdicts)) version)
       (equal (fn-own-conn-frontier
               (fn-own-conn-make-pinned id version frontier wire session archive
                                         config observation verdicts)) frontier)
       (equal (fn-own-conn-wire
               (fn-own-conn-make-pinned id version frontier wire session archive
                                         config observation verdicts)) wire)
       (equal (fn-own-conn-session
               (fn-own-conn-make-pinned id version frontier wire session archive
                                         config observation verdicts)) session)
       (equal (fn-own-conn-archive
               (fn-own-conn-make-pinned id version frontier wire session archive
                                         config observation verdicts)) archive)
       (equal (fn-own-conn-config
               (fn-own-conn-make-pinned id version frontier wire session archive
                                         config observation verdicts)) config)
       (equal (fn-own-conn-observation
               (fn-own-conn-make-pinned id version frontier wire session archive
                                         config observation verdicts)) observation)))
(defthm fn-own-conn-verdicts-of-fn-own-conn-make-pinned
  (equal (fn-own-conn-verdicts
          (fn-own-conn-make-pinned id version frontier wire session archive
                                    config observation verdicts))
         verdicts))
(defthm fn-own-conn-verdicts-of-fn-own-conn-make
  (equal (fn-own-conn-verdicts
          (fn-own-conn-make id version frontier wire session archive config
                             observation))
         nil))

(defthm fn-own-conn-shapep-of-fn-own-conn-make
  (fn-own-conn-shapep (fn-own-conn-make id version frontier wire session archive config observation)))
(defthm fn-own-conn-id-of-fn-own-conn-make
  (equal (fn-own-conn-id (fn-own-conn-make id version frontier wire session archive config observation)) id))
(defthm fn-own-conn-version-of-fn-own-conn-make
  (equal (fn-own-conn-version (fn-own-conn-make id version frontier wire session archive config observation))
         version))
(defthm fn-own-conn-frontier-of-fn-own-conn-make
  (equal (fn-own-conn-frontier (fn-own-conn-make id version frontier wire session archive config observation))
         frontier))
(defthm fn-own-conn-wire-of-fn-own-conn-make
  (equal (fn-own-conn-wire (fn-own-conn-make id version frontier wire session archive config observation))
         wire))
(defthm fn-own-conn-session-of-fn-own-conn-make
  (equal (fn-own-conn-session (fn-own-conn-make id version frontier wire session archive config observation))
         session))
(defthm fn-own-conn-archive-of-fn-own-conn-make
  (equal (fn-own-conn-archive (fn-own-conn-make id version frontier wire session archive config observation))
         archive))
(defthm fn-own-conn-config-of-fn-own-conn-make
  (equal (fn-own-conn-config (fn-own-conn-make id version frontier wire session archive config observation))
         config))
(defthm fn-own-conn-observation-of-fn-own-conn-make
  (equal (fn-own-conn-observation (fn-own-conn-make id version frontier wire session archive config observation))
         observation))
(defthm fn-own-conn-shapep-forward-shape
  (implies (fn-own-conn-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-own-conn-accessors-forward-consp
  (and (implies (fn-own-conn-id x) (consp x))
       (implies (fn-own-conn-version x) (consp x))
       (implies (fn-own-conn-frontier x) (consp x))
       (implies (fn-own-conn-wire x) (consp x))
       (implies (fn-own-conn-session x) (consp x))
       (implies (fn-own-conn-archive x) (consp x))
       (implies (fn-own-conn-config x) (consp x))
       (implies (fn-own-conn-observation x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-own-conn-id x) (consp x))
                                    :trigger-terms ((fn-own-conn-id x)))
                 (:forward-chaining :corollary (implies (fn-own-conn-version x) (consp x))
                                    :trigger-terms ((fn-own-conn-version x)))
                 (:forward-chaining :corollary (implies (fn-own-conn-frontier x) (consp x))
                                    :trigger-terms ((fn-own-conn-frontier x)))
                 (:forward-chaining :corollary (implies (fn-own-conn-wire x) (consp x))
                                    :trigger-terms ((fn-own-conn-wire x)))
                 (:forward-chaining :corollary (implies (fn-own-conn-session x) (consp x))
                                    :trigger-terms ((fn-own-conn-session x)))
                 (:forward-chaining :corollary (implies (fn-own-conn-archive x) (consp x))
                                    :trigger-terms ((fn-own-conn-archive x)))
                 (:forward-chaining :corollary (implies (fn-own-conn-config x) (consp x))
                                    :trigger-terms ((fn-own-conn-config x)))
                 (:forward-chaining :corollary (implies (fn-own-conn-observation x) (consp x))
                                    :trigger-terms ((fn-own-conn-observation x)))))
(in-theory (disable (:d fn-own-conn-shapep) (:d fn-own-conn-id) (:d fn-own-conn-version)
                    (:d fn-own-conn-frontier) (:d fn-own-conn-wire)
                    (:d fn-own-conn-session) (:d fn-own-conn-archive)
                    (:d fn-own-conn-config) (:d fn-own-conn-observation)
                    (:d fn-own-conn-verdicts) (:d fn-own-conn-index)
                    (:d fn-own-conn-make-indexed) (:d fn-own-conn-make-pinned)
                    (:d fn-own-conn-make)))

; -----------------------------------------------------------------------------
; The submission record: (id version mark decision).  A served read of
; connection `id`, pinned at `version`, injected `decision` (an
; fn-inj-injectedp decision record: the article's octets, Message-ID and
; groups, books/injection.lisp).  `mark` is nil in the queue and the length
; of the ledger at the moment fn-own-take-submission moved it into the durable path.

(defun fn-own-sub-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (or (equal (len x) 4) (equal (len x) 6))))
(defun fn-own-sub-id (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-own-sub-version (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-own-sub-mark (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-own-sub-decision (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-own-sub-make (id version mark decision)
  (declare (xargs :guard t))
  (list id version mark decision))

(defthm fn-own-sub-shapep-of-fn-own-sub-make
  (fn-own-sub-shapep (fn-own-sub-make id version mark decision)))
(defthm fn-own-sub-id-of-fn-own-sub-make
  (equal (fn-own-sub-id (fn-own-sub-make id version mark decision)) id))
(defthm fn-own-sub-version-of-fn-own-sub-make
  (equal (fn-own-sub-version (fn-own-sub-make id version mark decision)) version))
(defthm fn-own-sub-mark-of-fn-own-sub-make
  (equal (fn-own-sub-mark (fn-own-sub-make id version mark decision)) mark))
(defthm fn-own-sub-decision-of-fn-own-sub-make
  (equal (fn-own-sub-decision (fn-own-sub-make id version mark decision)) decision))
(defthm fn-own-sub-shapep-forward-shape
  (implies (fn-own-sub-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-own-sub-make-is-consp
  (consp (fn-own-sub-make id version mark decision))
  :rule-classes (:rewrite :type-prescription))

; The author of a served submission (SEC-006, PRF-210): the AUTHINFO USER
; name (LOGIN) and the principal id (ACCOUNT, books/nntp-auth.lisp
; fn-auth-session-subject) the connection had authenticated as BEFORE the
; read that completed the article (the session fn-own-finish-read is
; handed, not the one the read leaves: an AUTHINFO later in the same read
; never claims an article posted before it), recorded when it is enqueued.
; The account keys the RFC 8315 Cancel-Lock the stored octets carry, even
; when the connection is gone by the time the writer takes it; the login
; is what the posting-policy gate reads (books/login-binding.lisp
; fn-lb-inflight-login, PKT-619).  A submission without an author
; (control, BP, transit, an unauthenticated POST) keeps the four-element
; shape it always had: fn-own-sub-make-author with a nil login IS
; fn-own-sub-make.
(defun fn-own-sub-login (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(defun fn-own-sub-account (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))))
(defun fn-own-sub-make-author (id version mark decision login account)
  (declare (xargs :guard t))
  (if login
      (list id version mark decision login account)
    (fn-own-sub-make id version mark decision)))

(defthm fn-own-sub-make-author-of-no-login-by-definition
  (equal (fn-own-sub-make-author id version mark decision nil account)
         (fn-own-sub-make id version mark decision)))
(defthm fn-own-sub-login-of-fn-own-sub-make
  (equal (fn-own-sub-login (fn-own-sub-make id version mark decision)) nil))
(defthm fn-own-sub-account-of-fn-own-sub-make
  (equal (fn-own-sub-account (fn-own-sub-make id version mark decision)) nil))
(defthm fn-own-sub-shapep-of-fn-own-sub-make-author
  (fn-own-sub-shapep (fn-own-sub-make-author id version mark decision login account)))
(defthm fn-own-sub-id-of-fn-own-sub-make-author
  (equal (fn-own-sub-id (fn-own-sub-make-author id version mark decision login account)) id))
(defthm fn-own-sub-version-of-fn-own-sub-make-author
  (equal (fn-own-sub-version (fn-own-sub-make-author id version mark decision login account))
         version))
(defthm fn-own-sub-mark-of-fn-own-sub-make-author
  (equal (fn-own-sub-mark (fn-own-sub-make-author id version mark decision login account)) mark))
(defthm fn-own-sub-decision-of-fn-own-sub-make-author
  (equal (fn-own-sub-decision (fn-own-sub-make-author id version mark decision login account))
         decision))
(defthm fn-own-sub-login-of-fn-own-sub-make-author
  (equal (fn-own-sub-login (fn-own-sub-make-author id version mark decision login account))
         login))
(defthm fn-own-sub-account-of-fn-own-sub-make-author
  (equal (fn-own-sub-account (fn-own-sub-make-author id version mark decision login account))
         (if login account nil)))
(defthm fn-own-sub-make-author-is-consp
  (consp (fn-own-sub-make-author id version mark decision login account))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable (:d fn-own-sub-shapep) (:d fn-own-sub-id) (:d fn-own-sub-version)
                    (:d fn-own-sub-mark) (:d fn-own-sub-decision) (:d fn-own-sub-make)
                    (:d fn-own-sub-login) (:d fn-own-sub-account)
                    (:d fn-own-sub-make-author)))

; The queued (packed) submission's fields (lane chunked-body-2, B6b;
; fn-own-enqueue packs, fn-own-take-submission unpacks): the packing touches
; only the decision's octets and an injection's groups.
(defthm fn-own-sub-fields-of-pack
  (and (equal (fn-own-sub-id (fn-psub-pack-sub x)) (fn-own-sub-id x))
       (equal (fn-own-sub-version (fn-psub-pack-sub x)) (fn-own-sub-version x))
       (equal (fn-own-sub-mark (fn-psub-pack-sub x)) (fn-own-sub-mark x))
       (equal (fn-own-sub-login (fn-psub-pack-sub x)) (fn-own-sub-login x))
       (equal (fn-own-sub-account (fn-psub-pack-sub x)) (fn-own-sub-account x))
       (equal (fn-own-sub-decision (fn-psub-pack-sub x))
              (fn-psub-pack-decision (fn-own-sub-decision x)))
       (equal (fn-own-sub-shapep (fn-psub-pack-sub x)) (fn-own-sub-shapep x))
       (equal (consp (fn-psub-pack-sub x)) (consp x)))
  :hints (("Goal" :in-theory (enable fn-own-sub-id fn-own-sub-version fn-own-sub-mark
                                     fn-own-sub-login fn-own-sub-account
                                     fn-own-sub-decision fn-own-sub-shapep
                                     fn-psub-pack-sub fn-psub-pack-decision))))

(defthm fn-own-sub-fields-of-unpack
  (and (equal (fn-own-sub-id (fn-psub-unpack-sub x)) (fn-own-sub-id x))
       (equal (fn-own-sub-version (fn-psub-unpack-sub x)) (fn-own-sub-version x))
       (equal (fn-own-sub-mark (fn-psub-unpack-sub x)) (fn-own-sub-mark x))
       (equal (fn-own-sub-login (fn-psub-unpack-sub x)) (fn-own-sub-login x))
       (equal (fn-own-sub-account (fn-psub-unpack-sub x)) (fn-own-sub-account x))
       (equal (fn-own-sub-decision (fn-psub-unpack-sub x))
              (fn-psub-unpack-decision (fn-own-sub-decision x)))
       (equal (consp (fn-psub-unpack-sub x)) (consp x)))
  :hints (("Goal" :in-theory (enable fn-own-sub-id fn-own-sub-version fn-own-sub-mark
                                     fn-own-sub-login fn-own-sub-account
                                     fn-own-sub-decision
                                     fn-psub-unpack-sub fn-psub-unpack-decision))))

; The decision's fields the queue's readers use, packed.
(defthm fn-own-decision-heads-of-pack
  (and (equal (car (fn-psub-pack-decision d)) (car d))
       (equal (cadr (fn-psub-pack-decision d)) (cadr d))
       (equal (caddr (fn-psub-pack-decision d)) (caddr d))
       (implies (equal (car d) :transit)
                (equal (cadddr (fn-psub-pack-decision d)) (cadddr d)))
       (equal (consp (fn-psub-pack-decision d)) (consp d))
       (equal (consp (cdr (fn-psub-pack-decision d))) (consp (cdr d)))
       (equal (consp (cddr (fn-psub-pack-decision d))) (consp (cddr d)))
       (equal (consp (cdddr (fn-psub-pack-decision d))) (consp (cdddr d)))
       (equal (true-listp (fn-psub-pack-decision d)) (true-listp d))
       (equal (len (fn-psub-pack-decision d)) (len d)))
  :hints (("Goal" :in-theory (enable fn-psub-pack-decision))))

(defthm fn-own-decision-fields-of-pack
  (and (equal (fn-peer-submissionp (fn-psub-pack-decision d)) (fn-peer-submissionp d))
       (equal (fn-peer-submission-peer (fn-psub-pack-decision d)) (fn-peer-submission-peer d))
       (equal (fn-peer-submission-kind (fn-psub-pack-decision d)) (fn-peer-submission-kind d))
       (implies (equal (car d) :transit)
                (equal (fn-peer-submission-msgid (fn-psub-pack-decision d))
                       (fn-peer-submission-msgid d)))
       (equal (fn-inj-decision-status (fn-psub-pack-decision d)) (fn-inj-decision-status d))
       (equal (fn-inj-decision-reason (fn-psub-pack-decision d)) (fn-inj-decision-reason d))
       (equal (fn-inj-decision-msgid (fn-psub-pack-decision d)) (fn-inj-decision-msgid d)))
  :hints (("Goal" :in-theory (e/d (fn-peer-submissionp
                                   fn-peer-submission-shapep
                                   fn-peer-submission-peer fn-peer-submission-kind
                                   fn-peer-submission-msgid
                                   fn-inj-decision-status fn-inj-decision-reason
                                   fn-inj-decision-msgid fn-inj-nth fn-inj-car fn-inj-cdr)
                                  (fn-psub-pack-decision fn-af-message-idp
                                   fn-nntp-printable-tokenp))
                  :expand ((:free (x) (fn-inj-nth 0 x)) (:free (x) (fn-inj-nth 1 x))
                           (:free (x) (fn-inj-nth 2 x))))))

(defthm fn-own-inj-injectedp-of-pack
  (equal (fn-inj-injectedp (fn-psub-pack-decision d)) (fn-inj-injectedp d))
  :hints (("Goal" :in-theory (e/d (fn-inj-injectedp) (fn-psub-pack-decision)))))

; The decision a QUEUED submission carries: what the take installs.
(defun fn-own-sub-queued-decision (sub)
  (declare (xargs :guard t))
  (fn-psub-unpack-decision (fn-own-sub-decision sub)))

(defthm fn-own-sub-queued-decision-of-pack
  (equal (fn-own-sub-queued-decision (fn-psub-pack-sub x))
         (fn-own-sub-decision x)))

(in-theory (disable fn-own-sub-queued-decision))

; -----------------------------------------------------------------------------
; The committed view record:
;   (version frontier archive verdicts trie buckets withdrawals raw withdrawn
;    keyring)
; ARCHIVE is the state the view serves: the acceptance state of its prefix
; with the withdrawn targets out of its article list (C3, D29,
; `fn-ctl-visible-state').  WITHDRAWALS are the records decided for the
; cancels among RAW, the acceptance archive's own article list, which the
; next refresh compares with the grown archive to extend the visible list
; incrementally (`fn-ctl-refresh-visible').

; WITHDRAWN is the list of RAW's articles the view does not serve, carried
; by `fn-ctl-refresh-withdrawn' (books/control-served.lisp) so a reader's
; `423 withdrawn', `430 withdrawn' and `HDR :fn-control' read it without
; walking RAW (control-c3e).
(defun fn-own-view-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 10)))
(defun fn-own-view-version (v)
  (declare (xargs :guard t))
  (mbe :logic (car v) :exec (fn-ag-car v)))
(defun fn-own-view-frontier (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr v)) :exec (fn-ag-car (fn-ag-cdr v))))
(defun fn-own-view-archive (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr v))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr v)))))
(defun fn-own-view-verdicts (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr v))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr v))))))
(defun fn-own-view-index (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr v)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr v)))))))
(defun fn-own-view-group-index (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr v)))))))
(defun fn-own-view-withdrawals (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                         (fn-ag-cdr v))))))))
(defun fn-own-view-raw (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                         (fn-ag-cdr (fn-ag-cdr v)))))))))
(defun fn-own-view-withdrawn (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr v))))))))))
; KEYRING is the Store's keyring snapshots (`fn-sn-keyring-snapshots') at
; the refresh that committed the view: the node's keyring view a reader of
; this view is told the current enrollment against (HDR :fn-enrollment,
; books/nntp-enrollment.lisp).  Pinned with the view, like the verdicts.
(defun fn-own-view-keyring (v)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
               (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr v)))))))))))
(defun fn-own-view-make-visible
    (version frontier archive verdicts index buckets withdrawals raw withdrawn
             keyring)
  (declare (xargs :guard t))
  (list version frontier archive verdicts index buckets withdrawals raw
        withdrawn keyring))
(defun fn-own-view-make-group-indexed
    (version frontier archive verdicts index buckets)
  (declare (xargs :guard t))
  (list version frontier archive verdicts index buckets nil nil nil nil))
; The control pin a connection opened or advanced on this view carries: the
; withdrawn list, the withdrawal records and the keyring view.
(defun fn-own-view-control (v)
  (declare (xargs :guard t))
  (fn-enr-pin (fn-own-view-withdrawn v) (fn-own-view-withdrawals v)
              (fn-own-view-keyring v)))
(defthm fn-own-view-control-fields
  (and (equal (fn-ctl-pin-withdrawn (fn-own-view-control v)) (fn-own-view-withdrawn v))
       (equal (fn-ctl-pin-ws (fn-own-view-control v)) (fn-own-view-withdrawals v))
       (fn-enr-pin-has-keyring-p (fn-own-view-control v))
       (equal (fn-enr-pin-keyring (fn-own-view-control v)) (fn-own-view-keyring v))
       (fn-own-view-control v))
  :hints (("Goal" :use ((:instance fn-enr-pin-fields
                         (withdrawn (fn-own-view-withdrawn v))
                         (ws (fn-own-view-withdrawals v))
                         (keyring (fn-own-view-keyring v))))
           :in-theory (e/d (fn-own-view-control)
                           (fn-enr-pin-fields fn-enr-pin fn-ctl-pin-withdrawn
                            fn-ctl-pin-ws fn-enr-pin-has-keyring-p fn-enr-pin-keyring
                            fn-own-view-withdrawn fn-own-view-withdrawals
                            fn-own-view-keyring)))))
(in-theory (disable fn-own-view-control))
; The view as a served connection's LIVE pin (books/served.lisp
; fn-served-live-make; NNT-042): the seven values fn-own-open pins into a new
; connection, handed to every read so that GROUP and LISTGROUP can advance
; the connection to them between commands (fn-served-repin).
(defun fn-own-view-live (view)
  (declare (xargs :guard t))
  (fn-served-live-make (fn-own-view-version view) (fn-own-view-frontier view)
                       (fn-own-view-archive view) (fn-own-view-verdicts view)
                       (fn-own-view-index view) (fn-own-view-group-index view)
                       (fn-own-view-control view)))
(defthm fn-own-view-live-fields
  (let ((live (fn-own-view-live view)))
    (and live
         (equal (fn-served-live-version live) (fn-own-view-version view))
         (equal (fn-served-live-frontier live) (fn-own-view-frontier view))
         (equal (fn-served-live-archive live) (fn-own-view-archive view))
         (equal (fn-served-live-verdicts live) (fn-own-view-verdicts view))
         (equal (fn-served-live-index live) (fn-own-view-index view))
         (equal (fn-served-live-buckets live) (fn-own-view-group-index view))
         (equal (fn-served-live-control live) (fn-own-view-control view)))))
(in-theory (disable fn-own-view-live))
(defun fn-own-view-make-indexed (version frontier archive verdicts index)
  (declare (xargs :guard t))
  (fn-own-view-make-group-indexed version frontier archive verdicts index nil))
(defthm fn-own-view-group-index-of-make
  (equal (fn-own-view-group-index
          (fn-own-view-make-group-indexed
           version frontier archive verdicts index buckets))
         buckets))
(defthm fn-own-view-fields-of-make-visible
  (let ((v (fn-own-view-make-visible version frontier archive verdicts index
                                     buckets withdrawals raw withdrawn
                                     keyring)))
    (and (fn-own-view-shapep v)
         (equal (fn-own-view-version v) version)
         (equal (fn-own-view-frontier v) frontier)
         (equal (fn-own-view-archive v) archive)
         (equal (fn-own-view-verdicts v) verdicts)
         (equal (fn-own-view-index v) index)
         (equal (fn-own-view-group-index v) buckets)
         (equal (fn-own-view-withdrawals v) withdrawals)
         (equal (fn-own-view-raw v) raw)
         (equal (fn-own-view-withdrawn v) withdrawn)
         (equal (fn-own-view-keyring v) keyring))))
(defthm fn-own-view-shapep-of-group-indexed
  (fn-own-view-shapep
   (fn-own-view-make-group-indexed
    version frontier archive verdicts index buckets)))

(defthm fn-own-view-version-of-make-group-indexed
  (equal (fn-own-view-version
          (fn-own-view-make-group-indexed version frontier archive verdicts index buckets))
         version))

(defthm fn-own-view-frontier-of-make-group-indexed
  (equal (fn-own-view-frontier
          (fn-own-view-make-group-indexed version frontier archive verdicts index buckets))
         frontier))

(defthm fn-own-view-archive-of-make-group-indexed
  (equal (fn-own-view-archive
          (fn-own-view-make-group-indexed version frontier archive verdicts index buckets))
         archive))

(defthm fn-own-view-verdicts-of-make-group-indexed
  (equal (fn-own-view-verdicts
          (fn-own-view-make-group-indexed version frontier archive verdicts index buckets))
         verdicts))

(defthm fn-own-view-index-of-make-group-indexed
  (equal (fn-own-view-index
          (fn-own-view-make-group-indexed version frontier archive verdicts index buckets))
         index))
(defthm fn-own-view-shapep-of-fn-own-view-make-indexed
  (fn-own-view-shapep
   (fn-own-view-make-indexed version frontier archive verdicts index)))

(defthm fn-own-view-fields-of-fn-own-view-make-indexed
  (and (equal (fn-own-view-version
               (fn-own-view-make-indexed version frontier archive verdicts
                                         index))
              version)
       (equal (fn-own-view-frontier
               (fn-own-view-make-indexed version frontier archive verdicts
                                         index))
              frontier)
       (equal (fn-own-view-archive
               (fn-own-view-make-indexed version frontier archive verdicts
                                         index))
              archive)
       (equal (fn-own-view-verdicts
               (fn-own-view-make-indexed version frontier archive verdicts
                                         index))
              verdicts)))
(defun fn-own-view-make-pinned (version frontier archive verdicts)
  (declare (xargs :guard t))
  (fn-own-view-make-indexed version frontier archive verdicts nil))

(defthm fn-own-view-index-of-fn-own-view-make-indexed
  (equal (fn-own-view-index
          (fn-own-view-make-indexed version frontier archive verdicts index))
         index))

(defthm fn-own-view-index-of-fn-own-view-make-pinned
  (equal (fn-own-view-index
          (fn-own-view-make-pinned version frontier archive verdicts))
         nil))
(defun fn-own-view-make (version frontier archive)
  (declare (xargs :guard t))
  (fn-own-view-make-pinned version frontier archive nil))

(defthm fn-own-view-shapep-of-fn-own-view-make-pinned
  (fn-own-view-shapep
   (fn-own-view-make-pinned version frontier archive verdicts)))
(defthm fn-own-view-old-fields-of-fn-own-view-make-pinned
  (and (equal (fn-own-view-version
               (fn-own-view-make-pinned version frontier archive verdicts))
              version)
       (equal (fn-own-view-frontier
               (fn-own-view-make-pinned version frontier archive verdicts))
              frontier)
       (equal (fn-own-view-archive
               (fn-own-view-make-pinned version frontier archive verdicts))
              archive)))
(defthm fn-own-view-verdicts-of-fn-own-view-make-pinned
  (equal (fn-own-view-verdicts
          (fn-own-view-make-pinned version frontier archive verdicts))
         verdicts))
(defthm fn-own-view-verdicts-of-fn-own-view-make
  (equal (fn-own-view-verdicts
          (fn-own-view-make version frontier archive))
         nil))

(defthm fn-own-view-shapep-of-fn-own-view-make
  (fn-own-view-shapep (fn-own-view-make version frontier archive)))
(defthm fn-own-view-version-of-fn-own-view-make
  (equal (fn-own-view-version (fn-own-view-make version frontier archive)) version))
(defthm fn-own-view-frontier-of-fn-own-view-make
  (equal (fn-own-view-frontier (fn-own-view-make version frontier archive)) frontier))
(defthm fn-own-view-archive-of-fn-own-view-make
  (equal (fn-own-view-archive (fn-own-view-make version frontier archive)) archive))
(defthm fn-own-view-shapep-forward-shape
  (implies (fn-own-view-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-own-view-accessors-forward-consp
  (and (implies (fn-own-view-version x) (consp x))
       (implies (fn-own-view-frontier x) (consp x))
       (implies (fn-own-view-archive x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-own-view-version x) (consp x))
                                    :trigger-terms ((fn-own-view-version x)))
                 (:forward-chaining :corollary (implies (fn-own-view-frontier x) (consp x))
                                    :trigger-terms ((fn-own-view-frontier x)))
                 (:forward-chaining :corollary (implies (fn-own-view-archive x) (consp x))
                                    :trigger-terms ((fn-own-view-archive x)))))
(in-theory (disable (:d fn-own-view-shapep) (:d fn-own-view-version)
                    (:d fn-own-view-frontier) (:d fn-own-view-archive)
                    (:d fn-own-view-verdicts) (:d fn-own-view-index)
                    (:d fn-own-view-make-indexed) (:d fn-own-view-make-pinned)
                    (:d fn-own-view-make) (:d fn-own-view-make-visible)
                    (:d fn-own-view-withdrawals) (:d fn-own-view-raw)
                    (:d fn-own-view-withdrawn) (:d fn-own-view-keyring)))

; -----------------------------------------------------------------------------
; The owner record

(defun fn-own-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 15)))
(defun fn-own-store (o)
  (declare (xargs :guard t))
  (mbe :logic (car o) :exec (fn-ag-car o)))
(defun fn-own-view (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr o)) :exec (fn-ag-car (fn-ag-cdr o))))
(defun fn-own-conns (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr o))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr o)))))
(defun fn-own-next-id (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr o))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o))))))
(defun fn-own-max-conns (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr o)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o)))))))
(defun fn-own-pending (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr o))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o))))))))
; The ledger (PRF-283).  It grows by one pair per commit and never shrinks
; while the process lives, so it is held as a snoc-list (books/snoc-list.lisp:
; newest first, with its length): the field is its representation and
; fn-own-ledger reads the list back (fn-sl-list; a plain list, nil included,
; represents itself).  fn-own-make takes the FIELD: a transition that keeps
; the ledger passes (fn-own-ledger-field o) through, one pointer; the commit
; appends one pair with fn-sl-snoc, one cons, and fn-own-ledger of the result
; is the append for every field value (fn-sl-list-of-fn-sl-snoc).  Held as a
; plain list the commit copied the whole ledger: 16 B x POSTs-since-open per
; POST (post-alloc-2's packet), and the take and the outcome walked it for
; its length (now fn-own-ledger-count, O(1) on a snoc form).
(defun fn-own-ledger-field (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr o)))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o)))))))))
(defun fn-own-ledger (o)
  (declare (xargs :guard t))
  (fn-sl-list (fn-own-ledger-field o)))
(defun fn-own-ledger-count (o)
  (declare (xargs :guard t))
  (mbe :logic (len (fn-own-ledger o))
       :exec (fn-sl-count (fn-own-ledger-field o))))
(defun fn-own-clock (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr o))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o))))))))))
(defun fn-own-facts (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr o)))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o)))))))))))
(defun fn-own-config (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr o))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o))))))))))))
(defun fn-own-queue (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr o)))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o)))))))))))))
(defun fn-own-inflight (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr o))))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o))))))))))))))
(defun fn-own-feeds (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr o)))))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o)))))))))))))))
(defun fn-own-node-secret (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr o))))))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o))))))))))))))))
; PRF-235: the refused-offer memory (books/refused-offers.lisp), in memory
; only: fn-own-transit-outcome records into it, fn-own-conn-live-session
; re-pins it into every peer session per read, and a restart starts with
; none (the loss costs one re-parse per refused article; no answer changes).
(defun fn-own-refused (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr o)))))))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o)))))))))))))))))
(defun fn-own-make (store view conns next-id max-conns pending ledger clock facts
                          config queue inflight feeds node-secret refused)
  (declare (xargs :guard t))
  (list store view conns next-id max-conns pending ledger clock facts
        config queue inflight feeds node-secret refused))
(defthm fn-own-refused-of-fn-own-make
  (equal (fn-own-refused (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         refused))

(defthm fn-own-shapep-of-fn-own-make
  (fn-own-shapep (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused)))
(defthm fn-own-store-of-fn-own-make
  (equal (fn-own-store (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         store))
(defthm fn-own-view-of-fn-own-make
  (equal (fn-own-view (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         view))
(defthm fn-own-conns-of-fn-own-make
  (equal (fn-own-conns (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         conns))
(defthm fn-own-next-id-of-fn-own-make
  (equal (fn-own-next-id (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         next-id))
(defthm fn-own-max-conns-of-fn-own-make
  (equal (fn-own-max-conns (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         max-conns))
(defthm fn-own-pending-of-fn-own-make
  (equal (fn-own-pending (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         pending))
(defthm fn-own-ledger-field-of-fn-own-make
  (equal (fn-own-ledger-field (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         ledger))
(defthm fn-own-ledger-of-fn-own-make
  (equal (fn-own-ledger (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         (fn-sl-list ledger)))
; The field read back is the ledger (fn-own-ledger stays closed below).
(defthm fn-sl-list-of-fn-own-ledger-field
  (equal (fn-sl-list (fn-own-ledger-field o)) (fn-own-ledger o)))
(defthm fn-own-ledger-count-is-len
  (equal (fn-own-ledger-count o) (len (fn-own-ledger o))))
(defthm fn-own-clock-of-fn-own-make
  (equal (fn-own-clock (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         clock))
(defthm fn-own-facts-of-fn-own-make
  (equal (fn-own-facts (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         facts))
(defthm fn-own-config-of-fn-own-make
  (equal (fn-own-config (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         config))
(defthm fn-own-queue-of-fn-own-make
  (equal (fn-own-queue (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         queue))
(defthm fn-own-inflight-of-fn-own-make
  (equal (fn-own-inflight (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         inflight))
(defthm fn-own-feeds-of-fn-own-make
  (equal (fn-own-feeds (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         feeds))
(defthm fn-own-node-secret-of-fn-own-make
  (equal (fn-own-node-secret (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         node-secret))
(defthm fn-own-shapep-forward-shape
  (implies (fn-own-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-own-accessors-forward-consp
  (and (implies (fn-own-store x) (consp x))
       (implies (fn-own-view x) (consp x))
       (implies (fn-own-conns x) (consp x))
       (implies (fn-own-next-id x) (consp x))
       (implies (fn-own-max-conns x) (consp x))
       (implies (fn-own-pending x) (consp x))
       (implies (fn-own-ledger x) (consp x))
       (implies (fn-own-clock x) (consp x))
       (implies (fn-own-facts x) (consp x))
       (implies (fn-own-config x) (consp x))
       (implies (fn-own-queue x) (consp x))
       (implies (fn-own-inflight x) (consp x))
       (implies (fn-own-feeds x) (consp x))
       (implies (fn-own-node-secret x) (consp x))
       (implies (fn-own-refused x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-own-store x) (consp x))
                                    :trigger-terms ((fn-own-store x)))
                 (:forward-chaining :corollary (implies (fn-own-view x) (consp x))
                                    :trigger-terms ((fn-own-view x)))
                 (:forward-chaining :corollary (implies (fn-own-conns x) (consp x))
                                    :trigger-terms ((fn-own-conns x)))
                 (:forward-chaining :corollary (implies (fn-own-next-id x) (consp x))
                                    :trigger-terms ((fn-own-next-id x)))
                 (:forward-chaining :corollary (implies (fn-own-max-conns x) (consp x))
                                    :trigger-terms ((fn-own-max-conns x)))
                 (:forward-chaining :corollary (implies (fn-own-pending x) (consp x))
                                    :trigger-terms ((fn-own-pending x)))
                 (:forward-chaining :corollary (implies (fn-own-ledger x) (consp x))
                                    :trigger-terms ((fn-own-ledger x)))
                 (:forward-chaining :corollary (implies (fn-own-clock x) (consp x))
                                    :trigger-terms ((fn-own-clock x)))
                 (:forward-chaining :corollary (implies (fn-own-facts x) (consp x))
                                    :trigger-terms ((fn-own-facts x)))
                 (:forward-chaining :corollary (implies (fn-own-config x) (consp x))
                                    :trigger-terms ((fn-own-config x)))
                 (:forward-chaining :corollary (implies (fn-own-queue x) (consp x))
                                    :trigger-terms ((fn-own-queue x)))
                 (:forward-chaining :corollary (implies (fn-own-inflight x) (consp x))
                                    :trigger-terms ((fn-own-inflight x)))
                 (:forward-chaining :corollary (implies (fn-own-feeds x) (consp x))
                                    :trigger-terms ((fn-own-feeds x)))
                 (:forward-chaining :corollary (implies (fn-own-node-secret x) (consp x))
                                    :trigger-terms ((fn-own-node-secret x)))
                 (:forward-chaining :corollary (implies (fn-own-refused x) (consp x))
                                    :trigger-terms ((fn-own-refused x)))))
(in-theory (disable (:d fn-own-shapep) (:d fn-own-store) (:d fn-own-view) (:d fn-own-conns)
                    (:d fn-own-next-id) (:d fn-own-max-conns) (:d fn-own-pending)
                    (:d fn-own-ledger) (:d fn-own-ledger-field) fn-own-ledger-count
                    (:d fn-own-clock) (:d fn-own-facts)
                    (:d fn-own-config) (:d fn-own-queue) (:d fn-own-inflight)
                    (:d fn-own-feeds) (:d fn-own-node-secret) (:d fn-own-refused) (:d fn-own-make)))

; -----------------------------------------------------------------------------
; The group-configuration fact record: (:fn-own-group-fact name stamp).  The
; creation of a group, stamped with the clock observation current when it
; was recorded.  Facts are an append-only record kind; the live group view is
; their replay.

(defun fn-own-group-fact-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3) (equal (car x) :fn-own-group-fact)))
(defun fn-own-group-fact-name (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-own-group-fact-stamp (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-own-group-fact-make (name obs)
  (declare (xargs :guard t))
  (list :fn-own-group-fact name obs))

(defthm fn-own-group-fact-shapep-of-fn-own-group-fact-make
  (fn-own-group-fact-shapep (fn-own-group-fact-make name obs)))
(defthm fn-own-group-fact-name-of-fn-own-group-fact-make
  (equal (fn-own-group-fact-name (fn-own-group-fact-make name obs)) name))
(defthm fn-own-group-fact-stamp-of-fn-own-group-fact-make
  (equal (fn-own-group-fact-stamp (fn-own-group-fact-make name obs)) obs))
(defthm fn-own-group-fact-shapep-forward-shape
  (implies (fn-own-group-fact-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-own-group-fact-accessors-forward-consp
  (and (implies (fn-own-group-fact-name x) (consp x))
       (implies (fn-own-group-fact-stamp x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-own-group-fact-name x) (consp x))
                                    :trigger-terms ((fn-own-group-fact-name x)))
                 (:forward-chaining :corollary (implies (fn-own-group-fact-stamp x) (consp x))
                                    :trigger-terms ((fn-own-group-fact-stamp x)))))
(in-theory (disable (:d fn-own-group-fact-shapep) (:d fn-own-group-fact-name)
                    (:d fn-own-group-fact-stamp) (:d fn-own-group-fact-make)))

(defun fn-own-group-factp (x)
  (declare (xargs :guard t))
  (and (fn-own-group-fact-shapep x)
       (stringp (fn-own-group-fact-name x))
       (fn-clock-observationp (fn-own-group-fact-stamp x))))
(defthm fn-own-group-factp-forward-shape
  (implies (fn-own-group-factp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(defun fn-own-facts-okp (facts)
  (declare (xargs :guard t))
  (if (consp facts)
      (and (fn-own-group-factp (car facts))
           (fn-own-facts-okp (cdr facts)))
    (null facts)))

; Replay of the fact log: the created group names in creation order.
(defun fn-own-replay-facts (facts)
  (declare (xargs :guard t))
  (if (consp facts)
      (cons (fn-own-group-fact-name (car facts))
            (fn-own-replay-facts (cdr facts)))
    nil))

; -----------------------------------------------------------------------------
; The durable prefix a version names, and the archive it projects to.

; Executes by a loop (PKT-876, lane open-depth): N is a version, the durable
; record count, so the recursion was one control-stack frame per record.
; The :logic is the recursion, unchanged; equal by the guard proof.
(defun fn-own-take-rev (n xs acc)
  (declare (xargs :guard (true-listp acc)))
  (if (and (posp n) (consp xs))
      (fn-own-take-rev (1- n) (cdr xs) (cons (car xs) acc))
    (revappend acc nil)))

(defun fn-own-take (n xs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (and (posp n) (consp xs))
           (cons (car xs) (fn-own-take (1- n) (cdr xs)))
         nil)
       :exec (fn-own-take-rev n xs nil)))

(encapsulate ()
  (local
   (defthm fn-own-take-rev-is-revappend
     (equal (fn-own-take-rev n xs acc)
            (revappend acc (fn-own-take n xs)))))
  (verify-guards fn-own-take))

; The acceptance projection of the replay of the first `version` records,
; advanced to `frontier`.  Every pinned archive equals this over the durable
; history of the moment (fn-own-relation, owner-invariants.lisp).
(defun fn-own-prefix-archive (groups capacity records version frontier)
  (declare (xargs :guard t))
  (fn-node-acceptance
   (fn-sf-replay-node groups capacity (fn-own-take version records) frontier)))

; -----------------------------------------------------------------------------
; The committed view is refreshed at idle phases only.

(defun fn-own-store-idlep (s)
  (declare (xargs :guard t))
  (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files s))))

;; ---------------------------------------------------------------------------
;; The group index, extended instead of rebuilt (served-path-scale, PRF-173;
;; hot-path-scans section 4 item 1).  A refresh after one acceptance sees the
;; visible list grown by one article at its head; the index of the grown list
;; is the old index with that article's entries put in (`fn-gidx-build-of-
;; cons'), work in the article's memberships and the group count, not in N.
;; Any other change (a withdrawal, a verdict, a recovery view) rebuilds, as
;; `fn-midx-refresh' does for the Message-ID index.  The keystone
;; `fn-gidx-refresh-is-build': from an index that is the build of the old
;; list (or no index), the refreshed index IS the build of the new list, so
;; every served read over it answers as before.

(defun fn-gidx-put-all (entries buckets)
  (declare (xargs :guard t))
  (if (consp entries)
      (fn-gidx-put (car entries) (fn-gidx-put-all (cdr entries) buckets))
    buckets))

(defthm fn-gidx-build-entries-of-append
  (equal (fn-gidx-build-entries (append a b))
         (fn-gidx-put-all a (fn-gidx-build-entries b))))

(defthm fn-gidx-build-of-cons
  (equal (fn-gidx-build (cons article articles))
         (fn-gidx-put-all (fn-index-article-entries article)
                          (fn-gidx-build articles)))
  :hints (("Goal" :in-theory (enable fn-gidx-build fn-index-build))))

(defun fn-gidx-refresh (buckets old-articles new-articles)
  (declare (xargs :guard t))
  (cond ((null buckets) (fn-gidx-build new-articles))
        ((equal new-articles old-articles) buckets)
        ((and (consp new-articles)
              (equal (fn-ag-cdr new-articles) old-articles))
         (fn-gidx-put-all (fn-index-article-entries (fn-ag-car new-articles))
                          buckets))
        (t (fn-gidx-build new-articles))))

(defthm fn-gidx-refresh-is-build
  (implies (implies buckets
                    (equal buckets (fn-gidx-build old-articles)))
           (equal (fn-gidx-refresh buckets old-articles new-articles)
                  (fn-gidx-build new-articles)))
  :hints (("Goal" :in-theory (disable fn-gidx-build fn-gidx-put-all)
           :use ((:instance fn-gidx-build-of-cons
                            (article (car new-articles))
                            (articles (cdr new-articles)))))))

; The group index's number relation (PRF-189, books/group-bucket-index.lisp
; `fn-gidx-numbers-okp') is preserved by the one transition that changes the
; group index: the refresh, by a put of each new entry or a build.
(defthm fn-gidx-numbers-okp-of-put-all
  (implies (fn-gidx-numbers-okp buckets)
           (fn-gidx-numbers-okp (fn-gidx-put-all entries buckets)))
  :hints (("Goal" :in-theory (disable fn-gidx-put fn-gidx-numbers-okp))))

(defthm fn-gidx-numbers-okp-of-refresh
  (implies (fn-gidx-numbers-okp buckets)
           (fn-gidx-numbers-okp (fn-gidx-refresh buckets old-articles
                                                 new-articles)))
  :hints (("Goal" :in-theory (disable fn-gidx-put-all fn-gidx-build
                                      fn-gidx-numbers-okp))))

; The records a withdrawing article causes are decided by the refresh that
; first publishes it, under the configuration in force at that article's own
; Store txid (`fn-ctl-article-withdrawals': the txid of its acceptance record
; in the Store's records, the configuration journal `fn-sn-config-history').
; Recovery's rebuild decides alike (`fn-ctl-refresh-withdrawals-is-the-
; journal', books/control-visible.lisp).
(defun fn-own-refresh (o)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-sf-records-count
                                                           fn-ctl-refresh-withdrawals)))))
  (let ((s (fn-own-store o)))
    (if (fn-own-store-idlep s)
        (let* ((old-view (fn-own-view o))
               (acceptance (fn-node-acceptance (fn-sn-node s)))
               (raw (fn-state-articles acceptance))
               (old-raw (fn-own-view-raw old-view))
               (verdicts (fn-sn-verdicts s))
               ; The history is held as a snoc-list (books/store-files.lisp):
               ; reading it conses it back, so the refresh reads it only when
               ; the acceptance changed (a refresh that sees no new article
               ; keeps the withdrawals: the reference's first arm), and reads
               ; the count in O(1) (fn-sl-count-is-len).
               (withdrawals (mbe :logic (fn-ctl-refresh-withdrawals
                                         raw old-raw (fn-own-view-withdrawals old-view)
                                         verdicts (fn-sf-records (fn-sn-files s))
                                         (fn-sn-config-history s))
                                 :exec (if (equal raw old-raw)
                                           (fn-own-view-withdrawals old-view)
                                         (fn-ctl-refresh-withdrawals
                                          raw old-raw (fn-own-view-withdrawals old-view)
                                          verdicts (fn-sf-records (fn-sn-files s))
                                          (fn-sn-config-history s)))))
               (old-visible (fn-state-articles (fn-own-view-archive old-view)))
               (visible (fn-ctl-refresh-visible
                         raw old-raw old-visible withdrawals
                         (fn-own-view-verdicts old-view) verdicts))
               (archive (fn-ctl-visible-state-of acceptance visible))
               (withdrawn (fn-ctl-refresh-withdrawn
                           raw old-raw visible old-visible
                           (fn-own-view-withdrawn old-view)))
               (index (fn-midx-refresh
                       (fn-own-view-index old-view) old-visible visible)))
          (fn-own-make s
                     (fn-own-view-make-visible
                      (mbe :logic (len (fn-sf-records (fn-sn-files s)))
                           :exec (fn-sf-records-count (fn-sn-files s)))
                      (fn-sf-frontier (fn-sn-files s))
                      archive verdicts index
                      (fn-gidx-refresh (fn-own-view-group-index old-view)
                                       old-visible visible)
                      withdrawals raw withdrawn
                      (fn-sn-keyring-snapshots s))
                     (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                     (fn-own-pending o) (fn-own-ledger-field o) (fn-own-clock o)
                     (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
                     (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))
      o)))

; The owner of a store.  The host calls this once per process over the state
; fn-cpo-open-observed returned (books/config-observed.lisp;
; host/owner-host.lisp, fn-owner-recover).
(defun fn-own-start (store max-conns)
  (declare (xargs :guard t))
  (fn-own-refresh
   (fn-own-make store
                (let* ((prefix (fn-own-prefix-archive
                                (fn-sn-groups store) (fn-sn-capacity store)
                                (fn-sf-records (fn-sn-files store)) 0 0))
                       (archive (fn-ctl-visible-state prefix nil nil)))
                  (fn-own-view-make-visible
                   0 0 archive nil
                   (fn-midx-build (fn-state-articles archive))
                   (fn-gidx-build (fn-state-articles archive))
                   nil (fn-state-articles prefix)
                   (fn-ctl-subseq-diff (fn-state-articles prefix)
                                       (fn-state-articles archive))
                   nil))
                nil 0 max-conns nil nil nil nil nil nil nil nil nil nil)))

; -----------------------------------------------------------------------------
; Connections

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-own-replace-conn-loop (conn conns acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp conns)
      (if (equal (fn-own-conn-id (car conns)) (fn-own-conn-id conn))
          (revappend acc (cons conn (cdr conns)))
        (fn-own-replace-conn-loop conn (cdr conns) (cons (car conns) acc)))
    (revappend acc nil)))

(defun fn-own-replace-conn (conn conns)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp conns)
           (if (equal (fn-own-conn-id (car conns)) (fn-own-conn-id conn))
               (cons conn (cdr conns))
             (cons (car conns) (fn-own-replace-conn conn (cdr conns))))
         nil)
       :exec (fn-own-replace-conn-loop conn conns nil)))

(local
 (defthm fn-own-replace-conn-loop-is-revappend
   (equal (fn-own-replace-conn-loop conn conns acc)
          (revappend acc (fn-own-replace-conn conn conns)))
   :hints (("Goal" :induct (fn-own-replace-conn-loop conn conns acc)
                   :in-theory (union-theories '(fn-own-replace-conn-loop fn-own-replace-conn revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-own-replace-conn-loop)

(verify-guards fn-own-replace-conn
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-own-replace-conn)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-own-replace-conn-loop-is-revappend (acc nil))))))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-own-remove-conn-loop (id conns acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp conns)
      (if (equal (fn-own-conn-id (car conns)) id)
          (fn-own-remove-conn-loop id (cdr conns) acc)
        (fn-own-remove-conn-loop id (cdr conns) (cons (car conns) acc)))
    (revappend acc nil)))

(defun fn-own-remove-conn (id conns)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp conns)
           (if (equal (fn-own-conn-id (car conns)) id)
               (fn-own-remove-conn id (cdr conns))
             (cons (car conns) (fn-own-remove-conn id (cdr conns))))
         nil)
       :exec (fn-own-remove-conn-loop id conns nil)))

(local
 (defthm fn-own-remove-conn-loop-is-revappend
   (equal (fn-own-remove-conn-loop id conns acc)
          (revappend acc (fn-own-remove-conn id conns)))
   :hints (("Goal" :induct (fn-own-remove-conn-loop id conns acc)
                   :in-theory (union-theories '(fn-own-remove-conn-loop fn-own-remove-conn revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-own-remove-conn-loop)

(verify-guards fn-own-remove-conn
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-own-remove-conn)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-own-remove-conn-loop-is-revappend (acc nil))))))


(defun fn-own-find-conn (id conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (if (equal (fn-own-conn-id (car conns)) id)
          (car conns)
        (fn-own-find-conn id (cdr conns)))
    nil))

; The per-connection retained session is bounded by configuration: a POST
; session is a reader session and one bit (books/nntp-post.lisp), the reader
; session is four fields, its group is one of the configured names or nil, and its
; cursor is nil or inside RFC 3977 section 6's article-number range.  A read
; whose result leaves this set closes the connection (fn-own-read).  This is
; a four-field check and one member-equal over the configured names, not a
; whole-state recognizer.
; The connection's session is the SERVED session, and that is now
; fn-auth-step's: an auth session wrapping a peer session wrapping the
; POST-composed reader session.  This predicate still read it as a bare
; post session, so `fn-post-sessionp' was false on every connection and
; fn-own-read REMOVED each one after its first read -- the reply went out
; and the next command met a closed socket.  It has been that way since the
; peer port; the reader path has not survived two commands on dev since.
; The recognizer runs on the session only, never on the archive, which is
; what keeps it off the whole-state-revalidation list.
;
; History, because two lanes found this independently: the test was
; fn-post-sessionp until 2026-09-20.  A post session is two fields and
; the served session is three wrappers deep, so the test was FALSE on
; every connection the served path produces.  The branches guarded on it
; were never taken, the owner never enqueued a submission, fn-own-advance
; was a silent no-op, fn-own-read removed each connection after its first
; read, and fn-own-relation -- which conjoins this through
; fn-own-conn-okp -- was false on every state holding a connection, so
; every theorem hypothesising it was vacuous there.
(defun fn-own-conn-boundedp (conn groups)
  (declare (xargs :guard t))
  (let ((as (fn-own-conn-session conn)))
    (and (fn-auth-sessionp as)
         (let ((session (fn-auth-reader-session as)))
           (and (or (null (fn-nntp-session-group session))
                    (fn-ag-member (fn-nntp-session-group session) groups))
                (or (null (fn-nntp-session-current session))
                    (and (posp (fn-nntp-session-current session))
                         (<= (fn-nntp-session-current session)
                             *fn-nntp-max-article-number*))))))))

(defun fn-own-set-conns (o conns)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) conns (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))

(defun fn-own-reader-context (o id cfg)
  "Retain ACL2 node/config facts while the connection's role remains reader."
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if (and conn (fn-cfgp cfg))
        (let* ((as (fn-own-conn-session conn))
               (next-as
                (fn-auth-with-base
                 as (fn-peer-open-session (fn-own-conn-archive conn) nil
                                          (fn-sn-node (fn-own-store o)) cfg)))
               (next (fn-own-conn-make-group-indexed
                      (fn-own-conn-id conn) (fn-own-conn-version conn)
                      (fn-own-conn-frontier conn) (fn-own-conn-wire conn) next-as
                      (fn-own-conn-archive conn) (fn-own-conn-config conn)
                      (fn-own-conn-observation conn)
                      (fn-own-conn-verdicts conn)
                      (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn) (fn-own-conn-control conn))))
          (fn-own-set-conns o (fn-own-replace-conn next (fn-own-conns o))))
      o)))

; The wire limits of one connection.  RFC 3977 section 3.1's 512 octets
; include the CRLF (books/nntp-syntax.lisp).  A configured owner takes the
; article/body capacity from its pinned injection configuration, which the
; host builds from the same replayed Store profile used by direct acceptance.
; The positive fallback exists only for the pre-configuration model states
; that correctly refuse POST; it is not a production configuration default.
(defconst *fn-own-body-limit* 8192)
(defun fn-own-body-limit (o)
  (declare (xargs :guard t))
  (let ((limit (fn-inj-config-max-octets (fn-own-config o))))
    (if (posp limit)
        limit
      *fn-own-body-limit*)))

; Open pins the current committed view and opens one served connection over
; it (fn-served-open: the one place the whole-archive projection recognizer
; runs, once per connection, never per command).  The result is
; (effects . owner): the greeting the host writes, and the owner with the
; connection installed.  A refused open (bound reached) is (nil . o).  The
; posting configuration and the owner's latest clock observation are pinned
; into the connection here: one observation per connection, read by the
; served step from the connection and never from the owner.  That pin is the
; READER environment (DATE, NEWGROUPS) only.  The injection clock is not
; pinned: fn-own-read supplies the owner's current observation with every
; read, so each submission is injected at its own time (RFC 5537 section
; 3.4).
; `acfg' is the AUTHINFO/STARTTLS policy the operator configured
; (books/nntp-auth.lisp fn-auth-configp): the credentials, whether
; authentication is required and whether AUTHINFO needs a protected channel.
; It is pinned into the connection at open exactly as the posting
; configuration and the reader clock are, so no command re-reads it and a
; reconfiguration reaches only connections opened after it.  Anything that
; is not a configuration opens fn-auth-open-config, which requires nothing
; and offers nothing, so every owner theorem written before authentication
; keeps its meaning with `acfg' free.
(defun fn-own-open (o acfg)
  (declare (xargs :guard t))
  (if (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))
      (let* ((view (fn-own-view o))
             (archive (fn-own-view-archive view))
             (id (fn-own-next-id o))
             (opened (fn-served-open-group-indexed
                      archive (fn-own-view-index view)
                      (fn-own-view-group-index view)
                      (fn-own-view-verdicts view)
                      *fn-nntp-max-initial-line-octets*
                      (fn-own-body-limit o) (fn-own-config o)
                      (fn-own-clock o) (fn-own-clock o) acfg))
             (sconn (fn-served-result-conn opened))
             (conn (fn-own-conn-make-group-indexed id (fn-own-view-version view)
                                     (fn-own-view-frontier view)
                                     (fn-served-conn-wire sconn)
                                     (fn-served-conn-session sconn)
                                     archive (fn-own-config o) (fn-own-clock o)
                                     (fn-own-view-verdicts view)
                                     (fn-own-view-index view)
                                     (fn-own-view-group-index view) (fn-own-view-control view))))
        (cons (fn-served-result-effects opened)
              (fn-own-make (fn-own-store o) view (cons conn (fn-own-conns o))
                           (1+ (nfix id)) (fn-own-max-conns o) (fn-own-pending o)
                           (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))
    (cons nil o)))

; The transit port.  A peer connection is accepted on the SAME listener as a
; reader (specs/peering.md 1.1): the host resolves the source to a configured
; peer record at accept and passes its name here, and the role of the
; connection is decided by that record and by nothing the client says.  The
; session pins the peer record once (fn-served-open-peer ->
; fn-peer-open-session); the node it pins there is the opening value and is
; re-pinned per read by fn-own-conn-live-session, so the offer decision and
; the transfer decision both read the node as it is now.  RFC 4644 2.4.2
; makes a CHECK answer advisory -- a server MAY answer 238 and refuse later
; -- but it does not ask a server to forget what it holds, and answering 335
; for an article this connection delivered a moment ago costs the peer the
; whole article twice.  The body limit is the peer record's inbound-max-octets:
; an oversize article is cut by the wire machine and never by a second
; parser (specs/peering.md 1.3).  An unconfigured name opens a connection
; whose every offer is refused `:not-a-peer', which is the same refusal the
; decision function gives, not a second policy here.
; The body limit of a transit connection: the operator's profile bound
; (fn-own-body-limit, the same A a reader's POST meets), tightened by the
; peer record's inbound-max-octets when that is smaller.  Never the record's
; alone: `peer add' writes the record codec's payload ceiling
; (*fn-record-max-payload*, 4 GiB) there, and a connection opened with it
; retained whatever a peer streamed after TAKETHIS or IHAVE's 335 with no
; bound the operator chose (fuzz-nntp F2: 3.94 GiB of owner heap after 256
; MiB sent, neither a refusal nor a close).  AGENTS.md: bound the work and
; allocation one request may cause before consuming it; the wire closes the
; article at this limit (:body-overlimit) and books/peer-inbound.lisp
; fn-peer-transfer-unreceived-effects refuses it by name.
(defun fn-own-peer-body-limit (o record)
  (declare (xargs :guard t))
  (let ((profile (fn-own-body-limit o)))
    (if (and record (fn-cfg-peer-inbound record)
             (posp (fn-cfg-peer-inbound-max-octets record)))
        (min (fn-cfg-peer-inbound-max-octets record) profile)
      profile)))

(defthm fn-own-peer-body-limit-is-within-the-profile-bound
  (and (posp (fn-own-peer-body-limit o record))
       (<= (fn-own-peer-body-limit o record) (fn-own-body-limit o)))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary
                  (posp (fn-own-peer-body-limit o record))))
  :hints (("Goal" :in-theory (disable (:d fn-cfg-peer-inbound)
                                      (:d fn-cfg-peer-inbound-max-octets)))))

(defun fn-own-open-peer (o peer cfg acfg)
  (declare (xargs :guard t))
  (if (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))
      (let* ((view (fn-own-view o))
             (archive (fn-own-view-archive view))
             (id (fn-own-next-id o))
             (record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
             (limit (fn-own-peer-body-limit o record))
             ; The reader pin and the injection reading, in that order, as
             ; fn-own-open passes them: `fn-served-open-peer' gained the
             ; injection argument with the per-submission injection clock
             ; (w5/clock-seam) and this caller still passed eight, so
             ; books/owner did not admit at all against the merged
             ; books/served.  A transit connection takes the owner's current
             ; observation for both, exactly as a reader connection does.
             ; `acfg' is the owner's AUTHINFO policy, the same value
             ; `fn-own-open' pins into a reader.  It was not passed at all
             ; and `fn-served-open-peer' pinned the empty profile, so a
             ; connection the owner resolved to a peer record met no
             ; credential, no protected-only bit and no certificate --
             ; and on one box every client is resolved that way.
             (opened (fn-served-open-peer-group-indexed archive
                                          (fn-own-view-index view)
                                          (fn-own-view-group-index view)
                                          (fn-own-view-verdicts view)
                                          *fn-nntp-max-initial-line-octets*
                                          limit (fn-own-config o) (fn-own-clock o)
                                          (fn-own-clock o)
                                          peer (fn-sn-node (fn-own-store o)) cfg
                                          acfg))
             (sconn (fn-served-result-conn opened))
             (conn (fn-own-conn-make-group-indexed id (fn-own-view-version view)
                                     (fn-own-view-frontier view)
                                     (fn-served-conn-wire sconn)
                                     (fn-served-conn-session sconn)
                                     archive (fn-own-config o) (fn-own-clock o)
                                     (fn-own-view-verdicts view)
                                     (fn-own-view-index view)
                                     (fn-own-view-group-index view) (fn-own-view-control view))))
        (cons (fn-served-result-effects opened)
              (fn-own-make (fn-own-store o) view (cons conn (fn-own-conns o))
                           (1+ (nfix id)) (fn-own-max-conns o) (fn-own-pending o)
                           (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                           (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))
    (cons nil o)))

; The served port: one socket read of one connection is one fn-served-step
; over the connection's wire, session and pinned archive.  The result is
; (effects . owner); the host writes `effects` through fn-served-reply-octets
; and fn-served-closingp (host/owner-host.lisp, fn-owner-chunk-span-at) and takes no
; decision of its own.  An unknown connection reads nothing.  A read whose
; effects carry a submission (fn-served-submission: the :submit effect of an
; injected article) records it in the queue against this connection and its
; pinned version; the effects returned are still exactly the served step's.
;
; The served connection is rebuilt here from the owner's connection record
; and the owner's CURRENT clock observation, which is the injection clock of
; any submission this read produces; the connection's own pinned observation
; is passed unchanged as the reader environment.  One observation per
; connection would give every submission on a connection the same generated
; Message-ID, so the second post on a connection would be a duplicate of the
; first whatever its body.  The injection clock is therefore per read and
; the reader pin is per connection.
; The queue holds each submission PACKED (lane chunked-body-2, B6b;
; books/packed-submission.lisp): its article's octets one natural, its groups
; comma-joined into another, so a queued submission costs about an octet of
; heap an octet of its article instead of sixteen.  fn-own-take-submission
; unpacks it: the taken submission IS the enqueued one
; (fn-own-take-installs-the-enqueued-submission's round trip,
; fn-psub-unpack-of-pack-sub, holds with no hypothesis).  The fields the
; queue's readers look at -- id, version, mark, login, account, the
; Message-ID, whether it is transit or control -- are the packed record's
; own (the fn-own-sub-*-of-pack lemmas below).
(defun fn-own-enqueue (o sub)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-ag-append (fn-own-queue o) (list (fn-psub-pack-sub sub))) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))

; The local control channel is a submission port, not a second store writer.
; Its identifier is outside the natural-number connection namespace, so it
; cannot alias a socket and no control request consumes a connection slot.
(defconst *fn-own-control-id* :control)

;; The header limits the owner admits under (PRF-230, PKT-660): its
;; injection configuration's, which the host builds from the opened store
;; profile (host/owner-host.lisp `fn-owner-served-post-bound'), so a control
;; submission, a BP delivery and a peer transfer are refused past the same
;; max-header-fields, -lines and -octets as a POST.  A configuration of
;; another shape (none installed yet) reads the profile defaults.
(defun fn-own-config-header-limits (cfg)
  (declare (xargs :guard t))
  (if (fn-inj-config-shapep cfg)
      (fn-inj-config-header-limits cfg)
    *fn-article-default-limits*))

(defun fn-own-control-decision (cfg msgid groups octets)
  (declare (xargs :guard t))
  (if (and (fn-inj-config-allow cfg)
           (fn-af-message-idp msgid)
           (fn-inj-group-namesp groups)
           (consp groups)
           (fn-octet-listp octets)
           (posp (fn-inj-config-max-octets cfg))
           (<= (len octets) (fn-inj-config-max-octets cfg)))
      ; The CLI supplies an already-authored article object.  Preserve those
      ; octets exactly; NNTP POST separately calls fn-inj-decide because it
      ; receives a proto-article.  Both become the same owner submission
      ; record after that interface-specific boundary.  The profile's header
      ; limits hold here as for POST, refused by the limit's name.
      (let ((limit (fn-article-census-refusal
                    (fn-article-header-census octets)
                    (fn-own-config-header-limits cfg))))
        (if limit
            (fn-inj-refuse limit)
          (fn-inj-make-decision :injected nil msgid groups octets)))
    (fn-inj-refuse :control-invalid)))

(defun fn-own-control-submit-result (o msgid groups octets)
  (declare (xargs :guard t))
  (let ((decision (fn-own-control-decision (fn-own-config o)
                                           msgid groups octets)))
    (cond ((not (fn-inj-injectedp decision)) :refused)
          ; A control request is synchronous.  The host drains after every
          ; served read, so a non-idle writer here is a bounded busy refusal,
          ; never a second queue whose completion Python would have to match.
          ((or (consp (fn-own-queue o))
               (fn-own-inflight o)
               (fn-own-pending o)
               (not (equal (fn-sf-phase (fn-sn-files (fn-own-store o)))
                           :ready)))
           :busy)
          (t :submitted))))

(defun fn-own-control-submit (o msgid groups octets)
  (declare (xargs :guard t))
  (if (equal (fn-own-control-submit-result o msgid groups octets) :submitted)
      (fn-own-enqueue
       o (fn-own-sub-make *fn-own-control-id*
                          (fn-own-view-version (fn-own-view o)) nil
                          (fn-own-control-decision (fn-own-config o)
                                                   msgid groups octets)))
    o))

(defun fn-own-control-submissionp (sub)
  (declare (xargs :guard t))
  (and (consp sub) (equal (fn-own-sub-id sub) *fn-own-control-id*)))

; A BP application has no served connection.  It may enqueue the very same
; peer transit submission as a TAKETHIS transfer, using the control id only
; as the synchronous writer correlation key.  Admission is the current
; fn-peer-decide-transfer under the profile's header limits
; (fn-peer-decide-transfer-under), not the control/posting policy.
(defun fn-own-bp-transit-submit-result
    (o cfg peer msgid octets id subject)
  (declare (xargs :guard t :verify-guards nil))
  (let ((decision (fn-peer-decide-transfer-under
                   (fn-sn-node (fn-own-store o)) cfg peer msgid octets
                   (fn-own-clock o) id subject
                   (fn-own-config-header-limits (fn-own-config o)))))
    (cond ((not (equal (fn-peer-decision-kind decision) :want)) :refused)
          ((or (consp (fn-own-queue o)) (fn-own-inflight o)
               (fn-own-pending o)
               (not (equal (fn-sf-phase (fn-sn-files (fn-own-store o)))
                           :ready)))
           :busy)
          (t :submitted))))

(defun fn-own-bp-transit-submit (o cfg peer msgid octets id subject)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (fn-own-bp-transit-submit-result
              o cfg peer msgid octets id subject) :submitted)
      (fn-own-enqueue
       o (fn-own-sub-make *fn-own-control-id*
                          (fn-own-view-version (fn-own-view o)) nil
                          (fn-peer-make-submission peer :takethis
                                                   msgid octets)))
    o))

(defun fn-own-bp-transit-submissionp (sub)
  (declare (xargs :guard t))
  (and (fn-own-control-submissionp sub)
       (fn-peer-submissionp (fn-own-sub-decision sub))))

; The operator's submission: `fn operator CONFIG post' (host/native/operator.lisp
; `fnn-operator-execute-post', the local control channel, host/native/owner.lisp
; `fnn-owner-control-submit-serialized', host/owner-host.lisp
; `fn-owner-operator-submit', the (:operator-submit ...) event below).
;
; Until 2026-09-22 this verb reached `fn-own-control-submit': the supplied
; octets were stored as they came, with no Path, Injection-Date or
; Injection-Info, and the outbound feed offered them so; INN answered `437
; Missing "Path" header field' (planning/evidence/inn-lab-dabebb84-2026-09-22.md,
; finding 1).  An operator submitting a proto-article is a posting agent and
; this node its injecting agent (RFC 5537 section 3.5), exactly as for POST:
; the octets are fn-inj-decide's, under the owner's posting configuration and
; the owner's current clock reading, and with no clock nothing is injected
; (D10-a).  The Message-ID and the newsgroups the command line names must be
; the ones the injection reads from the article; a disagreement is refused
; (:control-mismatch), never reconciled.
;
; A retry of one proto-article after the clock has moved injects different
; octets (a new Injection-Date), which the store answers as a conflict: an
; operator whose first outcome was lost would be told `refused' of an article
; the node holds.  So when the live node already holds that Message-ID as an
; injection of these very source octets by this agent (fn-inj-reinjectionp),
; the submission IS the stored article and the store answers its duplicate
; (fn-own-operator-retry-resubmits-the-stored-injection, books/owner-invariants).
;
; STORED is those octets, or :absent when the node holds no article with the
; Message-ID.  After the records flip the acceptance article holds a HANDLE,
; which this pure step cannot read: the event carries the octets, and the
; entry that computes them reads them under the held handle through the
; arena (books/owner-served-invariants.lisp fn-own-operator-stored-octets,
; flip-L8-2).  Whatever STORED a caller passes, only a reinjection of the
; operator's own source by this agent is ever enqueued
; (fn-own-operator-decision-is-an-injection-of-the-payload), and the store's
; duplicate check over alpha decides duplicate or conflict.
;
; The hybrid-signed author path and the BP application path still submit
; exact authored octets through fn-own-control-submit: a signature binds
; those octets, and neither path is this verb.
; The handle of the node's article with MSGID, or :absent.
(fn-payload-kind fn-own-stored-handle :source "returns the stored article's handle")
(defun fn-own-stored-handle (node msgid)
  (declare (xargs :guard t))
  (let ((article (fn-find-article (fn-record-octets-string msgid)
                                  (fn-state-articles (fn-node-acceptance node)))))
    (if article (fn-article-payload article) :absent)))

(defun fn-own-clock-usablep (clock)
  (declare (xargs :guard t))
  (and (fn-clock-observationp clock) (fn-clock-has-wall clock) t))

(defun fn-own-operator-decision (cfg clock stored msgid groups octets)
  (declare (xargs :guard t))
  (if (not (fn-own-clock-usablep clock))
      (fn-inj-refuse :clock-unusable)
    (if (and (fn-inj-config-allow cfg)
             (not (equal stored :absent))
             (fn-inj-reinjectionp stored octets (fn-inj-config-agent cfg) msgid))
        (fn-inj-make-decision :injected nil msgid groups stored)
      (let ((d (fn-inj-decide octets cfg clock)))
        (cond ((not (fn-inj-injectedp d)) d)
              ((not (and (equal (fn-inj-decision-msgid d) msgid)
                         (equal (fn-inj-decision-groups d) groups)))
               (fn-inj-refuse :control-mismatch))
              (t d))))))

(defun fn-own-operator-decision-of (o msgid groups octets stored)
  (declare (xargs :guard t))
  (fn-own-operator-decision (fn-own-config o) (fn-own-clock o) stored msgid groups
                            octets))

(defun fn-own-operator-submit-result (o msgid groups octets stored)
  (declare (xargs :guard t))
  (let ((decision (fn-own-operator-decision-of o msgid groups octets stored)))
    (cond ((not (fn-inj-injectedp decision)) :refused)
          ((or (consp (fn-own-queue o))
               (fn-own-inflight o)
               (fn-own-pending o)
               (not (equal (fn-sf-phase (fn-sn-files (fn-own-store o)))
                           :ready)))
           :busy)
          (t :submitted))))

(defun fn-own-operator-submit (o msgid groups octets stored)
  (declare (xargs :guard t))
  (if (equal (fn-own-operator-submit-result o msgid groups octets stored) :submitted)
      (fn-own-enqueue
       o (fn-own-sub-make *fn-own-control-id*
                          (fn-own-view-version (fn-own-view o)) nil
                          (fn-own-operator-decision-of o msgid groups octets stored)))
    o))

; The node a peer connection's OFFER decision reads.
;
; `fn-peer-decide-offer' (books/peer-inbound.lisp, the IHAVE and CHECK arms
; of `fn-peer-command') answers from the node its session carries, and only
; `fn-peer-open-session' ever wrote that field: the offer was decided against
; the node as it stood when the connection opened, for the whole life of the
; connection.  A peer that transferred an article and then offered the same
; Message-ID again on the same connection was told `335'/`238' -- and then
; `437'/`439' after paying for the bytes -- because K3's duplicate
; suppression, which is proved of `fn-peer-decide-offer', was handed a node
; that did not hold the article yet.  A persistent streaming feed pays that
; for every article it has already sent.  Measured on `tools/v0_matrix.py'
; at `6fb30ca': `V0-TRANSIT-DUPLICATE-AB/BA' `335' where the model says
; `435', `V0-TRANSIT-CHECK-DUP-AB/BA' `238' where it says `438'.
;
; The node is re-pinned here from the owner's own store, once per socket
; read.  That is the finest granularity that can differ: nothing becomes
; durable inside one read (the submission this read produces is drained
; after it), so a finer re-pin could not change an answer.  It is one field
; assignment on one connection and no recognizer runs over the store, so it
; is not the whole-state revalidation D3 forbids on a served path.
;
; The PEER RECORD stays pinned: the owner holds no store configuration to
; re-read, so `fn-peer-session-cfg' is still the value `fn-own-open-peer'
; took at `:open'.  The transfer decision does read the live configuration,
; because the host passes it (host/owner-host.lisp `fn-owner-transit-decide').
; An ordinary reader connection is returned unchanged.  A contextual reader
; (one with a pinned peer configuration but no peer name yet) is refreshed as
; well: AUTHINFO may promote it and dispatch a following CHECK from the same
; socket read, before fn-own-read has another opportunity to refresh it.
(defun fn-own-conn-live-session (o conn)
  (declare (xargs :guard t))
  (let* ((as (fn-own-conn-session conn))
         (ps (fn-auth-session-base as)))
    (if (fn-peer-session-cfg ps)
        (fn-auth-with-base as (fn-peer-with-refused
                               (fn-peer-with-node ps (fn-sn-node (fn-own-store o)))
                               (fn-own-refused o)))
      as)))

; The served connection of an owner connection: its pin, SESSION (the live
; one for a peer, fn-own-conn-live-session; the connection's own for the
; per-event law), the owner's clock as the injection reading, its pin
; identity and the owner's committed view as the live pin GROUP and LISTGROUP
; advance to (NNT-042, books/served.lisp fn-served-repin).
(defun fn-own-served-conn (o conn session)
  (declare (xargs :guard t))
  (fn-served-make-conn-live (fn-own-conn-wire conn) session
                            (fn-own-conn-archive conn) (fn-own-conn-config conn)
                            (fn-own-conn-observation conn) (fn-own-clock o)
                            (fn-own-conn-verdicts conn) (fn-own-conn-index conn)
                            (fn-own-conn-group-index conn) (fn-own-conn-control conn)
                            (fn-served-pinned-make (fn-own-conn-version conn)
                                                   (fn-own-conn-frontier conn) nil)
                            (fn-own-view-live (fn-own-view o))))

; The login a served connection's session has authenticated as: the name
; AUTHINFO USER cached once AUTHINFO PASS set the subject (RFC 4643 section
; 2.3), nil before; and the account, the subject itself (the principal id
; of the credential that authenticated: the credential file's principal,
; or a redeemed account's local principal).
(defun fn-own-session-login (as)
  (declare (xargs :guard t))
  (if (fn-auth-session-subject as) (fn-auth-session-pending as) nil))

(defun fn-own-session-account (as)
  (declare (xargs :guard t))
  (fn-auth-session-subject as))


; The read's pin, taken back from the served connection: what it was, or the
; view's when GROUP or LISTGROUP advanced it (fn-served-step-pin-is-old-or-live).
; The submission's login is the one its :submit effect carries
; (books/served.lisp fn-served-login, read by fn-served-submission-login):
; the login of the session at the event that decided the article, so an
; AUTHINFO earlier in the same read as a complete POST is the article's
; login, and one later in the read never claims it (PKT-597).
(defun fn-own-finish-read (o conn result)
  (declare (xargs :guard t))
  (let* ((effects (fn-served-result-effects result))
         (sconn (fn-served-result-conn result))
         (id (fn-own-conn-id conn))
         (pinned (fn-served-conn-pinned sconn))
         (next (fn-own-conn-make-group-indexed id
                                 (fn-served-pinned-version pinned)
                                 (fn-served-pinned-frontier pinned)
                                 (fn-served-conn-wire sconn)
                                 (fn-served-conn-session sconn)
                                 (fn-served-conn-archive sconn)
                                 (fn-own-conn-config conn)
                                 (fn-own-conn-observation conn)
                                 (fn-served-conn-verdicts sconn)
                                 (fn-served-conn-index sconn)
                                 (fn-served-conn-group-index sconn)
                                 (fn-served-conn-control sconn)))
         (decision (fn-served-submission effects)))
    (cons effects
          (if (and (fn-own-conn-boundedp
                    next (fn-sn-groups (fn-own-store o)))
                   (fn-own-conn-boundedp
                    next (fn-state-groups (fn-own-conn-archive next))))
              (let ((o2 (fn-own-set-conns
                         o (fn-own-replace-conn next (fn-own-conns o)))))
                (if decision
                    (fn-own-enqueue
                     o2 (fn-own-sub-make-author
                         id (fn-own-conn-version conn) nil decision
                         (fn-served-submission-login effects)
                         (fn-served-submission-account effects)))
                  o2))
            (fn-own-set-conns o (fn-own-remove-conn id (fn-own-conns o)))))))

; Whether a served result moved the connection's pin (NNT-042): read off the
; pin identity, never by comparing archives.
(defun fn-own-result-repinned (result)
  (declare (xargs :guard t))
  (and (fn-served-pinned-repinned
        (fn-served-conn-pinned (fn-served-result-conn result)))
       t))

; The read with its third answer, whether the pin moved: the configured
; owner (books/owner-config.lisp fn-ocfg-with-read-owner) moves the
; connection's configuration pin with it, exactly as it does at :advance.
(defun fn-own-read-full (o id octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((result (fn-served-step
                        (fn-own-served-conn o conn (fn-own-conn-live-session o conn))
                        octets fn-arena))
               (finished (fn-own-finish-read o conn result)))
          (list (car finished) (cdr finished) (fn-own-result-repinned result)))
      (list nil o nil))))

(defun fn-own-read (o id octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((r (fn-own-read-full o id octets fn-arena)))
    (cons (car r) (car (cdr r)))))

(defun fn-own-read-repinned (o id octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (car (cdr (cdr (fn-own-read-full o id octets fn-arena)))))

; The per-event law under the served port: one framed wire event is one
; fn-served-dispatch (fn-nntp-post-step with the article-mode switch,
; books/served.lisp) against the connection's own pinned archive.
; fn-served-step is the byte fold that runs fn-served-dispatch on each framed
; event before the next byte is framed; this is that fold's one step with the
; owner's bookkeeping around it.  It records no submission: the served port
; does that once per read.
(defun fn-own-read-step-full (o id event fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((result (fn-served-dispatch
                        (fn-own-served-conn o conn (fn-own-conn-session conn))
                        event fn-arena))
               (sconn (fn-served-result-conn result))
               (pinned (fn-served-conn-pinned sconn))
               (next (fn-own-conn-make-group-indexed (fn-own-conn-id conn)
                                       (fn-served-pinned-version pinned)
                                       (fn-served-pinned-frontier pinned)
                                       (fn-served-conn-wire sconn)
                                       (fn-served-conn-session sconn)
                                       (fn-served-conn-archive sconn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-served-conn-verdicts sconn)
                                       (fn-served-conn-index sconn)
                                       (fn-served-conn-group-index sconn)
                                       (fn-served-conn-control sconn))))
          (list (fn-served-result-effects result)
                (if (and (fn-own-conn-boundedp
                          next (fn-sn-groups (fn-own-store o)))
                         (fn-own-conn-boundedp
                          next (fn-state-groups (fn-own-conn-archive next))))
                    (fn-own-set-conns o (fn-own-replace-conn next (fn-own-conns o)))
                  (fn-own-set-conns o (fn-own-remove-conn id (fn-own-conns o))))
                (fn-own-result-repinned result)))
      (list nil o nil))))

(defun fn-own-read-step (o id event fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((r (fn-own-read-step-full o id event fn-arena)))
    (cons (car r) (car (cdr r)))))

; Advance re-pins a connection to the newest committed view.  The projection
; verdict is recomputed for the new archive (one recognizer run per advance);
; the cursor is kept because local numbers are never reused (PRF-002); the
; wire framing state is kept because the peer's stream is unaffected.
(defun fn-own-advance-result (o id)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((view (fn-own-view o))
               (archive (fn-own-view-archive view))
               ; The served session is three deep -- auth over peer over
               ; the POST-composed reader -- and the re-pin replaces only
               ; the innermost one.  Rebuilding it as a bare post session
               ; (what this did) threw away the peer half and, since this
               ; lane, the login as well: the rebuilt connection then
               ; failed fn-own-conn-boundedp and the advance was silently
               ; refused, so ADVANCE has been a no-op since the peer port.
               (old (fn-own-conn-session conn))
               (pold (fn-auth-session-base old))
               (told (fn-peer-session-base pold))
               (base (fn-post-session-base told))
               (session (fn-auth-with-base
                         old
                         (fn-peer-with-base
                          pold
                          (fn-post-make-session
                           (fn-nntp-set-cursor (fn-nntp-open-session archive)
                                               (fn-nntp-session-group base)
                                               (fn-nntp-session-current base))
                           (fn-post-session-awaiting told)))))
               (next (fn-own-conn-make-group-indexed (fn-own-conn-id conn)
                                       (fn-own-view-version view)
                                       (fn-own-view-frontier view)
                                       (fn-own-conn-wire conn)
                                       session archive
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-view-verdicts view)
                                       (fn-own-view-index view)
                                       (fn-own-view-group-index view) (fn-own-view-control view))))
          (if (fn-own-conn-boundedp next (fn-sn-groups (fn-own-store o)))
              (cons :advanced
                    (fn-own-set-conns o
                                      (fn-own-replace-conn next
                                                           (fn-own-conns o))))
            (cons :refused o)))
      (cons :absent o))))

(defun fn-own-advance (o id)
  ; Existing owner callers consume only the state.  The configured wrapper
  ; consumes the outcome too, so a refused rebuild cannot move its pin.
  (declare (xargs :guard t))
  (cdr (fn-own-advance-result o id)))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-own-remove-subs-loop (id subs acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp subs)
      (if (equal (fn-own-sub-id (car subs)) id)
          (fn-own-remove-subs-loop id (cdr subs) acc)
        (fn-own-remove-subs-loop id (cdr subs) (cons (car subs) acc)))
    (revappend acc nil)))

(defun fn-own-remove-subs (id subs)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp subs)
           (if (equal (fn-own-sub-id (car subs)) id)
               (fn-own-remove-subs id (cdr subs))
             (cons (car subs) (fn-own-remove-subs id (cdr subs))))
         nil)
       :exec (fn-own-remove-subs-loop id subs nil)))

(local
 (defthm fn-own-remove-subs-loop-is-revappend
   (equal (fn-own-remove-subs-loop id subs acc)
          (revappend acc (fn-own-remove-subs id subs)))
   :hints (("Goal" :induct (fn-own-remove-subs-loop id subs acc)
                   :in-theory (union-theories '(fn-own-remove-subs-loop fn-own-remove-subs revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-own-remove-subs-loop)

(verify-guards fn-own-remove-subs
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-own-remove-subs)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-own-remove-subs-loop-is-revappend (acc nil))))))


; Closing drops the connection, its pending transaction, its queued
; submissions and its submission in flight (a durable path already running
; for it completes through the store events and is acknowledged to nobody).
(defun fn-own-close (o id)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o)
               (fn-own-remove-conn id (fn-own-conns o))
               (fn-own-next-id o) (fn-own-max-conns o)
               (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
               (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-own-remove-subs id (fn-own-queue o))
               (if (and (fn-own-inflight o)
                        (equal (fn-own-sub-id (fn-own-inflight o)) id))
                   nil
                 (fn-own-inflight o)) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))

; -----------------------------------------------------------------------------
; Transactions: the fn-sn machine, owned by one connection at a time.

(defun fn-own-begin (o id)
  (declare (xargs :guard t))
  (if (and (null (fn-own-pending o))
           (fn-own-find-conn id (fn-own-conns o))
           (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready))
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) id
                   (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))
    o))

; Every kernel/node transition of the store, including the resolution
; transitions, crash and recover, goes through the proved fn-snrt-step.  The
; guard is the invariant fn-snrt-step's callees carry; it is not verified
; because fn-snrt-step itself (store) is not.
(defun fn-own-store-step (o event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o)) :verify-guards nil))
  (fn-own-refresh
   (fn-own-make (fn-snrt-step (fn-own-store o) event) (fn-own-view o)
                (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger-field o) (fn-own-clock o)
                (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))

; Completion is the actual fn-sn-finish.  It is consumed exactly when the
; kernel is at :completing with a bound record; the consumed pair is the
; kernel's own completion, recorded once in the ledger.  Away from that phase
; a completion is a no-op on the whole owner.
(defun fn-own-complete (o)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (let ((s (fn-own-store o)))
    (if (fn-sn-completion-enabledp s)
        (fn-own-refresh
         (fn-own-make (fn-sn-finish s) (fn-own-view o) (fn-own-conns o)
                      (fn-own-next-id o) (fn-own-max-conns o) nil
                      (fn-sl-snoc (fn-own-ledger-field o) (fn-sf-completion (fn-sn-files s)))
                      (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                      (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))
      o)))

; A process restart.  The image (frontier records) is what the platform left
; behind (A-DURABILITY as the hypothesis fn-sf-crash-imagep); the new process
; reopens through fn-sn-open-observed, the store-only model reopen (the host
; reopens through fn-cpo-open-observed, which replays the configuration
; journal first; fn-own-reopen does not name it), with no
; connections, no pending transaction and no clock (the monotonic counter has
; no meaning across processes).  The ledger is proof-only and is kept.  This
; is a model event: the host restarts by calling fn-owner-recover, which
; dispatches on fn-sn-open-kind (fn-own-open-kind-ok-is-okp,
; owner-invariants.lisp); the two recognizers here are the model's crash
; relation and never run on a served path.
(defun fn-own-reopen (o frontier records)
  (declare (xargs :guard t))
  (let* ((s (fn-own-store o))
         (opened (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                      frontier records)))
    (if (and (fn-sf-crash-imagep (fn-sn-files s) frontier records)
             (fn-sn-open-okp opened))
        (fn-own-refresh
         (fn-own-make (fn-sn-open-state opened) (fn-own-view o) nil
                      (fn-own-next-id o) (fn-own-max-conns o) nil
                      (fn-own-ledger-field o) nil (fn-own-facts o) (fn-own-config o)
                      nil nil (fn-own-feed-restart-all (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o)))
      o)))

; -----------------------------------------------------------------------------
; Clock observations and clock-stamped group-configuration facts

; Three answers, and they are the owner's, not the host's (decision D10-a).
;
;   :invalid   the host supplied no clock observation at all.  A malformed
;              message changes nothing, including the clock.
;   :refused   the reading is not a LATER observation of the same clock
;              (fn-clock-later-observationp): the monotonic counter went
;              backwards, has-wall changed, or a widened error bound moved
;              the earliest admissible true time back.  The host has
;              contradicted the clock it was reporting.
;   :observed  the reading is admitted and becomes the owner's.  A reading
;              EQUAL to the one already held is :observed, not refused: it is
;              admitted, and nothing moved because nothing had to.
;
; host/owner-host.lisp used to infer the word by comparing the owner before
; and after the event, which spelled the equal-reading case exactly like a
; contradiction and put the decision in the host.  The word is this
; function's; the host reports it.
(defun fn-own-observe-outcome (o obs)
  (declare (xargs :guard t))
  (if (not (fn-clock-observationp obs))
      :invalid
    (if (or (null (fn-own-clock o))
            (and (fn-clock-observationp (fn-own-clock o))
                 (fn-clock-later-observationp (fn-own-clock o) obs)))
        :observed
      :refused)))

; A refusal COSTS the owner its clock.  specs/time.md: a node that discovers
; its clock was wrong is allowed to stop being sure.  Keeping the
; contradicted reading -- what this function used to do -- leaves the node
; deciding under a clock the host has just withdrawn: books/injection derives
; a generated Message-ID from the reading alone, so every POST after the
; first in that window mints the identity of the first, the durable path
; refuses it as a duplicate, and the poster is told `the article was
; refused'.  That is an article verdict for a clock fault.
;
; With no clock the owner injects nothing (fn-inj-decide answers
; :clock-unusable, whose 441 line is `this server has no usable clock
; reading'), declares no group (fn-own-declare-group) and answers DATE with
; 503 (fn-nntp-date-response) -- until the host supplies a reading it
; accepts, which, the clock being absent, is the very next one.  A nil clock
; is not a new state: fn-own-start and fn-own-reopen both leave one, and
; fn-own-relation admits it.
(defun fn-own-observe (o obs)
  (declare (xargs :guard t))
  (let ((outcome (fn-own-observe-outcome o obs)))
    (if (equal outcome :invalid)
        o
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                   (fn-own-ledger-field o)
                   (if (equal outcome :observed) obs nil)
                   (fn-own-facts o) (fn-own-config o)
                   (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))))

; No fact without a clock observation: creation is refused until the host
; has supplied one.
(defun fn-own-declare-group (o name)
  (declare (xargs :guard t))
  (if (and (stringp name)
           (fn-clock-observationp (fn-own-clock o))
           (not (member-equal name (fn-own-replay-facts (fn-own-facts o)))))
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                   (fn-own-ledger-field o) (fn-own-clock o)
                   (fn-ag-append (fn-own-facts o)
                                 (list (fn-own-group-fact-make name (fn-own-clock o))))
                   (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))
    o))

; -----------------------------------------------------------------------------
; The outbound feed (books/owner-feed.lisp; specs/peering.md sec. 3)
;
; The owner drives one feed per configured outbound peer.  Four things reach
; the feed table and nothing else does:
;
;   * a configuration (fn-own-feeds-reconfigure, the (:feeds cfg) arm), at
;     open and after every :set-peer / :remove-peer delta.  The peer records
;     are read THERE and copied into the table, so the durable path below
;     needs no configuration argument;
;   * a DURABLE acceptance (fn-own-feed-durable, inside fn-own-outcome and
;     fn-own-transit-outcome).  Nothing is enqueued on a refusal or on an
;     uncertain outcome: an offer is a claim that this node holds the
;     article, and only :durable is that claim;
;   * a tick (fn-own-tick) and a peer's reply (fn-own-feed-reply);
;   * a replay of the peer's FNFD journal at open (fn-own-feed-recover) and
;     the fence every feed gets when the process died (fn-own-reopen, which
;     restarts every feed: K5's restart-by-offer).
;
; Which peers an article goes to is books/owner-feed.lisp's decision and is
; proved there (fn-own-feed-never-offers-a-loop, fn-own-feed-target-is-in-scope,
; fn-own-feed-target-is-offerable with its converse).  Nothing here re-derives
; it and nothing in Python or host Lisp does either.

(defun fn-own-with-feeds (o feeds)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
               (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
               (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
               (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) feeds (fn-own-node-secret o) (fn-own-refused o)))

; What a submission tells the feed.  Both kinds carry the Message-ID and the
; article as octets; only a transit submission has an origin peer.  The octets
; are the submission's: books/injection's injected form for a POST (it
; carries the generated Path and Message-ID), which is what became durable,
; and the octets received from the peer for a transit article.  What the
; owner stages for a transit article is fn-peer-relayed-octets of those
; (fn-own-sub-stored-octets, books/owner-served-invariants.lisp: the Path
; with this node's identity prepended when one is set, Xref removed), so
; with a Path identity the durable octets differ from these.
(defun fn-own-sub-origin (sub)
  (declare (xargs :guard t))
  (if (fn-peer-submissionp (fn-own-sub-decision sub))
      (fn-peer-submission-peer (fn-own-sub-decision sub))
    nil))

(defun fn-own-sub-msgid (sub)
  (declare (xargs :guard t))
  (let ((d (fn-own-sub-decision sub)))
    (if (fn-peer-submissionp d)
        (fn-peer-submission-msgid d)
      (fn-inj-decision-msgid d))))

(defun fn-own-sub-octets (sub)
  (declare (xargs :guard t))
  (let ((d (fn-own-sub-decision sub)))
    (if (fn-peer-submissionp d)
        (fn-peer-submission-octets d)
      (fn-inj-decision-octets d))))

(defun fn-own-feed-stamp (o)
  (declare (xargs :guard t))
  (nfix (fn-clock-monotonic (fn-own-clock o))))

; The acceptance-intent half of the same path.  It is projected while the
; submission is in flight, before the store transaction begins.  The targets
; are fixed by the owner's current feed table and exact accepted article;
; peers that already hold this Message-ID in their durable feed need no new
; obligation.  Every remaining target must have room before any article
; commit is attempted, so a full feed cannot turn a durable acceptance into
; a silently lost obligation.
;
; A control article's scope (PKT-400, RFC 5537 sections 3.6 and 5.3).  A
; relaying agent selects an article for a peer by the names in its
; Newsgroups field (section 3.6), and a cancel "SHOULD have the same
; Newsgroups header field as the message it is cancelling" precisely so
; that it is relayed to the same servers (section 5.3).  fn FILES a control
; article in its filing group, control.<verb> (section 3.7;
; fn-pa-filing-plan), and a local or signed control submission carries that
; filing group as its only group.  Selecting by it alone meant a friend
; whose wildmat was `local.*' never received the cancel of a local.general
; article (the two-machine session of 2026-09-26).  So a control article is
; offered under the groups its Newsgroups names AND under its filing group:
; the first is the RFC's relaying rule, the second keeps a peer that asked
; for `control.cancel' by name.  An ordinary article's scope is unchanged.
;
; One parse: the article is read once (fn-own-feed-article-of) and both the
; classification (books/control-classify.lisp fn-ctl-classify, the one
; fn-pa-filing-plan uses) and the Newsgroups names (fn-af-relayed-article-check,
; the view fn-own-feed-groups-of reads) come from that parse.
(defun fn-own-feed-control-of (octets)
  (declare (xargs :guard t))
  (let ((a (fn-own-feed-article-of octets)))
    (if (null a) nil (fn-ctl-classify a))))

(defun fn-own-feed-control-groups-of (octets)
  (declare (xargs :guard t
                  :guard-hints (("Goal"
                                 :use fn-own-feed-article-of-is-syntax
                                 :in-theory
                                 (disable fn-own-feed-article-of-is-syntax
                                          fn-own-feed-article-of
                                          fn-ctl-classify
                                          fn-ctl-filing-group
                                          fn-record-string-octets)))))
  (let ((a (fn-own-feed-article-of octets)))
    (if (null a)
        nil
      (let ((c (fn-ctl-classify a)))
        (if (and (consp c) (eq (car c) :control) (consp (cdr c)))
            (cons (fn-record-string-octets (fn-ctl-filing-group (cadr c)))
                  (let ((check (fn-af-relayed-article-check a)))
                    (if (equal (fn-af-status-kind check) :ok)
                        (fn-frame-item 2 check)
                      nil)))
          nil)))))

; Closed from here on, in and out of the vocabulary: opened, every goal
; about a submission pays for the article grammar.
(in-theory (disable fn-own-feed-control-of fn-own-feed-control-groups-of))

(defun fn-own-sub-feed-base-groups (sub)
  (declare (xargs :guard t))
  (let ((d (fn-own-sub-decision sub)))
    (if (fn-peer-submissionp d)
        ; Transit is validated as a relayed article and its scope comes from
        ; that article.  A local/control submission already carries the
        ; injection decision's groups; using them preserves the exact
        ; authored bytes, including legacy articles with no Injection-Info.
        (fn-own-feed-groups-of (fn-own-sub-octets sub))
      (fn-inj-decision-groups d))))

; The groups the feed matches peers' wildmats against: the base groups,
; and for a control article its Newsgroups names and filing group too.
(defun fn-own-sub-feed-groups (sub)
  (declare (xargs :guard t))
  (let ((base (fn-own-sub-feed-base-groups sub))
        (ctl (fn-own-feed-control-groups-of (fn-own-sub-octets sub))))
    (if (consp ctl)
        (append (true-list-fix base) ctl)
      base)))

; The peers the in-flight submission is offered to: the scope decision
; (fn-own-feed-targets), then each peer's Distribution filter (PRF-237,
; fn-own-feed-distribution-targets over the article's own Distribution),
; then the peers whose queue does not already hold the Message-ID.
(defun fn-own-submission-targets (o)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (if (null sub)
        nil
      (let* ((tbl (fn-own-feeds o))
             (msgid (fn-own-sub-msgid sub))
             (octets (fn-own-sub-octets sub))
             (groups (fn-own-sub-feed-groups sub))
             ; PKT-658: a submission naming a moderation queue group of the
             ; owner's posting configuration (books/moderation.lisp) is
             ; offered to no peer: held posts never leave the node.
             ; PRF-237: otherwise the targets whose distributions the
             ; article's Distribution names.
             (targets (if (fn-mod-names-a-queuep
                           groups (fn-inj-config-closed (fn-own-config o)))
                          nil
                        (fn-own-feed-distribution-targets
                         (fn-own-feed-targets
                          tbl (fn-own-sub-origin sub) groups
                          (fn-own-feed-path-of octets))
                         tbl (fn-own-feed-distributions-of octets)))))
        (fn-own-feed-new-targets targets tbl msgid)))))

(defun fn-own-submission-intent-result (o evidence generation txid)
  (declare (xargs :guard t))
  (let* ((sub (fn-own-inflight o))
         (identity (and sub
                        (fn-own-feed-intent-id (fn-own-sub-msgid sub)
                                               (fn-own-sub-octets sub))))
         (targets (fn-own-submission-targets o)))
    (cond ((null sub) :absent)
          ((or (not (fn-feed-namep identity))
               (not (fn-feed-namep evidence))
               (not (natp generation)) (not (natp txid)))
           :refused)
          ((not (fn-own-feed-target-capacityp
                 targets (fn-own-feeds o) (fn-own-sub-msgid sub)))
           :capacity)
          (t :ready))))

; PRF-335: the word a submission whose intent is not :ready is answered
; with.  :capacity (a target peer's feed queue has no room) is named
; :feed-queue-full, which POST renders as its own 441 line and transit as 436
; (books/nntp-post.lisp fn-post-store-refusal-text, books/peer-inbound.lisp
; fn-peer-transit-code); anything else is the bare :refused.  Host:
; host/native/owner.lisp fnn-owner-drain-one.
(defun fn-own-intent-refusal-word (result)
  (declare (xargs :guard t))
  (if (equal result :capacity) :feed-queue-full :refused))

(defthm fn-own-intent-refusal-word-is-a-refusal
  (fn-post-store-refusalp (fn-own-intent-refusal-word result)))

(defun fn-own-submission-intent-records (o evidence generation txid)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (if (not (equal (fn-own-submission-intent-result
                     o evidence generation txid) :ready))
        nil
      (fn-own-feed-intent-records
       (fn-own-submission-targets o)
       (fn-own-sub-msgid sub)
       (fn-own-feed-intent-id (fn-own-sub-msgid sub) (fn-own-sub-octets sub))
       evidence generation txid (fn-own-feed-stamp o)))))



; The enqueue on a durable acceptance, and the FNFD records that authorize
; it.  The host appends the records to <journal>/feed/<peer>.fnfd and only
; then may the offer they enable be emitted.
(defun fn-own-feed-durable (o sub)
  (declare (xargs :guard t))
  (fn-own-feed-enqueue-all (fn-own-submission-targets o) (fn-own-feeds o)
                           (fn-own-sub-msgid sub) (fn-own-feed-stamp o)))

(defun fn-own-feed-durable-records (o sub)
  (declare (xargs :guard t))
  (fn-own-feed-enqueue-records (fn-own-submission-targets o)
                               (fn-own-sub-msgid sub)
                               (fn-own-feed-stamp o)))


; The configuration arm.  The owner reads the peer rows out of the live
; configuration value the host supplies -- the same value fn-own-open-peer
; takes -- and rebuilds the table: new outbound peers get a feed, existing
; ones keep their queue and get the fresh record, and a peer the
; configuration no longer feeds is dropped once its feed has drained.
(defun fn-own-feeds-reconfigure (o cfg)
  (declare (xargs :guard t))
  (fn-own-with-feeds
   o (fn-own-feed-reconfigure (fn-own-feeds o)
                              (fn-cfg-peers (fn-cfg-value cfg)))))

; The tick.  One fn-feed-tick-step per peer under that peer's own contact;
; the result is (effects . owner), each effect list tagged with its peer.
(defun fn-own-tick (o obs)
  (declare (xargs :guard t))
  (let ((r (fn-own-feed-tick (fn-own-feed-names (fn-own-feeds o))
                             (fn-own-feeds o) obs)))
    (cons (cdr r) (fn-own-with-feeds o (car r)))))

; The host drives one peer at a time: it holds one socket per peer and writes
; the records of one tick before that tick's bytes.
(defun fn-own-tick-peer (o peer obs)
  (declare (xargs :guard t))
  (let ((r (fn-own-feed-tick-peer peer (fn-own-feeds o) obs)))
    (cons (cdr r) (fn-own-with-feeds o (car r)))))

(defun fn-own-tick-peer-records (o peer obs)
  (declare (xargs :guard t))
  (fn-own-feed-tick-peer-records peer (fn-own-feeds o) obs))

(defun fn-own-tick-records (o obs)
  (declare (xargs :guard t))
  (fn-own-feed-tick-records (fn-own-feed-names (fn-own-feeds o))
                            (fn-own-feeds o) obs))

; The article one peer is owed, from the committed node.  The feed queue
; holds Message-IDs and no bytes (specs/peering.md sec. 3.1); this is where
; the bytes come from, at the moment the peer says it wants them.
(fn-payload-kind fn-own-feed-article :source "returns the article's handle (the host reads octets through fn-ofa-feed-article)")
(defun fn-own-feed-article (o msgid)
  (declare (xargs :guard t))
  (let ((a (fn-find-article
            (fn-record-octets-string msgid)
            (fn-state-articles
             (fn-node-acceptance (fn-sn-node (fn-own-store o)))))))
    (if (consp a) (fn-article-payload a) nil)))

; Resolve one intent only against a completely recovered authoritative node.
; The caller supplies no verdict: the binding identifies the exact archived
; object and its retention pin supplies the exact evidence stored with it.
; A different complete binding proves this incarnation did not commit; a
; partial binding/article/pin relation is recovery corruption and remains
; uncertain instead of losing the obligation.
(defun fn-own-retain-find-id-unguarded (id pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (if (equal id (fn-retain-obligation-id (car pins)))
          (car pins)
        (fn-own-retain-find-id-unguarded id (cdr pins)))
    nil))

(defun fn-own-feed-intent-reconcile-kind (node values)
  (declare (xargs :guard t))
  (let* ((msgid (fn-record-octets-string (fn-frame-item 1 values)))
         (identity (fn-record-octets-string (fn-frame-item 2 values)))
         (evidence (fn-record-octets-string (fn-frame-item 3 values)))
         (article (fn-find-article
                   msgid (fn-state-articles (fn-node-acceptance node))))
         (binding (fn-node-find-binding msgid (fn-node-bindings node)))
         (pin (and (consp binding)
                   (fn-own-retain-find-id-unguarded
                    (fn-node-binding-id binding)
                    (fn-retain-pins (fn-node-retention node))))))
    (cond ((and (consp article) (consp binding) (consp pin)
                (equal (fn-node-binding-id binding) identity)
                (equal (fn-retain-obligation-evidence pin) evidence))
           :feed-commit)
          ((and (null article) (null binding)) :feed-abort)
          ((and (consp article) (consp binding) (consp pin)) :feed-abort)
          (t :uncertain))))

(defun fn-own-feed-intent-reconcile-record (node values)
  (declare (xargs :guard t))
  (let ((kind (fn-own-feed-intent-reconcile-kind node values)))
    (if (member-equal kind '(:feed-commit :feed-abort))
        (fn-feed-journal-entry kind values)
      nil)))

; One reply line from one peer.  ACL2 reads the three-digit code
; (fn-own-feed-parse-response), maps it (fn-feed-observe) and renders what
; follows; the host frames bytes and takes no decision.  The result is
; (effects . owner); an unknown peer or an unreadable line changes nothing.
;; The article the feed port sends after a 335/238 is the row's BYTES: the
;; handle fn-own-feed-article returns, read through the arena (only read).
;; The host entry reads the same bytes (host/owner-host.lisp
;; fn-owner-feed-octets, books/owner-feed-article.lisp fn-ofa-feed-article).
(defun fn-own-feed-reply (o peer octets obs fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let* ((tbl (fn-own-feeds o))
         (e (fn-own-feed-entry-of peer tbl)))
    (if (null e)
        (cons nil o)
      (let* ((f (fn-own-feed-entry-feed e))
             (msgid (fn-own-feed-inflight-msgid (fn-feed-queue f)))
             (response (fn-own-feed-parse-response octets msgid)))
        (if (null response)
            (cons nil o)
          (mv-let (g effects)
            (fn-feed-observe f response
                             (fn-handle-bytes (fn-own-feed-article o msgid) fn-arena)
                             obs)
            (cons (if (null effects) nil (list (cons peer effects)))
                  (fn-own-with-feeds
                   o (fn-own-feed-put peer (fn-own-feed-entry-record e) g
                                      tbl)))))))))

(defun fn-own-feed-reply-records (o peer octets obs)
  (declare (xargs :guard t))
  (let* ((e (fn-own-feed-entry-of peer (fn-own-feeds o)))
         (f (fn-own-feed-entry-feed e))
         (msgid (fn-own-feed-inflight-msgid (fn-feed-queue f)))
         (response (fn-own-feed-parse-response octets msgid)))
    (if (and e response) (fn-feed-observe-records f response obs) nil)))

; The connection one peer's feed writes to.  The host opens the socket and
; reports its identifier here; nil stops selection at once
; (fn-feed-selection wants a natp conn).  It does NOT resolve the entry that
; was in flight: this comment used to say the next observation would, and
; there is no next observation once the socket is gone, so the entry sat at
; :sent until the process restarted (measured on gate a5c6792: node A
; reconnected every 5 s and offered nothing, seven times over).
; `fn-own-feed-lost' below is the transition for a lost connection and is
; what the host calls now.
;
; FORM is the connection's transfer form (PRF-207, RFC 4644 section 2.3):
; :ihave when this connection's MODE STREAM drew 500 or 501
; (books/feed-connection.lisp `fn-fc-mode-unsupportedp'), anything else when
; it streams or never asked.  The feed offers with CHECK and TAKETHIS on a
; connection only when the peer record asks for streaming AND the form is
; not :ihave; otherwise IHAVE (`fn-feed-offer', `fn-feed-send').  The bit is
; set on every connect, so a later streaming connection streams again; it is
; the only limit a connect touches, and a connect writes no FNFD record.
(defun fn-own-feed-streaming-of (record form)
  (declare (xargs :guard t))
  (and (not (equal form :ihave)) (fn-cfg-peer-streamingp record) t))

(defun fn-own-feed-with-streaming (f streamingp)
  (declare (xargs :guard t))
  (let ((l (fn-feed-limits-of f)))
    (fn-feed-make (fn-feed-peer f)
                  (fn-feed-limits (fn-feed-max-queue l) (fn-feed-backoff-base l)
                                  (fn-feed-retry-bound l) streamingp)
                  (fn-feed-queue f) (fn-feed-contact f) (fn-feed-backoff-until f)
                  (fn-feed-conn f) (fn-feed-next-attempt f))))

(defun fn-own-feed-connect (o peer conn form)
  (declare (xargs :guard t))
  (let ((e (fn-own-feed-entry-of peer (fn-own-feeds o))))
    (if (null e)
        o
      (fn-own-with-feeds
       o (fn-own-feed-put peer (fn-own-feed-entry-record e)
                          (fn-feed-with-conn
                           (fn-own-feed-with-streaming
                            (fn-own-feed-entry-feed e)
                            (fn-own-feed-streaming-of
                             (fn-own-feed-entry-record e) form))
                           conn)
                          (fn-own-feeds o))))))

; KEYSTONES (PRF-207): the form reaches the wire.  After a connect in the
; :ihave form, every offer the peer's feed emits is the IHAVE line
; (`fn-feed-offer', which `fn-feed-tick-step' runs under the host's
; `fn-owner-feed-tick' -> `fn-own-feed-port-tick-peer') and every transfer
; is the bare article after 335 (`fn-feed-send', under the host's
; `fn-owner-feed-octets'), never CHECK or TAKETHIS; after a connect in the
; streaming form, to a peer whose record streams, the offer is CHECK.  The
; subject is `fn-own-feed-connect', the :feed-conn arm of `fn-own-step',
; which the host's `fn-owner-feed-connect' runs with the form ACL2 computed
; (`fn-fc-connection-form', books/feed-connection.lisp).
(defthm fn-own-feed-connect-in-ihave-form-offers-ihave
  (let* ((f (fn-own-feed-entry-feed
             (fn-own-feed-entry-of peer (fn-own-feeds (fn-own-feed-connect o peer conn :ihave)))))
         (effects (mv-nth 1 (fn-feed-offer f msgid))))
    (implies effects
             (equal effects
                    (list (list :command conn (fn-feed-ihave-line msgid))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-feed-connect fn-feed-offer fn-feed-offer-line
                                   fn-own-feed-with-streaming fn-feed-with-conn
                                   fn-own-feed-streaming-of fn-own-with-feeds)
                                  (fn-feedp fn-feed-ihave-line fn-feed-check-line)))))

(defthm fn-own-feed-connect-in-ihave-form-sends-the-bare-article
  (let* ((f (fn-own-feed-entry-feed
             (fn-own-feed-entry-of peer (fn-own-feeds (fn-own-feed-connect o peer conn :ihave)))))
         (effects (mv-nth 1 (fn-feed-send f msgid article))))
    (implies effects
             (equal effects (list (list :command conn article)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-feed-connect fn-feed-send
                                   fn-own-feed-with-streaming fn-feed-with-conn
                                   fn-own-feed-streaming-of fn-own-with-feeds)
                                  (fn-feedp fn-feed-takethis-line)))))

(defthm fn-own-feed-connect-in-stream-form-offers-check
  (let* ((e (fn-own-feed-entry-of peer (fn-own-feeds o)))
         (f (fn-own-feed-entry-feed
             (fn-own-feed-entry-of peer (fn-own-feeds (fn-own-feed-connect o peer conn nil)))))
         (effects (mv-nth 1 (fn-feed-offer f msgid))))
    (implies (and effects (fn-cfg-peer-streamingp (fn-own-feed-entry-record e)))
             (equal effects
                    (list (list :command conn (fn-feed-check-line msgid))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-feed-connect fn-feed-offer fn-feed-offer-line
                                   fn-own-feed-with-streaming fn-feed-with-conn
                                   fn-own-feed-streaming-of fn-own-with-feeds)
                                  (fn-feedp fn-feed-ihave-line fn-feed-check-line)))))

; The connection to one peer is gone.  The host reports the EVENT -- the
; socket closed, the read returned nothing, a write failed -- and the model
; decides what it means: `fn-feed-lost' returns that peer's in-flight entry
; to :queued with one more attempt and a backoff and forgets the connection,
; so the next command for it is an offer (K5's restart-by-offer, and the
; reason the entry no longer waits for `fn-own-reopen').  PER PEER: settling
; another peer's genuinely in-flight entry would be the second transfer K5
; forbids, which is why this is not `fn-own-feed-restart-all'.
(defun fn-own-feed-lost (o peer obs)
  (declare (xargs :guard t))
  (fn-own-with-feeds o (fn-own-feed-lost-one peer (fn-own-feeds o) obs)))

; The FNFD record that authorizes it, read off the state BEFORE it moves:
; `(:feed-outcome peer msgid attempt 400)' for the entry in flight, and
; nothing at all when none is.
(defun fn-own-feed-lost-records (o peer obs)
  (declare (xargs :guard t))
  (fn-own-feed-lost-records-of peer (fn-own-feeds o) obs))

; Replay: the peer's FNFD journal, folded through the feed machine, before
; any command may be emitted.  The host reads the file and decodes each frame
; with fn-feed-decode; this is the fold and nothing else.
(defun fn-own-feed-recover (o peer entries)
  (declare (xargs :guard t))
  (let ((e (fn-own-feed-entry-of peer (fn-own-feeds o))))
    (if (null e)
        o
      (fn-own-with-feeds
       o (fn-own-feed-put peer (fn-own-feed-entry-record e)
                          (fn-feed-replay (fn-own-feed-entry-feed e) entries)
                          (fn-own-feeds o))))))

; -----------------------------------------------------------------------------
; The served POST path: configuration, the writer step and the outcome.

; The posting configuration new connections pin.  Open connections keep the
; configuration they were opened with.
(defun fn-own-configure (o config)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) config (fn-own-queue o)
               (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))

; The node secret the host read (STORE/keys/node-secret.key) and installs
; after every open and recovery (host/owner-host.lisp
; fn-owner-install-node-secret).  Nothing else writes the field: every other
; owner step copies it.
(defun fn-own-with-node-secret (o secret)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
               (fn-own-inflight o) (fn-own-feeds o) secret (fn-own-refused o)))

; The writer step takes the oldest queued submission into the durable path:
; only when nothing is in flight, no transaction is pending and the store is
; :ready, so at most one submission is in the durable path at a time and it
; owns the transaction (pending) exactly as a control-channel post would.
; The mark is the ledger length now; fn-own-outcome reads it.
(defun fn-own-take-submission (o)
  (declare (xargs :guard t))
  (if (and (null (fn-own-inflight o))
           (consp (fn-own-queue o))
           (null (fn-own-pending o))
           (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready))
      (let ((sub (fn-psub-unpack-sub (car (fn-own-queue o)))))
        (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                     (fn-own-next-id o) (fn-own-max-conns o) (fn-own-sub-id sub)
                     (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                     (fn-own-config o) (cdr (fn-own-queue o))
                     (fn-own-sub-make-author (fn-own-sub-id sub) (fn-own-sub-version sub)
                                             (mbe :logic (len (fn-own-ledger o))
                                                  :exec (fn-own-ledger-count o))
                                             (fn-own-sub-decision sub)
                                             (fn-own-sub-login sub)
                                             (fn-own-sub-account sub))
                     (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))
    o))

; The Store refusal words the host may relay.  Each is the kind an ACL2
; step decided: :duplicate and :conflict are fn-store-existing-action's
; (books/store-intern.lisp, the decision the host calls since D25),
; :malformed is fn-owner-prepare's :invalid, :unaffordable is the persisted
; profile's or the capacity's refusal, :storage-failed is a write that failed
; before publication whose reservation fn-owner-known-abort consumed, and
; :refused is a refusal no kind names.  The wire line for each is
; fn-post-store-refusal-line (books/nntp-post.lisp).
(defun fn-own-refusal-wordp (word)
  (declare (xargs :guard t))
  (fn-post-store-refusalp word))

; A completion was consumed into the ledger after the take: fn-own-complete
; is the only ledger writer, and it consumes the actual fn-sn-finish
; (fn-own-completion-consumed-once).
(defun fn-own-completion-consumedp (o)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (and sub
         (natp (fn-own-sub-mark sub))
         (< (fn-own-sub-mark sub)
            (mbe :logic (len (fn-own-ledger o))
                 :exec (fn-own-ledger-count o))))))

; The completion the owner reports for the submission in flight, from the
; word the host observed.  :durable needs a completion consumed into the
; ledger after the take; a host word of :durable without one is :uncertain,
; never 240.  A refusal word is :refused only while NO completion has been
; consumed after the take: once the record is durable and its completion
; consumed, no host word can make it a refusal, and anything but :durable is
; :uncertain (campaign W2, 2026-09-24: an OS error raised after publication
; was reported as `441 ... refused' for a durable article).  :clock-unusable
; remains a distinct owner-clock refusal, and all other words are :uncertain.
; The durable words: :durable, and :durable-key-change-refused, the served
; POST's word for a durable kind-4 composite whose kind-3 key change the
; Store refused (books/peer-authored-accept.lisp fn-pa-served-post-word;
; PKT-473, PRF-184).  Both are one outcome, durable; only the POST reply's
; text tells them apart (fn-own-post-rendering).
(defun fn-own-durable-wordp (word)
  (declare (xargs :guard t))
  (or (equal word :durable)
      (equal word :durable-key-change-refused)))

(defun fn-own-outcome-completion (o word)
  (declare (xargs :guard t))
  (cond ((and (fn-own-durable-wordp word)
              (fn-own-completion-consumedp o))
         :durable)
        ((fn-own-completion-consumedp o) :uncertain)
        ((equal word :clock-unusable) :clock-unusable)
        ((fn-own-refusal-wordp word) :refused)
        (t :uncertain)))

; What the served reply is rendered from: the completion, except that a
; refusal carries the kind the host relayed from the ACL2 step that refused
; (fn-post-store-refusal-line gives each its own 441 line).  Only the text of
; a refusal depends on the word; which of the outcomes it is does not.
(defun fn-own-outcome-rendering (o word)
  (declare (xargs :guard t))
  (let ((completion (fn-own-outcome-completion o word)))
    (if (equal completion :refused)
        word
      completion)))

; The served POST reply's rendering: fn-own-outcome-rendering, except that a
; durable completion reached by :durable-key-change-refused keeps that word,
; so fn-nntp-post-outcome's 240 names the refused key change.  Which outcome
; it is stays the completion's; transit renders fn-own-outcome-rendering.
(defun fn-own-post-rendering (o word)
  (declare (xargs :guard t))
  (let ((rendering (fn-own-outcome-rendering o word)))
    (if (and (equal rendering :durable)
             (equal word :durable-key-change-refused))
        word
      rendering)))

; Resolution repeats the complete intent identity.  Durable is projected from
; the consumed owner completion, never from the host word alone.  A known
; refusal (including the store's duplicate outcome) aborts this incarnation;
; an uncertain outcome writes neither record and recovery retains the intent.
(defun fn-own-submission-resolution-records (o word evidence generation txid)
  (declare (xargs :guard t))
  (let* ((sub (fn-own-inflight o))
         (completion (fn-own-outcome-completion o word))
         (kind (cond ((equal completion :durable) :feed-commit)
                     ((member-equal completion '(:refused :clock-unusable))
                      :feed-abort)
                     (t nil))))
    (if (or (null sub) (null kind))
        nil
      (fn-own-feed-resolution-records
       kind (fn-own-submission-targets o) (fn-own-sub-msgid sub)
       (fn-own-feed-intent-id (fn-own-sub-msgid sub) (fn-own-sub-octets sub))
       evidence generation txid (fn-own-feed-stamp o)))))


; The outcome reaches exactly the connection whose submission is in flight:
; the reply is fn-served-post-outcome over that connection's served state
; (fn-nntp-post-outcome's line, the only place 240 exists), the reply leaves
; the served state as it was (fn-served-post-outcome returns it), and no
; other connection is touched at all.  The result is (effects . owner);
; with nothing in flight for `id`, or an unknown connection, it is (nil . o).
;
; Read-back.  A 240 is a promise the poster can act on, so the poster's own
; pin moves: when the rendered completion is :durable the poster's
; connection is re-pinned to the committed view by one fn-own-advance, which
; is the same event the host's (:advance id) runs, on that connection alone.
; Its next GROUP or ARTICLE therefore reads the prefix that contains its own
; article (fn-own-read-is-served-step-on-pinned-prefix over the new pin;
; fn-own-durable-outcome-repins-the-poster, owner-invariants.lisp).  Every
; other connection keeps the pin it had: a reader open before the post still
; sees its own version, which is what K3 and the concurrency case in
; tests/test_post.py require.  A :refused or :uncertain outcome moves no
; pin.  The reply itself is rendered over the connection as it was when the
; submission was taken, so the rendered octets do not depend on the advance.
(defun fn-own-outcome (o id word)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id))
        (let* ((completion (fn-own-outcome-completion o word))
               (next (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal completion :durable)
                                     (fn-own-feed-durable o sub)
                                   (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))
          (cons (fn-served-result-effects
                 (fn-served-post-outcome
                  (fn-served-make-conn-group-indexed (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o)
                                       (fn-own-conn-verdicts conn)
                                       (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn) (fn-own-conn-control conn))
                  (fn-own-post-rendering o word)))
                (if (equal completion :durable)
                    (fn-own-advance next id)
                  next)))
      (cons nil o))))

; Control submissions use the same completion gate and the same feed update
; as served POST, but have no socket session to render or re-pin.  The result
; projection is closed and keeps a duplicate distinct for the CLI contract;
; a duplicate is a refusal to create a new acceptance, while remaining an
; idempotent success for the posting client.
(defun fn-own-control-outcome-result (o word)
  (declare (xargs :guard t))
  (if (not (fn-own-control-submissionp (fn-own-inflight o)))
      :absent
    (if (and (equal word :duplicate)
             (equal (fn-own-outcome-completion o word) :refused))
        :duplicate
      (case (fn-own-outcome-completion o word)
        (:durable :accepted)
        (:clock-unusable :clock-unusable)
        (:refused :refused)
        (otherwise :uncertain)))))

(defun fn-own-control-outcome (o word)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (if (not (fn-own-control-submissionp sub))
        o
      (let ((completion (fn-own-outcome-completion o word)))
        (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                     (fn-own-next-id o) (fn-own-max-conns o)
                     (if (equal (fn-own-pending o) *fn-own-control-id*)
                         nil (fn-own-pending o))
                     (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                     (fn-own-config o) (fn-own-queue o) nil
                     (if (equal completion :durable)
                         (fn-own-feed-durable o sub)
                       (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))))

(defun fn-own-control-outcome-records (o word)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (if (and (fn-own-control-submissionp sub)
             (equal (fn-own-outcome-completion o word) :durable))
        (fn-own-feed-durable-records o sub)
      nil)))

(defun fn-own-bp-transit-outcome-result (o word)
  (declare (xargs :guard t))
  (if (fn-own-bp-transit-submissionp (fn-own-inflight o))
      (fn-own-control-outcome-result o word)
    :absent))

(defun fn-own-bp-transit-outcome (o word)
  (declare (xargs :guard t))
  (if (fn-own-bp-transit-submissionp (fn-own-inflight o))
      (fn-own-control-outcome o word)
    o))

(defun fn-own-bp-transit-outcome-records (o word)
  (declare (xargs :guard t))
  (if (fn-own-bp-transit-submissionp (fn-own-inflight o))
      (fn-own-control-outcome-records o word)
    nil))

; A transit submission is the one the served path carried from a peer
; connection (books/peer-inbound, `(:transit peer kind msgid octets)`); an
; injected one is books/injection's.  The writer step does not look at which:
; fn-own-take-submission installs whichever is at the head of the one queue
; (fn-own-take-installs-the-queued-submission-whatever-it-carries,
; owner-invariants.lisp), so transit and POST share one durable path and one
; pending slot.
(defun fn-own-transit-subp (sub)
  (declare (xargs :guard t))
  (and (consp sub) (fn-peer-submissionp (fn-own-sub-decision sub))))

(defun fn-own-transit-inflightp (o)
  (declare (xargs :guard t))
  (fn-own-transit-subp (fn-own-inflight o)))

; The transit reply, after the durable attempt.  `kind' and `reason' are
; ACL2's own transfer decision, relayed back by the host exactly as the
; store's word is for POST (fn-owner-transit-decide, host/owner-host.lisp);
; the host names no code and no reason text.  A decision that is not `:want'
; means no attempt ran, so the completion the reply is rendered with is nil
; and fn-peer-transit-code takes the refusal or the deferral from the
; decision.  Three outcomes stay distinct: :durable is the only 2xx,
; :uncertain is 436 and a close, a refusal is 437/439.
; PRF-235: what a transit outcome leaves in the refused-offer memory.  Only
; a refusal whose reason the octets decide is considered, and the reason
; remembered is not the host's word: it is fn-peer-intrinsic-refusal of the
; in-flight octets, recomputed here (fn-peer-refused-record), under the
; capacity of the configuration the connection's session carries.  So a
; transfer that was accepted, deferred or refused for a reason of the peer,
; the node or the clock costs nothing and changes nothing.
(defun fn-own-transit-refused (o conn sub kind reason)
  (declare (xargs :guard t))
  (if (and (equal kind :refuse)
           (member-equal reason *fn-peer-intrinsic-reasons*))
      (let ((submission (fn-own-sub-decision sub)))
        (fn-peer-refused-record
         (fn-own-refused o)
         (fn-peer-session-cfg (fn-auth-session-base (fn-own-conn-session conn)))
         (fn-peer-submission-msgid submission)
         (fn-peer-submission-octets submission)))
    (fn-own-refused o)))

; Closed: no owner invariant reads the memory, so a proof about an outcome
; carries this term through unopened.
(in-theory (disable fn-own-transit-refused))

(defun fn-own-transit-outcome (o id kind reason word)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id) (fn-own-transit-subp sub))
        (let* ((d (fn-peer-decision kind reason))
               (completion (if (equal kind :want)
                               (fn-own-outcome-completion o word)
                             nil))
               (next (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                  (fn-own-next-id o) (fn-own-max-conns o)
                                  (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                  (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                  (fn-own-config o) (fn-own-queue o) nil
                                  (if (equal completion :durable)
                                      (fn-own-feed-durable o sub)
                                    (fn-own-feeds o)) (fn-own-node-secret o)
                                  (fn-own-transit-refused o conn sub kind reason))))
          (cons (fn-served-result-effects
                 (fn-served-transit-outcome
                  ; Six fields since the clock seam: the connection's
                  ; pinned reader observation and the owner's current
                  ; reading, as fn-own-outcome passes them.  This caller
                  ; still passed five, so books/owner did not admit.
                  (fn-served-make-conn-group-indexed (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o)
                                       (fn-own-conn-verdicts conn)
                                       (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn) (fn-own-conn-control conn))
                  (fn-own-sub-decision sub) d
                  ; A refusal is rendered with the word the host relayed,
                  ; as fn-own-outcome renders POST's: the 437 names the
                  ; reason (fn-peer-transit-refusal-line).  Which outcome
                  ; it is stays COMPLETION's.
                  (if (equal kind :want) (fn-own-outcome-rendering o word) nil)))
                (if (equal completion :durable)
                    (fn-own-advance next id)
                  next)))
      (cons nil o))))

; THE RECORDS THE OUTCOME OWES THE JOURNAL, read off the owner BEFORE the
; outcome moves it.  specs/peering.md sec. 3.3: `(:feed-enqueue peer msgid
; tick)' is written BEFORE the entry is :queued.  Nothing wrote it.
; `fn-own-outcome' and `fn-own-transit-outcome' both fold
; `fn-own-feed-durable' into the new owner and the host installed only the
; served effects, so a queued entry existed in memory and NOWHERE ELSE
; until its first offer -- and an article accepted while a peer was
; unreachable did not survive the process (measured: gate 15ac399, node A
; posts <fed-restart@example.invalid> with node B down, is killed with -9,
; restarts, replays EIGHT records, and never offers it; node B answers 430
; to 179 polls over 90 s).  The condition is the same one the transition
; itself uses, stated once here so the host does not restate it.
(defun fn-own-outcome-records (o id word)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id)
             (equal (fn-own-outcome-completion o word) :durable))
        (fn-own-feed-durable-records o sub)
      nil)))

; A shared submission intent/commit already is the durable journal event that
; authorizes this exact local enqueue.  Its following owner outcome must not
; emit the older standalone enqueue record a second time.  RESOLUTION-ID is
; the in-flight connection recorded by the host wrapper when it projected the
; resolution; direct callers pass nil and retain the legacy record path.
(defun fn-own-outcome-journal-records (o id word resolution-id)
  (declare (xargs :guard t))
  (if (equal id resolution-id)
      nil
    (fn-own-outcome-records o id word)))

(defun fn-own-transit-outcome-records (o id kind word)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id) (fn-own-transit-subp sub)
             (equal kind :want)
             (equal (fn-own-outcome-completion o word) :durable))
        (fn-own-feed-durable-records o sub)
      nil)))

; -----------------------------------------------------------------------------
; The owner event machine.  (:octets id octets) is the served port; (:read id
; event) is its per-event law; (:take) is the writer step; (:outcome id word)
; feeds the durable outcome of the submission in flight back through the
; book, which renders the reply (fn-own-outcome).

(defun fn-own-step (o event fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep (fn-own-store o)) :verify-guards nil))
  (case (car event)
    (:open (cdr (fn-own-open o (cadr event))))
    (:open-peer (cdr (fn-own-open-peer o (cadr event) (caddr event)
                                       (cadddr event))))
    (:octets (cdr (fn-own-read o (cadr event) (caddr event) fn-arena)))
    (:read (cdr (fn-own-read-step o (cadr event) (caddr event) fn-arena)))
    (:advance (fn-own-advance o (cadr event)))
    (:close (fn-own-close o (cadr event)))
    (:begin (fn-own-begin o (cadr event)))
    (:store (fn-own-store-step o (cadr event)))
    (:complete (fn-own-complete o))
    (:reopen (fn-own-reopen o (cadr event) (caddr event)))
    (:observe (fn-own-observe o (cadr event)))
    (:declare-group (fn-own-declare-group o (cadr event)))
    (:configure (fn-own-configure o (cadr event)))
    (:take (fn-own-take-submission o))
    (:control-submit (fn-own-control-submit o (cadr event) (caddr event)
                                            (cadddr event)))
    (:bp-transit-submit
     (fn-own-bp-transit-submit o (cadr event) (caddr event)
                               (cadddr event) (car (cddddr event))
                               (cadr (cddddr event))
                               (caddr (cddddr event))))
    (:operator-submit (fn-own-operator-submit o (cadr event) (caddr event)
                                              (cadddr event) (car (cddddr event))))
    (:outcome (cdr (fn-own-outcome o (cadr event) (caddr event))))
    (:control-outcome (fn-own-control-outcome o (cadr event)))
    (:bp-transit-outcome (fn-own-bp-transit-outcome o (cadr event)))
    (:transit-outcome (cdr (fn-own-transit-outcome o (cadr event) (caddr event)
                                                   (cadddr event)
                                                   (car (cddddr event)))))
    (:feeds (fn-own-feeds-reconfigure o (cadr event)))
    (:feed-conn (fn-own-feed-connect o (cadr event) (caddr event) (cadddr event)))
    (:feed-lost (fn-own-feed-lost o (cadr event) (caddr event)))
    (:feed-replay (fn-own-feed-recover o (cadr event) (caddr event)))
    (:tick (cdr (fn-own-tick o (cadr event))))
    (:tick-peer (cdr (fn-own-tick-peer o (cadr event) (caddr event))))
    (:feed-octets (cdr (fn-own-feed-reply o (cadr event) (caddr event)
                                          (cadddr event) fn-arena)))
    (otherwise o)))

(defun fn-own-run (o events fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep (fn-own-store o)) :verify-guards nil))
  (if (consp events)
      (fn-own-run (fn-own-step o (car events) fn-arena) (cdr events) fn-arena)
    o))

; The compaction floor: nothing below the lowest pinned version may be
; reclaimed.  Compaction does not exist yet; the floor is stated so that the
; invariant it must respect exists before the code that must respect it.
(defun fn-own-min-pinned (conns floor)
  (declare (xargs :guard t))
  (if (consp conns)
      (fn-own-min-pinned (cdr conns)
                         (if (and (natp (fn-own-conn-version (car conns)))
                                  (< (fn-own-conn-version (car conns)) (nfix floor)))
                             (fn-own-conn-version (car conns))
                           (nfix floor)))
    (nfix floor)))

(defun fn-own-reclaim-floor (o)
  (declare (xargs :guard t))
  (fn-own-min-pinned (fn-own-conns o) (fn-own-view-version (fn-own-view o))))

; -----------------------------------------------------------------------------
; Export theory.  What leaves enabled: the record lemmas and forward shape
; facts above, and the list-recursive vocabulary proofs induct on
; (fn-own-take, fn-own-{find,replace,remove}-conn, fn-own-facts-okp,
; fn-own-replay-facts, fn-own-remove-subs, fn-own-min-pinned).  Withdrawn: the recognizer of a
; fact, the glue predicates, the view projection, the transitions and the
; machine; owner-invariants opens them locally.

(deftheory fn-own-vocabulary
  '(fn-own-group-factp fn-own-prefix-archive fn-own-store-idlep fn-own-refresh
    fn-own-start fn-own-conn-boundedp fn-own-set-conns fn-own-reader-context fn-own-body-limit
    fn-own-peer-body-limit
    fn-own-open fn-own-enqueue
    fn-own-conn-live-session
    fn-own-read fn-own-read-step fn-own-advance fn-own-close fn-own-begin
    fn-own-control-decision fn-own-control-submit-result fn-own-control-submit
    fn-own-control-submissionp fn-own-control-outcome-result
    fn-own-stored-handle fn-own-clock-usablep fn-own-operator-decision
    fn-own-operator-decision-of fn-own-operator-submit-result
    fn-own-operator-submit
    fn-own-control-outcome fn-own-control-outcome-records
    fn-own-store-step fn-own-complete fn-own-reopen
    fn-own-observe-outcome fn-own-observe
    fn-own-declare-group fn-own-configure fn-own-take-submission fn-own-outcome-completion
    fn-own-outcome fn-own-step fn-own-run fn-own-reclaim-floor
    fn-own-open-peer fn-own-transit-subp fn-own-transit-inflightp
    fn-own-transit-outcome
    fn-own-with-feeds fn-own-sub-origin fn-own-sub-msgid fn-own-sub-octets
    fn-own-sub-feed-base-groups
    fn-own-sub-feed-groups fn-own-submission-targets
    fn-own-submission-intent-result fn-own-submission-intent-records
    fn-own-submission-resolution-records
    fn-own-feed-stamp fn-own-feed-durable fn-own-feed-durable-records
    fn-own-outcome-records fn-own-outcome-journal-records
    fn-own-transit-outcome-records
    fn-own-feeds-reconfigure fn-own-tick fn-own-tick-records
    fn-own-tick-peer fn-own-tick-peer-records
    fn-own-feed-article fn-own-retain-find-id-unguarded
    fn-own-feed-intent-reconcile-kind
    fn-own-feed-intent-reconcile-record
    fn-own-feed-reply fn-own-feed-reply-records
    fn-own-feed-connect fn-own-feed-lost fn-own-feed-lost-records
    fn-own-feed-recover))

(in-theory (disable fn-own-vocabulary))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:rewrite fn-gidx-refresh-is-build)))
