; fn: the mutable service owner over the live fn-sn composition (C1-05).
;
; One owner process serializes mutations of one store while readers observe a
; committed version.  This book is the executable model the host drives
; through host/owner-host.lisp (tools/run_owner.py).  It performs no I/O.
;
; The owner record is
;   (store view conns next-id max-conns pending ledger clock facts
;    config queue inflight feeds)
; where
;   store     the actual fn-sn composition (books/store-node.lisp), stepped
;             only through fn-snrt-step and fn-sn-finish;
;   view      the committed view (version frontier archive): version is the
;             generation, the length of the durable record history; archive
;             is the acceptance projection of the node at that generation;
;   conns     the open connections, each
;             (id version frontier wire session archive config observation):
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
;             taken, each (id version mark decision), in arrival order;
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
; PINNED archive, never over the live node.  fn-own-read-step is the
; per-event law underneath it (one fn-served-dispatch, the byte fold's step,
; against the pinned archive).
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
(include-book "served")
(include-book "clock")
(include-book "owner-feed")

; store's idle-phase predicate has no explicit guard; it is guard t and its
; body is one member-equal over a constant, so verify it here so that
; fn-own-refresh can be.  Redundant once store carries the event itself.
(verify-guards fn-snt-idle-phasep)

; -----------------------------------------------------------------------------
; The connection record:
;   (id version frontier wire session archive config observation)

(defun fn-own-conn-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 8)))
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
(defun fn-own-conn-make (id version frontier wire session archive config observation)
  (declare (xargs :guard t))
  (list id version frontier wire session archive config observation))

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
                    (:d fn-own-conn-make)))

; -----------------------------------------------------------------------------
; The submission record: (id version mark decision).  A served read of
; connection `id`, pinned at `version`, injected `decision` (an
; fn-inj-injectedp decision record: the article's octets, Message-ID and
; groups, books/injection.lisp).  `mark` is nil in the queue and the length
; of the ledger at the moment fn-own-take-submission moved it into the durable path.

(defun fn-own-sub-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))
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
(in-theory (disable (:d fn-own-sub-shapep) (:d fn-own-sub-id) (:d fn-own-sub-version)
                    (:d fn-own-sub-mark) (:d fn-own-sub-decision) (:d fn-own-sub-make)))

; -----------------------------------------------------------------------------
; The committed view record: (version frontier archive)

(defun fn-own-view-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)))
(defun fn-own-view-version (v)
  (declare (xargs :guard t))
  (mbe :logic (car v) :exec (fn-ag-car v)))
(defun fn-own-view-frontier (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr v)) :exec (fn-ag-car (fn-ag-cdr v))))
(defun fn-own-view-archive (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr v))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr v)))))
(defun fn-own-view-make (version frontier archive)
  (declare (xargs :guard t))
  (list version frontier archive))

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
                    (:d fn-own-view-make)))

; -----------------------------------------------------------------------------
; The owner record

(defun fn-own-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 13)))
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
(defun fn-own-ledger (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr o)))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o)))))))))
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
(defun fn-own-make (store view conns next-id max-conns pending ledger clock facts
                          config queue inflight feeds)
  (declare (xargs :guard t))
  (list store view conns next-id max-conns pending ledger clock facts
        config queue inflight feeds))

(defthm fn-own-shapep-of-fn-own-make
  (fn-own-shapep (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds)))
(defthm fn-own-store-of-fn-own-make
  (equal (fn-own-store (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         store))
(defthm fn-own-view-of-fn-own-make
  (equal (fn-own-view (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         view))
(defthm fn-own-conns-of-fn-own-make
  (equal (fn-own-conns (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         conns))
(defthm fn-own-next-id-of-fn-own-make
  (equal (fn-own-next-id (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         next-id))
(defthm fn-own-max-conns-of-fn-own-make
  (equal (fn-own-max-conns (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         max-conns))
(defthm fn-own-pending-of-fn-own-make
  (equal (fn-own-pending (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         pending))
(defthm fn-own-ledger-of-fn-own-make
  (equal (fn-own-ledger (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         ledger))
(defthm fn-own-clock-of-fn-own-make
  (equal (fn-own-clock (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         clock))
(defthm fn-own-facts-of-fn-own-make
  (equal (fn-own-facts (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         facts))
(defthm fn-own-config-of-fn-own-make
  (equal (fn-own-config (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         config))
(defthm fn-own-queue-of-fn-own-make
  (equal (fn-own-queue (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         queue))
(defthm fn-own-inflight-of-fn-own-make
  (equal (fn-own-inflight (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         inflight))
(defthm fn-own-feeds-of-fn-own-make
  (equal (fn-own-feeds (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds))
         feeds))
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
       (implies (fn-own-feeds x) (consp x)))
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
                                    :trigger-terms ((fn-own-feeds x)))))
(in-theory (disable (:d fn-own-shapep) (:d fn-own-store) (:d fn-own-view) (:d fn-own-conns)
                    (:d fn-own-next-id) (:d fn-own-max-conns) (:d fn-own-pending)
                    (:d fn-own-ledger) (:d fn-own-clock) (:d fn-own-facts)
                    (:d fn-own-config) (:d fn-own-queue) (:d fn-own-inflight)
                    (:d fn-own-feeds) (:d fn-own-make)))

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

(defun fn-own-take (n xs)
  (declare (xargs :guard t))
  (if (and (posp n) (consp xs))
      (cons (car xs) (fn-own-take (1- n) (cdr xs)))
    nil))

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

(defun fn-own-refresh (o)
  (declare (xargs :guard t))
  (let ((s (fn-own-store o)))
    (if (fn-own-store-idlep s)
        (fn-own-make s
                     (fn-own-view-make (len (fn-sf-records (fn-sn-files s)))
                                       (fn-sf-frontier (fn-sn-files s))
                                       (fn-node-acceptance (fn-sn-node s)))
                     (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                     (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
                     (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
                     (fn-own-inflight o) (fn-own-feeds o))
      o)))

; The owner of a store.  The host calls this once per process over the state
; fn-sn-open-observed returned (host/owner-host.lisp, fn-owner-recover).
(defun fn-own-start (store max-conns)
  (declare (xargs :guard t))
  (fn-own-refresh
   (fn-own-make store
                (fn-own-view-make 0 0 (fn-own-prefix-archive
                                       (fn-sn-groups store) (fn-sn-capacity store)
                                       (fn-sf-records (fn-sn-files store)) 0 0))
                nil 0 max-conns nil nil nil nil nil nil nil nil)))

; -----------------------------------------------------------------------------
; Connections

(defun fn-own-replace-conn (conn conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (if (equal (fn-own-conn-id (car conns)) (fn-own-conn-id conn))
          (cons conn (cdr conns))
        (cons (car conns) (fn-own-replace-conn conn (cdr conns))))
    nil))

(defun fn-own-remove-conn (id conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (if (equal (fn-own-conn-id (car conns)) id)
          (fn-own-remove-conn id (cdr conns))
        (cons (car conns) (fn-own-remove-conn id (cdr conns))))
    nil))

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
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)))

; The wire limits of one connection.  RFC 3977 section 3.1's 512 octets
; include the CRLF (books/nntp-syntax.lisp); the body limit is the reader's.
(defconst *fn-own-body-limit* 8192)

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
             (opened (fn-served-open archive *fn-nntp-max-initial-line-octets*
                                     *fn-own-body-limit* (fn-own-config o)
                                     (fn-own-clock o) (fn-own-clock o) acfg))
             (sconn (fn-served-result-conn opened))
             (conn (fn-own-conn-make id (fn-own-view-version view)
                                     (fn-own-view-frontier view)
                                     (fn-served-conn-wire sconn)
                                     (fn-served-conn-session sconn)
                                     archive (fn-own-config o) (fn-own-clock o))))
        (cons (fn-served-result-effects opened)
              (fn-own-make (fn-own-store o) view (cons conn (fn-own-conns o))
                           (1+ (nfix id)) (fn-own-max-conns o) (fn-own-pending o)
                           (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))))
    (cons nil o)))

; The transit port.  A peer connection is accepted on the SAME listener as a
; reader (specs/peering.md 1.1): the host resolves the source to a configured
; peer record at accept and passes its name here, and the role of the
; connection is decided by that record and by nothing the client says.  The
; session pins the node and the configuration once (fn-served-open-peer ->
; fn-peer-open-session), so the offer decision reads a snapshot and the
; transfer decides again over the live node, which is what RFC 4644 2.4.2
; makes advisory.  The body limit is the peer record's inbound-max-octets:
; an oversize article is cut by the wire machine and never by a second
; parser (specs/peering.md 1.3).  An unconfigured name opens a connection
; whose every offer is refused `:not-a-peer', which is the same refusal the
; decision function gives, not a second policy here.
(defun fn-own-open-peer (o peer cfg acfg)
  (declare (xargs :guard t))
  (if (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))
      (let* ((view (fn-own-view o))
             (archive (fn-own-view-archive view))
             (id (fn-own-next-id o))
             (record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
             (limit (if (and record (fn-cfg-peer-inbound record)
                             (posp (fn-cfg-peer-inbound-max-octets record)))
                        (fn-cfg-peer-inbound-max-octets record)
                      *fn-own-body-limit*))
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
             (opened (fn-served-open-peer archive
                                          *fn-nntp-max-initial-line-octets*
                                          limit (fn-own-config o) (fn-own-clock o)
                                          (fn-own-clock o)
                                          peer (fn-sn-node (fn-own-store o)) cfg
                                          acfg))
             (sconn (fn-served-result-conn opened))
             (conn (fn-own-conn-make id (fn-own-view-version view)
                                     (fn-own-view-frontier view)
                                     (fn-served-conn-wire sconn)
                                     (fn-served-conn-session sconn)
                                     archive (fn-own-config o) (fn-own-clock o))))
        (cons (fn-served-result-effects opened)
              (fn-own-make (fn-own-store o) view (cons conn (fn-own-conns o))
                           (1+ (nfix id)) (fn-own-max-conns o) (fn-own-pending o)
                           (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                           (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))))
    (cons nil o)))

; The served port: one socket read of one connection is one fn-served-step
; over the connection's wire, session and pinned archive.  The result is
; (effects . owner); the host writes `effects` through fn-served-reply-octets
; and fn-served-closingp (host/owner-host.lisp, fn-owner-chunk) and takes no
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
(defun fn-own-enqueue (o sub)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-ag-append (fn-own-queue o) (list sub)) (fn-own-inflight o) (fn-own-feeds o)))

(defun fn-own-read (o id octets)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((result (fn-served-step (fn-served-make-conn (fn-own-conn-wire conn)
                                                            (fn-own-conn-session conn)
                                                            (fn-own-conn-archive conn)
                                                            (fn-own-conn-config conn)
                                                            (fn-own-conn-observation conn)
                                                            (fn-own-clock o))
                                       octets))
               (effects (fn-served-result-effects result))
               (sconn (fn-served-result-conn result))
               (next (fn-own-conn-make (fn-own-conn-id conn)
                                       (fn-own-conn-version conn)
                                       (fn-own-conn-frontier conn)
                                       (fn-served-conn-wire sconn)
                                       (fn-served-conn-session sconn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)))
               (decision (fn-served-submission effects)))
          (cons effects
                (if (fn-own-conn-boundedp next (fn-sn-groups (fn-own-store o)))
                    (let ((o2 (fn-own-set-conns o (fn-own-replace-conn next (fn-own-conns o)))))
                      (if decision
                          (fn-own-enqueue o2 (fn-own-sub-make id (fn-own-conn-version conn)
                                                              nil decision))
                        o2))
                  (fn-own-set-conns o (fn-own-remove-conn id (fn-own-conns o))))))
      (cons nil o))))

; The per-event law under the served port: one framed wire event is one
; fn-served-dispatch (fn-nntp-post-step with the article-mode switch,
; books/served.lisp) against the connection's own pinned archive.
; fn-served-step is the byte fold that runs fn-served-dispatch on each framed
; event before the next byte is framed; this is that fold's one step with the
; owner's bookkeeping around it.  It records no submission: the served port
; does that once per read.
(defun fn-own-read-step (o id event)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((result (fn-served-dispatch
                        (fn-served-make-conn (fn-own-conn-wire conn)
                                             (fn-own-conn-session conn)
                                             (fn-own-conn-archive conn)
                                             (fn-own-conn-config conn)
                                             (fn-own-conn-observation conn)
                                             (fn-own-clock o))
                        event))
               (sconn (fn-served-result-conn result))
               (next (fn-own-conn-make (fn-own-conn-id conn)
                                       (fn-own-conn-version conn)
                                       (fn-own-conn-frontier conn)
                                       (fn-served-conn-wire sconn)
                                       (fn-served-conn-session sconn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn))))
          (cons (fn-served-result-effects result)
                (if (fn-own-conn-boundedp next (fn-sn-groups (fn-own-store o)))
                    (fn-own-set-conns o (fn-own-replace-conn next (fn-own-conns o)))
                  (fn-own-set-conns o (fn-own-remove-conn id (fn-own-conns o))))))
      (cons nil o))))

; Advance re-pins a connection to the newest committed view.  The projection
; verdict is recomputed for the new archive (one recognizer run per advance);
; the cursor is kept because local numbers are never reused (PRF-002); the
; wire framing state is kept because the peer's stream is unaffected.
(defun fn-own-advance (o id)
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
               (next (fn-own-conn-make (fn-own-conn-id conn)
                                       (fn-own-view-version view)
                                       (fn-own-view-frontier view)
                                       (fn-own-conn-wire conn)
                                       session archive
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn))))
          (if (fn-own-conn-boundedp next (fn-sn-groups (fn-own-store o)))
              (fn-own-set-conns o (fn-own-replace-conn next (fn-own-conns o)))
            o))
      o)))

(defun fn-own-remove-subs (id subs)
  (declare (xargs :guard t))
  (if (consp subs)
      (if (equal (fn-own-sub-id (car subs)) id)
          (fn-own-remove-subs id (cdr subs))
        (cons (car subs) (fn-own-remove-subs id (cdr subs))))
    nil))

; Closing drops the connection, its pending transaction, its queued
; submissions and its submission in flight (a durable path already running
; for it completes through the store events and is acknowledged to nobody).
(defun fn-own-close (o id)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o)
               (fn-own-remove-conn id (fn-own-conns o))
               (fn-own-next-id o) (fn-own-max-conns o)
               (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
               (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-own-remove-subs id (fn-own-queue o))
               (if (and (fn-own-inflight o)
                        (equal (fn-own-sub-id (fn-own-inflight o)) id))
                   nil
                 (fn-own-inflight o)) (fn-own-feeds o)))

; -----------------------------------------------------------------------------
; Transactions: the fn-sn machine, owned by one connection at a time.

(defun fn-own-begin (o id)
  (declare (xargs :guard t))
  (if (and (null (fn-own-pending o))
           (fn-own-find-conn id (fn-own-conns o))
           (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready))
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) id
                   (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))
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
                (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
                (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))))

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
                      (fn-ag-append (fn-own-ledger o)
                                    (list (fn-sf-completion (fn-sn-files s))))
                      (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                      (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)))
      o)))

; A process restart.  The image (frontier records) is what the platform left
; behind (A-DURABILITY as the hypothesis fn-sf-crash-imagep); the new process
; reopens through fn-sn-open-observed exactly as the host does, with no
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
                      (fn-own-ledger o) nil (fn-own-facts o) (fn-own-config o)
                      nil nil (fn-own-feed-restart-all (fn-own-feeds o))))
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
                   (fn-own-ledger o)
                   (if (equal outcome :observed) obs nil)
                   (fn-own-facts o) (fn-own-config o)
                   (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)))))

; No fact without a clock observation: creation is refused until the host
; has supplied one.
(defun fn-own-declare-group (o name)
  (declare (xargs :guard t))
  (if (and (stringp name)
           (fn-clock-observationp (fn-own-clock o))
           (not (member-equal name (fn-own-replay-facts (fn-own-facts o)))))
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                   (fn-own-ledger o) (fn-own-clock o)
                   (fn-ag-append (fn-own-facts o)
                                 (list (fn-own-group-fact-make name (fn-own-clock o))))
                   (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))
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
               (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
               (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) feeds))

; What a submission tells the feed.  Both kinds carry the Message-ID and the
; article as octets; only a transit submission has an origin peer.  The octets
; are the ones that became durable: books/injection's injected form for a
; POST (it carries the generated Path and Message-ID) and the peer's own
; octets for a transit article, which is what fn-peer-injection-arguments
; stages as the payload.
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

; The enqueue on a durable acceptance, and the FNFD records that authorize
; it.  The host appends the records to <journal>/feed/<peer>.fnfd and only
; then may the offer they enable be emitted.
(defun fn-own-feed-durable (o sub)
  (declare (xargs :guard t))
  (fn-own-feed-accept (fn-own-feeds o) (fn-own-sub-origin sub)
                      (fn-own-sub-msgid sub) (fn-own-sub-octets sub)
                      (fn-own-feed-stamp o)))

(defun fn-own-feed-durable-records (o sub)
  (declare (xargs :guard t))
  (fn-own-feed-accept-records (fn-own-feeds o) (fn-own-sub-origin sub)
                              (fn-own-sub-msgid sub) (fn-own-sub-octets sub)
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
(defun fn-own-feed-article (o msgid)
  (declare (xargs :guard t))
  (let ((a (fn-find-article
            (fn-record-octets-string msgid)
            (fn-state-articles
             (fn-node-acceptance (fn-sn-node (fn-own-store o)))))))
    (if (consp a) (fn-article-payload a) nil)))

; One reply line from one peer.  ACL2 reads the three-digit code
; (fn-own-feed-parse-response), maps it (fn-feed-observe) and renders what
; follows; the host frames bytes and takes no decision.  The result is
; (effects . owner); an unknown peer or an unreadable line changes nothing.
(defun fn-own-feed-reply (o peer octets obs)
  (declare (xargs :guard t))
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
            (fn-feed-observe f response (fn-own-feed-article o msgid) obs)
            (cons (if (null effects) nil (list (cons peer effects)))
                  (fn-own-with-feeds
                   o (fn-own-feed-put peer (fn-own-feed-entry-record e) g
                                      tbl)))))))))

(defun fn-own-feed-reply-records (o peer octets)
  (declare (xargs :guard t))
  (let* ((tbl (fn-own-feeds o))
         (e (fn-own-feed-entry-of peer tbl)))
    (if (null e)
        nil
      (let* ((f (fn-own-feed-entry-feed e))
             (msgid (fn-own-feed-inflight-msgid (fn-feed-queue f)))
             (code (fn-own-feed-response-code octets)))
        (if (or (null code) (null msgid))
            nil
          (fn-own-feed-reply-records-of
           peer msgid
           (fn-feed-state-attempt (fn-feed-state-of msgid (fn-feed-queue f)))
           code))))))

; The connection one peer's feed writes to.  The host opens the socket and
; reports its identifier here; nil stops selection at once
; (fn-feed-selection wants a natp conn).  It does NOT resolve the entry that
; was in flight: this comment used to say the next observation would, and
; there is no next observation once the socket is gone, so the entry sat at
; :sent until the process restarted (measured on gate a5c6792: node A
; reconnected every 5 s and offered nothing, seven times over).
; `fn-own-feed-lost' below is the transition for a lost connection and is
; what the host calls now.
(defun fn-own-feed-connect (o peer conn)
  (declare (xargs :guard t))
  (let ((e (fn-own-feed-entry-of peer (fn-own-feeds o))))
    (if (null e)
        o
      (fn-own-with-feeds
       o (fn-own-feed-put peer (fn-own-feed-entry-record e)
                          (fn-feed-with-conn (fn-own-feed-entry-feed e) conn)
                          (fn-own-feeds o))))))

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
(defun fn-own-feed-lost-records (o peer)
  (declare (xargs :guard t))
  (fn-own-feed-lost-records-of peer (fn-own-feeds o)))

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
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
               (fn-own-clock o) (fn-own-facts o) config (fn-own-queue o)
               (fn-own-inflight o) (fn-own-feeds o)))

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
      (let ((sub (car (fn-own-queue o))))
        (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                     (fn-own-next-id o) (fn-own-max-conns o) (fn-own-sub-id sub)
                     (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                     (fn-own-config o) (cdr (fn-own-queue o))
                     (fn-own-sub-make (fn-own-sub-id sub) (fn-own-sub-version sub)
                                      (len (fn-own-ledger o))
                                      (fn-own-sub-decision sub)) (fn-own-feeds o)))
    o))

; The completion the owner reports for the submission in flight, from the
; word the host observed.  :durable needs a completion consumed into the
; ledger after the take (fn-own-complete is the only ledger writer, and it
; consumes the actual fn-sn-finish, fn-own-completion-consumed-once); a host
; word of :durable without one is :uncertain, never 240.  :refused is the
; host's typed refusal (nothing was staged, or the reservation was consumed
; by a refusal); everything else is :uncertain.
(defun fn-own-outcome-completion (o word)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (cond ((and (equal word :durable)
                sub
                (natp (fn-own-sub-mark sub))
                (< (fn-own-sub-mark sub) (len (fn-own-ledger o))))
           :durable)
          ((equal word :refused) :refused)
          (t :uncertain))))

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
                                 (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal completion :durable)
                                     (fn-own-feed-durable o sub)
                                   (fn-own-feeds o)))))
          (cons (fn-served-result-effects
                 (fn-served-post-outcome
                  (fn-served-make-conn (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o))
                  completion))
                (if (equal completion :durable)
                    (fn-own-advance next id)
                  next)))
      (cons nil o))))

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
                                  (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                                  (fn-own-config o) (fn-own-queue o) nil
                                  (if (equal completion :durable)
                                      (fn-own-feed-durable o sub)
                                    (fn-own-feeds o)))))
          (cons (fn-served-result-effects
                 (fn-served-transit-outcome
                  ; Six fields since the clock seam: the connection's
                  ; pinned reader observation and the owner's current
                  ; reading, as fn-own-outcome passes them.  This caller
                  ; still passed five, so books/owner did not admit.
                  (fn-served-make-conn (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o))
                  (fn-own-sub-decision sub) d completion))
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

(defun fn-own-step (o event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o)) :verify-guards nil))
  (case (car event)
    (:open (cdr (fn-own-open o (cadr event))))
    (:open-peer (cdr (fn-own-open-peer o (cadr event) (caddr event)
                                       (cadddr event))))
    (:octets (cdr (fn-own-read o (cadr event) (caddr event))))
    (:read (cdr (fn-own-read-step o (cadr event) (caddr event))))
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
    (:outcome (cdr (fn-own-outcome o (cadr event) (caddr event))))
    (:transit-outcome (cdr (fn-own-transit-outcome o (cadr event) (caddr event)
                                                   (cadddr event)
                                                   (car (cddddr event)))))
    (:feeds (fn-own-feeds-reconfigure o (cadr event)))
    (:feed-conn (fn-own-feed-connect o (cadr event) (caddr event)))
    (:feed-lost (fn-own-feed-lost o (cadr event) (caddr event)))
    (:feed-replay (fn-own-feed-recover o (cadr event) (caddr event)))
    (:tick (cdr (fn-own-tick o (cadr event))))
    (:tick-peer (cdr (fn-own-tick-peer o (cadr event) (caddr event))))
    (:feed-octets (cdr (fn-own-feed-reply o (cadr event) (caddr event)
                                          (cadddr event))))
    (otherwise o)))

(defun fn-own-run (o events)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o)) :verify-guards nil))
  (if (consp events)
      (fn-own-run (fn-own-step o (car events)) (cdr events))
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
    fn-own-start fn-own-conn-boundedp fn-own-set-conns fn-own-open fn-own-enqueue
    fn-own-read fn-own-read-step fn-own-advance fn-own-close fn-own-begin
    fn-own-store-step fn-own-complete fn-own-reopen
    fn-own-observe-outcome fn-own-observe
    fn-own-declare-group fn-own-configure fn-own-take-submission fn-own-outcome-completion
    fn-own-outcome fn-own-step fn-own-run fn-own-reclaim-floor
    fn-own-open-peer fn-own-transit-subp fn-own-transit-inflightp
    fn-own-transit-outcome
    fn-own-with-feeds fn-own-sub-origin fn-own-sub-msgid fn-own-sub-octets
    fn-own-feed-stamp fn-own-feed-durable fn-own-feed-durable-records
    fn-own-outcome-records fn-own-transit-outcome-records
    fn-own-feeds-reconfigure fn-own-tick fn-own-tick-records
    fn-own-tick-peer fn-own-tick-peer-records
    fn-own-feed-article fn-own-feed-reply fn-own-feed-reply-records
    fn-own-feed-connect fn-own-feed-lost fn-own-feed-lost-records
    fn-own-feed-recover))

(in-theory (disable fn-own-vocabulary))
