; fn: the mutable service owner over the live fn-sn composition (C1-05).
;
; One owner process serializes mutations of one store while readers observe a
; committed version.  This book is the executable model the host drives
; through host/owner-host.lisp (tools/run_owner.py).  It performs no I/O.
;
; The owner record is
;   (store view conns next-id max-conns pending ledger clock facts
;    config queue inflight)
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
  (and (true-listp x) (equal (len x) 12)))
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
(defun fn-own-make (store view conns next-id max-conns pending ledger clock facts
                          config queue inflight)
  (declare (xargs :guard t))
  (list store view conns next-id max-conns pending ledger clock facts
        config queue inflight))

(defthm fn-own-shapep-of-fn-own-make
  (fn-own-shapep (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight)))
(defthm fn-own-store-of-fn-own-make
  (equal (fn-own-store (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         store))
(defthm fn-own-view-of-fn-own-make
  (equal (fn-own-view (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         view))
(defthm fn-own-conns-of-fn-own-make
  (equal (fn-own-conns (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         conns))
(defthm fn-own-next-id-of-fn-own-make
  (equal (fn-own-next-id (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         next-id))
(defthm fn-own-max-conns-of-fn-own-make
  (equal (fn-own-max-conns (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         max-conns))
(defthm fn-own-pending-of-fn-own-make
  (equal (fn-own-pending (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         pending))
(defthm fn-own-ledger-of-fn-own-make
  (equal (fn-own-ledger (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         ledger))
(defthm fn-own-clock-of-fn-own-make
  (equal (fn-own-clock (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         clock))
(defthm fn-own-facts-of-fn-own-make
  (equal (fn-own-facts (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         facts))
(defthm fn-own-config-of-fn-own-make
  (equal (fn-own-config (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         config))
(defthm fn-own-queue-of-fn-own-make
  (equal (fn-own-queue (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         queue))
(defthm fn-own-inflight-of-fn-own-make
  (equal (fn-own-inflight (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight))
         inflight))
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
       (implies (fn-own-inflight x) (consp x)))
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
                                    :trigger-terms ((fn-own-inflight x)))))
(in-theory (disable (:d fn-own-shapep) (:d fn-own-store) (:d fn-own-view) (:d fn-own-conns)
                    (:d fn-own-next-id) (:d fn-own-max-conns) (:d fn-own-pending)
                    (:d fn-own-ledger) (:d fn-own-clock) (:d fn-own-facts)
                    (:d fn-own-config) (:d fn-own-queue) (:d fn-own-inflight)
                    (:d fn-own-make)))

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
                     (fn-own-inflight o))
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
                nil 0 max-conns nil nil nil nil nil nil nil)))

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
(defun fn-own-conn-boundedp (conn groups)
  (declare (xargs :guard t))
  (let ((ps (fn-own-conn-session conn)))
    (and (fn-post-sessionp ps)
         (let ((session (fn-post-session-base ps)))
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
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)))

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
(defun fn-own-open (o)
  (declare (xargs :guard t))
  (if (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))
      (let* ((view (fn-own-view o))
             (archive (fn-own-view-archive view))
             (id (fn-own-next-id o))
             (opened (fn-served-open archive *fn-nntp-max-initial-line-octets*
                                     *fn-own-body-limit* (fn-own-config o)
                                     (fn-own-clock o) (fn-own-clock o)))
             (sconn (fn-served-result-conn opened))
             (conn (fn-own-conn-make id (fn-own-view-version view)
                                     (fn-own-view-frontier view)
                                     (fn-served-conn-wire sconn)
                                     (fn-served-conn-session sconn)
                                     archive (fn-own-config o) (fn-own-clock o))))
        (cons (fn-served-result-effects opened)
              (fn-own-make (fn-own-store o) view (cons conn (fn-own-conns o))
                           (1+ (nfix id)) (fn-own-max-conns o) (fn-own-pending o)
                           (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o))))
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
(defun fn-own-open-peer (o peer cfg)
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
             (opened (fn-served-open-peer archive
                                          *fn-nntp-max-initial-line-octets*
                                          limit (fn-own-config o) (fn-own-clock o)
                                          peer (fn-sn-node (fn-own-store o)) cfg))
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
                           (fn-own-config o) (fn-own-queue o) (fn-own-inflight o))))
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
               (fn-ag-append (fn-own-queue o) (list sub)) (fn-own-inflight o)))

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
               (old (fn-own-conn-session conn))
               (base (fn-post-session-base old))
               (session (fn-post-make-session
                         (fn-nntp-set-cursor (fn-nntp-open-session archive)
                                             (fn-nntp-session-group base)
                                             (fn-nntp-session-current base))
                         (fn-post-session-awaiting old)))
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
                 (fn-own-inflight o))))

; -----------------------------------------------------------------------------
; Transactions: the fn-sn machine, owned by one connection at a time.

(defun fn-own-begin (o id)
  (declare (xargs :guard t))
  (if (and (null (fn-own-pending o))
           (fn-own-find-conn id (fn-own-conns o))
           (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready))
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) id
                   (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o))
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
                (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o))))

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
                      (fn-own-queue o) (fn-own-inflight o)))
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
                      nil nil))
      o)))

; -----------------------------------------------------------------------------
; Clock observations and clock-stamped group-configuration facts

(defun fn-own-observe (o obs)
  (declare (xargs :guard t))
  (if (and (fn-clock-observationp obs)
           (or (null (fn-own-clock o))
               (and (fn-clock-observationp (fn-own-clock o))
                    (fn-clock-later-observationp (fn-own-clock o) obs))))
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                   (fn-own-ledger o) obs (fn-own-facts o) (fn-own-config o)
                   (fn-own-queue o) (fn-own-inflight o))
    o))

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
                   (fn-own-config o) (fn-own-queue o) (fn-own-inflight o))
    o))

; -----------------------------------------------------------------------------
; The served POST path: configuration, the writer step and the outcome.

; The posting configuration new connections pin.  Open connections keep the
; configuration they were opened with.
(defun fn-own-configure (o config)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
               (fn-own-clock o) (fn-own-facts o) config (fn-own-queue o)
               (fn-own-inflight o)))

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
                                      (fn-own-sub-decision sub))))
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
        (let ((completion (fn-own-outcome-completion o word))
              (next (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil)))
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
                                  (fn-own-config o) (fn-own-queue o) nil)))
          (cons (fn-served-result-effects
                 (fn-served-transit-outcome
                  (fn-served-make-conn (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn))
                  (fn-own-sub-decision sub) d completion))
                (if (equal completion :durable)
                    (fn-own-advance next id)
                  next)))
      (cons nil o))))

; -----------------------------------------------------------------------------
; The owner event machine.  (:octets id octets) is the served port; (:read id
; event) is its per-event law; (:take) is the writer step; (:outcome id word)
; feeds the durable outcome of the submission in flight back through the
; book, which renders the reply (fn-own-outcome).

(defun fn-own-step (o event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o)) :verify-guards nil))
  (case (car event)
    (:open (cdr (fn-own-open o)))
    (:open-peer (cdr (fn-own-open-peer o (cadr event) (caddr event))))
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
    fn-own-store-step fn-own-complete fn-own-reopen fn-own-observe
    fn-own-declare-group fn-own-configure fn-own-take-submission fn-own-outcome-completion
    fn-own-outcome fn-own-step fn-own-run fn-own-reclaim-floor
    fn-own-open-peer fn-own-transit-subp fn-own-transit-inflightp
    fn-own-transit-outcome))

(in-theory (disable fn-own-vocabulary))
