; fn: the mutable service owner over the live fn-sn composition (C1-05).
;
; One owner process serializes mutations of one store while readers observe a
; committed version.  This book is the executable model the host drives
; through host/owner-host.lisp (tools/run_owner.py).  It performs no I/O.
;
; The owner state is
;   (store view conns next-id max-conns pending ledger clock facts)
; where
;   store     the actual fn-sn composition (books/store-node.lisp), stepped
;             only through fn-snrt-step and fn-sn-finish;
;   view      the committed view (version frontier archive): version is the
;             generation, the length of the durable record history; archive
;             is the acceptance projection of the node at that generation;
;   conns     the open connections, each (id version frontier archive session)
;             pinned to one committed view, carrying one fn-nntp session;
;   next-id   the next connection identifier;
;   max-conns the configured bound on open connections;
;   pending   nil or the identifier of the connection that began the one
;             transaction the store admits at a time;
;   ledger    proof-only history: the (sequence . txid) pairs consumed by
;             fn-own-complete, in order.  The host keeps no such list; the
;             durability keystone reads it and the records carry the claim;
;   clock     nil or the latest fn-clock-observationp the host supplied;
;   facts     the persisted group-configuration fact records, each stamped
;             with the clock observation current when it was created.
;
; A reader step runs fn-nntp-step against the archive of ITS pinned version,
; never against the live node.  The committed view is refreshed only when the
; store is at an idle phase, where fn-snt-relation says the live node is the
; exact replay of the durable records (books/store-node-traces.lisp).

(in-package "ACL2")
(include-book "store-observed-traces")
(include-book "nntp")
(include-book "clock")

; -----------------------------------------------------------------------------
; Shapes

(defun fn-own-conn-make (id version frontier archive session)
  (declare (xargs :guard t :verify-guards nil))
  (list id version frontier archive session))
(defun fn-own-conn-id (c) (declare (xargs :guard t :verify-guards nil)) (car c))
(defun fn-own-conn-version (c) (declare (xargs :guard t :verify-guards nil)) (cadr c))
(defun fn-own-conn-frontier (c) (declare (xargs :guard t :verify-guards nil)) (caddr c))
(defun fn-own-conn-archive (c) (declare (xargs :guard t :verify-guards nil)) (cadddr c))
(defun fn-own-conn-session (c) (declare (xargs :guard t :verify-guards nil)) (car (cddddr c)))

(defun fn-own-view-make (version frontier archive)
  (declare (xargs :guard t :verify-guards nil))
  (list version frontier archive))
(defun fn-own-view-version (v) (declare (xargs :guard t :verify-guards nil)) (car v))
(defun fn-own-view-frontier (v) (declare (xargs :guard t :verify-guards nil)) (cadr v))
(defun fn-own-view-archive (v) (declare (xargs :guard t :verify-guards nil)) (caddr v))

(defun fn-own-make (store view conns next-id max-conns pending ledger clock facts)
  (declare (xargs :guard t :verify-guards nil))
  (list store view conns next-id max-conns pending ledger clock facts))
(defun fn-own-store (o) (declare (xargs :guard t :verify-guards nil)) (car o))
(defun fn-own-view (o) (declare (xargs :guard t :verify-guards nil)) (cadr o))
(defun fn-own-conns (o) (declare (xargs :guard t :verify-guards nil)) (caddr o))
(defun fn-own-next-id (o) (declare (xargs :guard t :verify-guards nil)) (cadddr o))
(defun fn-own-max-conns (o) (declare (xargs :guard t :verify-guards nil)) (car (cddddr o)))
(defun fn-own-pending (o) (declare (xargs :guard t :verify-guards nil)) (cadr (cddddr o)))
(defun fn-own-ledger (o) (declare (xargs :guard t :verify-guards nil)) (caddr (cddddr o)))
(defun fn-own-clock (o) (declare (xargs :guard t :verify-guards nil)) (cadddr (cddddr o)))
(defun fn-own-facts (o) (declare (xargs :guard t :verify-guards nil)) (car (cddddr (cddddr o))))

; -----------------------------------------------------------------------------
; The durable prefix a version names, and the archive it projects to.

(defun fn-own-take (n xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (posp n) (consp xs))
      (cons (car xs) (fn-own-take (1- n) (cdr xs)))
    nil))

; The acceptance projection of the replay of the first `version` records,
; advanced to `frontier`.  Every pinned archive equals this over the durable
; history of the moment (fn-own-relation, owner-invariants.lisp).
(defun fn-own-prefix-archive (groups capacity records version frontier)
  (declare (xargs :guard t :verify-guards nil))
  (fn-node-acceptance
   (fn-sf-replay-node groups capacity (fn-own-take version records) frontier)))

; -----------------------------------------------------------------------------
; The committed view is refreshed at idle phases only.

(defun fn-own-store-idlep (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files s))))

(defun fn-own-refresh (o)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s (fn-own-store o)))
    (if (fn-own-store-idlep s)
        (fn-own-make s
                     (fn-own-view-make (len (fn-sf-records (fn-sn-files s)))
                                       (fn-sf-frontier (fn-sn-files s))
                                       (fn-node-acceptance (fn-sn-node s)))
                     (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                     (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
                     (fn-own-facts o))
      o)))

; The owner of a store.  The host calls this once per process over the state
; fn-sn-open-observed returned (host/owner-host.lisp, fn-owner-recover).
(defun fn-own-start (store max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (fn-own-refresh
   (fn-own-make store
                (fn-own-view-make 0 0 (fn-own-prefix-archive
                                       (fn-sn-groups store) (fn-sn-capacity store)
                                       (fn-sf-records (fn-sn-files store)) 0 0))
                nil 0 max-conns nil nil nil nil)))

; -----------------------------------------------------------------------------
; Connections

(defun fn-own-replace-conn (conn conns)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp conns)
      (if (equal (car (car conns)) (car conn))
          (cons conn (cdr conns))
        (cons (car conns) (fn-own-replace-conn conn (cdr conns))))
    nil))

(defun fn-own-remove-conn (id conns)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp conns)
      (if (equal (car (car conns)) id)
          (fn-own-remove-conn id (cdr conns))
        (cons (car conns) (fn-own-remove-conn id (cdr conns))))
    nil))

(defun fn-own-find-conn (id conns)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp conns)
      (if (equal (car (car conns)) id)
          (car conns)
        (fn-own-find-conn id (cdr conns)))
    nil))

; The per-connection retained state is bounded by configuration: a session
; is four fields, its group is one of the configured names or nil, and its
; cursor is nil or inside RFC 3977 section 6's article-number range.  A step
; whose result leaves this set closes the connection (fn-own-read-step).
(defun fn-own-conn-boundedp (conn groups)
  (declare (xargs :guard t :verify-guards nil))
  (let ((session (fn-own-conn-session conn)))
    (and (fn-nntp-sessionp session)
         (or (null (fn-nntp-session-group session))
             (member-equal (fn-nntp-session-group session) groups))
         (or (null (fn-nntp-session-current session))
             (<= (fn-nntp-session-current session)
                 *fn-nntp-max-article-number*)))))

(defun fn-own-set-conns (o conns)
  (declare (xargs :guard t :verify-guards nil))
  (fn-own-make (fn-own-store o) (fn-own-view o) conns (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
               (fn-own-clock o) (fn-own-facts o)))

; Open pins the current committed view.  The whole-archive projection
; recognizer runs here once per connection (fn-nntp-open-session), never
; per command.
(defun fn-own-open (o)
  (declare (xargs :guard t :verify-guards nil))
  (if (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))
      (let* ((view (fn-own-view o))
             (archive (fn-own-view-archive view))
             (id (fn-own-next-id o))
             (conn (fn-own-conn-make id (fn-own-view-version view)
                                     (fn-own-view-frontier view) archive
                                     (fn-nntp-open-session archive))))
        (fn-own-make (fn-own-store o) view (cons conn (fn-own-conns o))
                     (1+ (nfix id)) (fn-own-max-conns o) (fn-own-pending o)
                     (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)))
    o))

; One reader step: (effects . owner).  The step is fn-nntp-step against the
; connection's own pinned archive.  The host writes `effects`; it is the
; result of exactly this call (host/owner-host.lisp, fn-owner-chunk).
(defun fn-own-read-step (o id event)
  (declare (xargs :guard t :verify-guards nil))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((result (fn-nntp-step (fn-own-conn-session conn)
                                     (fn-own-conn-archive conn) event))
               (next (fn-own-conn-make (fn-own-conn-id conn)
                                       (fn-own-conn-version conn)
                                       (fn-own-conn-frontier conn)
                                       (fn-own-conn-archive conn)
                                       (fn-nntp-result-session result))))
          (cons (fn-nntp-result-effects result)
                (if (fn-own-conn-boundedp next (fn-sn-groups (fn-own-store o)))
                    (fn-own-set-conns o (fn-own-replace-conn next (fn-own-conns o)))
                  (fn-own-set-conns o (fn-own-remove-conn id (fn-own-conns o))))))
      (cons nil o))))

; Advance re-pins a connection to the newest committed view.  The projection
; verdict is recomputed for the new archive (one recognizer run per advance);
; the cursor is kept because local numbers are never reused (PRF-002).
(defun fn-own-advance (o id)
  (declare (xargs :guard t :verify-guards nil))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((view (fn-own-view o))
               (archive (fn-own-view-archive view))
               (old (fn-own-conn-session conn))
               (session (fn-nntp-set-cursor (fn-nntp-open-session archive)
                                            (fn-nntp-session-group old)
                                            (fn-nntp-session-current old)))
               (next (fn-own-conn-make (fn-own-conn-id conn)
                                       (fn-own-view-version view)
                                       (fn-own-view-frontier view)
                                       archive session)))
          (if (fn-own-conn-boundedp next (fn-sn-groups (fn-own-store o)))
              (fn-own-set-conns o (fn-own-replace-conn next (fn-own-conns o)))
            o))
      o)))

(defun fn-own-close (o id)
  (declare (xargs :guard t :verify-guards nil))
  (fn-own-make (fn-own-store o) (fn-own-view o)
               (fn-own-remove-conn id (fn-own-conns o))
               (fn-own-next-id o) (fn-own-max-conns o)
               (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
               (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)))

; -----------------------------------------------------------------------------
; Transactions: the fn-sn machine, owned by one connection at a time.

(defun fn-own-begin (o id)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (null (fn-own-pending o))
           (fn-own-find-conn id (fn-own-conns o))
           (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready))
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) id
                   (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o))
    o))

; Every kernel/node transition of the store, including the resolution
; transitions, crash and recover, goes through the proved fn-snrt-step.
(defun fn-own-store-step (o event)
  (declare (xargs :guard t :verify-guards nil))
  (fn-own-refresh
   (fn-own-make (fn-snrt-step (fn-own-store o) event) (fn-own-view o)
                (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
                (fn-own-facts o))))

; Completion is the actual fn-sn-finish.  It is consumed exactly when the
; kernel is at :completing with a bound record; the consumed pair is the
; kernel's own completion, recorded once in the ledger.  Away from that phase
; a completion is a no-op on the whole owner.
(defun fn-own-complete (o)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s (fn-own-store o)))
    (if (fn-sn-completion-enabledp s)
        (fn-own-refresh
         (fn-own-make (fn-sn-finish s) (fn-own-view o) (fn-own-conns o)
                      (fn-own-next-id o) (fn-own-max-conns o) nil
                      (append (fn-own-ledger o)
                              (list (fn-sf-completion (fn-sn-files s))))
                      (fn-own-clock o) (fn-own-facts o)))
      o)))

; A process restart.  The image (frontier records) is what the platform left
; behind (A-DURABILITY as the hypothesis fn-sf-crash-imagep); the new process
; reopens through fn-sn-open-observed exactly as the host does, with no
; connections, no pending transaction and no clock (the monotonic counter has
; no meaning across processes).  The ledger is proof-only and is kept.
(defun fn-own-reopen (o frontier records)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s (fn-own-store o))
         (opened (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                      frontier records)))
    (if (and (fn-sf-crash-imagep (fn-sn-files s) frontier records)
             (fn-sn-open-okp opened))
        (fn-own-refresh
         (fn-own-make (fn-sn-open-state opened) (fn-own-view o) nil
                      (fn-own-next-id o) (fn-own-max-conns o) nil
                      (fn-own-ledger o) nil (fn-own-facts o)))
      o)))

; -----------------------------------------------------------------------------
; Clock observations and clock-stamped group-configuration facts

(defun fn-own-observe (o obs)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-clock-observationp obs)
           (or (null (fn-own-clock o))
               (and (fn-clock-observationp (fn-own-clock o))
                    (fn-clock-later-observationp (fn-own-clock o) obs))))
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                   (fn-own-ledger o) obs (fn-own-facts o))
    o))

; A group-configuration fact record: the creation of a group, stamped with
; the clock observation current when it was recorded.  Facts are an
; append-only record kind; the live group view is their replay.
(defun fn-own-group-fact-make (name obs)
  (declare (xargs :guard t :verify-guards nil))
  (list :fn-own-group-fact name obs))
(defun fn-own-group-fact-name (x) (declare (xargs :guard t :verify-guards nil)) (cadr x))
(defun fn-own-group-fact-stamp (x) (declare (xargs :guard t :verify-guards nil)) (caddr x))

(defun fn-own-group-factp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp x) (equal (len x) 3)
       (equal (car x) :fn-own-group-fact)
       (stringp (fn-own-group-fact-name x))
       (fn-clock-observationp (fn-own-group-fact-stamp x))))

(defun fn-own-facts-okp (facts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp facts)
      (and (fn-own-group-factp (car facts))
           (fn-own-facts-okp (cdr facts)))
    (null facts)))

; Replay of the fact log: the created group names in creation order.
(defun fn-own-replay-facts (facts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp facts)
      (cons (fn-own-group-fact-name (car facts))
            (fn-own-replay-facts (cdr facts)))
    nil))

; No fact without a clock observation: creation is refused until the host
; has supplied one.
(defun fn-own-declare-group (o name)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (stringp name)
           (fn-clock-observationp (fn-own-clock o))
           (not (member-equal name (fn-own-replay-facts (fn-own-facts o)))))
      (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                   (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                   (fn-own-ledger o) (fn-own-clock o)
                   (append (fn-own-facts o)
                           (list (fn-own-group-fact-make name (fn-own-clock o)))))
    o))

; -----------------------------------------------------------------------------
; The owner event machine

(defun fn-own-step (o event)
  (declare (xargs :guard t :verify-guards nil))
  (case (car event)
    (:open (fn-own-open o))
    (:read (cdr (fn-own-read-step o (cadr event) (caddr event))))
    (:advance (fn-own-advance o (cadr event)))
    (:close (fn-own-close o (cadr event)))
    (:begin (fn-own-begin o (cadr event)))
    (:store (fn-own-store-step o (cadr event)))
    (:complete (fn-own-complete o))
    (:reopen (fn-own-reopen o (cadr event) (caddr event)))
    (:observe (fn-own-observe o (cadr event)))
    (:declare-group (fn-own-declare-group o (cadr event)))
    (otherwise o)))

(defun fn-own-run (o events)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (fn-own-run (fn-own-step o (car events)) (cdr events))
    o))

; The compaction floor: nothing below the lowest pinned version may be
; reclaimed.  Compaction does not exist yet; the floor is stated so that the
; invariant it must respect exists before the code that must respect it.
(defun fn-own-min-pinned (conns floor)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp conns)
      (fn-own-min-pinned (cdr conns)
                         (if (and (natp (fn-own-conn-version (car conns)))
                                  (< (fn-own-conn-version (car conns)) (nfix floor)))
                             (fn-own-conn-version (car conns))
                           (nfix floor)))
    (nfix floor)))

(defun fn-own-reclaim-floor (o)
  (declare (xargs :guard t :verify-guards nil))
  (fn-own-min-pinned (fn-own-conns o) (fn-own-view-version (fn-own-view o))))
