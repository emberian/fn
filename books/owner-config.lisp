; fn: the configured owner -- packet R5 of specs/reconfiguration.md, the
; owner event `(:reconfigure id deltas)' and the per-connection
; configuration pin.
;
; WHAT THIS BOOK IS, AND THE ONE DEVIATION FROM THE DESIGN.  Section 2.2 of
; the design puts the configuration pin into the connection record, as a
; ninth slot of `fn-own-conn-make'.  It is not there.  `books/owner.lisp' is
; the file two other lanes are editing this cycle, `fn-own-conn-make' has
; eight slots and forty call sites, and a ninth slot rewrites every one of
; them.  So this book does to `books/owner' exactly what
; `books/node-config.lisp' did to `books/node': it pairs the owner with its
; configuration and with a pin TABLE beside it, and carries the coherence as
; recognizer conjuncts:
;
;   (fn-ocfg-make owner config pins staged)
;
;   owner   the `fn-own' state, stepped only through the owner's own events;
;   config  the live `(generation . value)': the configuration the durable
;           configuration-record history replays to;
;   pins    one `(id . config)' per OPEN connection: the configuration
;           generation that connection opened at.  `fn-ocfg-statep' requires
;           the table's domain to be exactly the open connections, so the pin
;           is a derived quantity the relation constrains, not an
;           independently writable field -- which is what section 2.2 asks
;           for;
;   staged  nil, or the one `fn-cfg-record' in the pending-transaction slot.
;
; `books/owner' and `books/owner-invariants' are UNTOUCHED, and every
; statement of theirs still holds of the owner inside.
;
; A reconfiguration is a transaction (design section 2.1): it takes the same
; single pending slot `fn-own-begin' takes, so the owner cannot hold a staged
; post and a staged reconfiguration at once, and the record's sequence is its
; position in the UNIFIED stream (`books/config-stream.lisp'), which is what
; lets a capacity change be re-checked at replay against the reservation
; total that was live when it was admitted.
;
; This book owns the prefix `fn-ocfg-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "owner-fault")
(include-book "owner-invariants")
(include-book "config-stream")

; -----------------------------------------------------------------------------
; The record

(defun fn-ocfg-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))
; The four accessors are total, as every other record's are
; (books/acceptance-alloc.lisp `fn-ag-car'/`fn-ag-cdr', books/owner.lisp:93
; for the same pattern): with `:guard t' a bare `(car x)' owes
; `(implies (not (consp x)) (equal x nil))', which is false at `x = 3', so
; this book has never been admitted -- none of its guard conjectures, none
; of the record lemmas that translate through them, and none of the eight
; theorems above the definitions.  The `:logic' bodies are unchanged, so
; every statement in the book keeps its meaning.
(defun fn-ocfg-owner (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-ocfg-config (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-ocfg-pins (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-ocfg-staged (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-ocfg-make (owner config pins staged)
  (declare (xargs :guard t))
  (list owner config pins staged))

(defthm fn-ocfg-shapep-of-fn-ocfg-make
  (fn-ocfg-shapep (fn-ocfg-make owner config pins staged)))
(defthm fn-ocfg-owner-of-fn-ocfg-make
  (equal (fn-ocfg-owner (fn-ocfg-make owner config pins staged)) owner))
(defthm fn-ocfg-config-of-fn-ocfg-make
  (equal (fn-ocfg-config (fn-ocfg-make owner config pins staged)) config))
(defthm fn-ocfg-pins-of-fn-ocfg-make
  (equal (fn-ocfg-pins (fn-ocfg-make owner config pins staged)) pins))
(defthm fn-ocfg-staged-of-fn-ocfg-make
  (equal (fn-ocfg-staged (fn-ocfg-make owner config pins staged)) staged))
(defthm fn-ocfg-shapep-forward-shape
  (implies (fn-ocfg-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-ocfg-shapep) (:d fn-ocfg-owner) (:d fn-ocfg-config)
                    (:d fn-ocfg-pins) (:d fn-ocfg-staged) (:d fn-ocfg-make)))

; -----------------------------------------------------------------------------
; The pin table.
;
; `fn-ocfg-pin-add' NEVER overwrites: opening a connection adds a pin for a
; new identifier and provably leaves every existing pin alone
; (`fn-ocfg-open-keeps-every-existing-pin').  Only `fn-ocfg-pin-set'
; replaces, and only `(:advance id)' calls it.
;
; The sentence that used to end the paragraph above --- "with no freshness
; hypothesis to discharge" --- was FALSE and was withdrawn (w11/snt-guards,
; 2026-09-20).  Not overwriting is exactly what makes freshness necessary: a
; STALE pin at the identifier about to be allocated would survive the add,
; and the new connection would then serve the stale configuration.  What
; discharges it is not a hypothesis about the pin table but the state
; relation: `fn-ocfg-open-pins-the-live-configuration' below hypothesises
; `(fn-ocfg-statep oc)', whose `fn-ocfg-pins-pin-conns-only' turns a pin at
; `(fn-own-next-id o)' into an OPEN CONNECTION there, and whose
; `fn-own-relation' bounds every open connection's identifier strictly below
; `fn-own-next-id' (`fn-own-ids-below-next-p',
; books/owner-invariants.lisp).  `fn-ocfg-pin-set' has the mirror of it (it
; returns nil on an empty table, so it only replaces a pin that is already
; there), and `fn-ocfg-advance-observes-the-live-configuration' discharges
; that from the same recognizer's `fn-ocfg-conns-pinnedp'.

(defun fn-ocfg-pin-find (id pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (if (and (consp (car pins)) (equal (car (car pins)) id))
          (car pins)
        (fn-ocfg-pin-find id (cdr pins)))
    nil))

(defun fn-ocfg-pin-add (id cfg pins)
  (declare (xargs :guard t))
  (if (fn-ocfg-pin-find id pins) pins (cons (cons id cfg) pins)))

(defun fn-ocfg-pin-set (id cfg pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (if (and (consp (car pins)) (equal (car (car pins)) id))
          (cons (cons id cfg) (cdr pins))
        (cons (car pins) (fn-ocfg-pin-set id cfg (cdr pins))))
    nil))

(defun fn-ocfg-pin-remove (id pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (if (and (consp (car pins)) (equal (car (car pins)) id))
          (fn-ocfg-pin-remove id (cdr pins))
        (cons (car pins) (fn-ocfg-pin-remove id (cdr pins))))
    nil))

(defthm fn-ocfg-pin-find-of-pin-add-other
  (implies (not (equal id other))
           (equal (fn-ocfg-pin-find id (fn-ocfg-pin-add other cfg pins))
                  (fn-ocfg-pin-find id pins))))
(defthm fn-ocfg-pin-find-of-pin-add-same
  (implies (fn-ocfg-pin-find id pins)
           (equal (fn-ocfg-pin-find id (fn-ocfg-pin-add other cfg pins))
                  (fn-ocfg-pin-find id pins))))
(defthm fn-ocfg-pin-find-of-pin-set-other
  (implies (not (equal id other))
           (equal (fn-ocfg-pin-find id (fn-ocfg-pin-set other cfg pins))
                  (fn-ocfg-pin-find id pins))))
(defthm fn-ocfg-pin-find-of-pin-set-same
  (implies (fn-ocfg-pin-find id pins)
           (equal (fn-ocfg-pin-find id (fn-ocfg-pin-set id cfg pins))
                  (cons id cfg))))
(defthm fn-ocfg-pin-find-of-pin-remove-other
  (implies (not (equal id other))
           (equal (fn-ocfg-pin-find id (fn-ocfg-pin-remove other pins))
                  (fn-ocfg-pin-find id pins))))

; The connection's pinned configuration, and the served table at that pin.
(defun fn-ocfg-conn-config (oc id)
  (declare (xargs :guard t))
  (cdr (fn-ocfg-pin-find id (fn-ocfg-pins oc))))

(defun fn-ocfg-conn-generation (oc id)
  (declare (xargs :guard t))
  (fn-cfg-generation (fn-ocfg-conn-config oc id)))

(defun fn-ocfg-served (oc id)
  ; THE served table of THIS connection: the live names at its pin.  Not the
  ; allocation domain, which is what the acceptance state carries.
  (declare (xargs :guard t))
  (fn-cnode-served-of (fn-ocfg-conn-config oc id)))

; -----------------------------------------------------------------------------
; The recognizer: the pin table's domain is exactly the open connections

(defun fn-ocfg-pins-okp (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (and (consp (car pins))
           (fn-cfgp (cdr (car pins)))
           (fn-ocfg-pins-okp (cdr pins)))
    (null pins)))

(defun fn-ocfg-conns-pinnedp (conns pins)
  (declare (xargs :guard t))
  (if (consp conns)
      (and (fn-ocfg-pin-find (fn-own-conn-id (car conns)) pins)
           (fn-ocfg-conns-pinnedp (cdr conns) pins))
    t))

(defun fn-ocfg-pins-pin-conns-only (pins conns)
  (declare (xargs :guard t))
  (if (consp pins)
      (and (consp (car pins))
           (fn-own-find-conn (car (car pins)) conns)
           (fn-ocfg-pins-pin-conns-only (cdr pins) conns))
    t))

; `fn-cfgp' types the live generation (books/config.lisp:504-508, through
; `fn-record-uint32p'), and books/config withdraws both definitions at export.
; Every `(+ 1 (fn-cfg-generation (fn-ocfg-config oc)))' in this book --- the
; staged clause below, `fn-ocfg-reconfig-record', `fn-ocfg-reconfig-refusal'
; --- owes `acl2-numberp' of that generation, so the fact is named once here
; and forward chained.  Guard vocabulary only, hence local.
(local
 (defthm fn-ocfg-configured-generation-is-natural
   (implies (fn-cfgp c) (natp (fn-cfg-generation c)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cfgp fn-record-uint32p)))))

(defun fn-ocfg-statep (oc)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (and (fn-ocfg-shapep oc)
         (fn-own-relation o)
         (fn-cfgp (fn-ocfg-config oc))
         (fn-ocfg-pins-okp (fn-ocfg-pins oc))
         ; one pin per open connection, and no pin for anything else
         (fn-ocfg-conns-pinnedp (fn-own-conns o) (fn-ocfg-pins oc))
         (fn-ocfg-pins-pin-conns-only (fn-ocfg-pins oc) (fn-own-conns o))
         (or (null (fn-ocfg-staged oc))
             (and (fn-cfg-recordp (fn-ocfg-staged oc))
                  (equal (fn-cfg-record-generation (fn-ocfg-staged oc))
                         (+ 1 (fn-cfg-generation (fn-ocfg-config oc)))))))))

; The live configured node: the store's node under the owner's configuration.
; This is what admissibility is checked against, and it is the same
; `fn-cnode' the store host builds (host/store-node-host.lisp).
(defun fn-ocfg-live-cnode (oc)
  (declare (xargs :guard t))
  (fn-cnode-make (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))
                 (fn-ocfg-config oc)))

; -----------------------------------------------------------------------------
; The reconfiguration event.
;
; D13: three outcomes stay distinct.  A refused reconfiguration leaves the
; state untouched and names its reason through `fn-ocfg-reconfig-refusal',
; which is never nil on a refusal; an accepted one stages a record in the one
; pending slot; uncertain is the store's own word, reported by the owner's
; existing outcome path and never inferred here.

(defun fn-ocfg-config-stamp (observation)
  ; Schema-0 configuration records have uint32 stamp fields, while the
  ; owner's clock uses milliseconds.  The durable record carries the ACL2
  ; seconds projection of that observation; no host clock conversion or
  ; alternate configuration timestamp exists.
  (declare (xargs :guard t))
  (fn-clock-observation (floor (nfix (fn-clock-monotonic observation)) 1000)
                        (floor (nfix (fn-clock-wall observation)) 1000)
                        (floor (nfix (fn-clock-wall-error observation)) 1000)
                        (fn-clock-has-wall observation)))

(defun fn-ocfg-reconfig-record (oc deltas)
  (declare (xargs :guard (fn-cfgp (fn-ocfg-config oc))))
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (node (fn-sn-node s)))
    (fn-cfg-record-make
     ; Configuration records live in their own durable directory.  Their
     ; sequence is therefore the prior configuration generation, exactly as
     ; fn-store-cfg-reconfigure constructs it; article-record count is a
     ; different coordinate and would reject a first live reconfiguration.
     (fn-cfg-generation (fn-ocfg-config oc))
     (fn-state-next-txid (fn-node-acceptance node))
     (+ 1 (fn-cfg-generation (fn-ocfg-config oc)))
     deltas
     (fn-ocfg-config-stamp (fn-own-clock o)))))

(defun fn-ocfg-delta-names-group (d name)
  (declare (xargs :guard t))
  (and (member-equal (fn-cfg-delta-kind d) '(:create-group :remove-group))
       (equal (fn-cfg-delta-a d) name)))

(defun fn-ocfg-deltas-touch-groupp (deltas name)
  (declare (xargs :guard t))
  (if (consp deltas)
      (or (fn-ocfg-delta-names-group (car deltas) name)
          (fn-ocfg-deltas-touch-groupp (cdr deltas) name))
    nil))

(defun fn-ocfg-group-pinned-by-readerp (deltas conns)
  ; The owner-side admissibility condition of design section 2.3: never
  ; retire or re-create a group a reader is standing in.  A reader pin is not
  ; durable state, so this condition never enters the record and replay never
  ; re-checks it.
  ;
  ; The selected group is THREE records in, not one.  A connection's session
  ; is an auth session over a peer session over the POST-composed reader
  ; session, and `fn-post-session-base' of the whole thing is the peer
  ; session, whose field 1 is the PEER NAME: this read the peer name where it
  ; meant the reader's group, so the condition was false of every reader and
  ; a reconfiguration could retire the group a reader was standing in.  The
  ; reach is now the named projection (books/nntp-auth.lisp).
  (declare (xargs :guard t))
  (if (consp conns)
      (or (and (fn-nntp-session-group
                (fn-auth-reader-session (fn-own-conn-session (car conns))))
               (fn-ocfg-deltas-touch-groupp
                deltas
                (fn-nntp-session-group
                 (fn-auth-reader-session (fn-own-conn-session (car conns))))))
          (fn-ocfg-group-pinned-by-readerp deltas (cdr conns)))
    nil))

(defun fn-ocfg-reconfig-okp (oc id deltas)
  (declare (xargs :guard (fn-cfgp (fn-ocfg-config oc))))
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o)))
    (and (fn-own-find-conn id (fn-own-conns o))
         (null (fn-own-pending o))
         (null (fn-ocfg-staged oc))
         (equal (fn-sf-phase (fn-sn-files s)) :ready)
         (fn-clock-observationp (fn-own-clock o))
         (fn-cfg-delta-listp deltas)
         (consp deltas)
         ; the requester composed against the generation that is still live
         (equal (fn-ocfg-conn-generation oc id)
                (fn-cfg-generation (fn-ocfg-config oc)))
         (fn-cnode-record-acceptablep (fn-ocfg-live-cnode oc)
                                      (fn-ocfg-reconfig-record oc deltas)
                                      (fn-cnode-line-ceiling))
         (not (fn-ocfg-group-pinned-by-readerp deltas (fn-own-conns o)))
         t)))

(defun fn-ocfg-reconfig-refusal (oc id deltas)
  ; A named reason, never nil when `fn-ocfg-reconfig-okp' is false.
  (declare (xargs :guard (fn-cfgp (fn-ocfg-config oc))))
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o)))
    (cond ((not (fn-own-find-conn id (fn-own-conns o))) :no-such-connection)
          ((not (fn-clock-observationp (fn-own-clock o))) :no-clock)
          ((or (fn-own-pending o) (fn-ocfg-staged oc)) :busy)
          ((not (equal (fn-sf-phase (fn-sn-files s)) :ready)) :not-ready)
          ((not (and (fn-cfg-delta-listp deltas) (consp deltas)))
           :malformed-delta)
          ((not (equal (fn-ocfg-conn-generation oc id)
                       (fn-cfg-generation (fn-ocfg-config oc))))
           :stale-generation)
          ((fn-ocfg-group-pinned-by-readerp deltas (fn-own-conns o))
           :group-pinned-by-reader)
          ((not (null (fn-node-stage (fn-sn-node (fn-own-store o)))))
           :group-staged)
          (t (or (fn-cfg-admissible-reason
                  (fn-cfg-value (fn-ocfg-config oc))
                  (+ 1 (fn-cfg-generation (fn-ocfg-config oc)))
                  (fn-own-clock o)
                  (fn-retain-reserved
                   (fn-node-retention (fn-sn-node (fn-own-store o))))
                  (fn-cnode-line-ceiling) deltas)
                 :record)))))

(defun fn-ocfg-reconfigure (oc id deltas)
  ; THE OWNER EVENT.  `(:reconfigure id deltas)': stage a configuration
  ; record in the one pending-transaction slot, exactly as `(:begin id)'
  ; stages a post.  Nothing becomes live here; `fn-ocfg-complete' publishes.
  (declare (xargs :guard (fn-cfgp (fn-ocfg-config oc))))
  (if (fn-ocfg-reconfig-okp oc id deltas)
      ; `staged' is the configuration transaction lock.  It is not an
      ; article-store pending record: the host persists this typed config
      ; record in the configuration journal, then reports :complete.  While
      ; it is held, fn-ocfg-step refuses :begin and :take below, so an article
      ; transaction cannot overlap the configuration generation.
      (fn-ocfg-make (fn-ocfg-owner oc)
                    (fn-ocfg-config oc)
                    (fn-ocfg-pins oc)
                    (fn-ocfg-reconfig-record oc deltas))
    oc))

; -----------------------------------------------------------------------------
; Completion publishes the staged record
;
; WHAT IS PUBLISHED IS WHAT RECOVERY REPLAYS.  The host calls `:complete'
; only after the staged record is durable in the configuration directory
; (host/owner-host.lisp `fn-owner-reconfigure-complete'), and at the next
; open `fn-owner-recover' replays that directory through
; `fn-cnode-config-replay', whose step on a configuration record is
; `fn-cnode-apply-config' over a configured node with no reservation and no
; stage.  So the live configuration after `:complete' is that step's
; configuration: `fn-cfg-apply-record' of the WHOLE record when the record
; is acceptable at reservation 0 (the gate replay applies), and the old
; configuration otherwise.  Never a prefix of the delta list.
;
; This used to be `(fn-cnode-config (fn-cnode-apply-config (fn-ocfg-live-cnode
; oc) record ...))', which gates on `fn-cnode-statep' of the LIVE node.  The
; live node's allocation domain and retention capacity are the store's
; recovery parameters (`fn-sn-groups', `fn-sn-capacity') and no live
; transition moves them, so after the first live `:create-group' or
; `:set-capacity' the live pair was no longer a `fn-cnode-statep' and every
; later completion kept the old configuration while the host had already
; made the record durable: a restart then recovered a generation the live
; owner never published.  Measured 2026-09-22 on the ground scenario in
; tests/acl2/owner-config-tests.lisp: the second of two live group
; creations violated `fn-cnode-apply-config''s guard at `:complete'.  The
; node half of that call was discarded here anyway; only its configuration
; was kept, and that half never depended on the live node.

(defun fn-ocfg-published-config (config record)
  (declare (xargs :guard t))
  (if (fn-cfg-record-acceptablep config record 0 (fn-cnode-line-ceiling))
      (fn-cfg-apply-record config record)
    config))

(defun fn-ocfg-complete (oc)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (let ((record (fn-ocfg-staged oc)))
    (if record
        ; The caller may use this arm only after the host has reported a
        ; durable config-journal write.  An uncertain write deliberately does
        ; not publish: the process must reopen and replay the observed prefix.
        (fn-ocfg-make
         (fn-ocfg-owner oc)
         (fn-ocfg-published-config (fn-ocfg-config oc) record)
         (fn-ocfg-pins oc) nil)
      (fn-ocfg-make (fn-own-complete (fn-ocfg-owner oc))
                    (fn-ocfg-config oc) (fn-ocfg-pins oc) nil))))

; -----------------------------------------------------------------------------
; The connection events that write a pin: open, advance, close.
;
; Every OTHER owner event leaves the table alone, which is the mechanism
; behind `fn-ocfg-pin-is-stable-without-advance' below.

(defun fn-ocfg-open (oc acfg)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (id (fn-own-next-id o))
         (opened (fn-own-open o acfg))
         (raw (cdr opened))
         (o2 (if (fn-own-find-conn id (fn-own-conns raw))
                 (fn-own-reader-context raw id (fn-ocfg-config oc))
               raw)))
    (cons (car opened)
          (fn-ocfg-make o2 (fn-ocfg-config oc)
                        (if (fn-own-find-conn id (fn-own-conns o2))
                            ; a new connection pins the LATEST configuration
                            (fn-ocfg-pin-add id (fn-ocfg-config oc)
                                             (fn-ocfg-pins oc))
                          (fn-ocfg-pins oc))
                        (fn-ocfg-staged oc)))))

(defun fn-ocfg-advance (oc id)
  (declare (xargs :guard t))
  (let ((o (fn-own-advance (fn-ocfg-owner oc) id)))
    (fn-ocfg-make o (fn-ocfg-config oc)
                  (if (fn-own-find-conn id (fn-own-conns o))
                      (fn-ocfg-pin-set id (fn-ocfg-config oc) (fn-ocfg-pins oc))
                    (fn-ocfg-pins oc))
                  (fn-ocfg-staged oc))))

(defun fn-ocfg-close (oc id)
  (declare (xargs :guard t))
  (fn-ocfg-make (fn-own-close (fn-ocfg-owner oc) id)
                (fn-ocfg-config oc)
                (fn-ocfg-pin-remove id (fn-ocfg-pins oc))
                (if (equal (fn-own-pending (fn-ocfg-owner oc)) id)
                    nil
                  (fn-ocfg-staged oc))))

; -----------------------------------------------------------------------------
; Owner operations which are not ordinary `fn-own-step' events still have to
; carry the configuration owner.  This is the single bridge used by the host:
; it retains a pin for every surviving connection, removes pins for a close or
; fault, and gives a newly opened connection the current live configuration.
; It is deliberately in ACL2, rather than a host-side mirror of the pin table.

(defun fn-ocfg-with-owner (oc owner)
  ; Reserved for raw owner transformations that preserve connection
  ; membership.  The host uses named fn-ocfg-open/read/fault transitions for
  ; membership changes, so this wrapper never reconstructs a second pin map.
  (declare (xargs :guard t))
  (fn-ocfg-make owner (fn-ocfg-config oc) (fn-ocfg-pins oc)
                (fn-ocfg-staged oc)))

(defun fn-ocfg-read (oc id octets)
  (declare (xargs :guard t))
  (let ((result (fn-own-read (fn-ocfg-owner oc) id octets)))
    (cons (car result) (fn-ocfg-with-owner oc (cdr result)))))

(defun fn-ocfg-read-step (oc id event)
  (declare (xargs :guard t))
  (let ((result (fn-own-read-step (fn-ocfg-owner oc) id event)))
    (cons (car result) (fn-ocfg-with-owner oc (cdr result)))))

(defun fn-ocfg-open-peer (oc peer acfg)
  (declare (xargs :guard t))
  (let ((result (fn-own-open-peer (fn-ocfg-owner oc) peer
                                  (fn-ocfg-config oc) acfg)))
    (cons (car result) (fn-ocfg-with-owner oc (cdr result)))))

(defun fn-ocfg-fault (oc id)
  (declare (xargs :guard t))
  (let ((result (fn-own-fault (fn-ocfg-owner oc) id)))
    (cons (car result)
          (fn-ocfg-make (cdr result) (fn-ocfg-config oc)
                        (fn-ocfg-pin-remove id (fn-ocfg-pins oc))
                        (fn-ocfg-staged oc)))))

(defun fn-ocfg-pass (oc event)
  ; Every owner event that touches no pin: the served port, the writer step,
  ; the store events, the clock.  The table goes through untouched.
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (fn-ocfg-with-owner oc (fn-own-step (fn-ocfg-owner oc) event)))

(defun fn-ocfg-step (oc event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (case (car event)
    (:open (cdr (fn-ocfg-open oc (cadr event))))
    (:advance (fn-ocfg-advance oc (car (cdr event))))
    (:close (fn-ocfg-close oc (car (cdr event))))
    (:octets (cdr (fn-ocfg-read oc (car (cdr event)) (car (cdr (cdr event))))))
    (:read (cdr (fn-ocfg-read-step oc (car (cdr event)) (car (cdr (cdr event))))))
    (:open-peer (cdr (fn-ocfg-open-peer oc (car (cdr event))
                                         (car (cdr (cdr (cdr event)))))))
    (:fault (cdr (fn-ocfg-fault oc (car (cdr event)))))
    (:reconfigure (fn-ocfg-reconfigure oc (car (cdr event)) (car (cdr (cdr event)))))
    (:complete (fn-ocfg-complete oc))
    (:begin (if (fn-ocfg-staged oc) oc (fn-ocfg-pass oc event)))
    (:take (if (fn-ocfg-staged oc) oc (fn-ocfg-pass oc event)))
    (otherwise (fn-ocfg-pass oc event))))

(defun fn-ocfg-run (oc events)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (if (consp events)
      (fn-ocfg-run (fn-ocfg-step oc (car events)) (cdr events))
    oc))

; -----------------------------------------------------------------------------
; LIST ACTIVE at the pin

(defun fn-ocfg-list-active (oc id)
  ; LIST ACTIVE answered from the connection's PINNED generation: the served
  ; table of the pin.  `fn-nntp-list-active' already takes its group list as
  ; an argument (books/nntp-responses.lisp); this is that argument supplied
  ; from the pin instead of from `(fn-state-groups archive)', which is the
  ; allocation domain and therefore lists retired names.
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
    (if conn
        (fn-nntp-result-effects
         (fn-nntp-list-active (fn-auth-reader-session (fn-own-conn-session conn))
                              (fn-own-conn-archive conn)
                              (fn-ocfg-served oc id)))
      nil)))

; -----------------------------------------------------------------------------
; KEYSTONES

; KEYSTONE.  A new connection pins the LIVE configuration: under
; `fn-ocfg-statep', if the open installs a connection at the identifier the
; owner was about to allocate, that connection's pinned configuration is the
; owner's live one.  Two hypotheses and no others: the state relation, and
; that the open was not refused.
;
; `fn-ocfg-pin-add' never overwrites, so the theorem is FALSE without the
; relation -- a stale pin at the identifier about to be allocated would
; survive the add and the new connection would serve the stale
; configuration.  It is the relation that rules that out, and not by
; assumption: `fn-ocfg-pins-pin-conns-only' turns a pin at `next-id' into an
; OPEN CONNECTION at `next-id', and `fn-own-relation' now carries
; `fn-own-ids-below-next-p' (books/owner-invariants.lisp), which says every
; open connection's identifier is strictly below `fn-own-next-id'.  That
; bound was already true of every reachable owner state --- `fn-own-open'
; and `fn-own-open-peer' are the only transitions that add a connection and
; both take `id = (fn-own-next-id o)' and write `(1+ (nfix id))' back --- so
; nothing about identifier allocation changed to close this; the bound was
; unstated, not false.  `fn-own-relation-has-no-connection-at-next-id' is
; the exported bridge.  Teeth: tests/acl2/owner-config-tests.lisp.
(local
 (defthm fn-ocfg-a-pinned-identifier-is-an-open-connection
   (implies (and (fn-ocfg-pins-pin-conns-only pins conns)
                 (fn-ocfg-pin-find id pins))
            (fn-own-find-conn id conns))
   ; :rule-classes nil, and not for hygiene: as a REWRITE rule this turns
   ; `(fn-own-find-conn id conns)' into T, which destroys the very hypothesis
   ; the :use below adds before `fn-own-relation-has-no-connection-at-next-id'
   ; can contradict it.  Measured: the keystone failed at `Subgoal 5''' with
   ; the pin in its hypotheses and the connection term gone.
   :rule-classes nil
   :hints (("Goal" :induct (fn-ocfg-pin-find id pins)
            :in-theory (enable (:d fn-ocfg-pin-find)
                               (:d fn-ocfg-pins-pin-conns-only))))))

; The `let' this used to carry was beta-equivalent and hid the hypothesis
; stack from every reader of the source, `tools/teeth_check.py' among them
; (`hypotheses_of' sees `let' and reports none), so the two hypotheses are
; spelled out.
(defthm fn-ocfg-open-pins-the-live-configuration
  (implies (and (fn-ocfg-statep oc)
                (fn-own-find-conn
                 (fn-own-next-id (fn-ocfg-owner oc))
                 (fn-own-conns (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))
           (equal (fn-ocfg-conn-config (cdr (fn-ocfg-open oc acfg))
                                       (fn-own-next-id (fn-ocfg-owner oc)))
                  (fn-ocfg-config oc)))
  :hints (("Goal" :in-theory (enable (:d fn-ocfg-open) (:d fn-ocfg-conn-config)
                                     (:d fn-ocfg-pin-add) (:d fn-ocfg-statep))
           :use ((:instance fn-ocfg-a-pinned-identifier-is-an-open-connection
                            (id (fn-own-next-id (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc))
                            (conns (fn-own-conns (fn-ocfg-owner oc))))))))

; Opening another connection never moves an existing pin.
(defthm fn-ocfg-open-keeps-every-existing-pin
  (implies (fn-ocfg-pin-find id (fn-ocfg-pins oc))
           (equal (fn-ocfg-pin-find id (fn-ocfg-pins (cdr (fn-ocfg-open oc acfg))))
                  (fn-ocfg-pin-find id (fn-ocfg-pins oc))))
  :hints (("Goal" :in-theory (enable (:d fn-ocfg-open)))))

; KEYSTONE.  EVERY CONNECTION BEGINS UNBOUND (PRF-049).
;
; host/owner-host.lisp fn-owner-open calls fn-ocfg-open for every accepted
; socket the host did not resolve to a source-address peer record.  If the
; open was accepted -- it returned a greeting -- the connection it installed
; at the identifier the owner allocated is a reader with no peer role, no
; authenticated subject, no cached AUTHINFO name, no TLS layer and no
; handshake in progress.  Nothing about the owner's other connections enters:
; a client whose previous connection logged in, bound a principal-derived
; peer role (books/nntp-auth.lisp
; fn-auth-step-binds-a-peer-role-only-by-a-principal-login) and then dropped,
; reconnects as a reader and must log in again for the role.
;
; One hypothesis, and without it the statement fails: an owner at its
; connection bound refuses the open and installs nothing, so no connection
; sits at the identifier (tests/acl2/owner-config-tests.lisp).
(defthm fn-ocfg-open-begins-unbound
  (implies (car (fn-ocfg-open oc acfg))
           (and (fn-own-find-conn
                 (fn-own-next-id (fn-ocfg-owner oc))
                 (fn-own-conns (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg)))))
                (not (fn-auth-session-peer
                      (fn-own-conn-session
                       (fn-own-find-conn
                        (fn-own-next-id (fn-ocfg-owner oc))
                        (fn-own-conns
                         (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))))
                (not (fn-auth-session-subject
                      (fn-own-conn-session
                       (fn-own-find-conn
                        (fn-own-next-id (fn-ocfg-owner oc))
                        (fn-own-conns
                         (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))))
                (not (fn-auth-session-pending
                      (fn-own-conn-session
                       (fn-own-find-conn
                        (fn-own-next-id (fn-ocfg-owner oc))
                        (fn-own-conns
                         (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))))
                (not (fn-auth-session-tlsp
                      (fn-own-conn-session
                       (fn-own-find-conn
                        (fn-own-next-id (fn-ocfg-owner oc))
                        (fn-own-conns
                         (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))))
                (not (fn-auth-session-handshakingp
                      (fn-own-conn-session
                       (fn-own-find-conn
                        (fn-own-next-id (fn-ocfg-owner oc))
                        (fn-own-conns
                         (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable (:d fn-ocfg-open) (:d fn-own-open)
                              (:d fn-own-reader-context) (:d fn-served-open) (:d fn-own-set-conns) (:d fn-auth-with-base)
                              (:d fn-auth-open-session)
                              (:d fn-peer-open-session)))))

; KEYSTONE.  A RECONFIGURATION NEVER CHANGES WHAT AN OPEN CONNECTION SERVES.
; Staging and publishing a configuration record moves the owner's live
; configuration and leaves every pin, and therefore every served table,
; exactly where it was -- including the pin of the connection that asked for
; the reconfiguration.
(defthm fn-ocfg-reconfiguration-never-changes-what-an-open-connection-serves
  (equal (fn-ocfg-served (fn-ocfg-complete (fn-ocfg-reconfigure oc other deltas)) id)
         (fn-ocfg-served oc id))
  :hints (("Goal" :in-theory (enable (:d fn-ocfg-reconfigure) (:d fn-ocfg-complete)
                                     (:d fn-ocfg-served) (:d fn-ocfg-conn-config)))))

; The pin moves only at `(:advance id)' -- and at `(:close id)', which
; removes it.  Across any other event list the connection keeps the
; configuration it opened at.
; `(car (car events))' and `(car (cdr (car events)))' under `:guard t' owe
; `(implies (not (consp x)) (equal x nil))' of the EVENT, which is false at
; `(list 3)'; the same defect the four accessors had.  The `mbe' leaves the
; :logic term unchanged, so `fn-ocfg-pin-is-stable-without-advance' below
; still unfolds to the same body.
(defun fn-ocfg-repins-forp (id events)
  (declare (xargs :guard t))
  (if (consp events)
      (or (and (member-equal (mbe :logic (car (car events))
                                  :exec (fn-ag-car (fn-ag-car events)))
                             '(:advance :close :fault))
               (equal (mbe :logic (car (cdr (car events)))
                           :exec (fn-ag-car (fn-ag-cdr (fn-ag-car events))))
                      id))
          (fn-ocfg-repins-forp id (cdr events)))
    nil))

(local (defthm fn-ocfg-step-keeps-other-pins
  (implies (and (fn-ocfg-pin-find id (fn-ocfg-pins oc))
                (not (and (member-equal (car event) '(:advance :close :fault))
                          (equal (car (cdr event)) id))))
           (equal (fn-ocfg-pin-find id (fn-ocfg-pins (fn-ocfg-step oc event)))
                  (fn-ocfg-pin-find id (fn-ocfg-pins oc))))
  :hints (("Goal" :in-theory (e/d ((:d fn-ocfg-step) (:d fn-ocfg-advance)
                                   (:d fn-ocfg-close) (:d fn-ocfg-pass)
                                   (:d fn-ocfg-reconfigure) (:d fn-ocfg-complete))
                                  (fn-own-step fn-own-advance fn-own-close
                                   fn-own-open fn-own-complete fn-own-begin))))))

; KEYSTONE.  Every connection keeps the configuration generation it opened
; at, for as long as it is not advanced.
(defthm fn-ocfg-pin-is-stable-without-advance
  (implies (and (fn-ocfg-pin-find id (fn-ocfg-pins oc))
                (not (fn-ocfg-repins-forp id events)))
           (equal (fn-ocfg-pin-find id (fn-ocfg-pins (fn-ocfg-run oc events)))
                  (fn-ocfg-pin-find id (fn-ocfg-pins oc))))
  :hints (("Goal" :induct (fn-ocfg-run oc events)
           :in-theory (e/d ((:d fn-ocfg-run) (:d fn-ocfg-repins-forp))
                           (fn-ocfg-step)))))

; KEYSTONE.  Advancing observes the live configuration: under
; `fn-ocfg-statep', a connection that survives its advance is re-pinned to
; the owner's live configuration.  This is application liveness under the
; owner's own scheduling, not a timing claim.  Two hypotheses and no others:
; the state relation, and that the advance kept the connection.
;
; `fn-ocfg-pin-set' REPLACES and never adds --- it returns `nil' on an empty
; table --- so `fn-ocfg-pin-find-of-pin-set-same' above needs a pin at `id'
; in the PRE-STATE table, and the conclusion is false without one (the
; re-pin silently does nothing and the connection keeps serving whatever the
; table said).  `fn-ocfg-statep' carries exactly that through
; `fn-ocfg-conns-pinnedp': every open connection has a pin.  The advance is
; on the post-state, so the two local lemmas below carry it back --- a
; connection present after the advance was present before it
; (`fn-own-advance-finds-only-what-it-had', books/owner-invariants.lisp),
; and an open connection has a pin.  The hypothesis cannot be moved to the
; pre-state: `fn-own-advance' DROPS a connection whose re-pinned session
; leaves `fn-own-conn-boundedp', and then `fn-ocfg-advance' leaves the table
; alone and the old pin stands.  Teeth: tests/acl2/owner-config-tests.lisp.
(local
 (defthm fn-ocfg-an-open-connection-has-a-pin
   (implies (and (fn-ocfg-conns-pinnedp conns pins)
                 (fn-own-find-conn id conns))
            (fn-ocfg-pin-find id pins))
   :rule-classes nil
   :hints (("Goal" :induct (fn-own-find-conn id conns)
            :in-theory (enable (:d fn-ocfg-conns-pinnedp))))))

(defthm fn-ocfg-advance-observes-the-live-configuration
  (implies (and (fn-ocfg-statep oc)
                (fn-own-find-conn id (fn-own-conns
                                      (fn-own-advance (fn-ocfg-owner oc) id))))
           (equal (fn-ocfg-conn-config (fn-ocfg-advance oc id) id)
                  (fn-ocfg-config oc)))
  :hints (("Goal" :in-theory (e/d ((:d fn-ocfg-advance) (:d fn-ocfg-conn-config)
                                   (:d fn-ocfg-statep))
                                  (fn-own-advance))
           :use ((:instance fn-own-advance-finds-only-what-it-had
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-ocfg-an-open-connection-has-a-pin
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (pins (fn-ocfg-pins oc)))))))

; KEYSTONE.  LIST ACTIVE lists the served table of the connection's
; generation.  `fn-nntp-list-active' renders exactly the group list it is
; given, and the list it is given here is the pin's served table --
; `fn-cfg-group-names' at the pinned generation -- never the allocation
; domain `(fn-state-groups archive)'.
(defthm fn-ocfg-list-active-lists-the-pinned-served-table
  (implies (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))
           (equal (fn-ocfg-list-active oc id)
                  (fn-nntp-result-effects
                   (fn-nntp-list-active
                    (fn-auth-reader-session
                     (fn-own-conn-session
                      (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                    (fn-own-conn-archive
                     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                    (fn-cfg-group-names
                     (fn-cfg-value (fn-ocfg-conn-config oc id))
                     (fn-cfg-generation (fn-ocfg-conn-config oc id)))))))
  :hints (("Goal" :in-theory (enable (:d fn-ocfg-list-active) (:d fn-ocfg-served)
                                     (:d fn-cnode-served-of)))))

; A refusal changes nothing, and names a reason.
(defthm fn-ocfg-refused-reconfiguration-changes-nothing
  (implies (not (fn-ocfg-reconfig-okp oc id deltas))
           (equal (fn-ocfg-reconfigure oc id deltas) oc))
  :hints (("Goal" :in-theory (enable (:d fn-ocfg-reconfigure)))))

; -----------------------------------------------------------------------------
; THE TWO HEADLINE THEOREMS of specs/reconfiguration.md (plan T8).
;
; The subject of both is the function the host calls.  host/owner-host.lisp
; `fn-owner-step' calls `fn-ocfg-step' (the line under `(defun
; fn-owner-step'), and the live administrative arm drives it with exactly
; three events under the owner mutex (host/native/admin.lisp
; `fnn-owner-live-admin-serialized'): `(:reconfigure cid deltas)' through
; `fn-owner-reconfigure-deltas', `(:close cid)' through `fn-owner-close',
; and, after the immutable publisher reports the record durable,
; `(:complete)' through `fn-owner-reconfigure-complete'.  Recovery is
; `fn-owner-recover', which replays the configuration directory through
; `fn-cnode-config-replay' and installs exactly that configuration with no
; staged record: the base case of the second theorem's hypothesis stack.
;
; The recovery half is proved with the record codec CLOSED: nothing below
; enables `fn-record-codec-vocabulary' or `fn-record-record-vocabulary'.  The
; replay loop, the journal-record recognizer and the configured-node
; transition are opened in the hints of the lemmas that step them.

; The replay-side vocabulary.  Admission of a configuration record depends on
; the reservation total only through `:set-capacity''s floor, so a record the
; live owner admitted under its real reservation total is admitted by the
; configuration-only replay, whose node reserves nothing.

(local (defthm fn-ocfg-delta-reason-at-zero
  (implies (not (fn-cfg-delta-reason v gen stamp reserved ceiling d))
           (not (fn-cfg-delta-reason v gen stamp 0 ceiling d)))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason)))))

(defthm fn-ocfg-admissible-at-any-reservation-is-admissible-at-zero
  (implies (not (fn-cfg-admissible-reason v gen stamp reserved ceiling deltas))
           (not (fn-cfg-admissible-reason v gen stamp 0 ceiling deltas)))
  :hints (("Goal" :induct (fn-cfg-admissible-reason v gen stamp reserved ceiling deltas)
           :in-theory (e/d (fn-cfg-admissible-reason) (fn-cfg-delta-reason fn-cfg-apply-delta)))))

(defthm fn-ocfg-acceptable-record-is-acceptable-at-zero-reservation
  (implies (fn-cfg-record-acceptablep cfg r reserved ceiling)
           (fn-cfg-record-acceptablep cfg r 0 ceiling))
  :hints (("Goal" :in-theory (e/d (fn-cfg-record-acceptablep fn-cfg-admissiblep)
                                  (fn-cfgp fn-cfg-recordp))
           :use ((:instance fn-ocfg-admissible-at-any-reservation-is-admissible-at-zero
                            (v (fn-cfg-value cfg)) (gen (fn-cfg-record-generation r))
                            (stamp (fn-cfg-record-stamp r))
                            (deltas (fn-cfg-record-change r)))))))


; What a configuration-only replay carries: a configured node with nothing
; reserved and nothing staged, whose generation is the replay's next
; journal sequence.  That last conjunct is why the live owner's record,
; whose sequence is the live generation (`fn-ocfg-reconfig-record'), lands
; exactly where the replay expects its next record.

(defun fn-ocfg-replay-cnode-okp (cn seq)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-cnode-statep cn)
       (equal (fn-retain-reserved (fn-node-retention (fn-cnode-node cn))) 0)
       (null (fn-node-stage (fn-cnode-node cn)))
       (equal (fn-cfg-generation (fn-cnode-config cn)) seq)))

(defthm fn-ocfg-replay-cnode-okp-of-apply-config
  (implies (and (fn-ocfg-replay-cnode-okp cn seq)
                (fn-cnode-record-acceptablep cn r ceiling))
           (fn-ocfg-replay-cnode-okp (fn-cnode-apply-config cn r ceiling) (+ 1 seq)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-apply-config)
                                  (fn-cnode-statep fn-cnode-record-acceptablep fn-cfg-apply-record))
           :use ((:instance fn-cnode-apply-config-preserves-state (record r))
                 (:instance fn-cnode-apply-config-bumps-the-generation (record r))))))

(defun fn-ocfg-cr-induct (cn ceiling records expected)
  (declare (xargs :verify-guards nil))
  (if (consp records)
      (fn-ocfg-cr-induct (fn-cnode-apply-config cn (car records) ceiling)
                         ceiling (cdr records) (+ 1 expected))
    (list cn ceiling expected)))

(defthm fn-ocfg-config-replay-loop-keeps-okp
  (implies (and (fn-ocfg-replay-cnode-okp cn expected)
                (equal (fn-replay-result-kind
                        (fn-cnode-replay-loop cn ceiling (fn-cnode-config-jrecs records) expected))
                       :ok))
           (fn-ocfg-replay-cnode-okp
            (fn-replay-result-node
             (fn-cnode-replay-loop cn ceiling (fn-cnode-config-jrecs records) expected))
            (fn-replay-result-sequence
             (fn-cnode-replay-loop cn ceiling (fn-cnode-config-jrecs records) expected))))
  :hints (("Goal" :induct (fn-ocfg-cr-induct cn ceiling records expected)
           :in-theory (e/d (fn-cnode-replay-loop fn-cnode-config-jrecs)
                           (fn-ocfg-replay-cnode-okp fn-cnode-apply-config
                            fn-cnode-record-acceptablep fn-jrec-p fn-cnode-apply-record)))
          ("Subgoal *1/1" :use ((:instance fn-ocfg-replay-cnode-okp-of-apply-config
                                           (r (car records)) (seq expected))))))

(defthm fn-ocfg-config-jrecs-of-append
  (equal (fn-cnode-config-jrecs (append a b))
         (append (fn-cnode-config-jrecs a) (fn-cnode-config-jrecs b)))
  :hints (("Goal" :in-theory (enable fn-cnode-config-jrecs))))
(defthm fn-ocfg-true-listp-of-config-jrecs
  (true-listp (fn-cnode-config-jrecs a))
  :hints (("Goal" :in-theory (enable fn-cnode-config-jrecs))))
(defthm fn-ocfg-initial-replay-cnode-okp
  (fn-ocfg-replay-cnode-okp (fn-cnode-initial (fn-cfg-initial)) 0))
(defthm fn-ocfg-config-replay-okp
  (implies (equal (fn-replay-result-kind (fn-cnode-config-replay h)) :ok)
           (fn-ocfg-replay-cnode-okp
            (fn-replay-result-node (fn-cnode-config-replay h))
            (fn-replay-result-sequence (fn-cnode-config-replay h))))
  :hints (("Goal" :in-theory (e/d (fn-cnode-config-replay fn-cnode-replay)
                                  (fn-ocfg-replay-cnode-okp fn-cnode-initial fn-cfg-initial
                                   fn-cnode-statep))
           :use ((:instance fn-ocfg-config-replay-loop-keeps-okp
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (ceiling (fn-cnode-line-ceiling))
                            (records h) (expected 0))))))

(local (defthm one-step
  (implies (and (fn-ocfg-replay-cnode-okp cn seq)
                (fn-cfg-record-acceptablep (fn-cnode-config cn) r reserved ceiling)
                (equal (fn-cfg-record-sequence r) seq))
           (equal (fn-cnode-replay-loop cn ceiling (fn-cnode-config-jrecs (list r)) seq)
                  (fn-replay-ok (fn-cnode-apply-config cn r ceiling) (+ 1 seq))))
  :hints (("Goal" :in-theory (e/d (fn-cnode-replay-loop fn-cnode-config-jrecs
                                   fn-cnode-record-acceptablep fn-jrec-p
                                   fn-ocfg-replay-cnode-okp fn-cfgp)
                                  (fn-cnode-apply-config fn-cnode-statep
                                   fn-cfg-record-acceptablep fn-cfg-valuep fn-cfg-recordp))
           :use ((:instance fn-ocfg-admissible-at-any-reservation-is-admissible-at-zero
                            (v (fn-cfg-value (fn-cnode-config cn)))
                            (gen (fn-cfg-record-generation r))
                            (stamp (fn-cfg-record-stamp r))
                            (deltas (fn-cfg-record-change r))))
           :expand ((:free (x) (fn-cfg-record-acceptablep (fn-cnode-config cn) r x ceiling))
                    (:free (x) (fn-cfg-admissiblep (fn-cfg-value (fn-cnode-config cn))
                                                   (fn-cfg-record-generation r)
                                                   (fn-cfg-record-stamp r) x ceiling
                                                   (fn-cfg-record-change r))))))))
(local (defthm one-step-config
  (implies (and (fn-ocfg-replay-cnode-okp cn seq)
                (fn-cfg-record-acceptablep (fn-cnode-config cn) r reserved ceiling))
           (equal (fn-cnode-config (fn-cnode-apply-config cn r ceiling))
                  (fn-cfg-apply-record (fn-cnode-config cn) r)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-apply-config fn-cnode-record-acceptablep
                                   fn-ocfg-replay-cnode-okp)
                                  (fn-cnode-statep fn-cfg-record-acceptablep fn-cfg-apply-record))
           :use ((:instance fn-ocfg-acceptable-record-is-acceptable-at-zero-reservation (cfg (fn-cnode-config cn))))))))
(local (defthm one-step-general
  (implies (and (fn-ocfg-replay-cnode-okp m s)
                (fn-cfg-record-acceptablep (fn-cnode-config m) r reserved ceiling)
                (equal (fn-cfg-record-sequence r) (fn-cfg-generation (fn-cnode-config m))))
           (and (equal (fn-replay-result-kind
                        (fn-cnode-replay-loop m ceiling (fn-cnode-config-jrecs (list r)) s))
                       :ok)
                (equal (fn-cnode-config
                        (fn-replay-result-node
                         (fn-cnode-replay-loop m ceiling (fn-cnode-config-jrecs (list r)) s)))
                       (fn-cfg-apply-record (fn-cnode-config m) r))))
  :hints (("Goal" :in-theory (disable fn-cnode-replay-loop fn-cnode-config-jrecs
                                      fn-cnode-apply-config fn-cfg-record-acceptablep
                                      fn-cfg-apply-record)
           :use ((:instance one-step (cn m) (seq s))
                 (:instance one-step-config (cn m) (seq s)))
           :expand ((fn-ocfg-replay-cnode-okp m s))))))
(defthm fn-ocfg-config-replay-of-one-more-record
  (implies (and (equal (fn-replay-result-kind (fn-cnode-config-replay h)) :ok)
                (fn-cfg-record-acceptablep
                 (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay h)))
                 r reserved (fn-cnode-line-ceiling))
                (equal (fn-cfg-record-sequence r)
                       (fn-cfg-generation
                        (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay h))))))
           (and (equal (fn-replay-result-kind (fn-cnode-config-replay (append h (list r)))) :ok)
                (equal (fn-cnode-config
                        (fn-replay-result-node (fn-cnode-config-replay (append h (list r)))))
                       (fn-cfg-apply-record
                        (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay h)))
                        r))))
  :hints (("Goal" :in-theory (e/d (fn-cnode-config-replay fn-cnode-replay)
                                  (fn-cnode-replay-loop fn-cnode-initial fn-cfg-initial
                                   fn-cnode-statep fn-ocfg-replay-cnode-okp
                                   fn-cfg-record-acceptablep fn-cfg-apply-record
                                   fn-cnode-apply-config fn-cnode-config-jrecs
                                   one-step one-step-config one-step-general
                                   fn-ocfg-config-replay-okp
                                   fn-cnode-replay-loop-splits-at-any-prefix))
           :use ((:instance fn-ocfg-config-replay-okp)
                 (:instance one-step-general
                            (m (fn-replay-result-node (fn-cnode-config-replay h)))
                            (s (fn-replay-result-sequence (fn-cnode-config-replay h)))
                            (ceiling (fn-cnode-line-ceiling)))
                 (:instance fn-cnode-replay-loop-splits-at-any-prefix
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (ceiling (fn-cnode-line-ceiling))
                            (a (fn-cnode-config-jrecs h))
                            (b (fn-cnode-config-jrecs (list r)))
                            (expected 0))))))


; KEYSTONE (headline 1).  NO READER OBSERVES A HALF CHANGE.  The two owner
; events a live reconfiguration consists of, `(:reconfigure other deltas)'
; and `(:complete)', leave the owner itself -- every open connection's
; record, hence its session, its pinned archive and every reply it will give
; to any input -- and every configuration pin exactly as they were; staging
; does not move the live configuration; and publication moves it to
; `fn-ocfg-published-config' of the staged record, which is the old
; configuration or `fn-cfg-apply-record' of the WHOLE record and nothing in
; between.  One hypothesis: that something was staged, which is the
; condition under which the host calls `(:complete)' at all
; (`fn-owner-reconfigure-complete' refuses otherwise); without it
; `(:complete)' is the article completion `fn-own-complete', which moves
; the owner.  The pin moves only at the connection's own `(:advance id)',
; `(:close id)' or `(:fault id)': `fn-ocfg-pin-is-stable-without-advance'
; above, over any finite list of `fn-ocfg-step' events, is the other half
; of the headline and is cited with this one.

(defthm fn-ocfg-no-reader-observes-a-half-change
  (implies (fn-ocfg-staged (fn-ocfg-step oc (list :reconfigure other deltas)))
           (let* ((staged (fn-ocfg-step oc (list :reconfigure other deltas)))
                  (published (fn-ocfg-step staged (list :complete))))
             (and (equal (fn-ocfg-owner published) (fn-ocfg-owner oc))
                  (equal (fn-ocfg-pins published) (fn-ocfg-pins oc))
                  (equal (fn-ocfg-config staged) (fn-ocfg-config oc))
                  (equal (fn-ocfg-config published)
                         (fn-ocfg-published-config (fn-ocfg-config oc)
                                                   (fn-ocfg-staged staged))))))
  :hints (("Goal" :in-theory (enable (:d fn-ocfg-step) (:d fn-ocfg-reconfigure)
                                     (:d fn-ocfg-complete)))))


; KEYSTONE (headline 2).  A CRASH AT ANY INSTANT RECOVERS THE LIVE
; GENERATION, AND NEVER A PARTIAL ONE.  Hypotheses: nothing is staged, and the
; durable configuration history replays (`fn-cnode-config-replay', the
; function `fn-owner-recover' calls) to the owner's live configuration --
; both established by `fn-owner-recover' and re-established by the
; theorem's own last three conjuncts, so the statement chains across every
; later live reconfiguration.  Over the host's exact event sequence
; (reconfigure, close the private connection, complete):
;
;   before the record is durable, the durable history still replays to
;   the live configuration, which staging did not move;
;
;   once the record is durable -- whether or not `(:complete)' has run --
;   the durable history (the old one with the staged record appended, or
;   the old one when nothing was staged) replays :ok, to exactly the
;   configuration `(:complete)' publishes, whose generation is the one the
;   last durable record names.
;
; A-DURABILITY enters where it always does: that a record the immutable
; publisher reported :durable is in the directory the next open reads, and
; that a torn staging file is not (the sweep of `.stage-' names).  An
; uncertain publication fences the owner and forces the reopen whose result
; is one of the two histories above.

(defthm fn-ocfg-crash-at-any-instant-recovers-the-live-generation
  (implies (and (not (fn-ocfg-staged oc))
                (equal (fn-replay-result-kind (fn-cnode-config-replay history)) :ok)
                (equal (fn-cnode-config
                        (fn-replay-result-node (fn-cnode-config-replay history)))
                       (fn-ocfg-config oc)))
           (let* ((staged (fn-ocfg-step (fn-ocfg-step oc (list :reconfigure id deltas))
                                       (list :close id)))
                  (record (fn-ocfg-staged staged))
                  (published (fn-ocfg-step staged (list :complete)))
                  (durable (if record (append history (list record)) history)))
             (and (equal (fn-cnode-config
                          (fn-replay-result-node (fn-cnode-config-replay history)))
                         (fn-ocfg-config staged))
                  (equal (fn-replay-result-kind (fn-cnode-config-replay durable)) :ok)
                  (equal (fn-cnode-config
                          (fn-replay-result-node (fn-cnode-config-replay durable)))
                         (fn-ocfg-config published))
                  (equal (fn-cfg-generation (fn-ocfg-config published))
                         (if record
                             (fn-cfg-record-generation record)
                           (fn-cfg-generation (fn-ocfg-config oc))))
                  (not (fn-ocfg-staged published)))))
  :hints (("Goal" :in-theory (e/d ((:d fn-ocfg-step) (:d fn-ocfg-reconfigure)
                                   (:d fn-ocfg-complete) (:d fn-ocfg-reconfig-okp) (:d fn-ocfg-close)
                                   (:d fn-ocfg-reconfig-record)
                                   (:d fn-ocfg-published-config)
                                   (:d fn-ocfg-live-cnode)
                                   fn-cnode-record-acceptablep)
                                  (fn-cfg-record-acceptablep fn-cfg-apply-record
                                   fn-cnode-config-replay fn-own-complete fn-own-close
                                   fn-ocfg-acceptable-record-is-acceptable-at-zero-reservation))
           :use ((:instance fn-ocfg-acceptable-record-is-acceptable-at-zero-reservation
                            (cfg (fn-ocfg-config oc))
                            (r (fn-ocfg-reconfig-record oc deltas))
                            (reserved (fn-retain-reserved
                                       (fn-node-retention
                                        (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))))
                            (ceiling 510))
                 (:instance fn-ocfg-config-replay-of-one-more-record
                            (h history)
                            (r (fn-ocfg-reconfig-record oc deltas))
                            (reserved (fn-retain-reserved
                                       (fn-node-retention
                                        (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))))))))

; -----------------------------------------------------------------------------
; OPEN, recorded rather than claimed (specs/reconfiguration.md section 8).
;
; 1. THE WIRE.  `fn-ocfg-list-active' is not the function the host calls.
;    The served port is `fn-own-read' -> `fn-served-step' ->
;    `fn-served-dispatch' -> `fn-nntp-dispatch', and `fn-nntp-dispatch'
;    supplies `(fn-state-groups archive)' -- the allocation domain -- at
;    books/nntp-responses.lisp lines 225, 308 and 319.  The equating theorem
;    the assurance rules require,
;
;      (defthm fn-ocfg-served-port-answers-list-active-at-the-pin
;        (implies (and (fn-ocfg-statep oc)
;                      (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
;                 (equal (car (fn-own-read-step (fn-ocfg-owner oc) id
;                                               *fn-nntp-list-active-event*))
;                        (fn-ocfg-list-active oc id))))
;
;    is FALSE today and is not stated as a theorem here.  It becomes true
;    when the NNTP cluster threads a served table through
;    `fn-served-conn'/`fn-nntp-dispatch' beside the archive; that is one
;    argument on three functions and is posted on the board as the R5 wire
;    seam.  Until then the domain is what a reader sees, as
;    specs/reconfiguration.md section 8 item (3) already records.
;
; 2. RECOVERY: CLOSED at the configuration level by
;    `fn-ocfg-crash-at-any-instant-recovers-the-live-generation' above, over
;    `fn-cnode-config-replay', which is what `fn-owner-recover' replays.
;    `fn-own-reopen' still replays the article history only; the owner's
;    reopen is the host's process restart, not a model event.
;
; 3. THE LIVE NODE DOES NOT ADOPT A NEW DOMAIN OR CAPACITY.  Publication
;    moves the configuration and nothing else: the store's allocation
;    domain `fn-sn-groups' and capacity `fn-sn-capacity' are the recovery
;    parameters, `fn-own-relation' ties every connection's pinned archive to
;    them, and no owner transition changes them.  So a group created live is
;    in the published served table (and in the injection configuration
;    `fn-own-configure' is refreshed with) but not in the acceptance state's
;    group list: GROUP and LIST ACTIVE on any connection answer from that
;    list, and the node's prepare refuses the group, until a restart
;    replays the configuration first.  A capacity change likewise reaches
;    the retention ledger only at restart.  Closing this is an owner and
;    store cluster step (a per-connection domain in `fn-own-conn-okp', and a
;    store re-parameterisation proved against `fn-snt-relation'), not an
;    owner-config one.

; -----------------------------------------------------------------------------
; Export theory.

(deftheory fn-ocfg-vocabulary
  '((:d fn-ocfg-pin-find) (:d fn-ocfg-pin-add) (:d fn-ocfg-pin-set)
    (:d fn-ocfg-pin-remove) (:d fn-ocfg-conn-config) (:d fn-ocfg-conn-generation)
    (:d fn-ocfg-served) (:d fn-ocfg-pins-okp) (:d fn-ocfg-conns-pinnedp)
    (:d fn-ocfg-pins-pin-conns-only) (:d fn-ocfg-statep) (:d fn-ocfg-live-cnode)
    (:d fn-ocfg-config-stamp) (:d fn-ocfg-reconfig-record) (:d fn-ocfg-delta-names-group)
    (:d fn-ocfg-deltas-touch-groupp) (:d fn-ocfg-group-pinned-by-readerp)
    (:d fn-ocfg-reconfig-okp) (:d fn-ocfg-reconfig-refusal)
    (:d fn-ocfg-reconfigure) (:d fn-ocfg-published-config) (:d fn-ocfg-complete)
    (:d fn-ocfg-open) (:d fn-ocfg-replay-cnode-okp)
    (:d fn-ocfg-advance) (:d fn-ocfg-close) (:d fn-ocfg-pass) (:d fn-ocfg-step)
    (:d fn-ocfg-run) (:d fn-ocfg-list-active) (:d fn-ocfg-repins-forp)))

(in-theory (disable fn-ocfg-vocabulary))
