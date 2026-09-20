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
(include-book "owner-invariants")
(include-book "config-stream")

; -----------------------------------------------------------------------------
; The record

(defun fn-ocfg-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))
(defun fn-ocfg-owner (x)
  (declare (xargs :guard t))
  (car x))
(defun fn-ocfg-config (x)
  (declare (xargs :guard t))
  (car (cdr x)))
(defun fn-ocfg-pins (x)
  (declare (xargs :guard t))
  (car (cdr (cdr x))))
(defun fn-ocfg-staged (x)
  (declare (xargs :guard t))
  (car (cdr (cdr (cdr x)))))
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
; new identifier and provably leaves every existing pin alone, with no
; freshness hypothesis to discharge.  Only `fn-ocfg-pin-set' replaces, and
; only `(:advance id)' calls it.

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

(defun fn-ocfg-reconfig-record (oc deltas)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (node (fn-sn-node s)))
    (fn-cfg-record-make
     ; The sequence is the position in the UNIFIED stream
     ; (books/config-stream.lisp), so that replay re-checks this record at
     ; the node the earlier article records produced.
     (len (fn-sf-records (fn-sn-files s)))
     (fn-state-next-txid (fn-node-acceptance node))
     (+ 1 (fn-cfg-generation (fn-ocfg-config oc)))
     deltas
     (fn-own-clock o))))

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
  (declare (xargs :guard t))
  (if (consp conns)
      (or (and (fn-nntp-session-group
                (fn-post-session-base (fn-own-conn-session (car conns))))
               (fn-ocfg-deltas-touch-groupp
                deltas
                (fn-nntp-session-group
                 (fn-post-session-base (fn-own-conn-session (car conns))))))
          (fn-ocfg-group-pinned-by-readerp deltas (cdr conns)))
    nil))

(defun fn-ocfg-reconfig-okp (oc id deltas)
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
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
          ((consp (fn-node-stage (fn-sn-node (fn-own-store o)))) :group-staged)
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
  (declare (xargs :guard t))
  (if (fn-ocfg-reconfig-okp oc id deltas)
      (fn-ocfg-make (fn-own-begin (fn-ocfg-owner oc) id)
                    (fn-ocfg-config oc)
                    (fn-ocfg-pins oc)
                    (fn-ocfg-reconfig-record oc deltas))
    oc))

; -----------------------------------------------------------------------------
; Completion publishes the staged record

(defun fn-ocfg-complete (oc)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (let* ((o (fn-ocfg-owner oc))
         (next (fn-own-complete o))
         (record (fn-ocfg-staged oc)))
    (if (equal next o)
        oc
      (if (null record)
          (fn-ocfg-make next (fn-ocfg-config oc) (fn-ocfg-pins oc) nil)
        (fn-ocfg-make next
                      (fn-cnode-config
                       (fn-cnode-apply-config (fn-ocfg-live-cnode oc) record
                                              (fn-cnode-line-ceiling)))
                      (fn-ocfg-pins oc)
                      nil)))))

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
         (o2 (cdr opened)))
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

(defun fn-ocfg-pass (oc event)
  ; Every owner event that touches no pin: the served port, the writer step,
  ; the store events, the clock.  The table goes through untouched.
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (fn-ocfg-make (fn-own-step (fn-ocfg-owner oc) event)
                (fn-ocfg-config oc) (fn-ocfg-pins oc) (fn-ocfg-staged oc)))

(defun fn-ocfg-step (oc event)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (case (car event)
    (:open (cdr (fn-ocfg-open oc (cadr event))))
    (:advance (fn-ocfg-advance oc (car (cdr event))))
    (:close (fn-ocfg-close oc (car (cdr event))))
    (:reconfigure (fn-ocfg-reconfigure oc (car (cdr event)) (car (cdr (cdr event)))))
    (:complete (fn-ocfg-complete oc))
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
         (fn-nntp-list-active (fn-post-session-base (fn-own-conn-session conn))
                              (fn-own-conn-archive conn)
                              (fn-ocfg-served oc id)))
      nil)))

; -----------------------------------------------------------------------------
; KEYSTONES

; A new connection pins the latest configuration.
(defthm fn-ocfg-open-pins-the-live-configuration
  (let ((oc2 (cdr (fn-ocfg-open oc acfg))))
    (implies (fn-own-find-conn (fn-own-next-id (fn-ocfg-owner oc))
                               (fn-own-conns (fn-ocfg-owner oc2)))
             (equal (fn-ocfg-conn-config oc2 (fn-own-next-id (fn-ocfg-owner oc)))
                    (fn-ocfg-config oc))))
  :hints (("Goal" :in-theory (enable (:d fn-ocfg-open) (:d fn-ocfg-conn-config)
                                     (:d fn-ocfg-pin-add)))))

; Opening another connection never moves an existing pin.
(defthm fn-ocfg-open-keeps-every-existing-pin
  (implies (fn-ocfg-pin-find id (fn-ocfg-pins oc))
           (equal (fn-ocfg-pin-find id (fn-ocfg-pins (cdr (fn-ocfg-open oc acfg))))
                  (fn-ocfg-pin-find id (fn-ocfg-pins oc))))
  :hints (("Goal" :in-theory (enable (:d fn-ocfg-open)))))

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
(defun fn-ocfg-repins-forp (id events)
  (declare (xargs :guard t))
  (if (consp events)
      (or (and (member-equal (car (car events)) '(:advance :close))
               (equal (car (cdr (car events))) id))
          (fn-ocfg-repins-forp id (cdr events)))
    nil))

(local (defthm fn-ocfg-step-keeps-other-pins
  (implies (and (fn-ocfg-pin-find id (fn-ocfg-pins oc))
                (not (and (member-equal (car event) '(:advance :close))
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

; KEYSTONE.  Advancing observes the live configuration, and nothing else is
; required of a connection: this is application liveness under the owner's
; own scheduling, not a timing claim.
(defthm fn-ocfg-advance-observes-the-live-configuration
  (implies (fn-own-find-conn id (fn-own-conns (fn-own-advance (fn-ocfg-owner oc) id)))
           (equal (fn-ocfg-conn-config (fn-ocfg-advance oc id) id)
                  (fn-ocfg-config oc)))
  :hints (("Goal" :in-theory (e/d ((:d fn-ocfg-advance) (:d fn-ocfg-conn-config))
                                  (fn-own-advance)))))

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
                    (fn-post-session-base
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
; 2. RECOVERY.  `fn-own-reopen' replays the ARTICLE history only; the owner's
;    crash image carries no configuration records, so this book cannot state
;    the reopened generation.  Section 3.5's owner statement
;    (`fn-own-acknowledged-reconfiguration-survives-reopen') therefore has no
;    subject here and is NOT stated.  Its store-level half is proved:
;    `fn-cnode-recovered-generation-is-at-most-the-live-generation'
;    (books/node-config.lisp) is STO-004's `<=' over the configuration
;    history, and `fn-cstr-ok-merged-replay-ends-in-a-configured-node'
;    (books/config-stream.lisp) is the merged-stream form.  Closing the owner
;    half needs `fn-own-reopen' to take the configuration records, which is a
;    `books/owner' signature change and belongs to the owner lane.

; -----------------------------------------------------------------------------
; Export theory.

(deftheory fn-ocfg-vocabulary
  '((:d fn-ocfg-pin-find) (:d fn-ocfg-pin-add) (:d fn-ocfg-pin-set)
    (:d fn-ocfg-pin-remove) (:d fn-ocfg-conn-config) (:d fn-ocfg-conn-generation)
    (:d fn-ocfg-served) (:d fn-ocfg-pins-okp) (:d fn-ocfg-conns-pinnedp)
    (:d fn-ocfg-pins-pin-conns-only) (:d fn-ocfg-statep) (:d fn-ocfg-live-cnode)
    (:d fn-ocfg-reconfig-record) (:d fn-ocfg-delta-names-group)
    (:d fn-ocfg-deltas-touch-groupp) (:d fn-ocfg-group-pinned-by-readerp)
    (:d fn-ocfg-reconfig-okp) (:d fn-ocfg-reconfig-refusal)
    (:d fn-ocfg-reconfigure) (:d fn-ocfg-complete) (:d fn-ocfg-open)
    (:d fn-ocfg-advance) (:d fn-ocfg-close) (:d fn-ocfg-pass) (:d fn-ocfg-step)
    (:d fn-ocfg-run) (:d fn-ocfg-list-active) (:d fn-ocfg-repins-forp)))

(in-theory (disable fn-ocfg-vocabulary))
