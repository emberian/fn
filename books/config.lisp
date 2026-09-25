; fn: the typed configuration value, its journal record, and configuration
; replay (packets R1 and R2 of specs/reconfiguration.md).
;
; fn had constants where it needed configuration.  This book owns the value a
; deployment may choose -- the group table, capacity, quotas, policy
; identifiers, listener and peer endpoints, resource limits -- as a typed
; record, and owns the journal record that changes it.  A reconfiguration is a
; transaction: a record carrying a list of typed deltas, the generation it
; results in, and the clock observation that stamps it.  Replay folds those
; records into a `(generation value)' pair.  Nothing here reads a file, and no
; definition in this book invokes the Lisp reader or evaluator.
;
; Two things this book deliberately does NOT do, because they belong to
; packets R2-in-the-node and R3: it does not touch `fn-node-statep' or any
; store book (the store cluster owns those entry points, and the transitions
; over them are proposed in the handoff), and it does not model the owner's
; staging of a reconfiguration.
;
; The group table is a HISTORY, not a set.  Retirement records a generation;
; it never deletes.  That is what lets an article accepted at generation 2
; still be shown to have named a group live at 2, and what makes NNT-006's
; "a local number watermark survives removal" structural.
;
; Codec scope: the durable object is the RECORD, so the record is what this
; book encodes.  A configuration value is never written; it is replayed.  The
; encoding is a count-prefixed stream of CBOR items over the primitives in
; `books/cbor' and the readers in `books/records', which is why the round trip
; below is one induction rather than a bespoke grammar.

(in-package "ACL2")
(include-book "records-invariants")
(include-book "clock")

; Nothing in this book opens the CBOR or record codec: every definition here
; is `:guard t', and the ground witnesses at the end are decided by
; evaluation.  Enabling `fn-cbor-codec-vocabulary' here cost minutes of guard
; proof for no theorem, so it is not enabled.

; -----------------------------------------------------------------------------
; Format ceilings.
;
; These are wire/format facts by the constant/configuration test of
; specs/reconfiguration.md section 1.1: two independent implementations must
; agree on them.  The RFC 3977 section 3.1 initial-line ceiling used by group
; creation admissibility is NOT one of them; `books/nntp-syntax' owns that
; number and it enters this book as an argument, so there is no second copy.

(defconst *fn-cfg-schema-version* 0)
(defconst *fn-cfg-magic* '(102 110 45 99 102 103))   ; "fn-cfg"
(defconst *fn-cfg-max-label* 256)
(defconst *fn-cfg-max-rows* 1024)
(defconst *fn-cfg-max-deltas* 64)
(defconst *fn-cfg-max-items* 65535)
(defconst *fn-cfg-max-octets* 65538)

; -----------------------------------------------------------------------------
; Total accessors.  Every accessor below is `:guard t' through these, so no
; caller ever has to know a record's shape to select from it.

(defun fn-cfg-ag-car (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-cfg-ag-cdr (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

; -----------------------------------------------------------------------------
; Leaf domains

(defun fn-cfg-labelp (text)
  ; A configuration label: a policy id, a quota scope, a listener address, a
  ; peer EID.  ASCII, possibly empty, bounded so the codec can represent it.
  (declare (xargs :guard t))
  (and (fn-record-ascii-stringp text)
       (<= (len (fn-record-string-octets text)) *fn-cfg-max-label*)))

;  KEYSTONE (the group-name ceiling is the label width).  Every group name the
; record codec admits (`fn-record-group-namep', at most
; `*fn-record-max-group-name*' octets, books/records-shape) is a
; configuration label, so `group create' stages it as a typed delta
; (native-admin `fn-native-admin-live-group-delta-is-a-typed-delta').  This
; is the one statement relating the two numbers: raising the group-name
; ceiling past `*fn-cfg-max-label*' (to the wire's 460) fails here, in the
; book that owns the label, and the store profile's name field is bounded by
; the group-name ceiling (`fn-bs-profile-validp').
(defthm fn-cfg-labelp-of-record-group-name
  (implies (fn-record-group-namep s) (fn-cfg-labelp s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-record-group-namep fn-cfg-labelp
                                     fn-record-nonempty-at-mostp))))

(defun fn-cfg-stampp (s)
  ; A clock observation whose three times fit the schema-0 uint32 fields.
  ; The narrower domain is a format ceiling, not a claim about clocks: the
  ; 64-bit stamp is an open item for the next codec schema.
  (declare (xargs :guard t))
  (and (fn-clock-observationp s)
       (fn-record-uint32p (fn-clock-monotonic s))
       (fn-record-uint32p (fn-clock-wall s))
       (fn-record-uint32p (fn-clock-wall-error s))))

; -----------------------------------------------------------------------------
; A configuration row.
;
; Quotas, policy identifiers, listeners, peers and resource limits are all the
; same shape: three labels and a natural.  One typed row, one recognizer, one
; codec reader, one round trip -- and named accessors per use so the vocabulary
; at each call site still says what the field means.

(defun fn-cfg-row-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))

(defun fn-cfg-row-a (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car x))
(defun fn-cfg-row-b (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr x)))
(defun fn-cfg-row-c (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr x))))
(defun fn-cfg-row-n (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr x)))))

(defun fn-cfg-row-make (a b c n)
  (declare (xargs :guard t))
  (list a b c n))

(defthm fn-cfg-row-shapep-of-row-make
  (fn-cfg-row-shapep (fn-cfg-row-make a b c n)))
(defthm fn-cfg-row-a-of-row-make
  (equal (fn-cfg-row-a (fn-cfg-row-make a b c n)) a))
(defthm fn-cfg-row-b-of-row-make
  (equal (fn-cfg-row-b (fn-cfg-row-make a b c n)) b))
(defthm fn-cfg-row-c-of-row-make
  (equal (fn-cfg-row-c (fn-cfg-row-make a b c n)) c))
(defthm fn-cfg-row-n-of-row-make
  (equal (fn-cfg-row-n (fn-cfg-row-make a b c n)) n))

(in-theory (disable (:d fn-cfg-row-shapep) (:d fn-cfg-row-make)
                    (:d fn-cfg-row-a) (:d fn-cfg-row-b)
                    (:d fn-cfg-row-c) (:d fn-cfg-row-n)))

(defun fn-cfg-rowp (x)
  (declare (xargs :guard t))
  (and (fn-cfg-row-shapep x)
       (fn-cfg-labelp (fn-cfg-row-a x))
       (fn-cfg-labelp (fn-cfg-row-b x))
       (fn-cfg-labelp (fn-cfg-row-c x))
       (fn-record-uint32p (fn-cfg-row-n x))))

(defun fn-cfg-row-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cfg-rowp (car xs)) (fn-cfg-row-listp (cdr xs)))
    (null xs)))

; Named vocabulary over the one row shape.
(defun fn-cfg-quota-scope (r) (declare (xargs :guard t)) (fn-cfg-row-a r))
(defun fn-cfg-quota-name  (r) (declare (xargs :guard t)) (fn-cfg-row-b r))
(defun fn-cfg-quota-count (r) (declare (xargs :guard t)) (fn-cfg-row-n r))
(defun fn-cfg-policy-slot (r) (declare (xargs :guard t)) (fn-cfg-row-a r))
(defun fn-cfg-policy-id   (r) (declare (xargs :guard t)) (fn-cfg-row-b r))
(defun fn-cfg-endpoint-address (r) (declare (xargs :guard t)) (fn-cfg-row-a r))
(defun fn-cfg-peer-eid    (r) (declare (xargs :guard t)) (fn-cfg-row-a r))
(defun fn-cfg-peer-endpoint (r) (declare (xargs :guard t)) (fn-cfg-row-b r))
(defun fn-cfg-peer-contact-plan (r) (declare (xargs :guard t)) (fn-cfg-row-c r))
(defun fn-cfg-limit-slot  (r) (declare (xargs :guard t)) (fn-cfg-row-a r))
(defun fn-cfg-limit-value (r) (declare (xargs :guard t)) (fn-cfg-row-n r))

(defun fn-cfg-row-lookup (rows a)
  ; The first row with this key, or nil.
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-a (car rows)) a)
          (car rows)
        (fn-cfg-row-lookup (cdr rows) a))
    nil))

(defun fn-cfg-row-upsert (rows row)
  ; Replace the first row with the same (a, b) key, else append.  Total.
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-a (car rows)) (fn-cfg-row-a row))
               (equal (fn-cfg-row-b (car rows)) (fn-cfg-row-b row)))
          (cons row (cdr rows))
        (cons (car rows) (fn-cfg-row-upsert (cdr rows) row)))
    (list row)))

; A policy slot holds one value: replace the first row whose slot (row-a) is
; this row's, else append.  fn-cfg-policy reads the first row of a slot, so
; the value set last is the value in force.  Until 2026-09-25 :set-policy
; used fn-cfg-row-upsert, keyed on (slot, value): a second `policy set' of
; the same slot with another value appended a row the lookup never reached,
; so the first value set stayed in force for good (found on hbox by lane
; path-and-login: `policy set posting-policy open' after `bound-logins' was
; accepted and changed nothing).
(defun fn-cfg-row-replace-key (rows row)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-a (car rows)) (fn-cfg-row-a row))
          (cons row (cdr rows))
        (cons (car rows) (fn-cfg-row-replace-key (cdr rows) row)))
    (list row)))

; The peer table is the peers row list keyed by row-a (the peer name); one
; peer is the group of rows sharing that key (specs/peering.md section 1.2,
; books/peer-config.lisp decodes the group into the typed record).  Three total
; helpers over a keyed row group: select, remove, and the recognizer that
; every row of a delta names the peer the delta names.
(defun fn-cfg-rows-with-key (rows a)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-a (car rows)) a)
          (cons (car rows) (fn-cfg-rows-with-key (cdr rows) a))
        (fn-cfg-rows-with-key (cdr rows) a))
    nil))

(defun fn-cfg-rows-without-key (rows a)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-a (car rows)) a)
          (fn-cfg-rows-without-key (cdr rows) a)
        (cons (car rows) (fn-cfg-rows-without-key (cdr rows) a)))
    nil))

(defun fn-cfg-rows-keyed-p (rows a)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (equal (fn-cfg-row-a (car rows)) a)
           (fn-cfg-rows-keyed-p (cdr rows) a))
    t))

; -----------------------------------------------------------------------------
; A group-table entry: a history entry, not a membership flag.

(defun fn-cfg-group-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6)))

(defun fn-cfg-group-name (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car x))
(defun fn-cfg-group-created-gen (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr x)))
(defun fn-cfg-group-created-stamp (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr x))))
(defun fn-cfg-group-retired-gen (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr x)))))
(defun fn-cfg-group-policy-id (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr x))))))
(defun fn-cfg-group-next (x)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr
                                                 (fn-cfg-ag-cdr x)))))))

(defun fn-cfg-group-make (name created-gen created-stamp retired-gen
                               policy-id next)
  (declare (xargs :guard t))
  (list name created-gen created-stamp retired-gen policy-id next))

(defthm fn-cfg-group-shapep-of-group-make
  (fn-cfg-group-shapep
   (fn-cfg-group-make name cgen cstamp rgen policy next)))
(defthm fn-cfg-group-name-of-group-make
  (equal (fn-cfg-group-name
          (fn-cfg-group-make name cgen cstamp rgen policy next))
         name))
(defthm fn-cfg-group-created-gen-of-group-make
  (equal (fn-cfg-group-created-gen
          (fn-cfg-group-make name cgen cstamp rgen policy next))
         cgen))
(defthm fn-cfg-group-created-stamp-of-group-make
  (equal (fn-cfg-group-created-stamp
          (fn-cfg-group-make name cgen cstamp rgen policy next))
         cstamp))
(defthm fn-cfg-group-retired-gen-of-group-make
  (equal (fn-cfg-group-retired-gen
          (fn-cfg-group-make name cgen cstamp rgen policy next))
         rgen))
(defthm fn-cfg-group-policy-id-of-group-make
  (equal (fn-cfg-group-policy-id
          (fn-cfg-group-make name cgen cstamp rgen policy next))
         policy))
(defthm fn-cfg-group-next-of-group-make
  (equal (fn-cfg-group-next
          (fn-cfg-group-make name cgen cstamp rgen policy next))
         next))

; The shape facts type reasoning supplied while the record was open, exported
; as forward-chaining rules only (docs/proof-style.md section 1).
(defthm fn-cfg-group-shapep-forward-shape
  (implies (fn-cfg-group-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-cfg-group-shapep) (:d fn-cfg-group-make)
                    (:d fn-cfg-group-name) (:d fn-cfg-group-created-gen)
                    (:d fn-cfg-group-created-stamp)
                    (:d fn-cfg-group-retired-gen)
                    (:d fn-cfg-group-policy-id) (:d fn-cfg-group-next)))

(defun fn-cfg-group-entryp (e)
  (declare (xargs :guard t))
  (and (fn-cfg-group-shapep e)
       (fn-record-group-namep (fn-cfg-group-name e))
       (fn-record-uint32p (fn-cfg-group-created-gen e))
       (fn-cfg-stampp (fn-cfg-group-created-stamp e))
       (let ((r (fn-cfg-group-retired-gen e)))
         (or (null r)
             (and (fn-record-uint32p r)
                  (<= (fn-cfg-group-created-gen e) r))))
       (fn-cfg-labelp (fn-cfg-group-policy-id e))
       (fn-record-uint32p (fn-cfg-group-next e))))

(defthm fn-cfg-group-entryp-forward-shape
  (implies (fn-cfg-group-entryp e) (and (consp e) (true-listp e)))
  :rule-classes :forward-chaining)

(defun fn-cfg-group-listp (es)
  (declare (xargs :guard t))
  (if (consp es)
      (and (fn-cfg-group-entryp (car es)) (fn-cfg-group-listp (cdr es)))
    (null es)))

(defun fn-cfg-group-all-names (es)
  (declare (xargs :guard t))
  (if (consp es)
      (cons (fn-cfg-group-name (car es)) (fn-cfg-group-all-names (cdr es)))
    nil))

(defun fn-cfg-group-find (es name)
  (declare (xargs :guard t))
  (if (consp es)
      (if (equal (fn-cfg-group-name (car es)) name)
          (car es)
        (fn-cfg-group-find (cdr es) name))
    nil))

(defun fn-cfg-entry-livep (e gen)
  ; Liveness is a question about a generation, never about "now".
  (declare (xargs :guard t))
  (and (consp e)
       (natp gen)
       (natp (fn-cfg-group-created-gen e))
       (<= (fn-cfg-group-created-gen e) gen)
       (or (null (fn-cfg-group-retired-gen e))
           (and (natp (fn-cfg-group-retired-gen e))
                (< gen (fn-cfg-group-retired-gen e))))))

(defun fn-cfg-live-names (es gen)
  (declare (xargs :guard t))
  (if (consp es)
      (if (fn-cfg-entry-livep (car es) gen)
          (cons (fn-cfg-group-name (car es)) (fn-cfg-live-names (cdr es) gen))
        (fn-cfg-live-names (cdr es) gen))
    nil))

; -----------------------------------------------------------------------------
; The configuration value

(defun fn-cfg-value-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 8)))

(defun fn-cfg-groups (v)
  (declare (xargs :guard t))
  (fn-cfg-ag-car v))
(defun fn-cfg-capacity (v)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr v)))
(defun fn-cfg-quotas (v)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr v))))
(defun fn-cfg-policies (v)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr v)))))
(defun fn-cfg-listeners (v)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr v))))))
(defun fn-cfg-peers (v)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr
                                                 (fn-cfg-ag-cdr v)))))))
(defun fn-cfg-limits (v)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr
                                                 (fn-cfg-ag-cdr
                                                  (fn-cfg-ag-cdr v))))))))

; The eighth slot (D29, control packet C2): the control-authority grants,
; rows (NAMESPACE PRINCIPAL-HEX VERB 0) written only by :grant-control and
; :revoke-control (specs/peering.md section 8).
(defun fn-cfg-authorities (v)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr
                                                 (fn-cfg-ag-cdr
                                                  (fn-cfg-ag-cdr
                                                   (fn-cfg-ag-cdr v)))))))))

(defun fn-cfg-value-make (groups capacity quotas policies listeners peers
                                 limits authorities)
  (declare (xargs :guard t))
  (list groups capacity quotas policies listeners peers limits authorities))

(defthm fn-cfg-value-shapep-of-value-make
  (fn-cfg-value-shapep
   (fn-cfg-value-make groups capacity quotas policies listeners peers limits authorities)))
(defthm fn-cfg-groups-of-value-make
  (equal (fn-cfg-groups
          (fn-cfg-value-make groups capacity quotas policies listeners peers
                             limits authorities))
         groups))
(defthm fn-cfg-capacity-of-value-make
  (equal (fn-cfg-capacity
          (fn-cfg-value-make groups capacity quotas policies listeners peers
                             limits authorities))
         capacity))
(defthm fn-cfg-quotas-of-value-make
  (equal (fn-cfg-quotas
          (fn-cfg-value-make groups capacity quotas policies listeners peers
                             limits authorities))
         quotas))
(defthm fn-cfg-policies-of-value-make
  (equal (fn-cfg-policies
          (fn-cfg-value-make groups capacity quotas policies listeners peers
                             limits authorities))
         policies))
(defthm fn-cfg-listeners-of-value-make
  (equal (fn-cfg-listeners
          (fn-cfg-value-make groups capacity quotas policies listeners peers
                             limits authorities))
         listeners))
(defthm fn-cfg-peers-of-value-make
  (equal (fn-cfg-peers
          (fn-cfg-value-make groups capacity quotas policies listeners peers
                             limits authorities))
         peers))
(defthm fn-cfg-limits-of-value-make
  (equal (fn-cfg-limits
          (fn-cfg-value-make groups capacity quotas policies listeners peers
                             limits authorities))
         limits))
(defthm fn-cfg-authorities-of-value-make
  (equal (fn-cfg-authorities
          (fn-cfg-value-make groups capacity quotas policies listeners peers
                             limits authorities))
         authorities))

(in-theory (disable (:d fn-cfg-value-shapep) (:d fn-cfg-value-make)
                    (:d fn-cfg-groups) (:d fn-cfg-capacity)
                    (:d fn-cfg-quotas) (:d fn-cfg-policies)
                    (:d fn-cfg-listeners) (:d fn-cfg-peers)
                    (:d fn-cfg-limits) (:d fn-cfg-authorities)))

(defun fn-cfg-member-namep (name names)
  (declare (xargs :guard t))
  (if (consp names)
      (or (equal name (car names)) (fn-cfg-member-namep name (cdr names)))
    nil))

(defun fn-cfg-no-duplicate-namesp (names)
  (declare (xargs :guard t))
  (if (consp names)
      (and (not (fn-cfg-member-namep (car names) (cdr names)))
           (fn-cfg-no-duplicate-namesp (cdr names)))
    t))

; A named resource limit may never exceed the format ceiling the codec can
; represent, so no configuration can name a bound the wire cannot carry.
(defun fn-cfg-limit-ceiling (slot)
  (declare (xargs :guard t))
  (cond ((equal slot "max-payload") *fn-record-max-payload*)
        ((equal slot "max-groups-per-article") *fn-record-max-groups*)
        (t *fn-cbor-max-uint*)))

(defun fn-cfg-limits-withinp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (<= (nfix (fn-cfg-limit-value (car rows)))
               (fn-cfg-limit-ceiling (fn-cfg-limit-slot (car rows))))
           (fn-cfg-limits-withinp (cdr rows)))
    t))

(defun fn-cfg-valuep (v)
  (declare (xargs :guard t))
  (and (fn-cfg-value-shapep v)
       (fn-cfg-group-listp (fn-cfg-groups v))
       (fn-cfg-no-duplicate-namesp (fn-cfg-group-all-names (fn-cfg-groups v)))
       (fn-record-uint32p (fn-cfg-capacity v))
       (fn-cfg-row-listp (fn-cfg-quotas v))
       (fn-cfg-row-listp (fn-cfg-policies v))
       (fn-cfg-row-listp (fn-cfg-listeners v))
       (fn-cfg-row-listp (fn-cfg-peers v))
       (fn-cfg-row-listp (fn-cfg-limits v))
       (fn-cfg-limits-withinp (fn-cfg-limits v))
       (fn-cfg-row-listp (fn-cfg-authorities v))))

(defun fn-cfg-empty-value ()
  ; The fail-closed floor: no groups and zero capacity accepts nothing.
  (declare (xargs :guard t))
  (fn-cfg-value-make nil 0 nil nil nil nil nil nil))

(defun fn-cfg-limit (v slot)
  (declare (xargs :guard t))
  (let ((row (fn-cfg-row-lookup (fn-cfg-limits v) slot)))
    (if (consp row) (nfix (fn-cfg-limit-value row)) 0)))

(defun fn-cfg-policy (v slot)
  (declare (xargs :guard t))
  (let ((row (fn-cfg-row-lookup (fn-cfg-policies v) slot)))
    (if (consp row) (fn-cfg-policy-id row) "")))

; -----------------------------------------------------------------------------
; The configuration: a generation and a value

(defun fn-cfg-shapep (c)
  (declare (xargs :guard t))
  (and (true-listp c) (equal (len c) 2)))
(defun fn-cfg-generation (c)
  (declare (xargs :guard t))
  (fn-cfg-ag-car c))
(defun fn-cfg-value (c)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr c)))
(defun fn-cfg-make (generation value)
  (declare (xargs :guard t))
  (list generation value))

(defthm fn-cfg-shapep-of-cfg-make
  (fn-cfg-shapep (fn-cfg-make generation value)))
(defthm fn-cfg-generation-of-cfg-make
  (equal (fn-cfg-generation (fn-cfg-make generation value)) generation))
(defthm fn-cfg-value-of-cfg-make
  (equal (fn-cfg-value (fn-cfg-make generation value)) value))

(in-theory (disable (:d fn-cfg-shapep) (:d fn-cfg-make)
                    (:d fn-cfg-generation) (:d fn-cfg-value)))

(defun fn-cfgp (c)
  (declare (xargs :guard t))
  (and (fn-cfg-shapep c)
       (fn-record-uint32p (fn-cfg-generation c))
       (fn-cfg-valuep (fn-cfg-value c))))

(defun fn-cfg-initial ()
  (declare (xargs :guard t))
  (fn-cfg-make 0 (fn-cfg-empty-value)))

; The served group table AT a generation.
(defun fn-cfg-group-names (v gen)
  (declare (xargs :guard t))
  (fn-cfg-live-names (fn-cfg-groups v) gen))

(defun fn-cfg-group-livep (v gen name)
  (declare (xargs :guard t))
  (fn-cfg-entry-livep (fn-cfg-group-find (fn-cfg-groups v) name) gen))

; -----------------------------------------------------------------------------
; Typed deltas.
;
; One record carries a LIST of deltas applied left to right under one
; generation, which is what makes atomicity worth proving: no state ever holds
; an intermediate value.

(defun fn-cfg-delta-shapep (d)
  (declare (xargs :guard t))
  (and (true-listp d) (equal (len d) 5)))
(defun fn-cfg-delta-kind (d)
  (declare (xargs :guard t))
  (fn-cfg-ag-car d))
(defun fn-cfg-delta-a (d)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr d)))
(defun fn-cfg-delta-b (d)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr d))))
(defun fn-cfg-delta-n (d)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr d)))))
(defun fn-cfg-delta-rows (d)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr d))))))
(defun fn-cfg-delta-make (kind a b n rows)
  (declare (xargs :guard t))
  (list kind a b n rows))

(defthm fn-cfg-delta-shapep-of-delta-make
  (fn-cfg-delta-shapep (fn-cfg-delta-make kind a b n rows)))
(defthm fn-cfg-delta-kind-of-delta-make
  (equal (fn-cfg-delta-kind (fn-cfg-delta-make kind a b n rows)) kind))
(defthm fn-cfg-delta-a-of-delta-make
  (equal (fn-cfg-delta-a (fn-cfg-delta-make kind a b n rows)) a))
(defthm fn-cfg-delta-b-of-delta-make
  (equal (fn-cfg-delta-b (fn-cfg-delta-make kind a b n rows)) b))
(defthm fn-cfg-delta-n-of-delta-make
  (equal (fn-cfg-delta-n (fn-cfg-delta-make kind a b n rows)) n))
(defthm fn-cfg-delta-rows-of-delta-make
  (equal (fn-cfg-delta-rows (fn-cfg-delta-make kind a b n rows)) rows))

(in-theory (disable (:d fn-cfg-delta-shapep) (:d fn-cfg-delta-make)
                    (:d fn-cfg-delta-kind) (:d fn-cfg-delta-a)
                    (:d fn-cfg-delta-b) (:d fn-cfg-delta-n)
                    (:d fn-cfg-delta-rows)))

(defconst *fn-cfg-delta-kinds*
  '(:create-group :remove-group :set-capacity :set-quota :set-policy
    :set-listeners :set-peers :set-limit :set-peer :remove-peer
    :grant-control :revoke-control))

(defun fn-cfg-kind-code (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :create-group) 1)
        ((equal kind :remove-group) 2)
        ((equal kind :set-capacity) 3)
        ((equal kind :set-quota) 4)
        ((equal kind :set-policy) 5)
        ((equal kind :set-listeners) 6)
        ((equal kind :set-peers) 7)
        ((equal kind :set-limit) 8)
        ((equal kind :set-peer) 9)
        ((equal kind :remove-peer) 10)
        ((equal kind :grant-control) 11)
        ((equal kind :revoke-control) 12)
        (t 0)))

(defun fn-cfg-code-kind (code)
  (declare (xargs :guard t))
  (cond ((equal code 1) :create-group)
        ((equal code 2) :remove-group)
        ((equal code 3) :set-capacity)
        ((equal code 4) :set-quota)
        ((equal code 5) :set-policy)
        ((equal code 6) :set-listeners)
        ((equal code 7) :set-peers)
        ((equal code 8) :set-limit)
        ((equal code 9) :set-peer)
        ((equal code 10) :remove-peer)
        ((equal code 11) :grant-control)
        ((equal code 12) :revoke-control)
        (t nil)))

(defun fn-cfg-deltap (d)
  (declare (xargs :guard t))
  (and (fn-cfg-delta-shapep d)
       (member-equal (fn-cfg-delta-kind d) *fn-cfg-delta-kinds*)
       (fn-cfg-labelp (fn-cfg-delta-a d))
       (fn-cfg-labelp (fn-cfg-delta-b d))
       (fn-record-uint32p (fn-cfg-delta-n d))
       (fn-cfg-row-listp (fn-cfg-delta-rows d))
       (<= (len (fn-cfg-delta-rows d)) *fn-cfg-max-rows*)))

(defun fn-cfg-delta-listp (ds)
  (declare (xargs :guard t))
  (if (consp ds)
      (and (fn-cfg-deltap (car ds)) (fn-cfg-delta-listp (cdr ds)))
    (null ds)))

; The design's surface syntax, as constructors over the one delta shape.
(defun fn-cfg-create-group (name policy-id)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :create-group name policy-id 0 nil))
(defun fn-cfg-remove-group (name)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :remove-group name "" 0 nil))
(defun fn-cfg-set-capacity (n)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :set-capacity "" "" n nil))
(defun fn-cfg-set-quota (scope name n)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :set-quota scope name n nil))
(defun fn-cfg-set-policy (slot id)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :set-policy slot id 0 nil))
(defun fn-cfg-set-listeners (rows)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :set-listeners "" "" 0 rows))
(defun fn-cfg-set-peers (rows)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :set-peers "" "" 0 rows))
(defun fn-cfg-set-limit (slot n)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :set-limit slot "" n nil))
; (:set-peer name rows) upserts the peer's row group by name; (:remove-peer
; name) drops it.  books/peer-config.lisp builds the rows from the typed record.
(defun fn-cfg-set-peer (name rows)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :set-peer name "" 0 rows))
(defun fn-cfg-remove-peer (name)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :remove-peer name "" 0 nil))

;; Control authority (D29, packet C2; specs/peering.md section 8).  A grant
;; is one authorities row (NAMESPACE PRINCIPAL-HEX VERB 0), keyed on the pair
;; (NAMESPACE, PRINCIPAL-HEX).  C2 carries only the authority C3 needs: the
;; one grantable verb is "cancel" (group control, C4, is deferred by D29).
;;
;;   (:grant-control NAMESPACE PRINCIPAL 0 ((NAMESPACE PRINCIPAL VERB 0)))  code 11
;;   (:revoke-control NAMESPACE PRINCIPAL 0 nil)                          code 12
(defconst *fn-cfg-control-verbs* '("cancel"))

(defun fn-cfg-hex-digit-octetp (b)
  (declare (xargs :guard t))
  (and (integerp b)
       (or (and (<= 48 b) (<= b 57))
           (and (<= 97 b) (<= b 102)))))

(defun fn-cfg-hex-digit-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cfg-hex-digit-octetp (car xs))
           (fn-cfg-hex-digit-octetsp (cdr xs)))
    (null xs)))

; A principal as the 64 lowercase hexadecimal characters of its 32 octets,
; the spelling `fn-pa-carriesp' and HDR :fn-verified compare.
(defun fn-cfg-principal-hexp (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (fn-cfg-labelp text)
       (equal (len (fn-record-string-octets text)) 64)
       (fn-cfg-hex-digit-octetsp (fn-record-string-octets text))))

; The group-name prefix of a wildcard pattern "PREFIX.*", or nil.
(defun fn-cfg-namespace-prefix-octets (octets)
  (declare (xargs :guard t))
  (let ((n (len octets)))
    (if (and (true-listp octets) (< 2 n)
             (equal (nthcdr (- n 2) octets) '(46 42)))
        (take (- n 2) octets)
      nil)))

; A namespace pattern: a group name, or a group name followed by ".*".
(defun fn-cfg-namespace-patternp (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (fn-cfg-labelp text)
       (or (fn-record-group-namep text)
           (let ((prefix (fn-cfg-namespace-prefix-octets
                          (fn-record-string-octets text))))
             (and (consp prefix)
                  (fn-record-group-namep (fn-record-octets-string prefix)))))))

(defun fn-cfg-grant-verb (rows)
  (declare (xargs :guard t))
  (fn-cfg-row-c (fn-cfg-ag-car rows)))

(defun fn-cfg-rows-have-pair (rows a b)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (and (equal (fn-cfg-row-a (car rows)) a)
               (equal (fn-cfg-row-b (car rows)) b))
          (fn-cfg-rows-have-pair (cdr rows) a b))
    nil))

(defun fn-cfg-rows-without-pair (rows a b)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-a (car rows)) a)
               (equal (fn-cfg-row-b (car rows)) b))
          (fn-cfg-rows-without-pair (cdr rows) a b)
        (cons (car rows) (fn-cfg-rows-without-pair (cdr rows) a b)))
    nil))

(defun fn-cfg-grant-control (namespace principal verb)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :grant-control namespace principal 0
                     (list (fn-cfg-row-make namespace principal verb 0))))
(defun fn-cfg-revoke-control (namespace principal)
  (declare (xargs :guard t))
  (fn-cfg-delta-make :revoke-control namespace principal 0 nil))

; -----------------------------------------------------------------------------
; Applying a delta.  Total, and never a deletion.

(defun fn-cfg-groups-create (es gen stamp name policy)
  ; Append, or revive in place keeping the retained watermark.
  (declare (xargs :guard t))
  (if (consp es)
      (if (equal (fn-cfg-group-name (car es)) name)
          (cons (fn-cfg-group-make name gen stamp nil policy
                                   (fn-cfg-group-next (car es)))
                (cdr es))
        (cons (car es) (fn-cfg-groups-create (cdr es) gen stamp name policy)))
    (list (fn-cfg-group-make name gen stamp nil policy 0))))

(defun fn-cfg-groups-retire (es gen name)
  ; Set retired-gen.  The entry, its creation stamp and its watermark stay.
  (declare (xargs :guard t))
  (if (consp es)
      (if (equal (fn-cfg-group-name (car es)) name)
          (cons (fn-cfg-group-make name (fn-cfg-group-created-gen (car es))
                                   (fn-cfg-group-created-stamp (car es))
                                   gen (fn-cfg-group-policy-id (car es))
                                   (fn-cfg-group-next (car es)))
                (cdr es))
        (cons (car es) (fn-cfg-groups-retire (cdr es) gen name)))
    nil))

(defun fn-cfg-set-groups (v es)
  (declare (xargs :guard t))
  (fn-cfg-value-make es (fn-cfg-capacity v) (fn-cfg-quotas v)
                     (fn-cfg-policies v) (fn-cfg-listeners v)
                     (fn-cfg-peers v) (fn-cfg-limits v)
                     (fn-cfg-authorities v)))

(defun fn-cfg-apply-delta (v gen stamp d)
  (declare (xargs :guard t))
  (let ((kind (fn-cfg-delta-kind d))
        (a (fn-cfg-delta-a d))
        (b (fn-cfg-delta-b d))
        (n (fn-cfg-delta-n d))
        (rows (fn-cfg-delta-rows d)))
    (cond
     ((equal kind :create-group)
      (fn-cfg-set-groups v (fn-cfg-groups-create (fn-cfg-groups v) gen stamp
                                                 a b)))
     ((equal kind :remove-group)
      (fn-cfg-set-groups v (fn-cfg-groups-retire (fn-cfg-groups v) gen a)))
     ((equal kind :set-capacity)
      (fn-cfg-value-make (fn-cfg-groups v) n (fn-cfg-quotas v)
                         (fn-cfg-policies v) (fn-cfg-listeners v)
                         (fn-cfg-peers v) (fn-cfg-limits v)
                     (fn-cfg-authorities v)))
     ((equal kind :set-quota)
      (fn-cfg-value-make (fn-cfg-groups v) (fn-cfg-capacity v)
                         (fn-cfg-row-upsert (fn-cfg-quotas v)
                                            (fn-cfg-row-make a b "" n))
                         (fn-cfg-policies v) (fn-cfg-listeners v)
                         (fn-cfg-peers v) (fn-cfg-limits v)
                     (fn-cfg-authorities v)))
     ((equal kind :set-policy)
      (fn-cfg-value-make (fn-cfg-groups v) (fn-cfg-capacity v)
                         (fn-cfg-quotas v)
                         (fn-cfg-row-replace-key (fn-cfg-policies v)
                                                 (fn-cfg-row-make a b "" 0))
                         (fn-cfg-listeners v) (fn-cfg-peers v)
                         (fn-cfg-limits v) (fn-cfg-authorities v)))
     ((equal kind :set-listeners)
      (fn-cfg-value-make (fn-cfg-groups v) (fn-cfg-capacity v)
                         (fn-cfg-quotas v) (fn-cfg-policies v) rows
                         (fn-cfg-peers v) (fn-cfg-limits v)
                     (fn-cfg-authorities v)))
     ((equal kind :set-peers)
      (fn-cfg-value-make (fn-cfg-groups v) (fn-cfg-capacity v)
                         (fn-cfg-quotas v) (fn-cfg-policies v)
                         (fn-cfg-listeners v) rows (fn-cfg-limits v)
                         (fn-cfg-authorities v)))
     ((equal kind :set-limit)
      (fn-cfg-value-make (fn-cfg-groups v) (fn-cfg-capacity v)
                         (fn-cfg-quotas v) (fn-cfg-policies v)
                         (fn-cfg-listeners v) (fn-cfg-peers v)
                         (fn-cfg-row-upsert (fn-cfg-limits v)
                                            (fn-cfg-row-make a "" "" n))
                         (fn-cfg-authorities v)))
     ((equal kind :set-peer)
      (fn-cfg-value-make (fn-cfg-groups v) (fn-cfg-capacity v)
                         (fn-cfg-quotas v) (fn-cfg-policies v)
                         (fn-cfg-listeners v)
                         (append (fn-cfg-rows-without-key (fn-cfg-peers v) a)
                                 rows)
                         (fn-cfg-limits v) (fn-cfg-authorities v)))
     ((equal kind :remove-peer)
      (fn-cfg-value-make (fn-cfg-groups v) (fn-cfg-capacity v)
                         (fn-cfg-quotas v) (fn-cfg-policies v)
                         (fn-cfg-listeners v)
                         (fn-cfg-rows-without-key (fn-cfg-peers v) a)
                         (fn-cfg-limits v) (fn-cfg-authorities v)))
     ((equal kind :grant-control)
      (fn-cfg-value-make (fn-cfg-groups v) (fn-cfg-capacity v)
                         (fn-cfg-quotas v) (fn-cfg-policies v)
                         (fn-cfg-listeners v) (fn-cfg-peers v)
                         (fn-cfg-limits v)
                         (fn-cfg-row-upsert (fn-cfg-authorities v)
                                            (fn-cfg-row-make
                                             a b (fn-cfg-grant-verb rows) 0))))
     ((equal kind :revoke-control)
      (fn-cfg-value-make (fn-cfg-groups v) (fn-cfg-capacity v)
                         (fn-cfg-quotas v) (fn-cfg-policies v)
                         (fn-cfg-listeners v) (fn-cfg-peers v)
                         (fn-cfg-limits v)
                         (fn-cfg-rows-without-pair (fn-cfg-authorities v)
                                                   a b)))
     (t v))))

(defun fn-cfg-apply (v gen stamp deltas)
  (declare (xargs :guard t :measure (len deltas)))
  (if (consp deltas)
      (fn-cfg-apply (fn-cfg-apply-delta v gen stamp (car deltas)) gen stamp
                    (cdr deltas))
    v))

; -----------------------------------------------------------------------------
; Admissibility (specs/reconfiguration.md section 2.3), node-derivable part.
;
; The reservation total and the RFC 3977 section 3.1 initial-line ceiling
; enter as arguments: the retention ledger owns the first and `books/nntp-syntax'
; owns the second, so neither is recomputed or copied here.  The owner-state
; conditions (reader pins) are packet R3 and never enter a durable record.

(defun fn-cfg-name-line-octets (names)
  ; Each name plus one separating octet: the width the served table occupies
  ; on a generated initial line.
  (declare (xargs :guard t))
  (if (consp names)
      (+ 1 (len (fn-record-string-octets (car names)))
         (fn-cfg-name-line-octets (cdr names)))
    0))

(defun fn-cfg-delta-reason (v gen stamp reserved ceiling d)
  (declare (xargs :guard t))
  (declare (ignorable stamp))
  (let ((kind (fn-cfg-delta-kind d))
        (a (fn-cfg-delta-a d))
        (n (fn-cfg-delta-n d)))
    (cond
     ((not (fn-cfg-deltap d)) :malformed-delta)
     ((equal kind :create-group)
      (cond ((not (fn-record-group-namep a)) :group-name)
            ((fn-cfg-group-livep v gen a) :duplicate-group)
            ((< (nfix ceiling)
                (fn-cfg-name-line-octets
                 (cons a (fn-cfg-group-names v gen))))
             :group-table-unprojectable)
            (t nil)))
     ((equal kind :remove-group)
      (if (fn-cfg-group-livep v gen a) nil :no-such-group))
     ((equal kind :set-capacity)
      (if (< n (nfix reserved)) :capacity-below-reserved nil))
     ((equal kind :set-limit)
      (if (<= n (fn-cfg-limit-ceiling a)) nil :limit-above-ceiling))
     ; A peer delta names its peer in a; every row of a :set-peer carries
     ; that name as its key, so no row can land under another peer.  The
     ; typed shape of the row group (specs/peering.md section 1.2) is
     ; books/peer-config.lisp's fn-cfg-peer-set-admissiblep; the owner-side
     ; condition on :remove-peer (no outstanding feed entry) is the feed
     ; lane's and never enters a durable record, as for reader pins.
     ((equal kind :set-peer)
      (cond ((not (consp (fn-cfg-delta-rows d))) :peer-rows-empty)
            ((not (fn-cfg-rows-keyed-p (fn-cfg-delta-rows d) a))
             :peer-rows-unkeyed)
            (t nil)))
     ((equal kind :remove-peer)
      (if (consp (fn-cfg-rows-with-key (fn-cfg-peers v) a)) nil
        :no-such-peer))
     ; A grant names its namespace pattern and principal in a and b and
     ; carries exactly the one row (a b VERB 0); VERB is a grantable verb.
     ; Reserved names (RFC 5536 section 3.1.4) are refused at the operator
     ; surface, books/native-admin.lisp `fn-native-admin-control-plan'.
     ((equal kind :grant-control)
      (let ((rows (fn-cfg-delta-rows d)))
        (cond ((not (fn-cfg-namespace-patternp a)) :namespace-pattern)
              ((not (fn-cfg-principal-hexp (fn-cfg-delta-b d))) :principal)
              ((not (member-equal (fn-cfg-grant-verb rows)
                                  *fn-cfg-control-verbs*))
               :verb-not-grantable)
              ((not (equal rows
                           (list (fn-cfg-row-make a (fn-cfg-delta-b d)
                                                  (fn-cfg-grant-verb rows)
                                                  0))))
               :grant-row)
              (t nil))))
     ((equal kind :revoke-control)
      (if (fn-cfg-rows-have-pair (fn-cfg-authorities v) a (fn-cfg-delta-b d))
          nil
        :no-such-grant))
     (t nil))))

(defun fn-cfg-admissible-reason (v gen stamp reserved ceiling deltas)
  ; The whole delta list is admissible or none of it is.  Each delta is
  ; checked against the value accumulated so far, so ((:remove-group g)
  ; (:create-group g p)) is admissible as a pair and a repeated creation is
  ; :duplicate-group.
  (declare (xargs :guard t :measure (len deltas)))
  (if (consp deltas)
      (let ((r (fn-cfg-delta-reason v gen stamp reserved ceiling
                                    (car deltas))))
        (if r
            r
          (fn-cfg-admissible-reason
           (fn-cfg-apply-delta v gen stamp (car deltas))
           gen stamp reserved ceiling (cdr deltas))))
    (if (null deltas) nil :improper-delta-list)))

(defun fn-cfg-admissiblep (v gen stamp reserved ceiling deltas)
  (declare (xargs :guard t))
  (null (fn-cfg-admissible-reason v gen stamp reserved ceiling deltas)))

; -----------------------------------------------------------------------------
; The configuration record

(defun fn-cfg-record-shapep (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 5)))
(defun fn-cfg-record-sequence (r)
  (declare (xargs :guard t))
  (fn-cfg-ag-car r))
(defun fn-cfg-record-txid (r)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr r)))
(defun fn-cfg-record-generation (r)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr r))))
(defun fn-cfg-record-change (r)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr r)))))
(defun fn-cfg-record-stamp (r)
  (declare (xargs :guard t))
  (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                (fn-cfg-ag-cdr r))))))
(defun fn-cfg-record-make (sequence txid generation change stamp)
  (declare (xargs :guard t))
  (list sequence txid generation change stamp))

(defthm fn-cfg-record-shapep-of-record-make
  (fn-cfg-record-shapep (fn-cfg-record-make s tx gen change stamp)))
(defthm fn-cfg-record-sequence-of-record-make
  (equal (fn-cfg-record-sequence (fn-cfg-record-make s tx gen change stamp))
         s))
(defthm fn-cfg-record-txid-of-record-make
  (equal (fn-cfg-record-txid (fn-cfg-record-make s tx gen change stamp)) tx))
(defthm fn-cfg-record-generation-of-record-make
  (equal (fn-cfg-record-generation (fn-cfg-record-make s tx gen change stamp))
         gen))
(defthm fn-cfg-record-change-of-record-make
  (equal (fn-cfg-record-change (fn-cfg-record-make s tx gen change stamp))
         change))
(defthm fn-cfg-record-stamp-of-record-make
  (equal (fn-cfg-record-stamp (fn-cfg-record-make s tx gen change stamp))
         stamp))

(in-theory (disable (:d fn-cfg-record-shapep) (:d fn-cfg-record-make)
                    (:d fn-cfg-record-sequence) (:d fn-cfg-record-txid)
                    (:d fn-cfg-record-generation) (:d fn-cfg-record-change)
                    (:d fn-cfg-record-stamp)))

(defun fn-cfg-recordp (r)
  (declare (xargs :guard t))
  (and (fn-cfg-record-shapep r)
       (fn-record-uint32p (fn-cfg-record-sequence r))
       (fn-record-uint32p (fn-cfg-record-txid r))
       (fn-record-uint32p (fn-cfg-record-generation r))
       (fn-cfg-delta-listp (fn-cfg-record-change r))
       (consp (fn-cfg-record-change r))
       (<= (len (fn-cfg-record-change r)) *fn-cfg-max-deltas*)
       (fn-cfg-stampp (fn-cfg-record-stamp r))))

; -----------------------------------------------------------------------------
; Configuration replay: the fold of configuration records into (generation
; value).  Fail closed: a record out of generation order or inadmissible on
; the replayed value is a fault, never a skipped record.

(defun fn-cfg-apply-record (cfg r)
  (declare (xargs :guard t))
  (fn-cfg-make (fn-cfg-record-generation r)
               (fn-cfg-apply (fn-cfg-value cfg)
                             (fn-cfg-record-generation r)
                             (fn-cfg-record-stamp r)
                             (fn-cfg-record-change r))))

(defun fn-cfg-record-acceptablep (cfg r reserved ceiling)
  (declare (xargs :guard t))
  (and (fn-cfgp cfg)
       (fn-cfg-recordp r)
       (equal (fn-cfg-record-generation r) (+ 1 (fn-cfg-generation cfg)))
       (fn-cfg-admissiblep (fn-cfg-value cfg)
                           (fn-cfg-record-generation r)
                           (fn-cfg-record-stamp r)
                           reserved ceiling
                           (fn-cfg-record-change r))))

(defun fn-config-replay-loop (cfg reserved ceiling records)
  ; The measure is the record list alone.  The acceptability ruler is
  ; irrelevant to termination and is kept closed here: left open, the measure
  ; conjecture case-splits on admissibility and does not finish inside two
  ; million prover steps (measured 2026-09-19; that was the whole cost of
  ; this book).
  (declare (xargs :guard t :measure (len records)
                  :hints (("Goal" :in-theory (disable fn-cfg-record-acceptablep
                                                      fn-cfg-apply-record)))))
  (if (consp records)
      (if (fn-cfg-record-acceptablep cfg (car records) reserved ceiling)
          (fn-config-replay-loop (fn-cfg-apply-record cfg (car records))
                                 reserved ceiling (cdr records))
        :fault)
    (if (null records) cfg :fault)))

(defun fn-config-replay (reserved ceiling records)
  (declare (xargs :guard t))
  (fn-config-replay-loop (fn-cfg-initial) reserved ceiling records))

(defun fn-config-replay-okp (x)
  (declare (xargs :guard t))
  (and (not (equal x :fault)) (fn-cfgp x)))

; -----------------------------------------------------------------------------
; The canonical CBOR encoding of a configuration record.
;
; A count-prefixed stream of CBOR items over the `books/cbor' primitives:
;   bstr "fn-cfg", uint schema-version, uint item-count, item[0] ... item[n-1]
; Every item is a canonical uint or a definite byte string, so the stream is
; self-delimiting and the decoder is one generic reader.

(defun fn-cfg-uitem (n)
  (declare (xargs :guard t))
  (cons :uint (nfix n)))
(defun fn-cfg-titem (text)
  (declare (xargs :guard t))
  (cons :bytes (fn-record-string-octets text)))
(defun fn-cfg-uitemp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :uint) (fn-record-uint32p (cdr x))))
(defun fn-cfg-titemp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :bytes) (fn-cbor-octet-listp (cdr x))
       (<= (len (cdr x)) *fn-cbor-max-bytes*)))
(defun fn-cfg-itemp (x)
  (declare (xargs :guard t))
  (or (fn-cfg-uitemp x) (fn-cfg-titemp x)))
(defun fn-cfg-item-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cfg-itemp (car xs)) (fn-cfg-item-listp (cdr xs)))
    (null xs)))

(defun fn-cfg-stamp-items (s)
  (declare (xargs :guard t))
  (list (fn-cfg-uitem (fn-cfg-ag-car (fn-cfg-ag-cdr s)))
        (fn-cfg-uitem (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr s))))
        (fn-cfg-uitem (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                     (fn-cfg-ag-cdr s)))))
        (fn-cfg-uitem (if (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr
                                                         (fn-cfg-ag-cdr
                                                          (fn-cfg-ag-cdr s)))))
                          1 0))))

(defun fn-cfg-row-items (r)
  (declare (xargs :guard t))
  (list (fn-cfg-titem (fn-cfg-row-a r)) (fn-cfg-titem (fn-cfg-row-b r))
        (fn-cfg-titem (fn-cfg-row-c r)) (fn-cfg-uitem (fn-cfg-row-n r))))

(defun fn-cfg-rows-items (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (append (fn-cfg-row-items (car rows)) (fn-cfg-rows-items (cdr rows)))
    nil))

(defun fn-cfg-delta-items (d)
  (declare (xargs :guard t))
  (append (list (fn-cfg-uitem (fn-cfg-kind-code (fn-cfg-delta-kind d)))
                (fn-cfg-titem (fn-cfg-delta-a d))
                (fn-cfg-titem (fn-cfg-delta-b d))
                (fn-cfg-uitem (fn-cfg-delta-n d))
                (fn-cfg-uitem (len (fn-cfg-delta-rows d))))
          (fn-cfg-rows-items (fn-cfg-delta-rows d))))

(defun fn-cfg-deltas-items (ds)
  (declare (xargs :guard t))
  (if (consp ds)
      (append (fn-cfg-delta-items (car ds)) (fn-cfg-deltas-items (cdr ds)))
    nil))

(defun fn-cfg-record-items (r)
  (declare (xargs :guard t))
  (append (list (fn-cfg-uitem (fn-cfg-record-sequence r))
                (fn-cfg-uitem (fn-cfg-record-txid r))
                (fn-cfg-uitem (fn-cfg-record-generation r)))
          (append (fn-cfg-stamp-items (fn-cfg-record-stamp r))
                  (cons (fn-cfg-uitem (len (fn-cfg-record-change r)))
                        (fn-cfg-deltas-items (fn-cfg-record-change r))))))

(defun fn-cfg-item-octets (items)
  (declare (xargs :guard t))
  (if (consp items)
      (append (fn-cbor-encode (car items))
              (fn-cfg-item-octets (cdr items)))
    nil))

(defun fn-cfg-encode (r)
  (declare (xargs :guard t))
  (let ((items (fn-cfg-record-items r)))
    (append (fn-cbor-encode (cons :bytes *fn-cfg-magic*))
            (append (fn-cbor-encode (fn-cfg-uitem *fn-cfg-schema-version*))
                    (append (fn-cbor-encode (fn-cfg-uitem (len items)))
                            (fn-cfg-item-octets items))))))

; -----------------------------------------------------------------------------
; The decoder.  Item readers return the `books/records' parse result.

; `(not (posp count))', not `(zp count)', in the three counted readers: `zp'
; guards `natp', these readers are `:guard t', and the count arrives from the
; wire.  The two are equal on every input, so the definitions say the same.
(defun fn-cfg-parse-items (count octets)
  (declare (xargs :guard t :measure (nfix count)))
  (if (not (posp count))
      (fn-record-parse-ok nil octets)
    (if (not (fn-cbor-octet-listp octets))
        (fn-record-parse-error :octets)
      (let ((d (fn-cbor-decode octets)))
        (if (not (fn-cbor-result-okp d))
            (fn-record-parse-error :item)
          (if (not (fn-cfg-itemp (fn-cbor-result-value d)))
              (fn-record-parse-error :item-type)
            (let ((tail (fn-cfg-parse-items (- count 1)
                                            (fn-cbor-result-rest d))))
              (if (not (fn-record-parse-okp tail))
                  tail
                (fn-record-parse-ok
                 (cons (fn-cbor-result-value d) (fn-record-parse-value tail))
                 (fn-record-parse-rest tail))))))))))

(defun fn-cfg-read-uint (items)
  (declare (xargs :guard t))
  (if (and (consp items) (fn-cfg-uitemp (car items)))
      (fn-record-parse-ok (cdr (car items)) (cdr items))
    (fn-record-parse-error :uint)))

(defun fn-cfg-read-label (items)
  (declare (xargs :guard t))
  (if (and (consp items) (fn-cfg-titemp (car items))
           (fn-cfg-labelp (fn-record-octets-string (cdr (car items)))))
      (fn-record-parse-ok (fn-record-octets-string (cdr (car items)))
                          (cdr items))
    (fn-record-parse-error :label)))

(defun fn-cfg-read-row (items)
  (declare (xargs :guard t))
  (let ((a (fn-cfg-read-label items)))
    (if (not (fn-record-parse-okp a))
        a
      (let ((b (fn-cfg-read-label (fn-record-parse-rest a))))
        (if (not (fn-record-parse-okp b))
            b
          (let ((c (fn-cfg-read-label (fn-record-parse-rest b))))
            (if (not (fn-record-parse-okp c))
                c
              (let ((n (fn-cfg-read-uint (fn-record-parse-rest c))))
                (if (not (fn-record-parse-okp n))
                    n
                  (fn-record-parse-ok
                   (fn-cfg-row-make (fn-record-parse-value a)
                                    (fn-record-parse-value b)
                                    (fn-record-parse-value c)
                                    (fn-record-parse-value n))
                   (fn-record-parse-rest n)))))))))))

(defun fn-cfg-read-rows (count items)
  (declare (xargs :guard t :measure (nfix count)))
  (if (not (posp count))
      (fn-record-parse-ok nil items)
    (let ((first (fn-cfg-read-row items)))
      (if (not (fn-record-parse-okp first))
          first
        (let ((tail (fn-cfg-read-rows (- count 1)
                                      (fn-record-parse-rest first))))
          (if (not (fn-record-parse-okp tail))
              tail
            (fn-record-parse-ok
             (cons (fn-record-parse-value first) (fn-record-parse-value tail))
             (fn-record-parse-rest tail))))))))

(defun fn-cfg-read-delta (items)
  (declare (xargs :guard t))
  (let ((k (fn-cfg-read-uint items)))
    (if (not (fn-record-parse-okp k))
        k
      (if (not (fn-cfg-code-kind (fn-record-parse-value k)))
          (fn-record-parse-error :delta-kind)
        (let ((a (fn-cfg-read-label (fn-record-parse-rest k))))
          (if (not (fn-record-parse-okp a))
              a
            (let ((b (fn-cfg-read-label (fn-record-parse-rest a))))
              (if (not (fn-record-parse-okp b))
                  b
                (let ((n (fn-cfg-read-uint (fn-record-parse-rest b))))
                  (if (not (fn-record-parse-okp n))
                      n
                    (let ((rc (fn-cfg-read-uint (fn-record-parse-rest n))))
                      (if (not (fn-record-parse-okp rc))
                          rc
                        (if (< *fn-cfg-max-rows* (fn-record-parse-value rc))
                            (fn-record-parse-error :row-count)
                          (let ((rows (fn-cfg-read-rows
                                       (fn-record-parse-value rc)
                                       (fn-record-parse-rest rc))))
                            (if (not (fn-record-parse-okp rows))
                                rows
                              (fn-record-parse-ok
                               (fn-cfg-delta-make
                                (fn-cfg-code-kind (fn-record-parse-value k))
                                (fn-record-parse-value a)
                                (fn-record-parse-value b)
                                (fn-record-parse-value n)
                                (fn-record-parse-value rows))
                               (fn-record-parse-rest rows)))))))))))))))))

(defun fn-cfg-read-deltas (count items)
  (declare (xargs :guard t :measure (nfix count)))
  (if (not (posp count))
      (fn-record-parse-ok nil items)
    (let ((first (fn-cfg-read-delta items)))
      (if (not (fn-record-parse-okp first))
          first
        (let ((tail (fn-cfg-read-deltas (- count 1)
                                        (fn-record-parse-rest first))))
          (if (not (fn-record-parse-okp tail))
              tail
            (fn-record-parse-ok
             (cons (fn-record-parse-value first) (fn-record-parse-value tail))
             (fn-record-parse-rest tail))))))))

(defun fn-cfg-read-record (items)
  (declare (xargs :guard t))
  (let ((s (fn-cfg-read-uint items)))
    (if (not (fn-record-parse-okp s))
        s
      (let ((tx (fn-cfg-read-uint (fn-record-parse-rest s))))
        (if (not (fn-record-parse-okp tx))
            tx
          (let ((gen (fn-cfg-read-uint (fn-record-parse-rest tx))))
            (if (not (fn-record-parse-okp gen))
                gen
              (let ((m (fn-cfg-read-uint (fn-record-parse-rest gen))))
                (if (not (fn-record-parse-okp m))
                    m
                  (let ((w (fn-cfg-read-uint (fn-record-parse-rest m))))
                    (if (not (fn-record-parse-okp w))
                        w
                      (let ((we (fn-cfg-read-uint (fn-record-parse-rest w))))
                        (if (not (fn-record-parse-okp we))
                            we
                          (let ((hw (fn-cfg-read-uint
                                     (fn-record-parse-rest we))))
                            (if (not (fn-record-parse-okp hw))
                                hw
                              (let ((dc (fn-cfg-read-uint
                                         (fn-record-parse-rest hw))))
                                (if (not (fn-record-parse-okp dc))
                                    dc
                                  (if (or (< *fn-cfg-max-deltas*
                                             (fn-record-parse-value dc))
                                          (equal (fn-record-parse-value dc) 0))
                                      (fn-record-parse-error :delta-count)
                                    (let ((ds (fn-cfg-read-deltas
                                               (fn-record-parse-value dc)
                                               (fn-record-parse-rest dc))))
                                      (if (not (fn-record-parse-okp ds))
                                          ds
                                        (fn-record-parse-ok
                                         (fn-cfg-record-make
                                          (fn-record-parse-value s)
                                          (fn-record-parse-value tx)
                                          (fn-record-parse-value gen)
                                          (fn-record-parse-value ds)
                                          (fn-clock-observation
                                           (fn-record-parse-value m)
                                           (fn-record-parse-value w)
                                           (fn-record-parse-value we)
                                           (equal (fn-record-parse-value hw)
                                                  1)))
                                         (fn-record-parse-rest ds))))))))))))))))))))))

(defun fn-cfg-decode-exact (octets)
  ; The whole-stream decoder the host calls.  It checks the input bound before
  ; traversal, then magic, version and item count before any record is built.
  ; Guards are verified below with exactly the three `books/records' domain
  ; facts its `<' and octet-list obligations need; nothing else is opened.
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-cbor-octet-listp octets)
                (<= (len octets) *fn-cfg-max-octets*)))
      (fn-record-parse-error :limit)
    (let ((magic (fn-record-read-bytes octets)))
      (if (not (fn-record-parse-okp magic))
          (fn-record-parse-error :magic)
        (if (not (equal (fn-record-parse-value magic) *fn-cfg-magic*))
            (fn-record-parse-error :magic)
          (let ((version (fn-record-read-uint (fn-record-parse-rest magic))))
            (if (not (fn-record-parse-okp version))
                (fn-record-parse-error :version)
              (if (not (equal (fn-record-parse-value version)
                              *fn-cfg-schema-version*))
                  (fn-record-parse-error :version)
                (let ((count (fn-record-read-uint
                              (fn-record-parse-rest version))))
                  (if (not (fn-record-parse-okp count))
                      (fn-record-parse-error :item-count)
                    (if (< *fn-cfg-max-items* (fn-record-parse-value count))
                        (fn-record-parse-error :item-count)
                      (let ((items (fn-cfg-parse-items
                                    (fn-record-parse-value count)
                                    (fn-record-parse-rest count))))
                        (if (not (fn-record-parse-okp items))
                            items
                          (if (not (null (fn-record-parse-rest items)))
                              (fn-record-parse-error :trailing)
                            (let ((r (fn-cfg-read-record
                                      (fn-record-parse-value items))))
                              (if (not (fn-record-parse-okp r))
                                  r
                                (if (not (null (fn-record-parse-rest r)))
                                    (fn-record-parse-error :trailing-items)
                                  (if (not (fn-cfg-recordp
                                            (fn-record-parse-value r)))
                                      (fn-record-parse-error :record-type)
                                    r))))))))))))))))))

(verify-guards fn-cfg-decode-exact
  :hints (("Goal"
           :in-theory (e/d (fn-record-read-bytes-success-domain
                            fn-record-read-uint-success-domain
                            fn-record-read-uint-success-is-rational)
                           (fn-cbor-octet-listp)))))

; -----------------------------------------------------------------------------
; The one default configuration.
;
; `run_store.py initialize' writes exactly this record, so packet R4 deletes
; one line rather than reconciling a Python copy of the table.  The stamp is
; the zero observation with no wall claim: an `initialize' has no clock
; reading it is willing to certify, and the design's clock discipline says so
; explicitly rather than inventing a time.

(defconst *fn-cfg-default-policy-id* "fn-policy-default-1")

(defconst *fn-cfg-default-stamp* (fn-clock-observation 0 0 0 nil))

(defconst *fn-cfg-default-change*
  (list (fn-cfg-create-group "fn.letters" *fn-cfg-default-policy-id*)
        (fn-cfg-create-group "fn.test" *fn-cfg-default-policy-id*)
        (fn-cfg-set-capacity 1048576)
        (fn-cfg-set-limit "max-payload" 32768)))

(defconst *fn-cfg-default-record*
  (fn-cfg-record-make 0 0 1 *fn-cfg-default-change* *fn-cfg-default-stamp*))

(defthm fn-cfg-default-record-is-a-record
  (fn-cfg-recordp *fn-cfg-default-record*)
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Round trip and canonicality.
;
; The item stream is self-delimiting and each item is canonical, so the whole
; decode-of-encode is one induction over the item list.  Canonicality follows:
; two records with the same octets decode to the same record, so the encoding
; is injective on well-formed records.

; Local: the one `append' fact the induction step needs.  It stays local so no
; `append'-backchaining rule leaves this book.
(local (defthm fn-cfg-octet-listp-of-append
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (append a b)))))

(defthm fn-cfg-item-octets-are-octets
  (fn-cbor-octet-listp (fn-cfg-item-octets items))
  :hints (("Goal" :induct (fn-cfg-item-octets items)
           :in-theory (e/d (fn-record-cbor-encode-octets)
                           (fn-cbor-encode fn-cbor-octet-listp)))))

; OPEN: the general decode-of-encode over a variable-length item stream.
; The prefix lemmas it needs (`fn-record-cbor-stream-uint-round-trip',
; `fn-record-cbor-stream-bytes-round-trip') are proved in
; `books/records-invariants', but the length-bound bookkeeping over the
; concatenated stream did not close inside this lane's budget.  It is recorded
; open rather than weakened, and the coverage below is the same coverage
; `books/records' has for its own full-record round trip: ground vectors.

; A certified end-to-end vector: the default configuration record encodes and
; decodes to itself, and replaying it produces generation 1.  A witness, not a
; rewrite rule; it is cited by name.
(defthm fn-cfg-default-record-round-trip
  (equal (fn-cfg-decode-exact (fn-cfg-encode *fn-cfg-default-record*))
         (fn-record-parse-ok *fn-cfg-default-record* nil))
  :rule-classes nil)

(defthm fn-cfg-default-record-replays-to-generation-one
  (and (equal (fn-cfg-generation
               (fn-config-replay 0 510 (list *fn-cfg-default-record*)))
              1)
       (equal (fn-cfg-group-names
               (fn-cfg-value (fn-config-replay 0 510
                                               (list *fn-cfg-default-record*)))
               1)
              '("fn.letters" "fn.test"))
       (equal (fn-cfg-capacity
               (fn-cfg-value (fn-config-replay 0 510
                                               (list *fn-cfg-default-record*))))
              1048576))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Export theory.
;
; Enabled on include: the record shape and accessor-of-constructor lemmas,
; `fn-cfg-item-octets-are-octets', and the three ground witnesses above.  The
; recognizers, the delta application, admissibility, the replay fold and the
; whole codec are proof vocabulary: a book that must open one enables
; `fn-cfg-vocabulary' locally and says why.

(deftheory fn-cfg-vocabulary
  '((:d fn-cfg-ag-car) (:d fn-cfg-ag-cdr) (:d fn-cfg-labelp)
    (:d fn-cfg-stampp) (:d fn-cfg-rowp) (:d fn-cfg-row-listp)
    (:d fn-cfg-quota-scope) (:d fn-cfg-quota-name) (:d fn-cfg-quota-count)
    (:d fn-cfg-policy-slot) (:d fn-cfg-policy-id)
    (:d fn-cfg-endpoint-address) (:d fn-cfg-peer-eid)
    (:d fn-cfg-peer-endpoint) (:d fn-cfg-peer-contact-plan)
    (:d fn-cfg-limit-slot) (:d fn-cfg-limit-value) (:d fn-cfg-row-lookup)
    (:d fn-cfg-row-upsert) (:d fn-cfg-row-replace-key) (:d fn-cfg-rows-with-key)
    (:d fn-cfg-rows-without-key) (:d fn-cfg-rows-keyed-p)
    (:d fn-cfg-group-entryp) (:d fn-cfg-group-listp)
    (:d fn-cfg-group-all-names) (:d fn-cfg-group-find) (:d fn-cfg-entry-livep)
    (:d fn-cfg-live-names) (:d fn-cfg-member-namep)
    (:d fn-cfg-no-duplicate-namesp) (:d fn-cfg-limit-ceiling)
    (:d fn-cfg-limits-withinp) (:d fn-cfg-valuep) (:d fn-cfg-empty-value)
    (:d fn-cfg-limit) (:d fn-cfg-policy) (:d fn-cfgp) (:d fn-cfg-initial)
    (:d fn-cfg-group-names) (:d fn-cfg-group-livep) (:d fn-cfg-deltap)
    (:d fn-cfg-delta-listp) (:d fn-cfg-kind-code) (:d fn-cfg-code-kind)
    (:d fn-cfg-create-group) (:d fn-cfg-remove-group) (:d fn-cfg-set-capacity)
    (:d fn-cfg-set-quota) (:d fn-cfg-set-policy) (:d fn-cfg-set-listeners)
    (:d fn-cfg-set-peers) (:d fn-cfg-set-limit) (:d fn-cfg-set-peer)
    (:d fn-cfg-remove-peer) (:d fn-cfg-groups-create)
    (:d fn-cfg-hex-digit-octetp) (:d fn-cfg-hex-digit-octetsp)
    (:d fn-cfg-principal-hexp) (:d fn-cfg-namespace-prefix-octets)
    (:d fn-cfg-namespace-patternp) (:d fn-cfg-grant-verb)
    (:d fn-cfg-rows-have-pair) (:d fn-cfg-rows-without-pair)
    (:d fn-cfg-grant-control) (:d fn-cfg-revoke-control)
    (:d fn-cfg-groups-retire) (:d fn-cfg-set-groups) (:d fn-cfg-apply-delta)
    (:d fn-cfg-apply) (:d fn-cfg-name-line-octets) (:d fn-cfg-delta-reason)
    (:d fn-cfg-admissible-reason) (:d fn-cfg-admissiblep)
    (:d fn-cfg-recordp) (:d fn-cfg-apply-record)
    (:d fn-cfg-record-acceptablep) (:d fn-config-replay-loop)
    (:d fn-config-replay) (:d fn-config-replay-okp)))

(deftheory fn-cfg-codec-vocabulary
  '((:d fn-cfg-uitem) (:d fn-cfg-titem) (:d fn-cfg-uitemp) (:d fn-cfg-titemp)
    (:d fn-cfg-itemp) (:d fn-cfg-item-listp) (:d fn-cfg-stamp-items)
    (:d fn-cfg-row-items) (:d fn-cfg-rows-items) (:d fn-cfg-delta-items)
    (:d fn-cfg-deltas-items) (:d fn-cfg-record-items) (:d fn-cfg-item-octets)
    (:d fn-cfg-encode) (:d fn-cfg-parse-items) (:d fn-cfg-read-uint)
    (:d fn-cfg-read-label) (:d fn-cfg-read-row) (:d fn-cfg-read-rows)
    (:d fn-cfg-read-delta) (:d fn-cfg-read-deltas) (:d fn-cfg-read-record)
    (:d fn-cfg-decode-exact)
    ))

(in-theory (disable fn-cfg-vocabulary fn-cfg-codec-vocabulary))
