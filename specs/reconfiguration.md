# Assured live reconfiguration

Status: design. This document contains no proved theorem. Every ACL2 form below
is a proposed definition or a proposed theorem *statement*; none has been
submitted to ACL2, and nothing here licenses a claim under the
[assurance rules](../AGENTS.md#assurance-rules-adopted-2026-09-18-after-the-independent-review).
The lane that lands each packet earns its own events.

fn today has no configuration. It has *constants*: the carried group list is a
`defconst` in [`books/store-config.lisp`](../books/store-config.lisp), retention
capacity is a `defconst` in [`host/store-host.lisp`](../host/store-host.lisp),
the BP policy/terms/issuer identifiers and the inbound group map are `defconst`s
in [`host/bp-ingress-host.lisp`](../host/bp-ingress-host.lisp), and
`tools/run_store.py` refuses to open a store whose JSON configuration is not
`==` to `DEFAULT_CONFIG`. Adding a newsgroup means recompiling the core and
rewriting every store's configuration file by hand.

The headline feature this design buys is **assured live reconfiguration**: an
operator changes the served configuration of a running node — creates a group,
raises capacity, retires a peer — and the node keeps serving throughout, with a
proof that no reader ever saw half a change, no accepted article was bound to a
group that did not exist, no reservation was lost, and a crash at any instant
recovers the same configuration generation the live node had.

The claim is not "configuration is a file we reread". It is that a
reconfiguration is *a transaction in the same journal, under the same durability
and replay discipline as a post*, and that the machine's existing invariants are
extended to range over it.

## 1. Configuration as durable state

### 1.1 The constant/configuration test

One line decides whether a value stays a `defconst`:

> A constant stays a constant iff it is an RFC fact or a wire/format fact — a
> value two independent implementations must agree on to interoperate. A
> constant becomes configuration iff a reasonable deployment could rationally
> choose a different value and remain the same protocol.

`*fn-nntp-max-command-octets*` (RFC 3977 §3.1) stays. `*fn-record-max-payload*`
(the codec's uint32 field width) stays. `*fn-store-groups*` goes.

### 1.2 The configuration value

A new book `books/config.lisp` owns the prefix `fn-cfg-` (register it in
[`docs/prefixes.md`](../docs/prefixes.md) in packet 1).

```lisp
; A group-table entry is a HISTORY entry, not a membership flag.  Retirement
; records a generation, never a deletion, so an article accepted at generation
; g can still be shown to have named a group that was live at g, and so a local
; number watermark survives removal (NNT-006).
(defun fn-cfg-group-make (name created-gen created-stamp retired-gen policy-id next)
  (list name created-gen created-stamp retired-gen policy-id next))
(defun fn-cfg-group-name        (e) (car e))
(defun fn-cfg-group-created-gen (e) (cadr e))
(defun fn-cfg-group-created-stamp (e) (caddr e))   ; fn-clock-observationp
(defun fn-cfg-group-retired-gen (e) (cadddr e))    ; natp or nil
(defun fn-cfg-group-policy-id   (e) (car (cddddr e)))
(defun fn-cfg-group-next        (e) (cadr (cddddr e)))  ; retained watermark

(defun fn-cfg-value-make (groups capacity quotas policies listeners peers limits)
  (list groups capacity quotas policies listeners peers limits))
(defun fn-cfg-groups    (v) (car v))       ; fn-cfg-group-listp, no duplicate names
(defun fn-cfg-capacity  (v) (cadr v))      ; natp
(defun fn-cfg-quotas    (v) (caddr v))     ; ((scope name . natp) ...)
(defun fn-cfg-policies  (v) (cadddr v))    ; ((slot . id-string) ...)
(defun fn-cfg-listeners (v) (car (cddddr v)))
(defun fn-cfg-peers     (v) (cadr (cddddr v)))   ; ((eid endpoint contact-plan) ...)
(defun fn-cfg-limits    (v) (caddr (cddddr v)))  ; ((slot . natp) ...)
```

Liveness of a group is a question about a generation, never about "now":

```lisp
(defun fn-cfg-group-livep (v gen name)
  (let ((e (fn-cfg-group-entry v name)))
    (and (consp e)
         (natp gen)
         (<= (fn-cfg-group-created-gen e) gen)
         (or (null (fn-cfg-group-retired-gen e))
             (< gen (fn-cfg-group-retired-gen e))))))

(defun fn-cfg-group-names (v gen)   ; the served table AT a generation
  (fn-cfg-live-names (fn-cfg-groups v) gen))
```

`fn-cfg-valuep` is fail-closed against the format ceilings, so no configuration
can name a bound the codec cannot represent:

```lisp
(defun fn-cfg-valuep (v)
  (and (true-listp v) (equal (len v) 7)
       (fn-cfg-group-listp (fn-cfg-groups v))
       (fn-no-duplicatesp (fn-cfg-group-all-names (fn-cfg-groups v)))
       (natp (fn-cfg-capacity v))
       (fn-cfg-quota-listp (fn-cfg-quotas v))
       (fn-cfg-policy-listp (fn-cfg-policies v))
       (fn-cfg-endpoint-listp (fn-cfg-listeners v))
       (fn-cfg-peer-listp (fn-cfg-peers v))
       (fn-cfg-limit-listp (fn-cfg-limits v))
       (<= (fn-cfg-limit v :max-payload) *fn-record-max-payload*)
       (<= (fn-cfg-limit v :max-text)    *fn-frame-max-text*)
       (<= (fn-cfg-limit v :max-groups-per-article) *fn-record-max-groups*)))
```

### 1.3 The configuration generation

```lisp
(defun fn-cfg-make (generation value) (cons generation value))
(defun fn-cfg-generation (c) (car c))
(defun fn-cfg-value (c) (cdr c))
(defun fn-cfgp (c) (and (consp c) (natp (fn-cfg-generation c))
                        (fn-cfg-valuep (fn-cfg-value c))))
(defun fn-cfg-initial () (fn-cfg-make 0 (fn-cfg-empty-value)))
```

The generation counts **configuration records only** — not journal records. The
committed *version* (the owner's `(len records)`) and the configuration
*generation* are deliberately different numbers: a thousand posts leave the
generation at 3. A reader that has not seen a reconfiguration need not be
advanced to answer correctly, and "the reply is consistent with exactly one
generation" stays true across a busy posting period.

### 1.4 The record kind

The journal becomes a two-kind stream. The frame layer already carries a kind
octet; today only `*fn-frame-store-kind*` = 1 is used.

```lisp
(defconst *fn-frame-store-article-kind* 1)   ; unchanged value, renamed
(defconst *fn-frame-store-config-kind*  2)

(defun fn-jrec-make (kind sequence body) (list kind sequence body))
(defun fn-jrec-kind (j) (car j))
(defun fn-jrec-sequence (j) (cadr j))
(defun fn-jrec-body (j) (caddr j))

(defun fn-jrec-p (j)
  (and (true-listp j) (equal (len j) 3)
       (fn-record-uint32p (fn-jrec-sequence j))
       (case (fn-jrec-kind j)
         (:article (and (fn-record-p (fn-jrec-body j))
                        (equal (fn-record-sequence (fn-jrec-body j))
                               (fn-jrec-sequence j))))
         (:config  (and (fn-cfg-recordp (fn-jrec-body j))
                        (equal (fn-cfg-record-sequence (fn-jrec-body j))
                               (fn-jrec-sequence j))))
         (otherwise nil))))
```

A configuration record is a transaction record with the same durability fields
as an article record, plus the typed change and the clock observation that
stamps it (the clock discipline is the owner design (`specs/owner.md`, on the pending owner lane)'s
`fn-own-every-fact-is-clock-stamped`, generalized from group facts to all of
configuration):

```lisp
(defun fn-cfg-record-make (sequence txid generation change stamp)
  (list sequence txid generation change stamp))
(defun fn-cfg-record-sequence   (r) (car r))
(defun fn-cfg-record-txid       (r) (cadr r))
(defun fn-cfg-record-generation (r) (caddr r))   ; the generation this RESULTS IN
(defun fn-cfg-record-change     (r) (cadddr r))  ; a list of deltas
(defun fn-cfg-record-stamp      (r) (car (cddddr r)))
```

### 1.5 The typed deltas

One record carries a *list* of deltas applied left to right. That is what makes
atomicity worth proving: "create fn.dtn and raise capacity" is one generation
bump, and no state ever holds the intermediate value.

```lisp
(defconst *fn-cfg-delta-kinds*
  '(:create-group :remove-group :set-capacity :set-quota :set-policy
    :set-listeners :set-peers :set-limit))
```

| Delta | Form | Effect on the value |
| --- | --- | --- |
| create group | `(:create-group name policy-id)` | appends or revives a group entry at the new generation, restoring `fn-cfg-group-next` if the name was retired |
| remove group | `(:remove-group name)` | sets `retired-gen` to the new generation; the entry, its creation stamp and its watermark stay |
| capacity | `(:set-capacity n)` | replaces `fn-cfg-capacity` |
| quota | `(:set-quota scope name n)` | upserts a quota row |
| policy | `(:set-policy slot id)` | upserts a policy identifier (`:acceptance`, `:terms`, `:issuer-eid`, `:bp-destination`) |
| listeners | `(:set-listeners endpoints)` | replaces the listener list |
| peers | `(:set-peers peers)` | replaces the peer/contact-plan list |
| limit | `(:set-limit slot n)` | upserts a resource limit |

```lisp
(defun fn-cfg-apply-delta (v gen stamp delta) ...)   ; value, total
(defun fn-cfg-apply (v gen stamp deltas)
  (if (consp deltas)
      (fn-cfg-apply (fn-cfg-apply-delta v gen stamp (car deltas)) gen stamp (cdr deltas))
    v))
```

Every delta in one record sees the *same* `gen`, so a group created and a group
retired in one record carry the same generation number. Admissibility (§2.3) is
checked against the record's whole delta list before any of it is applied.

### 1.6 `fn-initial-state` takes no groups

```lisp
(defun fn-initial-state ()
  (fn-make-state nil (fn-initial-nexts nil) nil 0 nil nil))

(defun fn-node-initial-state ()
  (fn-node-make-state (fn-initial-state) (fn-retain-initial-state 0)
                      nil nil (fn-cfg-initial)))

(defun fn-replay (records)
  (fn-replay-loop (fn-node-initial-state) records 0))

(defun fn-sf-replay-node (records frontier) ...)      ; two arguments, not four
(defun fn-sn-open-observed (frontier records) ...)    ; two arguments, not four
(defun fn-sn-make (files node) ...)                   ; two slots, not four
```

An empty history is a node with **no groups and zero capacity**, which accepts
nothing. That is the correct fail-closed floor: a store that has not been
configured cannot accept an article, rather than accepting one into a
compiled-in default.

The node gains a fifth slot and two coherence conjuncts — this pair is the whole
"no mixed generation" story, carried in `fn-node-statep` rather than recomputed:

```lisp
(defun fn-node-make-state (acceptance retention stage bindings config) ...)
(defun fn-node-config (s) (car (cddddr s)))

(defun fn-node-statep (s)
  (and ...                                            ; every existing conjunct
       (fn-cfgp (fn-node-config s))
       ; The acceptance state's served group table IS the configuration's
       ; live table at the current generation.  Not a copy: an equality.
       (equal (fn-state-groups (fn-node-acceptance s))
              (fn-cfg-group-names (fn-cfg-value (fn-node-config s))
                                  (fn-cfg-generation (fn-node-config s))))
       ; The retention ledger's capacity IS the configuration's capacity.
       (equal (fn-retain-capacity (fn-node-retention s))
              (fn-cfg-capacity (fn-cfg-value (fn-node-config s))))
       ; Every accepted article names groups live at ITS OWN generation.
       (fn-cfg-articles-boundp (fn-state-articles (fn-node-acceptance s))
                               (fn-node-config s))))
```

`fn-sn-groups` and `fn-sn-capacity` survive as names, as *derived* accessors, so
the downstream books (`bp-receiver-*-invariants`, `store-node-traces`) keep
their call sites:

```lisp
(defun fn-sn-groups (s)
  (let ((c (fn-node-config (fn-sn-node s))))
    (fn-cfg-group-names (fn-cfg-value c) (fn-cfg-generation c))))
(defun fn-sn-capacity (s)
  (fn-cfg-capacity (fn-cfg-value (fn-node-config (fn-sn-node s)))))
```

### 1.7 Every deleted constant, and where its consumer reads it instead

| Deleted `defconst` | File | Consumer now reads |
| --- | --- | --- |
| `*fn-store-groups*` | `books/store-config.lisp` | `fn-cfg-group-names` of the node's config; `fn-store-group-name`/`-code-in` keep their `groups` parameter and lose their `*fn-store-groups*`-specialized wrappers |
| `*fn-store-group-table-id*` | `books/store-config.lisp` | nothing. A store's group table *is* its configuration record history; `fn-cfg-generation` identifies it exactly, and the id had to be hand-bumped |
| `*fn-store-capacity*` | `host/store-host.lisp` | `fn-cfg-capacity`, via `fn-store-capacity (store)` |
| `*fn-store-max-text*` | `host/store-host.lisp` | `(fn-cfg-limit v :max-text)`, ceiling `*fn-frame-max-text*` |
| `*fn-store-max-payload*` | `host/store-host.lisp` | `(fn-cfg-limit v :max-payload)`, ceiling `*fn-record-max-payload*`; `fn-store-post-boundary` takes the value as an argument |
| `*fn-bpi-host-destination*` | `host/bp-ingress-host.lisp` | `(fn-cfg-policy v :bp-destination)` |
| `*fn-bpi-host-group-map*` | `host/bp-ingress-host.lisp` | `fn-cfg-bp-group-map`, derived from the live group table — the hand-synchronised octet/name pairs disappear |
| `*fn-bpi-host-policy-id*`, `*fn-bpi-host-terms-id*`, `*fn-bpi-host-issuer-eid*` | `host/bp-ingress-host.lisp` | `(fn-cfg-policy v :acceptance)`, `:terms`, `:issuer-eid` |
| `*fn-reader-groups*`, `*fn-reader-archive*`, `*fn-reader-id*`, `*fn-reader-payload*` | `host/reader-host.lisp` | a test fixture: move to `tests/acl2/reader-fixture.lisp` built over an explicit configuration record. The seed archive is not a deployment default |
| `*fn-sim-groups*` | `host/simulator.lisp` | the scenario's own configuration record |
| `DEFAULT_CONFIG["capacity"]`, `["group_table"]` | `tools/run_store.py` | the configuration record history, through the bridge |

`*fn-reader-greeting*` stays: it is a protocol response, not a deployment
choice. All of `*fn-record-*`, `*fn-frame-*`, `*fn-nntp-max-*` stay by the §1.1
test.

`DEFAULT_CONFIG` shrinks to the facts Python needs in order to slice bytes it
does not interpret:

```python
DEFAULT_CONFIG = {
    "format": "fn-store-experiment-5",
    "max_recovery_record_bytes": MAX_RECOVERY_RECORD_BYTES,
    "max_transactions": MAX_TRANSACTION_COUNT,
    "allocation_frontier_format": "fn-store-allocation-frontier-1",
}
```

`_load_config` keeps its exact-equality check against *that* dictionary. Every
value it used to carry that a deployment could choose now lives in the journal,
where ACL2 owns it — which is the [one-owner rule](../AGENTS.md) applied to the
last place Python still held a semantic value.

## 2. The reconfiguration transition in the owner machine

### 2.1 A reconfiguration is a transaction

It is not a side door. It is staged, made durable, and published through
`fn-snrt-step` exactly as a post is, and it takes the same single pending-
transaction slot. This is the mechanism behind most of §3: the owner cannot
have a staged post and a staged reconfiguration at the same time, because
`fn-own-begin` refuses a second claim on `fn-own-pending`.

The owner's event list gains one event and loses one:

```lisp
; replaces (:declare-group name)
(:reconfigure id deltas)
```

`(:declare-group name)` of the owner design (`specs/owner.md`, on the pending owner lane) becomes the special case
`(:reconfigure id ((:create-group name policy-id)))`, and the in-process,
non-persisted fact log it kept — the first open item of that document — is
deleted: the fact log *is* the configuration record history.

```lisp
(defun fn-own-reconfigure (o id deltas)
  (if (and (fn-own-find-conn id (fn-own-conns o))
           (null (fn-own-pending o))
           (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready)
           (fn-clock-observationp (fn-own-clock o))
           (fn-cfg-delta-listp deltas)
           (fn-own-reconfig-admissiblep o deltas)
           (equal (fn-own-conn-config-generation (fn-own-find-conn id (fn-own-conns o)))
                  (fn-cfg-generation (fn-node-config (fn-sn-node (fn-own-store o))))))
      (fn-own-set-pending
       (fn-own-set-staged-config
        o (fn-cfg-record-make
           (len (fn-sf-records (fn-sn-files (fn-own-store o))))
           (fn-state-next-txid (fn-node-acceptance (fn-sn-node (fn-own-store o))))
           (+ 1 (fn-cfg-generation (fn-node-config (fn-sn-node (fn-own-store o)))))
           deltas
           (fn-own-clock o)))
       id)
    (fn-own-refuse o id (fn-own-reconfig-refusal o deltas))))
```

`fn-own-reconfig-refusal` returns a *named reason*, never `nil`: `:no-clock`,
`:busy`, `:not-ready`, `:stale-generation`, or one of the admissibility reasons
of §2.3. The D13 three-outcome rule applies unchanged: refused, uncertain and
accepted stay distinct out to the control-channel reply and the CLI exit code.

### 2.2 Per-connection pinned configuration generation

The connection gains a configuration pin next to its committed-version pin, and
the pin is a *derived* quantity the relation constrains — not an independently
writable field:

```lisp
(defun fn-own-conn-make (id version frontier archive config session) ...)
(defun fn-own-conn-config (c) (car (cddddr c)))
(defun fn-own-conn-config-generation (c) (fn-cfg-generation (fn-own-conn-config c)))

(defun fn-own-conn-okp (conn records)
  (and ...
       (equal (fn-own-conn-config conn)
              (fn-node-config (fn-sf-replay-node
                               (fn-own-take (fn-own-conn-version conn) records)
                               (fn-own-conn-frontier conn))))))
```

`fn-own-view` likewise gains `fn-own-view-config`. `fn-own-open` pins the view's
configuration; `fn-own-advance` re-pins to the newest; nothing else writes it.

### 2.3 The exact rules

**In-flight transactions.** A pending post under generation *g* completes under
*g* or is refused — never under *g+1* silently. Three mechanisms, all needed:

1. The article record gains an eleventh slot, `config-generation`, set at
   prepare time from the node's generation. `fn-record-p` requires
   `(fn-record-uint32p (fn-record-config-generation record))`.
2. `fn-node-prepare` refuses when the offered generation is not the node's:

   ```lisp
   (defun fn-node-prepare (node cfg-gen gen msgid payload groups oid subj ev charge)
     (if (not (equal cfg-gen (fn-cfg-generation (fn-node-config node))))
         node                                   ; refused, node unchanged
       ...))
   ```
3. The single pending slot: while a post is staged, `fn-own-reconfigure`
   refuses with `:busy`, and while a reconfiguration is staged, `fn-own-begin`
   refuses. A post therefore *cannot* straddle a generation bump; the only
   reachable straddle is the client-level one, where a connection began
   composing at *g* and the generation moved before `:begin`, and that is
   refused with `:stale-generation`.

Replay re-runs check 2 on the durable record. A record whose
`config-generation` does not match the replayed node's generation is a
`fn-replay-fault`, not a skipped record — fail closed, never reinterpret.

**Readers.** A connection observes exactly one configuration generation until
it is advanced. `fn-own-read-step` steps `fn-nntp-step` against the connection's
pinned archive and pinned config and writes neither. Only `(:advance id)` moves
the pin; `(:reopen ...)` drops all connections rather than silently re-pinning
them. Stated as `fn-own-conn-config-stable-without-advance` (§3.2).

**Group removal.** Never while any obligation or pin references the group.
Admissibility splits into a replay-checkable layer and an owner layer, because
reader pins are not durable state:

```lisp
(defun fn-cfg-remove-group-node-reason (node name)
  ; Checked at prepare AND at replay.  Fail closed.
  (cond ((not (fn-cfg-group-livep (fn-cfg-value (fn-node-config node))
                                  (fn-cfg-generation (fn-node-config node)) name))
         :no-such-group)
        ((fn-cfg-group-has-articlesp name (fn-state-articles (fn-node-acceptance node)))
         :group-has-articles)
        ((fn-cfg-group-has-obligationsp name node)   ; via fn-node-bindings into fn-retain-pins
         :group-has-obligations)
        ((consp (fn-node-stage node)) :group-staged)
        (t nil)))

(defun fn-own-remove-group-reason (o name)
  (let ((r (fn-cfg-remove-group-node-reason (fn-sn-node (fn-own-store o)) name)))
    (cond (r r)
          ((fn-own-group-pinned-by-readerp name (fn-own-conns o)) :group-pinned-by-reader)
          (t nil))))
```

`fn-own-group-pinned-by-readerp` holds when some connection's
`fn-nntp-session-group` is that name, at *any* pinned generation. The entry and
its watermark are never deleted; `:remove-group` only sets `retired-gen`, so
NNT-006's "allocation watermarks survive removal and restart" is structural
rather than a rule to remember, and re-creating the name resumes its numbering.

**Capacity decrease.** Never below current reservations:

```lisp
(defun fn-cfg-set-capacity-node-reason (node n)
  (cond ((not (natp n)) :capacity-type)
        ((< n (fn-retain-reserved (fn-node-retention node))) :capacity-below-reserved)
        (t nil)))
```

**Group creation.** Admissible only if the resulting served table still renders
inside RFC 3977 §3.1's 512-octet initial line and satisfies
`fn-nntp-safe-group-listp`. Without this, one reconfiguration could make
`fn-nntp-projectionp` fail for every *future* connection while existing pinned
connections kept working — a live, self-inflicted denial of service that the
current whole-archive recognizer would report only as a refusal at open. Reason
`:group-table-unprojectable`.

**Listener and peer changes are effects, not state.** They change what the host
does, never what the model accepts or retains. The configuration value carries
them so that they are durable and replayable; a generation bump that touches
only them emits `(:listen endpoints)` and `(:contact peers)` effects and leaves
acceptance and retention *equal*, which is theorem §3.7.

### 2.4 The whole delta list is admissible or none of it is

```lisp
(defun fn-cfg-node-admissible-reason (node deltas)
  ; Checks each delta against the value accumulated so far, so that
  ; ((:remove-group g) (:create-group g p)) is admissible as a pair and
  ; ((:create-group g p) (:create-group g p)) is :duplicate-group.
  ...)
(defun fn-cfg-node-admissiblep (node deltas)
  (null (fn-cfg-node-admissible-reason node deltas)))
```

## 3. Keystone theorem statements

Each is a *proposed* statement. Teeth are named per hypothesis: every keystone
gets, in `tests/acl2/config-tests.lisp` or `tests/acl2/owner-tests.lisp`, one
reachable non-degenerate witness plus one `must-fail` per hypothesis, as a
concrete instance with that hypothesis dropped. No hypothesis may be the
negation of its own branch test, and no witness may be a state with one group.

### 3.1 Reconfiguration atomicity

No state observes a mix of two generations.

```lisp
(defthm fn-cfg-apply-config-is-atomic
  (implies (and (fn-node-statep node)
                (fn-cfg-recordp record)
                (fn-cfg-node-admissiblep node (fn-cfg-record-change record))
                (equal (fn-cfg-record-generation record)
                       (+ 1 (fn-cfg-generation (fn-node-config node)))))
           (let ((next (fn-node-apply-config node record)))
             (and (fn-node-statep next)
                  (equal (fn-node-config next)
                         (fn-cfg-make (fn-cfg-record-generation record)
                                      (fn-cfg-apply (fn-cfg-value (fn-node-config node))
                                                    (fn-cfg-record-generation record)
                                                    (fn-cfg-record-stamp record)
                                                    (fn-cfg-record-change record))))))))
```

The "no mix" half is carried, not recomputed — it is the pair of equalities in
`fn-node-statep` (§1.6), exported as:

```lisp
(defthm fn-node-state-is-single-generation
  (implies (fn-node-statep node)
           (and (equal (fn-state-groups (fn-node-acceptance node))
                       (fn-cfg-group-names (fn-cfg-value (fn-node-config node))
                                           (fn-cfg-generation (fn-node-config node))))
                (equal (fn-retain-capacity (fn-node-retention node))
                       (fn-cfg-capacity (fn-cfg-value (fn-node-config node)))))))
```

and by the refusal direction, which is what stops a half-applied record:

```lisp
(defthm fn-cfg-inadmissible-config-changes-nothing
  (implies (and (fn-node-statep node)
                (not (fn-cfg-node-admissiblep node (fn-cfg-record-change record))))
           (equal (fn-node-apply-config node record) node)))
```

Teeth. `fn-cfg-apply-config-is-atomic`: drop `fn-node-statep` (a malformed node
whose groups already disagree with its config); drop `fn-cfg-recordp` (a record
with a non-`natp` generation); drop admissibility (a `(:set-capacity 0)` under
a nonzero reservation, which breaks `fn-node-statep` of the result); drop the
generation equality (a record claiming generation `g+7`, so the state's
generation and the record history disagree). Witness: a three-delta record
(`:create-group`, `:set-capacity`, `:set-peers`) over a node with two groups,
one staged-then-completed article and a live reservation, where each of the
three intermediate values differs from the final value.
`fn-node-state-is-single-generation` must not be stated as
`fn-node-statep → fn-node-statep`; the separating witness is a hand-built
5-tuple whose acceptance groups are the *previous* generation's table and whose
config is the next, which must fail `fn-node-statep`.

### 3.2 Reader consistency

Every reply is consistent with exactly one configuration generation.

```lisp
(defthm fn-own-reply-is-one-generation
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o)))
           (let ((conn (fn-own-find-conn id (fn-own-conns o))))
             (equal (car (fn-own-read-step o id event))
                    (fn-nntp-result-effects
                     (fn-nntp-step (fn-own-conn-session conn)
                                   (fn-node-acceptance
                                    (fn-sf-replay-node
                                     (fn-own-take (fn-own-conn-version conn)
                                                  (fn-sf-records (fn-sn-files (fn-own-store o))))
                                     (fn-own-conn-frontier conn)))
                                   (fn-own-conn-config conn)
                                   event))))))

(defthm fn-own-conn-config-is-the-pinned-prefix-config
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o)))
           (let ((conn (fn-own-find-conn id (fn-own-conns o))))
             (equal (fn-own-conn-config conn)
                    (fn-node-config
                     (fn-sf-replay-node
                      (fn-own-take (fn-own-conn-version conn)
                                   (fn-sf-records (fn-sn-files (fn-own-store o))))
                      (fn-own-conn-frontier conn)))))))

(defthm fn-own-conn-config-stable-without-advance
  (implies (and (fn-own-relation o)
                (fn-own-find-conn id (fn-own-conns o))
                (fn-own-no-advance-forp id events)
                (fn-own-find-conn id (fn-own-conns (fn-own-run o events))))
           (equal (fn-own-conn-config (fn-own-find-conn id (fn-own-conns (fn-own-run o events))))
                  (fn-own-conn-config (fn-own-find-conn id (fn-own-conns o))))))
```

Teeth. Witness: two connections open at generations 2 and 3 with a
`(:reconfigure ...)` that creates `fn.dtn` between them; `LIST ACTIVE` on the
older connection must *omit* `fn.dtn` while the newer includes it, and the older
must keep omitting it across a hundred further events. Drop `fn-own-relation`:
a hand-built owner whose connection carries a config generation the record
prefix does not produce. Drop the connection-exists hypothesis: `fn-own-read-step`
on an unknown id returns `nil` effects, while the right-hand side is the reply
of the *stepped* session — a `must-fail` that separates by more than the empty
list, because the chosen event is `LIST ACTIVE`, whose reply is non-empty. Drop
`fn-own-no-advance-forp`: an event list containing `(:advance id)` around a
committed reconfiguration.

### 3.3 Acceptance/configuration binding

Every accepted article names a group that exists at its configuration
generation, and replay reproduces that binding.

```lisp
(defthm fn-node-accepted-article-names-live-groups
  (implies (and (fn-node-statep node)
                (member-equal article (fn-state-articles (fn-node-acceptance node))))
           (fn-cfg-groups-livep (fn-cfg-value (fn-node-config node))
                                (fn-article-config-generation article)
                                (fn-article-groups article))))

; The independent enumeration: the left side walks the node, the right side
; walks the records.  Neither is defined in terms of the other.
(defthm fn-replay-reproduces-acceptance-binding
  (implies (and (fn-jrec-listp records)
                (fn-replay-okp (fn-replay records)))
           (equal (fn-cfg-bindings-of-node (fn-replay-result-node (fn-replay records)))
                  (fn-cfg-bindings-of-records records))))

; An untrusted article can never change configuration (architecture.md).
(defthm fn-node-article-prepare-never-changes-config
  (equal (fn-node-config
          (fn-node-prepare node cfg-gen gen msgid payload groups oid subj ev charge))
         (fn-node-config node)))
```

`fn-cfg-bindings-of-node` collects `(msgid config-generation . groups)` from
`fn-state-articles`; `fn-cfg-bindings-of-records` collects the same triples from
the `:article` journal records, skipping none. An omitted or fabricated binding
fails the equality regardless of whether the rest is right.

Teeth. Witness: an article accepted at generation 2 into a group retired at
generation 3, still bound and still retrievable at generation 4 — the case that
makes the per-article generation load-bearing rather than decorative. Drop
`fn-node-statep`: a node whose articles list holds a membership in a name that
was never created. Drop `fn-replay-okp`: a faulted replay whose node is the
partial one. Drop `fn-jrec-listp`: a record list with a 10-slot article record,
so the eleventh slot reads as `nil` and the binding triple is wrong.
`fn-node-article-prepare-never-changes-config` has no hypotheses, so its tooth
is a separating witness rather than a `must-fail`: a `fn-node-prepare` call
whose `groups` argument is a group name and whose `payload` spells a
`(:create-group ...)` delta, which must leave the configuration untouched.

### 3.4 Reservation preservation across reconfiguration

```lisp
(defthm fn-cfg-apply-config-preserves-reservations
  (implies (and (fn-node-statep node)
                (fn-cfg-recordp record)
                (fn-cfg-node-admissiblep node (fn-cfg-record-change record)))
           (let ((next (fn-node-apply-config node record)))
             (and (equal (fn-retain-reserved (fn-node-retention next))
                         (fn-retain-reserved (fn-node-retention node)))
                  (equal (fn-retain-pins (fn-node-retention next))
                         (fn-retain-pins (fn-node-retention node)))
                  (equal (fn-retain-releases (fn-node-retention next))
                         (fn-retain-releases (fn-node-retention node)))
                  (<= (fn-retain-reserved (fn-node-retention next))
                      (fn-retain-capacity (fn-node-retention next)))))))
```

The fourth conjunct is the one a capacity decrease could break; it is exactly
`fn-retain-accounting-within-capacity` re-established at the new capacity.

Teeth. Witness: a node with three pins totalling a nonzero reservation,
reconfigured by `(:set-capacity r)` where `r` is precisely the current
reservation — the boundary case, admissible, and leaving no headroom. Drop
admissibility: `(:set-capacity (- r 1))`, which must fail the fourth conjunct.
Drop `fn-node-statep`: a node whose `fn-retain-reserved` already exceeds its
capacity. A witness whose reservation is zero does not count: it separates only
by the weakest clause.

### 3.5 Recovery replays configuration

Open-observed yields the same generation as live.

```lisp
(defthm fn-sn-open-observed-config-is-the-replay-config
  (implies (fn-sn-open-okp (fn-sn-open-observed frontier records))
           (equal (fn-node-config
                   (fn-sn-node (fn-sn-open-state (fn-sn-open-observed frontier records))))
                  (fn-node-config (fn-sf-replay-node records frontier)))))

(defthm fn-snt-relation-implies-live-config-is-replay-config
  (implies (and (fn-snt-relation s)
                (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files s))))
           (equal (fn-node-config (fn-sn-node s))
                  (fn-node-config (fn-sf-replay-node (fn-sf-records (fn-sn-files s))
                                                     (fn-sf-frontier (fn-sn-files s)))))))

; The acknowledged-reconfiguration analogue of
; fn-own-completed-post-survives-close-and-any-trace.
(defthm fn-own-acknowledged-reconfiguration-survives-reopen
  (implies (and (fn-own-relation o)
                (member-equal entry (fn-own-cfg-ledger o))
                (fn-sf-crash-imagep (fn-sn-files (fn-own-store o)) frontier records)
                (fn-sn-open-okp (fn-sn-open-observed frontier records)))
           (<= (fn-cfg-entry-generation entry)
               (fn-cfg-generation
                (fn-node-config (fn-sn-node (fn-own-store (fn-own-reopen o frontier records))))))))
```

A-DURABILITY enters exactly where it does today, as the `fn-sf-crash-imagep`
hypothesis. The claim is deliberately `<=`, not `=`: an unacknowledged
reconfiguration in the lost tail is permitted to vanish (STO-004), an
acknowledged one is not.

Teeth. Witness: four configuration records and forty article records, a crash
image that truncates the last article record but not the last configuration
record, reopened, with a fresh connection seeing generation 4. Drop
`fn-sn-open-okp`: an error result whose `fn-sn-open-state` is `nil`. Drop
`fn-sf-crash-imagep`: an image with a *fabricated* fifth configuration record,
which must not be licensed. Drop the ledger membership: a generation the owner
never acknowledged, sitting above the reopened one.

### 3.6 Liveness of application

A durable reconfiguration is observed by every connection that advances.

```lisp
(defthm fn-own-advance-observes-the-committed-config
  (implies (and (fn-own-relation o)
                (fn-own-store-idlep (fn-own-store o))
                (fn-own-find-conn id (fn-own-conns (fn-own-advance o id))))
           (equal (fn-own-conn-config (fn-own-find-conn id (fn-own-conns (fn-own-advance o id))))
                  (fn-node-config (fn-sn-node (fn-own-store o))))))

(defthm fn-own-view-config-generation-is-monotone
  (implies (fn-own-relation o)
           (<= (fn-cfg-generation (fn-own-view-config (fn-own-view o)))
               (fn-cfg-generation (fn-own-view-config (fn-own-view (fn-own-run o events)))))))

; The published-ness half: once the reconfiguration transaction completes at an
; idle phase, the view carries it, so every later advance meets 3.6's conclusion.
(defthm fn-own-completed-reconfiguration-reaches-the-view
  (implies (and (fn-own-relation o)
                (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :completing)
                (fn-own-staged-config o))
           (equal (fn-cfg-generation (fn-own-view-config (fn-own-view (fn-own-complete o))))
                  (fn-cfg-record-generation (fn-own-staged-config o)))))
```

This is application liveness under the owner's own scheduling, not a timing
claim: no wall-clock bound is asserted, and a connection that is never advanced
is never required to observe anything. The honest sentence is "advancing is
sufficient and nothing else is required", and that is what the three statements
say.

Teeth. Witness: a connection open across a committed reconfiguration whose
`LIST ACTIVE` changes exactly at the `(:advance id)` event and not before. Drop
`fn-own-store-idlep`: an owner mid-record-phase, whose view has not refreshed,
where the equality fails. Drop `fn-own-relation`: a hand-built view whose config
is not the store's. Monotonicity's separating witness must include a `:reopen`
in `events` (the only event that could lower a generation, and does not).

### 3.7 Listener and peer changes are effects, not state

```lisp
(defthm fn-cfg-transport-only-change-preserves-the-node
  (implies (and (fn-node-statep node)
                (fn-cfg-recordp record)
                (fn-cfg-transport-only-deltasp (fn-cfg-record-change record)))
           (let ((next (fn-node-apply-config node record)))
             (and (equal (fn-node-acceptance next) (fn-node-acceptance node))
                  (equal (fn-node-retention next) (fn-node-retention node))
                  (equal (fn-node-bindings next) (fn-node-bindings node))
                  (equal (fn-node-stage next) (fn-node-stage node))
                  (equal (+ 1 (fn-cfg-generation (fn-node-config node)))
                         (fn-cfg-generation (fn-node-config next)))))))
```

The generation still bumps — a peer change is durable and ordered — but nothing
a reader or an acceptance decision can see is touched. Tooth: drop
`fn-cfg-transport-only-deltasp` with a change list containing one
`(:create-group ...)`, which must fail the first conjunct.

## 4. What existing theorems change

**`fn-nntp-projectionp` becomes a per-generation verdict.**

```lisp
(defun fn-nntp-projectionp (archive config)
  (and (fn-statep archive)
       (fn-cfgp config)
       (fn-nntp-safe-group-listp (fn-cfg-group-names (fn-cfg-value config)
                                                     (fn-cfg-generation config)))
       (fn-nntp-nexts-boundedp (fn-state-nexts archive))
       (<= (len (fn-state-articles archive)) *fn-nntp-max-article-number*)))

(defun fn-nntp-open-session (archive config)
  (fn-nntp-make-session t nil nil (if (fn-nntp-projectionp archive config) t nil)))
```

NNT-007 is unchanged in force — the recognizer still runs once per connection
open and once per advance, never per command — and gains a new statement, which
is what makes the per-connection verdict meaningful rather than incidental:

```lisp
(defthm fn-nntp-projection-verdict-depends-only-on-the-generation
  (implies (and (equal (fn-cfg-generation c1) (fn-cfg-generation c2))
                (equal (fn-cfg-value c1) (fn-cfg-value c2))
                (equal (fn-state-nexts a1) (fn-state-nexts a2))
                (equal (len (fn-state-articles a1)) (len (fn-state-articles a2)))
                (fn-statep a1) (fn-statep a2))
           (equal (fn-nntp-projectionp a1 c1) (fn-nntp-projectionp a2 c2))))
```

`fn-nntp-step` takes the config, reads the carried verdict, and
`fn-nntp-step-preserves-carried-projection` keeps its shape with the extra
argument. `host/reader-host.lisp`'s `fn-reader-use-store` reads the config from
`fn-node-config` of the store's node instead of assuming one.

**`fn-snt-relation` carries the configuration.** Its `let*` loses `groups` and
`capacity` and every `fn-sf-replay-node groups capacity ...` call drops two
arguments; the `:reserved`, record-phase, `:completing` and `:replaying` arms
are otherwise unchanged, except that the `:replaying` arm compares against
`(fn-node-initial-state)` with no arguments. `fn-snt-relation-implies-observed-
configuration` is replaced by `fn-snt-relation-implies-live-config-is-replay-
config` (§3.5). The seven `bp-receiver-*-invariants` books that name
`fn-sn-initial` and `fn-sf-replay-node` in their `in-theory` hint lists need
those hints updated and nothing else, because `fn-sn-groups`/`fn-sn-capacity`
survive as derived accessors (§1.6).

**NEWGROUPS consumes creation facts.** The command becomes implementable for
the first time, because the creation observation now exists:

```lisp
(defun fn-nntp-newgroups-response (config since)
  (fn-nntp-group-lines
   (fn-cfg-groups-created-after (fn-cfg-value config)
                                (fn-cfg-generation config) since)))

(defthm fn-nntp-newgroups-is-sound-and-complete-at-the-generation
  (implies (and (fn-cfgp config) (fn-clock-observationp since))
           (let ((names (fn-cfg-groups-created-after (fn-cfg-value config)
                                                     (fn-cfg-generation config) since)))
             (and (fn-cfg-all-livep (fn-cfg-value config)
                                    (fn-cfg-generation config) names)
                  (fn-cfg-all-created-afterp (fn-cfg-value config) names since)
                  (fn-cfg-no-live-creation-omittedp (fn-cfg-value config)
                                                    (fn-cfg-generation config)
                                                    since names)))))
```

Soundness and completeness are separate directions against the group-table
history, in the shape [`specs/index.md`](index.md) uses for the index. The
NEWGROUPS row of [`specs/nntp.md`](nntp.md) moves from planned to specified, and
[`specs/nntp-audit.md`](nntp-audit.md) gains its branch rows. A connection
answers NEWGROUPS from its *pinned* generation, so a group created after the
connection opened is not announced until it advances — which is §3.2 applied to
the one command whose whole job is to report reconfiguration.

**The store format id.** `fn-store-experiment-4` becomes
`fn-store-experiment-5`. The bump is load-bearing rather than cosmetic: the
journal is now a two-kind stream, the article record has eleven slots, and a
format-4 store has no configuration records at all. `*fn-store-group-table-id*`
is deleted outright — its whole purpose was to name a compiled table version,
and there is no longer a compiled table. There is no format-4 reader: the
migration is by re-init with a configuration record, because no deployed store
exists (`specs/store-experiment.md` is an experiment).

**`fn-own-every-fact-is-clock-stamped` and friends.** The three group-fact
theorems of the owner design (`specs/owner.md`, on the pending owner lane) are subsumed:
`fn-own-declared-group-is-replayed` becomes §3.5's replay statements over the
real record history, and `fn-own-declare-group-without-clock-is-refused` becomes
`fn-own-reconfigure-without-clock-is-refused` with reason `:no-clock`. The
owner's first open item ("persist the group-configuration fact log") closes.

## 5. Migration

Ordered packets. Each names an owner role from
[`planning/swarm-cycles.md`](../planning/swarm-cycles.md) and an acceptance
criterion that is checkable without reading the implementer's summary.

**Packet R1 — configuration value and record, no behavior change.** Owner:
model. Add `books/config.lisp` (`fn-cfg-` value, group history, deltas,
`fn-cfg-apply`, admissibility reasons), the `fn-jrec` wrapper, the eleventh
article-record slot, and the `:config` frame kind. `fn-initial-state` takes no
groups; `fn-node-initial-state`, `fn-replay`, `fn-sf-replay-node`,
`fn-sn-open-observed` and `fn-sn-make` lose their configuration parameters;
`fn-sn-groups`/`fn-sn-capacity` become derived. `run_store.py init` writes one
configuration record carrying the deltas that reproduce today's constants
(`(:create-group "fn.letters" ...)`, `(:create-group "fn.test" ...)`,
`(:set-capacity 1048576)`, the three limits, the four policy ids). Register
`fn-cfg-` in `docs/prefixes.md`.
*Acceptance: every existing test passes unchanged, against a store whose journal
begins with exactly one configuration record. No test may name a group the
default record did not create. Format id at `fn-store-experiment-5`. The `init`
record's content is a single named constant in `tools/run_store.py`, so it is
one deletable line when packet R4 lands operator-supplied configuration.*

**Packet R2 — the node transition and its keystones.** Owner: model + proofs.
`fn-node-apply-config`, the two `fn-node-statep` coherence conjuncts,
`fn-node-prepare`'s generation check, and §3.1, §3.3, §3.4, §3.7 with their
teeth. `fn-replay-apply-record` dispatches on `fn-jrec-kind` and faults on a
config record whose change is inadmissible or whose generation is not the
successor.
*Acceptance: the four theorems certify with a `must-fail` per stated hypothesis
and the §3 witnesses, including the retired-group-still-bound witness and the
reservation-boundary witness. The delta-list witness must have three deltas with
three distinct intermediate values.*

**Packet R3 — the owner event and the reader pin.** Owner: owner lane. Depends
on the w2 owner landing. `(:reconfigure id deltas)` replaces
`(:declare-group name)`; the connection and view gain their config pins;
`fn-own-conn-okp` gains its derived-pin conjunct; §3.2, §3.5's owner statement
and §3.6 with their teeth. Delete `fn-own-facts`, `fn-own-group-fact-*`,
`fn-own-replay-facts`, `fn-own-declare-group` and the three fact theorems.
*Acceptance: the two-connections-across-a-reconfiguration witness answers
`LIST ACTIVE` differently at the two pins, and keeps doing so across a hundred
further events; the owner state shrinks by one slot rather than growing.*

**Packet R4 — hosts and the CLI.** Owner: host lane. Delete every `defconst`
in §1.7's table; thread the store's configuration into `fn-store-post-boundary`,
`fn-store-group-names`, `fn-bpi-host-policy` and `fn-bpi-host-context`; move the
reader seed to `tests/acl2/reader-fixture.lisp`. `run_store.py` gains
`reconfigure` (deltas in, D13 exit codes out) and `config` (print the generation
and value); `run_owner.py` gains a `RECONFIGURE` control line. `DEFAULT_CONFIG`
shrinks to §1.7's four keys.
*Acceptance: `grep -n '^(defconst' host/*.lisp` returns only format and
protocol constants by the §1.1 test, one line of justification each; a fresh
store created with two groups and a store created with nine serve both without
recompiling; `reconfigure` refusals exit 1, uncertain 3, accepted 0.*

**Packet R5 — NNTP per-generation verdict and NEWGROUPS.** Owner: NNTP lane.
`fn-nntp-projectionp`/`fn-nntp-open-session` take the config;
`fn-nntp-newgroups-response` and its soundness/completeness pair; the audit rows
in `specs/nntp-audit.md`; `specs/nntp.md`'s NEWGROUPS row moves out of "planned".
*Acceptance: NEWGROUPS answered from a pinned generation omits a group created
after the connection opened and includes it after `:advance` — as a transcript
test, not only a model test; the group-table-unprojectable admissibility reason
is exercised by a `:create-group` that would overflow RFC 3977 §3.1's 512
octets.*

**Packet R6 — quotas, peers and contact plans become live.** Owner: BP lane.
The quota and peer/contact-plan slots stop being carried-but-unread: the BP
outbound path reads its peer endpoints and contact plan from the configuration
generation, and the ingress path reads its quota. Requires the BP lanes' own
contact-plan model.
*Acceptance: a peer added by `reconfigure` is contacted without a restart, and
§3.7 still certifies — the acceptance and retention states are untouched by
that change.*

### Requirements and proof registry

Packet R1 adds a requirement row for durable configuration and a proof row per
§3 keystone to `planning/requirements.json` and `planning/proofs.json`; the rows
stay `open` until the owning packet's theorems certify. Counts come from
`tools/ledger.py`, never from this document.

### What this design does not do

No operator authentication or authorization model: *who* may submit a
reconfiguration is the deployment profile's open question
([architecture.md](../docs/architecture.md), "Human/agent identity"), and this
design only guarantees that an untrusted *article* cannot (§3.3). No
configuration checkpointing: the group-table history grows without bound, which
STO-006 will have to preserve when compaction arrives — the history is exactly
the "relevant policy context" that clause already requires a checkpoint to keep.
No multi-node configuration agreement: a configuration generation is local, and
D11's portable group authority is M4 work.

## 8. Status

Packets R1 and R2 landed on lane `w4/config-records`; R3 (model) and R4
(store host) on lane `w5/config-groups`; the two-kind stream decision, the
owner event and the capacity command on lane `w9/reconfig` (2026-09-20).
Contact plans as configuration records and propagation between peers remain
design, with the seams named in the last two bullets of this section.
Everything above this section is still a *proposal* except what this section
names. The landed books do not follow the design's shapes exactly, and the
differences are deliberate:

- **What landed.** [`books/config.lisp`](../books/config.lisp) (the typed
  value, the typed deltas, node-derivable admissibility, the configuration
  record, its canonical CBOR encoding, and `fn-config-replay`),
  [`books/config-invariants.lisp`](../books/config-invariants.lisp) (the five
  replay properties), [`books/config-records.lisp`](../books/config-records.lisp)
  (the two-kind journal record and `fn-config-aware-replay`), and
  [`tests/acl2/config-tests.lisp`](../tests/acl2/config-tests.lisp).
  `tools/run_store.py initialize` writes one default configuration record
  through the bridge and `recover` replays it, refusing a store that has none.
- **Certified 2026-09-19.** `books/config`, `books/config-invariants`,
  `books/config-records` and `tests/acl2/config-tests` each certify in under a
  second (evidence directories in the lane handoff). Three statements were
  false as first written and were corrected rather than weakened, each with a
  concrete tooth in the test book: the two `fn-cfg-group-find` lemmas hold over
  a group list, `fn-cfg-groups-retire-preserves-group-listp` over an entry live
  at the retiring generation, and the config-only agreement of
  `fn-config-aware-loop` with `fn-config-replay-loop` over histories the
  configuration replay accepts (on a refused record the aware loop keeps the
  last good configuration beside its fault; the configuration replay is
  `:fault`). Still open: the general decode-of-encode over a variable-length
  item stream (`books/config.lisp` states it as OPEN; coverage is the ground
  default-record vector), and the host Python suite, whose bridge cannot start
  in a worktree without certificates for `books/identity`,
  `books/article-fields`, `books/store-observed` and
  `books/store-node-resolution`.
- **Keystones proved.** `fn-config-replay-loop-splits-at-any-prefix` (replay is
  a fold, which is what determinism means for a resumed recovery);
  `fn-config-replay-generation-counts-config-records` (the generation is the
  configuration-record count, so a busy posting period does not move it);
  `fn-cfg-groups-retire-keeps-the-watermark` and
  `fn-cfg-groups-create-resumes-the-watermark` (retirement never deletes;
  NNT-006 made structural); `fn-cfg-apply-preserves-valuep` (an admissible
  change preserves the typed value, hence every format ceiling);
  `fn-cfg-recovered-generation-is-at-most-the-live-generation` (STO-004's `<=`,
  with the `=` direction explicitly not claimed);
  `fn-cfg-inadmissible-record-is-not-applied` (the refusal direction: no state
  holds a partially applied delta list); and
  `fn-config-aware-replay-is-fn-replay-on-transaction-only-histories`, which is
  what lets the two-kind stream be adopted without reproving article replay.
- **Shape differences from section 1.** Quotas, policies, listeners, peers and
  limits are one typed row (three labels and a natural) rather than five
  shapes, and a delta is `(kind a b n rows)` rather than eight variant forms,
  with the design's surface syntax kept as constructors (`fn-cfg-create-group`,
  `fn-cfg-set-capacity`, ...). One row type means one codec reader and one
  round trip instead of six.
- **Ceilings that are arguments, not copies.** The reservation total and RFC
  3977 section 3.1's initial-line ceiling enter `fn-cfg-admissible-reason` as
  arguments, so `books/retention` and `books/nntp-syntax` stay their only
  owners. `host/config-host.lisp` currently repeats the number 510 at the one
  call site; that is an open twin, closed by R5.
- **Packets R3 (model) and R4 (store host) landed on lane `w5/config-groups`
  (2026-09-20).** [`books/node-config.lisp`](../books/node-config.lisp) is
  the configured node: `fn-cnode` pairs a `fn-node` state with its
  `(generation value)` configuration as an opaque record, and
  `fn-cnode-statep` carries the coherence of section 1.6 as two equalities.
  The shape differs from section 1.6 in one deliberate way: the acceptance
  state's group list is the allocation **domain** (`fn-cfg-group-all-names`,
  every name the history ever created) rather than the served table, because
  `fn-nexts-for-p` keys the watermarks on exactly that list and `fn-articlep`
  binds every article's groups inside it -- a retired name that left the list
  would lose its watermark and unbind its articles. The served table
  (`fn-cfg-group-names` at the generation) is derived, and admission checks
  it in `fn-cnode-selection-servedp`, the predicate `fn-cnode-prepare` and
  the store host both call. This is what makes NNT-006 structural: retirement
  never touches the acceptance state's watermarks or articles (keystone
  `fn-cnode-apply-config-keeps-watermarks-and-articles`, with the separating
  witness in `tests/acl2/config-tests.lisp`: after retiring `fn.test` the
  served table lacks it, the domain and its watermark 3 stay, both articles
  stay bound, a post into it is refused by the configured node while the
  plain node would still stage it, and revival resumes at local number 3).
  Also proved: `fn-cnode-prepare-stages-only-served-groups` (a staged article
  names the offered groups, every one served at the caller's pin, which is
  the node's generation), `fn-cnode-replay-loop-splits-at-any-prefix` (the
  two-kind replay is a fold), `fn-cnode-recovered-generation-is-at-most-the-
  live-generation` (STO-004, `<=` only), the four `-preserves-state`
  theorems, and the ground equality `fn-cnode-initial-of-the-default-record-
  is-fn-initial-state-of-its-groups`. `books/acceptance`, `books/node` and
  `books/replay` are untouched; `fn-initial-state` keeps its groups argument
  (a core-cluster signature change with whole-tree blast radius, recorded
  open below), and the compatibility statement is the ground equality above.
  The RFC 3977 section 3.1 ceiling is cited once, `fn-cnode-line-ceiling` =
  `*fn-nntp-max-initial-line-octets*`; `fn-cfg-host-line-ceiling` and its
  `510` are gone.
- **Store host (R4).** `*fn-store-groups*`, `*fn-store-group-table-id*`,
  `fn-store-group-code`, `fn-store-group-of-name`, `fn-store-group-names`,
  `fn-cfg-host-default-octets`, `fn-cfg-host-replay-octets` and
  `DEFAULT_CONFIG["group_table"]` are deleted. A store's group table is its
  configuration record history under `config/NNNNNNNN.cfg` (one record per
  generation); `run_store.py init --group <name>...` writes generation 1 from
  its arguments (default: the two experimental groups, so every existing test
  is unchanged), `group create <name>` and `group retire <name>` obtain an
  admitted record from `fn-store-cfg-reconfigure` (the same
  `fn-cnode-record-acceptablep` replay applies, against the live node's
  reservation total) and make it durable, with refused (1), uncertain (3)
  and accepted (0) distinct; `config` prints the generation, served table
  and domain. At open, `fn-store-sn-recover` replays the configuration
  history through `fn-cnode-config-replay` and the article history into a
  node whose domain and capacity come from the configured node; codes are
  positions in the domain, stable across retirement and revival.
- **The two-kind stream, decided (lane `w9/reconfig`).** The layout stays
  two directories -- article records in the transaction journal, configuration
  records under `config/` -- and the STREAM is one: every record of either
  kind carries its position in the unified stream in its own sequence field,
  and recovery merges the two files by that field before it replays anything.
  [`books/config-stream.lisp`](../books/config-stream.lisp) (`fn-cstr-`) is
  that merge. Keystones: `fn-cstr-merge-keeps-every-config-record` and
  `-keeps-every-article-record` (the merge drops nothing and invents nothing;
  the left side walks the merge, the right side walks the input file),
  `fn-cstr-merge-is-sequence-ordered` (two sequence-ordered files merge to one
  sequence-ordered stream, so the split loses no ordering information),
  `fn-cstr-ok-merged-replay-ends-in-a-configured-node` (an `:ok` merged replay
  ends in a state carrying `reserved <= capacity`, which a configuration-only
  replay cannot say because its nodes have replayed no articles), and the two
  per-generation facts a pin observes,
  `fn-cstr-created-group-is-served-exactly-from-its-generation` and
  `fn-cstr-retired-group-is-served-exactly-below-its-generation` -- both
  directions, so a connection pinned below the creating generation must NOT
  see the group. `fn-cnode-replay-loop` and its fold keystone are unchanged.
  The separating witness in
  [`tests/acl2/config-stream-tests.lisp`](../tests/acl2/config-stream-tests.lisp)
  is the argument for the whole decision: one `(:set-capacity 1)` over a
  history whose two articles hold a reservation total of 2, which the
  configuration-only replay accepts (`:ok`, capacity 1, about to replay two
  articles that need 2) and the merged replay refuses at the record with
  `:config-refusal`. Controls: a raise and a decrease to exactly the
  reservation total are both admitted, so the merged replay is not simply
  refusing every decrease.
- **The owner event and the per-connection pin (lane `w9/reconfig`).**
  [`books/owner-config.lisp`](../books/owner-config.lisp) (`fn-ocfg-`) pairs
  the `fn-own` state with its live configuration, a per-connection pin table
  and one staged configuration record. `(:reconfigure id deltas)` takes the
  owner's single pending-transaction slot, so a post and a reconfiguration
  cannot straddle a generation bump; `fn-ocfg-reconfig-refusal` is a named
  reason and never `nil`. Keystones:
  `fn-ocfg-reconfiguration-never-changes-what-an-open-connection-serves`,
  `fn-ocfg-pin-is-stable-without-advance`,
  `fn-ocfg-open-pins-the-live-configuration`,
  `fn-ocfg-advance-observes-the-live-configuration`,
  `fn-ocfg-list-active-lists-the-pinned-served-table`.
  **Deviation from section 2.2**: the pin is a table beside the owner, not a
  ninth slot of `fn-own-conn-make`; `books/owner.lisp` and
  `books/owner-invariants.lisp` are untouched. `fn-ocfg-statep` requires the
  table's domain to be exactly the open connections, which is what makes the
  pin a derived quantity the relation constrains rather than a writable field.
  **Certified** (w11/owner-config, persvati `run-20260921T001423Z-0f98`,
  ACL2 8.7): the book and its new test root `tests/acl2/owner-config-tests`
  both pass, with 74 of 74 roots in the closure. Four of the five keystones
  are PRF-028 events, each with a `pending_subject`: no host line calls any
  `fn-ocfg-` function yet (item 7 below). Two of them carry the hypothesis
  `(fn-ocfg-statep oc)`, which is what makes them true --- see §2.3's reader
  rule and the note on the identifier bound below.
- **Capacity as a configuration change (R6, lane `w9/reconfig`).**
  `fn store capacity <n>` and `run_store.py capacity <n>`;
  `fn-store-cfg-reconfigure` gains `:set-capacity` and hands it to the same
  `fn-cnode-record-acceptablep` replay applies, against the live node's
  reservation total -- the rule is `books/config`'s
  (`:capacity-below-reserved`) and Python owns none of it. Because the two
  kinds are not yet interleaved ON DISK, a decrease carries one extra gate
  before anything becomes durable: the candidate configuration history is
  replayed against the store's real article records in a second core, and the
  record is refused if that store would not open. Three outcomes stay
  distinct: refused 1, uncertain 3, accepted 0. `*fn-store-capacity*` is gone
  from `fn-store-sn-reset`, whose state before any open now has capacity zero
  -- section 1.6's fail-closed floor. It survives in
  `host/checkpoint-host.lisp` only.
- **R7, contact plans as configuration records: OPEN, with its seam.** The
  configuration value has no contact slot and neither does `fn-cfg-peerp`
  (`books/peer-config.lisp`), so a contact plan cannot be written today
  without changing one of the two most depended-on books while another lane
  is certifying both. The design: two delta kinds `:set-contact name rows` /
  `:remove-contact name`, writing rows keyed by peer name and slot-labelled
  `"contact"` into the peers slot, with a slot-aware `fn-cfg-rows-without-key`
  variant so that a contact upsert does not clobber the peer's transport rows;
  and a reader book `books/contact-config.lisp` deriving
  `fn-sched-contact peer start end` (`books/scheduler.lisp` line 66) from the
  configuration generation, with the keystone that a contact read from an
  admissible configuration is a `fn-sched-contactp` and every scheduler
  keystone unchanged. Owner: the BP/scheduler lane, after `books/config` and
  `books/peer-config` are both quiet.
- **R8, propagation between peers: the guarantee is proved, the path is
  OPEN.** The requirement's core -- a group creation on A becomes a
  configuration record on B only through B's own admissibility -- is
  `fn-cnode-article-transitions-never-change-config`
  ([`books/node-config.lisp`](../books/node-config.lisp)): every article and
  ingest transition leaves `fn-cnode-config` equal, so nothing a peer sends
  can move B's served table. The only transition that moves it is
  `fn-cnode-apply-config` on a record B's own `fn-cnode-record-acceptablep`
  admits. What is NOT built: the proposal path. The design, posted on the
  board for the substrate lane: a peer's group creation reaches B as a
  `:proposed-group` artifact that is **not** a configuration record and never
  enters the configuration value -- it is a control-channel notice the
  operator sees and answers with `fn group create`, or a `:policy` statement
  (substrate lane) that a local admissibility rule may consult. Keeping it out
  of the configuration value is what preserves the guarantee above: if a
  proposal were a delta, the theorem that a peer cannot change B's served
  table would have to be reproved and would be weaker. The two-node harness
  scenario (create on A, propose to B, admit on B, post reaches B's new group)
  is NOT in `tools/twonode_gate.py`: `fn group create` refuses while an owner
  is live (the writer lock), so the scenario needs the owner's
  `(:reconfigure ...)` wired into `host/owner-host.lisp`, which is the R5 host
  step this lane did not take.
- **Still open, recorded rather than claimed.** (1) The two-kind stream on
  disk: configuration records live beside the transaction journal, not
  interleaved in it, so a capacity decrease cannot be replayed against the
  reservation total that was live when it was admitted; `set-capacity` is
  therefore not offered by the CLI until the store cluster interleaves the
  kinds (`books/store-files`). (2) The owner event `(:reconfigure id
  deltas)` and the per-connection pin: the standalone reader pins the
  generation it opened at (its `LISTENING` line says so) and holds the
  shared lock, so a reconfiguration while it is open is refused at the lock;
  the two-connections-across-a-reconfiguration witness needs the owner
  (proposal on the board). (3) The plain node's `LIST ACTIVE` lists the
  domain, retired names included, until R5's per-generation projection takes
  the configuration. (4) `fn-initial-state (groups)` keeps its signature.
  (5) `*fn-store-capacity*` in `fn-store-sn-reset`: CLOSED by
  `w9/reconfig` (capacity zero, the fail-closed floor). (6) The `true-listp` hypothesis of
  `fn-cnode-recovered-generation-is-at-most-the-live-generation` has no
  known violating value (the `<=` also holds for an improper prefix); it is
  inherited from the split lemma the proof goes through. The schema-0 stamp
  fields are uint32, so a clock time beyond 2^32 is outside the codec; the
  64-bit stamp is an open item for the next codec schema.
- **Still open after `w9/reconfig`.** (7) The served port answers
  `LIST ACTIVE` from the allocation domain, not from the pin:
  `fn-nntp-dispatch` supplies `(fn-state-groups archive)` at
  [`books/nntp-responses.lisp`](../books/nntp-responses.lisp) lines 225, 308
  and 319, so `fn-ocfg-list-active` is not yet the function the host calls and
  the equating theorem is written down in the book but deliberately not
  stated. The fix is one served-table argument on `fn-served-conn`,
  `fn-served-dispatch` and `fn-nntp-dispatch`; owner, the NNTP cluster. (8)
  `fn-own-reopen` replays the article history only, so the owner cannot state
  the recovered generation; section 3.5's owner statement has no subject and
  is not stated. Its store-level half is proved
  (`fn-cnode-recovered-generation-is-at-most-the-live-generation`,
  `fn-cstr-ok-merged-replay-ends-in-a-configured-node`). (9) The two kinds are
  interleaved in the MODEL and not on disk; `host/store-node-host.lisp` still
  replays configuration first and gates a capacity decrease with a dry-run
  replay instead. (10) `books/owner-config` CERTIFIES as of
  2026-09-20 (w11/owner-config) and its four pin keystones are PRF-028
  events; what is still open about them is item (7), the wire: no host line
  calls any `fn-ocfg-` function, so each event carries a `pending_subject`
  and the equating theorem is recorded rather than stated. Closing the first
  keystone needed one new conjunct of `fn-own-relation`,
  `fn-own-ids-below-next-p` --- every open connection's identifier is
  strictly below `fn-own-next-id` --- which was already true of every
  reachable owner state and merely unstated, so identifier allocation did
  not change.

### Native live administration update (2026-09-21)

The public native operator sends group, capacity, and peer plans through the
bounded FNCT Unix control channel when the configured owner is running. ACL2
decodes the argument vector and reconstructs the existing native-admin plan.
The shared owner stages the delta, the immutable publisher makes the exact
owner-produced configuration record durable, and only then does
`fn-owner-reconfigure-complete` publish the generation and
`fn-owner-feed-configure` refresh the feed table. Newly selected peers gain
FNFD journals before the socket runtime observes them; removed peers lose
their socket worker only when ACL2 removes them from its feed table, while
historical journals remain available for replay. An ambiguous publication
fences the owner and requires reopen. Offline administration remains the
fallback only when no control socket exists.

The offline publisher calls the state-free
`fn-store-cfg-native-admin-authorize` through `fnn-core`: this operation takes
six explicit arguments and returns one authorization value. It neither accepts
ACL2's global `state` nor returns an error/value/state tuple. The raw boundary
regression `tests/native_admin_authorize_boundary.lisp` exercises the deployed
wrapper, its octet-list marshalling, and both accepted and refused observations.
This catches an ABI mismatch found by the native two-node gate; it does not
establish the logical authorization predicate or physical publication safety.
