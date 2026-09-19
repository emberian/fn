# Handoff: w4/config-records (packets R1 and R2)

Lane `w4/config-records`, branched at `ca66782`. Deliverable: durable
configuration as a journal transaction --
[`books/config.lisp`](../../books/config.lisp),
[`books/config-invariants.lisp`](../../books/config-invariants.lisp),
[`books/config-records.lisp`](../../books/config-records.lisp),
[`tests/acl2/config-tests.lisp`](../../tests/acl2/config-tests.lisp),
[`host/config-host.lisp`](../../host/config-host.lisp), and the R1 host change
in `tools/run_store.py`. The landed scope and what is explicitly *not* claimed
are in [`specs/reconfiguration.md`](../../specs/reconfiguration.md) section 8,
which is the walked-back version of the design for everything this lane did
not earn.

## What changed, and why it is shaped this way

- **One typed row instead of five shapes.** Quotas, policy identifiers,
  listeners, peers and resource limits are all `(a b c n)`: three labels and a
  natural, with named accessors per use (`fn-cfg-quota-scope`,
  `fn-cfg-peer-eid`, ...). One recognizer, one codec reader, one round trip.
  The design's five separate list types would have meant five of each.
- **One delta shape instead of eight.** A delta is `(kind a b n rows)`; the
  design's surface syntax survives as the constructors `fn-cfg-create-group`,
  `fn-cfg-remove-group`, `fn-cfg-set-capacity`, `fn-cfg-set-quota`,
  `fn-cfg-set-policy`, `fn-cfg-set-listeners`, `fn-cfg-set-peers`,
  `fn-cfg-set-limit`.
- **Ceilings are arguments, never copies.** `fn-cfg-admissible-reason` takes
  the reservation total and the RFC 3977 section 3.1 initial-line ceiling as
  arguments, so `books/retention` and `books/nntp-syntax` remain their only
  owners. The format ceilings that *are* wire facts (`*fn-record-max-payload*`,
  `*fn-record-max-groups*`) are read from `books/records` through
  `fn-cfg-limit-ceiling`.
- **The codec encodes the record, not the value.** The durable object is the
  record; a value is replayed, never written. The encoding is a count-prefixed
  stream of canonical CBOR items, which makes the whole decode-of-encode one
  induction over the item list rather than a bespoke grammar.
- **`books/replay.lisp` is untouched.** `fn-config-aware-loop` is an
  independently written loop over the two-kind stream; the keystone says it
  agrees with `fn-replay-loop`, fault reasons included, on transaction-only
  histories. Neither loop is defined in terms of the other, so the theorem is
  not vacuous.

## Proposal: the cross-cluster steps this lane could not take

Each is an interface change in a book this lane does not own.

1. **Store cluster (`books/node`, `books/replay`, `books/store-node`).** The
   node gains a fifth slot carrying `(generation value)` and two
   `fn-node-statep` conjuncts: acceptance groups *are*
   `fn-cfg-group-names` of the config at its generation, and retention
   capacity *is* `fn-cfg-capacity`. `fn-node-apply-config` is
   `fn-cfg-apply-record` lifted to the node under
   `fn-cfg-record-acceptablep` with the node's real reservation total.
   `fn-replay-loop` gains the `:config` arm that `fn-config-aware-loop`
   already has; the keystone above is what says the article arm is unchanged.
2. **Core (`books/acceptance`).** `fn-initial-state` loses its `groups`
   argument once the node carries the configuration; `fn-replay`,
   `fn-sf-replay-node`, `fn-sn-open-observed` and `fn-sn-make` lose their
   configuration parameters (packet R2-in-the-node, then R4).
3. **`books/nntp-syntax`.** Export `*fn-nntp-max-initial-line-octets*` to the
   admissibility call site so `host/config-host.lisp`'s
   `fn-cfg-host-line-ceiling` (which repeats `510`) is deleted. This is the
   one twin this lane introduced and it is deliberate and flagged.
4. **Owner lane (packet R3).** `(:reconfigure id deltas)` takes the single
   pending slot; `fn-own-facts` is deleted, because the fact log *is* the
   configuration record history.

## Open, recorded rather than weakened

- **`books/replay` does not certify at `dev`.** `(verify-guards
  fn-replay-loop)` fails on `(IMPLIES (FN-RECORD-P (CAR RECORDS)) (TRUE-LISTP
  (CAR RECORDS)))`: the export-hygiene commit withdrew `(:d
  fn-record-shapep)`, so `fn-record-p` no longer concludes `true-listp`. The
  one-line fix is `(local (in-theory (enable fn-record-record-vocabulary
  fn-record-codec-vocabulary)))` in `books/replay.lisp`, or a
  `:forward-chaining` rule `fn-record-p -> true-listp` exported from
  `books/records`. `books/config-records.lisp` includes `replay` and is
  therefore blocked behind that fix; it is written and its keystones are
  stated. Posted to the board.
- **The 64-bit clock stamp.** Schema 0 encodes the three clock times as
  uint32, so a wall reading beyond 2^32 milliseconds is outside the codec.
  `fn-cfg-stampp` is fail-closed about it rather than silently truncating.
- **The group-table history grows without bound**, as the design already says.
  STO-006 must preserve it as the "relevant policy context" that clause names.
- **Who may submit a reconfiguration** is the deployment profile's question.
  This lane only guarantees that an untrusted *article* cannot.

## Host R1

`run_store.py initialize` writes `config-record` (the octets of
`*fn-cfg-default-record*`, obtained through the bridge) alongside
`config.json`; `recover` reads it and calls `fn-cfg-host-replay-octets`,
refusing with `refusing store with no durable configuration record` when it is
absent and `unusable durable configuration record` when the core will not
decode or replay it -- both refusals, distinct from an uncertain persistence
observation. `DEFAULT_CONFIG` is unchanged in this packet; R4 shrinks it to
the four pure format keys and deletes `*fn-store-groups*`, at which point
`fn-cfg-default-change` is the single line that decides a new store's table.

## Certification status at handoff (2026-09-19, lane close)

Honest state, not a claim: **no `.cert` for the four new books exists yet.**
`books/cbor`, `books/cbor-invariants`, `books/records` and
`books/records-invariants` certified in this worktree. `books/config` was
still in `certify-book` when the lane's budget ran out (the run was relaunched
in the background at close; its log is the scratchpad's `w4-certify.log`), and
the machine was contended with the codecs deputy re-certifying the same
`books/records` closure at the same time. Two defects were found and fixed
during the attempts -- a `member-equal` guard obligation in
`fn-cfg-no-duplicate-namesp`, and missing `:measure (len deltas)` on
`fn-cfg-apply` and `fn-cfg-admissible-reason` -- and the general
decode-of-encode lemma was removed and recorded open when it did not close.
`books/config-invariants`, `tests/acl2/config-tests` and the Python suite
(`tests.test_store tests.test_store_lifecycle tests.test_store_corruption
tests.test_reader`) were queued behind `books/config` and did not run.

Whoever picks this up: `python3 tools/certs.py install` then
`FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py --jobs 1
books/config books/config-invariants books/store-config
tests/acl2/config-tests`, one at a time, and treat every `defthm` in
`books/config-invariants.lisp` as unproved until its certificate exists.
