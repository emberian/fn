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

## Second pass (2026-09-19, after the convergence lane fixed `books/replay`)

`git merge dev` (merge `34e3da6`; conflicts in `planning/ledger.*` taken from
dev, `tools/frame_bridge.py` unioned so `config_record_*` and `format_id` both
survive). `make certs-install` installed 28 of ~100. Certified in place, in
order, each one at a time: `books/replay` **3s OK**, `books/store-config`
**1s OK**, `books/clock` **OK** (its cached certificate was stale against
dev's `clock.lisp` and was deleted first). So the blocking finding is closed:
replay certifies, and `books/config-records` is no longer blocked by it.

`books/config` is the remaining cost centre: it does not finish inside ~12
minutes of `certify-book` on a machine shared with three other lanes. One
cause was found and removed -- the book opened
`fn-cbor-codec-vocabulary`/`fn-record-codec-vocabulary`/`fn-record-invariants-vocabulary`
globally for the whole book, so every `:guard t` definition in it paid for the
whole CBOR and record codec being enabled; after the general
decode-of-encode lemma was withdrawn nothing needed them, and the enable is
gone. The remaining suspect is the guard proof of the deep reader nest
(`fn-cfg-read-record`, `fn-cfg-decode-exact`); the next pass should
`(local (in-theory (disable ...)))` the reader functions between their
definitions, as `books/records.lisp` does at its own `verify-guards` forms.

**Still unverified at this handoff**: `books/config`,
`books/config-invariants`, `books/config-records`, `tests/acl2/config-tests`
have no certificate, and the Python suite has not run. A run covering all of
them plus `tools/ledger.py --write` and `check_scaffold.py` was left going in
the background; its log is the scratchpad's `w4final.log`. Treat every
`defthm` in the three new books as unproved until its certificate exists.

## Third pass (2026-09-19): the four books certify

All four roots now certify, each in under a second of book wall time on this
laptop (ACL2 8.7, SBCL 2.6.8): `books/config` (evidence
`build/acl2/certify-20260919T222842Z-67740`, 0.68 s), `books/config-invariants`
(`certify-20260919T223027Z-68508`, 0.65 s), `books/config-records`
(`certify-20260919T223425Z-70936`, 0.73 s), `tests/acl2/config-tests`
(`certify-20260919T223427Z-70956`, 0.44 s).

**The cost centre was never a guard proof.** Measured on a scratch `ld`
driver with `(set-verify-guards-eagerness 0)` and every function
guard-verified one at a time under a two-million-step limit: every
`verify-guards` in the book, the reader nest included, is 0.00 s. What did
not finish was the *measure conjecture* of `fn-config-replay-loop`, which had
no `:measure` and so was proved by `acl2-count` with
`fn-cfg-record-acceptablep` and `fn-cfg-apply-record` open; it case-split
through admissibility to subgoal depth twenty and hit the step limit. The fix
is `:measure (len records)` with a `:hints` that keeps those two closed. Three
guard defects were also real and are fixed: `(zp count)` in the three counted
readers and in `fn-cfg-take` guards `natp` on a `:guard t` function (now
`(not (posp count))`, the same function); `fn-cfg-decode-exact` needed the
three `books/records` domain facts (`fn-record-read-bytes-success-domain`,
`fn-record-read-uint-success-domain`, `-is-rational`) for its `<` and
octet-list obligations and is now a `verify-guards` with exactly those
enabled; and `fn-cfg-item-octets-are-octets` needed a local
`fn-cbor-octet-listp`-of-`append` lemma.

**Three statements were false as written and are corrected, with teeth.**
This is a correction, not a weakening: each had a concrete counterexample,
now an `assert-event` in `tests/acl2/config-tests.lisp`.
`fn-cfg-groups-create-keeps-the-names-or-adds-one` and
`fn-cfg-group-find-nil-means-not-a-name` hold over a `fn-cfg-group-listp`
(`fn-cfg-group-find` answers `nil` both for "absent" and for a found non-cons
entry; witness `es` = `(nil)`, `name` = `nil`).
`fn-cfg-groups-retire-preserves-group-listp` needs the entry live at `gen`
(retiring at generation 0 an entry created at 1 leaves `retired-gen <
created-gen`); the hypothesis is `fn-cfg-group-livep` opened, which is what
admissibility already checks. `fn-config-replay-loop-generation-counts-records`
needs a numeric starting generation (on the empty history the loop returns
its argument). `fn-config-aware-loop-is-fn-config-replay-on-config-only-
histories` (`books/config-records`) needs the configuration replay not to
fault: on a refused record the aware loop keeps the last good configuration
beside its fault while `fn-config-replay-loop` is `:fault`, by design.
`config-tests` now includes `config-records` so the cluster has one test
book. `fn-cfg-group-shapep-forward-shape` and `fn-cfg-group-entryp-forward-
shape` are exported as forward-chaining rules per docs/proof-style.md.

**Python: `Ran 38 tests`, `FAILED (errors=25)`.** Every error is
`ValueError: write to closed file` at `tools/run_store.py:435`: the host
bridge's ACL2 process has exited before the first call. `host/store-host.lisp`
and `host/store-node-host.lisp` include `books/identity`,
`books/article-fields`, `books/store-observed` and
`books/store-node-resolution`, none of which has a certificate in this
worktree (`make certs-install` placed 28 of ~100). The 13 tests that do not
reach the bridge pass. Open: install those certificates (box/certs cache),
then rerun; nothing in this pass touches the host or the bridge.
