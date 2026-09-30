# Receiver journal proof scope

The receiver invariant books reason about `fn-bpr` operations and the
receiver-only `fn-bprr-apply-record`, `fn-bprr-replay-rest` and
`fn-bprr-replay` journal model. The native host's `fn-bprj-install`
(`host/bp-receipt-journal-host.lisp`) calls `fn-bpaj-replay`, tests its
success flag, and installs the receiver component of the returned joined
state. Its served preflight/apply calls use `fn-bpaj-apply-record-fast`.
These are distinct subjects.

The source-admitted PKT-413 equation in `books/bp-native-app-replay-bridge.lisp`,
`fn-bpaj-replay-receiver-is-receiver-replay`, projects both the actual replay
success flag and its receiver state to the receiver-only replay result.
Its explicit `fn-bpaj-receiver-only-recordsp` hypothesis excludes both
`:request-transit-intent` and `:request-transit-context` records. This is a
proof-domain predicate, never an additional served-path validation. The
initial joined state has no intents or facts and is not strict; successful
context-first records preserve that shape. Refusal retains the same accepted
prefix in both interpreters. Transit is a separate domain: a valid transit
intent succeeds in the join and is refused by the receiver-only model.
`fn-bpaj-replay-rest-receiver-is-receiver-replay-rest` additionally covers
an arbitrary finite suffix from a context-first joined state. Its
`fn-bpaj-context-firstp` premise names the exact pre-transit shape
(receiver, no intents, no facts, non-strict); the receiver itself need not
be well formed because both interpreters refuse malformed receiver states.
The second premise is the same no-transit-record domain. The test book
checks a request plus committed receipt, duplicate-request refusal, the
reachable transit-record separation, and a reachable strict joined state
which refuses a context-first request that the receiver-only model accepts. Source admission, matching
certification, host reach classification and native execution are separate
evidence coordinates; this source statement is not a qualification claim.

## The relation over an evolving Store

The host does not hold the Store fixed: `tools/run_bp_receive.py` runs Store
ingress (`fn-sn-io`, `fn-sn-prepare`, `fn-sn-finish`, lines 210 to 217)
between receiver calls, and a process restart reopens the Store through
`fn-sn-open-observed`. The relation the receiver maintains is therefore
indexed by the Store's record history alone
(`books/bp-receiver-evolving-history-invariants.lisp`, design in
[bp-evolving-store.md](bp-evolving-store.md)):

- `fn-bprv-history-relationalp history st`: every retained context is
  grounded in `history` by a record satisfying `fn-bprv-record-grounds` (the
  live gate `fn-bpr-request-acceptablep` with the Store conjunct replaced by
  history membership); each committed or pending receipt entry is linked to
  its retained context and the canonical receipt constructor; a pending entry
  excludes an already committed receipt for the same work ID.
- `fn-bprv-evolving-invariantp store st journal` adds the typed receiver state
  and a typed `:committed` journal decision for every committed receipt.
- `fn-bprv-system-invariantp store st journal` adds the Store's own
  live-history relation `fn-snt-relation`, which every process holds from its
  reopen entry (`fn-sn-open-observed-success-has-live-history-relation`).

The relation mentions neither the file phase nor the node, so it holds of a
Store in every ingress phase and of the empty post-crash node. The live gate
is not weakened: accepting a new context still requires a `:ready` Store whose
node commits the record.

## Keystones

Monotonicity under the Store (`books/bp-receiver-evolving-store-invariants.lisp`):

- `fn-bprv-store-step-preserves-evolving-invariant`: under `fn-snt-relation`,
  every `fn-snrt-step` (prepare, io, finish, crash, recover,
  refuse-reservation, known-abort) preserves the invariant with the receiver
  state unchanged, because every composed transition extends the history
  (`fn-snrt-step-records-prefix`) and grounding is monotone under prefix
  (`fn-bprv-history-relational-monotone`).
- `fn-bprv-system-run-preserves-invariant`: any finite alternation of Store
  events and journaled receiver records preserves `fn-bprv-system-invariantp`.
- `fn-bprv-evolving-invariant-survives-observed-reopen`: with A-DURABILITY as
  the hypothesis `fn-sf-crash-imagep`, and the image's identity replay
  succeeding (`fn-sn-observed-identity-okp`, the hypothesis every kernel reopen
  guarantee carries since `4857c648`), the host's reopen entry succeeds and the
  invariant holds against the reopened Store.

Preservation under the receiver
(`books/bp-receiver-evolving-history-invariants.lisp`):

- `fn-bprv-acceptable-implies-grounded`: the live gate grounds the derived
  context in the history it inspected.
- `fn-bprv-apply-record-preserves-evolving-invariant` and
  `fn-bprv-replay-rest-preserves-evolving-invariant`: the actual journal
  transition and its finite interpreter preserve the invariant, with the
  journal-membership hypothesis recording provenance.
- `fn-bprv-initial-evolving-invariant` and
  `fn-bprv-successful-replay-has-evolving-invariant`: the initial state and a
  successful replay satisfy it against every Store whose history extends the
  one replayed against.

Grounded receipt:

- `fn-bprv-evolving-output-is-history-grounded`: a nonempty receipt ADU
  implies an exact history record with the request's article and subject, a
  retained committed entry, a matching journal decision and the canonical
  encoding, in every phase.
- `fn-bprv-history-record-is-node-committed-when-idle`
  (`books/bp-receiver-evolving-node-invariants.lisp`): under `fn-snt-relation`
  and an idle phase (`:ready`, `:recovering`, `:fenced-recovery`), every
  article record (`fn-record-p`) of the history is node-committed, because the
  idle node is the replay of the history and replay installs each record's
  article and binding (`fn-bprv-apply-record-installs-record`) which every
  later Store event preserves (`fn-bprv-apply-store-event-keeps-committed`:
  retention and identity events leave articles and bindings alone, the article
  arm is a durable completion).  The history also carries retention and
  statement events (`6ab2c783`, `346a8f99`), which install nothing under their
  own name; the test book commits a retention undertake on a related `:ready`
  Store and shows the conclusion false of it without `fn-record-p`.
- `fn-bprv-evolving-output-is-node-grounded-when-idle`: the node conclusion of
  the original `fn-bprv-replayed-receipt-is-grounded`, under the relation the
  Store maintains instead of a `:ready` hypothesis on a positional argument.

The live receiver trace (`fn-bpr-live-step`, `fn-bpr-live-run`,
`fn-bpr-live-install` over the call sequence of `tools/run_bp_receive.py`):

- `fn-bprv-apply-record-agrees-at-ready-extension`: a receiver step that
  succeeded against the live Store is the same step against every ready
  related Store whose history extends it.
- `fn-bpr-live-state-is-replay-of-journal`: the live receiver state is the
  replay of its journal against every such Store.
- `fn-bpr-live-receipt-regenerated-after-restart`: after any live trace, any
  admissible crash image whose identity replay succeeds, the host's reopen and any recovery trace reaching
  `:ready`, `fn-bprj-install` reconstructs the live state and
  `fn-bprj-receipt-adu` regenerates the same bytes.

The original fixed-Store theorems remain certified in
`books/bp-receiver-*-invariants.lisp`, including
`fn-bprv-replayed-receipt-is-grounded`; they are the `later := store` case of
the restated ones.

## Teeth and scope

`tests/acl2/bp-receiver-evolving-tests.lisp` runs one live trace over a real
Store: a request accepted, an unrelated article ingested with receiver steps
taken while the Store is `:record-staged` and `:completing`, a crash, the
observed reopen, five recovery barriers and the reinstall. The restated
invariant holds at every intermediate state; the retired fixed-Store
`fn-bprv-invariantp` fails at every non-ready phase; the receipt after reinstall
is the receipt the live receiver held. Each keystone has one `must-fail` per
hypothesis in that book.

These are logical theorems over the kernel's transitions and the observed
reopen entry. `:committed` is the durable decision observation supplied by the
adapter; its physical fsync, filesystem, BPA deletion, transport and
authentication behavior are not proved. The two D4 crash points and the
`F_FULLFSYNC` assumption enter as `fn-sf-crash-imagep`. The host obligation
that `fn-bprj-preflight` and `fn-bprj-apply` see the same Store and state
(`tools/receipt_journal.py` lines 56 to 79) is A-HOST; the proofs do not
establish cryptography, liveness, raw Lisp guard verification, or an arbitrary
concurrent disk execution trace. See [receiver semantics](bp-receipt.md) and
[adapter ordering](bp-receive.md).

## Native receipt operator path

The DTN native image's `app-journal receipt-complete` command opens the already
selected Store once, replays FNRJ against that Store, then persists request
context, receipt intent, and committed receipt decision through the actual
`fn-bprj-*` functions named above.  `receipt-replay` in a fresh process
regenerates the canonical nonempty receipt bytes from the durable decision.
The shared `fn-aj` frontier owns the FNRJ name, count, aggregate, frame bound,
and resolution reservation; the shared `fn-jpub` machine owns physical
publication classification.  An empty FNRJ explicitly resets only the receipt
domain state before configuration.

This operator path supplies a concrete native persistence and restart witness.
Wiring it to the native TCPCL receive handler remains a composition join; the
current command receives a bounded request file and Store-record file from its
operator boundary.  Physical barriers and filesystem behavior remain A-HOST.
