# Receiver journal proof scope

The receiver invariant books reason about the existing `fn-bpr` operations and
the actual `fn-bprr-apply-record`, `fn-bprr-replay-rest` and `fn-bprr-replay`
journal interpreters, which are the functions the host calls
(`host/bp-receipt-journal-host.lisp`: `fn-bprj-install` line 12,
`fn-bprj-preflight` line 18, `fn-bprj-apply` line 22, `fn-bprj-receipt-adu`
line 38). They add proof predicates and record witnesses; they do not alter
receipt generation or filter outputs on a desired conclusion.

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
  the hypothesis `fn-sf-crash-imagep`, the host's reopen entry succeeds and the
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
  history record is node-committed, because the idle node is the replay of the
  history and replay installs each record's article and binding
  (`fn-bprv-apply-record-installs-record`) which every later record preserves
  (`fn-bprv-apply-record-keeps-committed`).
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
  admissible crash image, the host's reopen and any recovery trace reaching
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
