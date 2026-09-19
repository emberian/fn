# Relay undertaking

Status: wave-2 laboratory profile (C2-07, D12). A relay node is
receiver-then-sender. This specification names what a relay's receipt
promises, what must be durable before the promise may be issued, and the
crash-then-replay argument that keeps the two apart. The executable decisions
are `books/relay.lisp`; the theorems are `books/relay-invariants.lisp` (transition preservation) and `books/relay-crash-invariants.lisp` (crash argument and keystones); the
reachable witness and the teeth are `tests/acl2/relay-tests.lisp`.

## Composed state

The relay state is `(store receiver sender terms undertakings)`:

- `store` is the relay's Store, an input exactly as it is to
  `fn-bpr-accept-request`;
- `receiver` is an `fn-bpr` state (contexts, committed receipt entries, one
  pending receipt intent);
- `sender` is an `fn-bp` state; `fn-relay-statep` requires
  `fn-bp-binding-statep` and pins its node image to `(fn-sn-node store)`;
- `terms` is the relay's terms table: which terms identifier promises what at
  this relay, `:archived` or `:forwarding` (`fn-relay-kindp`). There is no
  destination-application kind; a relay never emits one;
- `undertakings` is the durable ledger of which onward work backs which
  upstream context: `(upstream-work-id onward-work-id)`.

The relay uses only the receiver's public entry points
(`fn-bpr-accept-request`, `fn-bpr-prepare-receipt`, `fn-bpr-commit-receipt`,
`fn-bpr-receipt-adu`) and the sender's dispatcher `fn-bp-step`. It does not
restate the receiver's Store relation, which another lane owns this wave.

## The undertaking rule

RET-001 and RET-003: a receipt that promises onward forwarding is an acceptance
of onward responsibility and may be prepared only when

- (a) the content is durably accepted in the relay's Store:
  `fn-relay-content-durablep` finds the committed article/archive binding the
  request context names, with the context's immutable subject and archive
  obligation id; and
- (b) a durable onward work item exists bound to that content:
  `fn-relay-record-undertaking` requires `fn-relay-onward-durablep`, a work in
  the sender's durable `fn-bp-state-works` (never the pending intent) whose
  Message-ID, subject and archive id are the context's, and records the
  pairing; `fn-relay-undertake` then requires the recorded undertaking and
  `fn-relay-onward-presentp` for its onward work.

An archival-only receipt (`:archived` terms) needs (a) alone. `fn-relay-undertake`
returns `(kind state)` with the kind determined by the terms table and `nil` on
every refusal, including the receiver's own (unauthorized A-POLICY input,
duplicate receipt, live intent, unknown context). The typed receipt
`fn-relay-receipt` is `(kind receipt)` once committed and `nil` while only an
intent exists; the bytes come from `fn-bpr-receipt-adu` as before.

## Crash then replay over both journals

The receiver journal replays to its durable contexts and receipts; a receipt
intent with no outcome is resolved by inspecting the published receipt, which
is `fn-bpr-commit-receipt` with `:committed` or `:absent`. The sender journal
replays through `fn-bp-restart`, which fences a pending intent, and the fenced
intent resolves through `fn-bp-recover` with `:committed` or `:absent`. The
undertakings ledger is durable before any receipt intent relies on it (this is
the proposed FNWF record `(:relay-undertaking upstream-work-id onward-work-id)`,
modeled as the `fn-relay-record-undertaking` transition; its byte grammar is
open). `fn-relay-crash-recover` composes one receiver outcome with one sender
result; every combination is one crash and recovery of the relay.

## What is proved

`fn-relay-invp`: every committed or pending receipt entry has a known kind,
durably bound content, and, when its kind is `:forwarding`, a recorded
undertaking whose onward work is present in the sender's durable works.

- `fn-relay-step-monotone`: `fn-bp-step` never loses a durable work (works are
  only consed, replaced by identity, or mapped by restart).
- `fn-relay-sender-step-preserves-invp`, `fn-relay-accept-preserves-invp`,
  `fn-relay-record-undertaking-preserves-invp`,
  `fn-relay-undertake-preserves-invp`, `fn-relay-commit-receipt-preserves-invp`,
  `fn-relay-crash-recover-preserves-invp`: every transition and every
  crash-recovery combination preserves the invariant.
- `fn-relay-forwarding-receipt-has-durable-onward-obligation`: under the
  invariant, a `:forwarding` typed receipt has its recorded onward work
  present, bound to the node's committed binding (via
  `fn-bp-binding-statep`), and durably bound content.
- `fn-relay-crash-recover-never-yields-a-promise-alone`: the same after any
  crash and recovery. Partial cross-journal completion recovers to no promise
  or to a promise with its obligation.
- `fn-relay-receipt-kind-is-archived-or-forwarding`: the relay commits no
  other receipt kind; destination acceptance is not a relay receipt.

Teeth (`tests/acl2/relay-tests.lisp`): the forwarding intent is refused with no
onward work, with only a pending enqueue, with a durable work but no recorded
undertaking, with a work naming other content, with unknown terms, with
A-POLICY `nil`, and for an unknown context; the crash constructor at the
pending-enqueue point yields no promise for both sender results and at the
receipt-intent point yields no promise or a backed promise; the same bytes
under an archival terms table yield an `:archived` receipt with an empty
sender; a fabricated forwarding receipt with no undertaking is `fn-relay-statep`
and not `fn-relay-invp`.

## Limits

- Content identity in the invariant is the recorded onward work id; the
  Message-ID/subject/archive equalities are checked when the undertaking is
  recorded and are not carried as an invariant across later sender steps. A
  fabricated pending work that shares an id with a durable work but names
  other content is admitted by `fn-bp-statep`; carrying the identity fields
  needs a pending-agrees-with-durable invariant on the sender (open).
- The Store is fixed across the relay's transitions, as in the receiver
  theorems. Ingress between relay steps is not modeled here.
- A-PEER: the promise's meaning to the upstream sender rests on
  `fn-assume-peer-retainsp` for the relay's own onward receipt; nothing here
  proves the next hop honors it.
- No byte grammar for the undertaking record, no host wiring, and no
  destination-application receipt.
