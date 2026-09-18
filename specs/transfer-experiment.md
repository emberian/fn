# Bounded resumable-object assembly experiment

Status: executable ACL2 staging experiment for M4 planning. This is not a
selected portable exchange encoding, a disk queue, a transfer protocol, or an
application-acceptance path.

The kernel in [`books/transfer.lisp`](../books/transfer.lisp) accepts opaque
bounded octet labels, a declared total length, explicit offsets, and bounded
octet chunks. It has no parser for object contents and never calls a Lisp reader
or evaluator. The only representation used here is a logical ACL2 list model;
it does not define raw bytes for a batch/object envelope, a content ID, a
signature preimage, or a persistent record.

## Local profile and reservation

A profile is `(capacity max-object max-chunk max-chunks max-label
max-reservations)`. All fields are natural-number local limits. A label and a
chunk are preflighted against its length limit before their octets are traversed.
`max-chunks` separately limits retained fragments for one reservation, and
`max-reservations` separately bounds active transfer records and their metadata
work, including zero-length objects. State validity checks that count before it
traverses entries or performs pairwise label checks. These are local resource
choices for this experiment, not D15/D16 final values.

`max-chunks = 0` is valid and admits no nonempty fragment. It still permits a
zero-length declaration to produce its explicit empty candidate.

`max-reservations = 0` is also valid, but refuses every new declaration with
`:reservation-limit`, including empty objects. At a positive limit, an empty
object consumes one reservation slot; an equal replay remains `:already-reserved`
and a distinct label at the limit is refused without altering staged evidence.

`reserve(state, label, declared-length)` performs the capacity decision first.
It refuses a length over `max-object`, a new declaration that would make the
sum of active declared lengths exceed `capacity`, and a different declaration
for an already reserved label. A repeated equal declaration is a no-op. Thus a
six-byte object charges six bytes before its first chunk arrives; received byte
count is never used as a substitute for the reservation.

The empty-object case is explicit: reserving declared length zero produces an
empty assembled candidate, `(:candidate nil)`, with no chunks. It is still only
a candidate and creates no application fact, obligation, receipt, or authority.

## Fragment staging and resumption

An entry retains `(label declared-length chunks)`, and every chunk retains
`(offset octets)`. A nonempty incoming chunk must lie entirely in
`[0, declared-length)`. Chunks may arrive in any nonoverlapping order. The
kernel reports missing bytes as explicit `(offset length)` pairs (currently
length-one pairs; a later scheduler can coalesce adjacent pairs while preserving
their covered byte set).

An exact already-retained `(offset octets)` pair is `:duplicate` and leaves the
state exact. A new overlapping range is `:overlap-conflict`; its diagnostic
contains the existing retained chunk and the state is exact. This deliberately
conservative local policy also rejects a partially overlapping byte-identical
piece: only an exact whole-fragment duplicate is idempotent. No arrival-order or
wall-clock winner exists. Empty chunks are explicit no-ops after bounds checks.

Only when every declared offset is present does the result carry
`(:candidate assembled-octets)`. Assembly is sorted by declared offset, so its
bytes do not depend on chunk arrival order. A complete candidate remains staged;
the experiment neither validates nor deletes it.

## Result boundary

Each transition returns `(outcome state diagnostic candidate)`. Rejection and
conflict outcomes preserve the input state. Diagnostics are evidence about the
local staging decision, not receipt messages. In particular, completion cannot:

- issue an application acceptance or retention/forwarding obligation;
- issue or regenerate a receipt;
- authorize a peer, group, operation, or exchange fact;
- validate a hash, signature, dependency, schema, content ID, or object bytes;
- imply durable retention, socket delivery, transport acknowledgement, or
  restart recovery.

This keeps the kernel separate from the validated immutable facts in
[`books/exchange.lisp`](../books/exchange.lisp), whose facts require a separate
validation policy, and from acceptance/retention decisions. It supports the
bounded partial-transfer direction in REP-003, but does not itself satisfy the
M4 persistence, authorization, or codec portions of that requirement.

## Composition still required

A real exchange layer must select a versioned bounded container grammar under
D08/D15; bind the assembled bytes to an independently verified object identity
and signature policy; validate dependencies and authorization; persist transfer
reservation/progress across failures; decide cancellation, expiry, restart, and
incarnation behavior; then invoke the existing acceptance and retention model
under its own capacity/commit rules. The later persistence refinement must not
infer durable fragment progress from a transport acknowledgement or in-memory
state update.

The [preservation book](../books/transfer-invariants.lisp) proves general reserve
and add-chunk state/accounting preservation, including refusal paths. The
[assembly book](../books/transfer-assembly-invariants.lisp) proves candidate
length/octet/retained-byte agreement and exact missing positions. The
[work contract](transfer-work.md) gives value-corresponding costed hot-path
polynomial bounds; public validation/lookup and host runtime costs are separate.
Assertion vectors cover reorder, duplicates, gaps, overlap, capacity/count
limits, empty objects and Lisp-looking bytes. Persistence, codec/cryptographic
validation and an interoperable transfer format remain composition work.
