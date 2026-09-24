# Persistent storage

Status: specialized storage direction agreed. The actual immutable-file Store,
record/replay codecs and live file/node composition are implemented with scoped
proof and fault evidence; see the [refinement contract](store-refinement.md).
Final segment/checkpoint layouts, complete byte/host correspondence and platform
qualification remain open under D06–D09/D14. The separate isolated-slot
`books/journal.lisp` experiment is not the running adapter model.

## Authority and layout

The proposed backend uses append-only object segments, a transaction journal,
and versioned checkpoints. Segment locations and index layouts are local.
Portable objects do not reference filesystem paths or physical offsets.

STO-001: committed journal/checkpoint state is authoritative. Lookup indexes are
derived from it. Rebuilding an index preserves the same committed mappings.
If an index answers a range query, validate completeness as well as correctness of
returned entries; validating individual object hashes does not prove no entries
were omitted. An externally implemented index is part of the trust boundary until
a suitable correspondence/checking argument exists.

Proposed on-disk roles, not a frozen directory ABI:

```text
objects/       active and sealed object segments
journal/       transaction generations
checkpoints/   committed model snapshots and their journal frontiers
staging/       bounded incomplete transfers and transaction input
indexes/       rebuildable lookup/search structures
```

STO-002: acceptance publishes one transaction containing the source references,
duplicate-history effects, all local group allocations, and any obligations or
reservations accepted in that operation. No partially committed cross-post or
promised-but-unaccounted retention can become visible.

## Commit protocol

The semantic phases are:

1. Validate against committed state; reserve resources and stage an identified
   transaction. The proposal is not yet visible to readers.
2. Make all referenced object bytes and their required namespace reachability
   durable according to the platform contract.
3. Make the transaction's complete commit record durable.
4. Publish the committed state and generate the protocol/application success.

STO-003: successful acceptance is emitted only after the corresponding durable
commit result. Host completion events name the transaction and generation; stale,
duplicate, or unrelated completions cannot publish another transaction.

Only one shared-state commit is in flight initially. Network input may continue
within quotas. A disconnected requester does not cancel an already durable
transaction. If it retries, history prevents repeated allocation/effects.

STO-004: a known abort and an indeterminate I/O result are distinct. After an
indeterminate result, fence shared-state mutations and recover before continuing.
Do not assume an error means nothing reached disk. It is valid for an unacknowledged
transaction to appear after recovery; it is not valid for a modeled acknowledged
commit to vanish. Transport/application retries must accommodate that uncertainty.

## Recovery

STO-005: under the [crash model](failures.md), recovery produces an invariant-
preserving committed history containing every acknowledged transaction, with no
partial transaction. Unacknowledged complete commits may also survive. Recovery
checks framing, integrity, dependencies, journal order, and checkpoint linkage.

The exact rule for choosing a journal/checkpoint generation is still open. Do
not implement “pick the newest timestamp.” Incomplete uncommitted tails and
detected damage to committed data have different handling. Quarantine/report
detected corruption; do not silently reinterpret it as successful rollback.
Detecting rollback of an entire otherwise valid store requires an independent
trusted anchor and is outside the crash-only claim until D14 supplies one.

The current journal experiment distinguishes contiguous journal sequence from
acceptance transaction IDs, which are consumed even on a known abort. Its
durable acknowledgement anchor is an explicit assumed input, not a mechanism
implemented by the book. A staged marker makes an abort uncertain because the
marker could survive; recovery must resolve it. That isolated-slot journal is not
connected to the composed node or physical adapter. The actual immutable-file/store-node path is connected and tested; its
remaining physical correspondence is tracked in [store refinement](store-refinement.md).

Object bytes may survive without a committing reference. Such orphans are not
visible articles and are reclaimable only after transaction/recovery roots are
accounted for. Conversely, committed references must never resolve to missing
objects under the stated crash assumptions.

## Checkpointing and compaction

The current compaction tranche publishes an immutable selected transaction
prefix pack containing the exact canonical bytes of every covered Store event.
Recovery validates each surviving covered transaction byte-for-byte against
that pack, permits covered files to be absent after an interrupted reclaim,
and requires a complete contiguous suffix from the coverage boundary.  An
unknown gap or conflicting surviving record is corruption.  Reclaim resumes
by unlinking only the ACL2-issued surviving covered names under the writer
lease and fencing until the transaction-directory barrier succeeds.  The pack
does not summarize or discard semantic history: generic replay still consumes
the reconstructed full event stream, including retention and identity events.
The current native `pack-reclaim` command opens the Store for writing and holds
its exclusive lock through the last unlink and directory barrier. A live owner
or read-only opener holds an incompatible Store lock while a reader uses its
pinned archive, so this command refuses before deletion when such a reader is
active. This is an offline exclusion rule for this command; it is not a general
proof of concurrent physical reclamation under a different storage layout.
One selected pack is limited to 4096 events and 4 MiB of encoded bytes.  Since
this tranche stores the complete canonical prefix rather than a semantic
summary, it cannot compact an arbitrarily large history; rolling packs or a
proved state summary remain future work.

STO-006: replacing history with a checkpoint preserves the full logical state
needed for future behavior, including allocation watermarks, duplicate history,
outstanding obligations, relevant policy context, and receipt/release evidence.
Never checkpoint just the currently visible article list. Evidence is a typed
provenance (RET-007, `books/provenance.lisp`), carried through the checkpoint
as the bounded printable string the record grammar already holds; a
provenance written before the typed value existed is the `:legacy` kind and
keeps its bytes and its meaning.

STO-007: compaction preserves every retained object's exact bytes and identity,
and every required record. The replacement becomes durable and reachable before
old storage is reclaimed. A crash at each phase must recover a complete valid
generation. Temporary space is reserved; no-space during compaction cannot force
deletion of protected content. In-flight readers pin their storage dependencies.

STO-008: stored bytes are checked when used according to the integrity policy.
Detectable corruption triggers explicit degraded/quarantined state. Scrubbing,
redundant copies, repair, and erasure coding are later mechanisms with separate
assumptions; a digest alone does not repair content or guarantee all faults are
detectable. Recovery must not emit a fresh success for missing or corrupt data.

Composed recovery requires both article/retention replay and identity-evidence
replay to succeed. A structurally valid atomic signed article with a missing
historical enrollment is a recovery fault even when its embedded article alone
replays successfully. `fn-sn-recover` leaves the observed history intact and
sets the file phase to `:fault`; recovery barriers cannot turn that state into
`:ready`. `fn-sn-open-observed` reports its existing `:replay` error instead of
opening the seed's empty node. The negative composed trace in
`tests/acl2/store-identity-traces-tests.lisp` exercises this separation;
fresh certification and native corrupt-history startup evidence remain open.

## First executable scope

Model logical transactions before selecting sector alignment, frame lengths,
segment sizes, checkpoint layout, or a disk index. Then refine to bytes and the
chosen platform contract. These choices are M2 exit criteria, not details to
invent independently inside a file-writing adapter.
