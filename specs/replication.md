# Replication and disconnected operation

Status: transport-independent batches agreed. Exchange schema and authorization
profile depend on D01, D02, D08–D12, and D15.

## Portable input

REP-001: exchange immutable objects and scoped statements. Local disk offsets,
journal positions, and NNTP group numbers never acquire global identity. Local
acceptance allocates local memberships once under the same rules used by posting.
Incoming bytes do not directly install a remote node's database state.

REP-002: ingestion tolerates duplicates and reordering. Under a fixed specified
validation profile, set union of validated immutable facts is associative,
commutative, and idempotent. Dependency-incomplete input may remain bounded pending
state; it is not falsely accepted as a complete article or undertaking. Forks,
conflicting claims, and policy differences do not disappear through arrival order.

This convergence claim does not require identical local group numbering, policy,
storage quotas, article visibility, or selected legacy variant. Do not extend it
to those projections without separate hypotheses and a resolution specification.

## Batches

REP-003: a batch describes its version, objects, lengths/identities, statements,
dependencies, and intended exchange scope. It can be imported from a connection,
carried media, or BP application payload. Hash and dependency checks precede
semantic publication. Partial transfer progress is resumable and bounded; an
incomplete batch cannot generate a complete-acceptance receipt.

The acceptance unit must be explicit: a container may include independent article
transactions. An article and its required dependency closure are accepted
atomically, while unrelated articles need not wait for the whole container.
The final batch/chunk grammar is D08/D15, not implicitly an archive format.

REP-004: support sending useful bounded batches using previously known peer
inventory. Reconciliation may exchange summaries or Merkle structures, but an
interactive discovery dialogue is not required before every useful delivery.
Peer inventory is evidence of knowledge, not a durable retention promise.
Avoid assuming a link has a low RTT, symmetric capacity, or a reply opportunity.

A Merkle inventory needs a canonical set representation if roots are to be
comparable independent of insertion order. A random local B-tree root is not
automatically that representation. Treat claimed omissions as untrusted until
the relevant reconciliation algorithm establishes what it actually knows.

## Scheduling and transport

The [resumable-object experiment](transfer-experiment.md) implements a first
bounded staging kernel beneath complete-object validation. It reserves declared
bytes and a metadata slot before accepting fragments, retains nonoverlapping
chunks, and reports missing ranges or an unverified candidate. This logical
experiment has no persistent queue, selected exchange encoding, dependency
validator, or application receipt; those remain REP-003/REP-005 work.

REP-005: queue durable work with explicit resource limits, retry state, and policy.
Contacts and monotonic elapsed time arrive as environmental observations.
Scheduling may prioritize small letters and receipts, but starvation and eventual
delivery claims require a specified fairness/resource policy. Wall-clock time is
not a proof of non-delivery or permission to reclaim an obligated object.

REP-006: BP and LTP are adapters/services below fn's application acceptance.
Use an existing BP implementation when adding DTN integration. LTP retransmission
and BP status reports do not substitute for fn's signed/authorized obligation
receipts. BP lifetime and fn retention lifetime are separately specified.

## Authorization and privacy

Limit what each peer can request, introduce, or learn through inventories. A
content-addressed store does not make private object enumeration harmless.
The shared-group first proposal avoids promising confidentiality; D04 determines
whether encrypted groups/letters are required for the first release. End-to-end
encryption would require an explicit metadata-leakage and key-rotation design.
