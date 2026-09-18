# Local persistence experiment

This M2 experiment connects versioned transaction bytes, replay, and the composed
node to real local file operations. It is not the final segment layout, portable
native-message format, or a platform qualification. The broader
[storage contract](storage.md) and [failure assumptions](failures.md) still apply.

## Scope and representation

Each final file contains one complete local acceptance transaction, including
the exact article payload, all requested local groups, transaction/generation
identity, archive obligation identity/subject/evidence, and abstract charge.
The initial configuration identifies groups and reservation capacity explicitly.
Recovery must rebuild both articles and their archive obligations using the same
ACL2 definitions used in the logical proofs.

A separately persisted local allocation frontier records the next unused
transaction ID. Reserving an ID advances that frontier durably before the core
prepares a post. An aborted or refused attempt may leave a gap; reopening cannot
reuse the reservation. This is local transaction identity, not a portable origin
sequence or an author identity. Exhaustion refuses new attempts.

Local transaction records use an experimental schema 0. Their codec is a bounded
fixed sequence of deterministic CBOR primitives: a magic byte string, schema
version, journal sequence, acceptance transaction ID, generation, Message-ID,
payload, group count and groups, obligation identity, content subject, release
evidence, and charge. The source book defines the exact field domains and golden
vectors. This format is local and provisional; it is not D01/D09's signed native
article envelope. Source bytes never enter a Lisp reader as executable forms.

The first adapter uses one immutable transaction file per sequence. This buys
simple write isolation and fault injection before segment packing/compaction.
Packing these records into segments later needs its own recovery argument. A
complete transaction carries its article once even when it names several groups.

## Publication boundary

The intended adapter sequence is:

1. Hold exclusive ownership of the store. Recover and validate its committed
   history and configuration before preparing new work.
2. Ask the actual node core to prepare the article and archive reservation. If
   it refuses, publish no file and allocate no additional obligation.
3. Encode the complete transaction with the ACL2 record codec. Write a bounded,
   exclusively created staging file and complete its data durability barrier.
4. Atomically give the complete file its final immutable sequence name without
   overwriting an existing record. Complete the final directory's durability
   barrier and all required namespace prerequisites.
5. Only then deliver matching durable completion to the logical node and report
   acceptance. A requester disconnecting does not undo a published transaction.

A failure before any final-name publication attempt can be a known abort because
staging names are never recovery authority. A failed or interrupted publication
attempt, or failed final directory barrier, is indeterminate: fence mutation and
reconcile through recovery. Do not derive a known abort merely from an exception.
An existing final name is not permission to overwrite it.

Configuration creation also needs data and namespace barriers. A stable lock
file mediates cooperating writers; its pathname must not be replaced to evade
an existing lock. Locking is an adapter ownership mechanism, not proof against
an administrator modifying the store behind its back.

The bounded, checksummed allocation frontier is replaced atomically only after
its new file data barrier; its directory barrier precedes use of the reserved
ID. A possibly completed replacement is indeterminate on error. Recovery must
reject a frontier behind committed history, restore the node's next transaction
counter through `fn-replay-advance-txid`, and establish the observed frontier's
data and namespace barriers before allowing another preparation. The adapter
uses the reserved transaction ID as its completion generation.

## Recovery

Read only bounded files in the final namespace. Reject symlinks, inconsistent
names, malformed frames, integrity failures, unknown versions, sequence gaps,
and any decoded record that the core cannot replay. Staging orphans are not
committed transactions. Fault reporting may name a last-good prefix for
diagnosis; it must not report that prefix as an ordinary successfully recovered
store or proceed to mutate it.

Replay requires contiguous journal sequence but permits forward gaps in local
acceptance transaction IDs. Those gaps represent consumed, known-aborted
preparations. A dedicated logical operation advances only an idle/unfenced
transaction counter monotonically before replaying the recorded preparation;
it cannot lower the counter or change existing article numbers/bindings.

Seeing a final filename after an earlier barrier error is not a new durability
proof. Validate the observed history, then complete the necessary directory
barrier before calling the recovered frontier durable and resuming acceptance.
An unacknowledged complete transaction can become committed through that path.
Retrying it must preserve the existing article and obligation.

Initialization can fail after leaving parseable configuration or visible
directories. Recovery therefore re-establishes configuration/frontier data and
store-parent namespace prerequisites as well as the transaction directory
barrier; merely validating their bytes does not settle an earlier I/O failure.

The initial adapter bounds the number and aggregate bytes of recovered records
before building the process input. These are provisional operational limits and
must also restrict new publication, so the adapter does not create a store it
would refuse to reopen. Staging orphans remain outside recovery authority;
best-effort cleanup after a completed commit does not revoke that commit.

The tested development profile fixes two groups (`fn.letters`, `fn.test`), 128
transactions, 32,768 payload octets per article, 65,538 encoded record octets,
and 8,388,864 aggregate record octets on recovery. Configuration is checksummed
and exact-versioned; the adapter refuses other profiles rather than silently
using host defaults. The aggregate cap bounds the temporary all-record replay
input. A future streaming/checkpoint implementation requires its own argument.

An integrity trailer detects the classes of damage covered by its primitive
assumption. It cannot detect replacement by an older entirely valid store.
The earlier journal book's independent acknowledgement anchor is not silently
instantiated by these filenames: anchor realization and the relation between
these adapter steps and the isolated-slot model remain explicit proof work.

## Evidence required for this experiment

Exercise real temporary directories, reopen/replay, duplicate and conflicting
IDs, two-group acceptance, lock contention, truncation/corruption/gaps, orphan
staging, and injected failures before publication and after publication. Verify
that each uncertain result stops further mutation and that recovery reconstructs
both content and charged obligations. Run the actual codec/replay/node in ACL2,
not an independent Python acceptance implementation.

These tests establish process/I/O behavior under injected outcomes. They do not
qualify power-loss behavior of a filesystem, drive, or macOS development machine.
Completed file/directory barriers and write isolation remain A-DURABILITY and
A-WRITE-ISOLATION. The initial reservation ledger uses abstract charges, not a
proved physical disk-space accounting model. Real no-space errors still follow
the same refusal/uncertainty rules; they never authorize deleting retained posts.

Native signatures, gateway attestation, authenticated release, POST injection,
and a production service remain separate work. This local persistence experiment
does not relabel unsigned data as author-signed content.
