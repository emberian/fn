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

The [refinement contract](store-refinement.md) defines the implemented
immutable-file model and its relationship to the actual replay/node functions.
It explains why the separate isolated-slot journal model does not yet prove
this adapter's behavior.

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

After publication, the host also remains fenced until the matching ACL2 durable
completion succeeds. A rejected completion or missing reply requires recovery,
even when the core may already have completed and the transaction file is
durable. It must not produce a success reply or permit another mutation through
the same host object. Recovery reconciles the retained transaction; it does not
silently discard it to match an older in-memory view.

Configuration creation also needs data and namespace barriers, and it publishes
the same way a transaction does. Initialization writes `config.json` and
`allocation-frontier.json` to exclusively created staging names, completes
their data barriers, links them into place without overwriting an existing
name, and completes the store directory's barrier. Writing them at their final
names in place would let an interrupted first write leave an unparseable store
that no retry can repair. A final name that already exists is loaded and
checked, never replaced.

A stable lock file mediates cooperating writers; its pathname must not be
replaced to evade an existing lock, and opening that pathname is a distinct
outcome from contending for the lock. A missing, non-regular or symlinked lock
pathname is an invalid store state; only a refused lock means another owner
holds the store. Locking is an adapter ownership mechanism, not proof against
an administrator modifying the store behind its back.

Every barrier named here is the platform's strongest available primitive: on
darwin `fcntl(fd, F_FULLFSYNC)`, which asks the device to flush its own write
cache, because `fsync(2)` on APFS returns before that flush. A filesystem that
rejects the request falls back to `fsync(2)` and then carries only the
`fsync(2)` contract. [The host boundary](host.md#durability-barriers-by-platform)
holds the platform table. This chooses the strongest primitive offered; it does
not qualify power-loss behavior, and A-DURABILITY and A-WRITE-ISOLATION remain
assumptions about the device and filesystem.

The bounded, checksummed allocation frontier is replaced atomically only after
its new file data barrier; its directory barrier precedes use of the reserved
ID. A possibly completed replacement is indeterminate on error. Recovery must
reject a frontier behind committed history, restore the node's next transaction
counter through `fn-replay-advance-txid`, and establish the observed frontier's
data and namespace barriers before allowing another preparation. The adapter
uses the reserved transaction ID as its completion generation.
Recovery rereads the on-disk frontier while holding the store lock, including
recovery through the same host object after an uncertain update. A cached
pre-error frontier cannot substitute for the observed replacement.

## Recovery

Recovery closes the host mutation gate before scanning and opens it only after
validation, replay, and all required barriers succeed. An unexpected file-read
or runtime exception cannot leave a previously usable host object unfenced.

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
would refuse to reopen. Every admission path enforces the transaction bound
before allocating or charging, including the BP receiver: a record published
past the bound would make every later reopen fault with no recovery path.
Staging orphans remain outside recovery authority; best-effort cleanup after a
completed commit does not revoke that commit. Recovery enumerates the staging
namespace and reports what it found, bounded for reporting, so an interrupted
publication is visible to an operator; it never deletes a staged name and never
treats one as history.

The tested development profile fixes two groups (`fn.letters`, `fn.test`), 128
transactions, 32,768 payload octets per article, and 8,388,864 aggregate record
octets on recovery. Configuration is checksummed
and exact-versioned; the adapter refuses other profiles rather than silently
using host defaults. The aggregate cap bounds the temporary all-record replay
input. A future streaming/checkpoint implementation requires its own argument.
The group list is no longer written into the configuration:
[`books/store-config.lisp`](../books/store-config.lisp) owns it, the two
directions of the name/code mapping are proved inverse, and a store records
only which version of the table it was written under (`fn-store-groups-1`).
The 65,538-octet encoded-record bound is a model constant, not store
configuration: `books/frame.lisp`'s `*fn-frame-max-store-payload*` is its one
owner, `tools/run_store.py` reads it from the bridge to size its bounded read
and passes no bound to `unframe`, and the configuration no longer carries a
`max_record_bytes` a host could disagree with.
The Message-ID bound is `books/article-fields`'s `fn-af-message-idp` for every
caller, and the charge is `books/identity`'s `fn-charge-for-payload`.

## Framing: what is proved and what is assumed

A transaction file is one frame of the grammar in
[`books/frame.lisp`](../books/frame.lisp), shared with both journals:
magic `FNST`, version, record kind, a four-octet big-endian payload length,
the encoded record, and a 32-octet integrity trailer. Store format
`fn-store-experiment-4` is the current one; a store written under the previous
Python framing, or under the configuration that still carried the record
bound, is refused by its configuration version rather than misread. The
decoder keeps its refusals distinct: a file whose header declares more payload
than the octets hold is `:truncated`, a declared length past the caller's cap
is `:limit`, and `:length` is only octets past the frame the header
describes.

Proved, in [`books/frame-invariants.lisp`](../books/frame-invariants.lisp):
`fn-frame-decode-of-encode` recovers every accepted value, and
`fn-frame-encode-of-decode` reproduces every accepted octet string, so an
accepted frame has exactly one spelling; `fn-frame-decode-bounds-its-payload`
holds the payload inside the caller's cap; and
`fn-frame-decode-refuses-oversize-before-validation` refuses an over-long input
with no hypothesis about its contents, so the refusal precedes octet validation
and every allocation. `tools/run_store.py` computes none of this: `frame` and
`unframe` are bridge calls to `fn-frame-store-protected` and
`fn-frame-store-decode`.

Assumed, as A-CRYPTO: the trailer function. ACL2 constrains `fn-frame-digest`
to yield 32 octets and knows nothing else about it; SHA-256 is computed by the
host over byte strings it does not interpret, and the theorems that connect the
host's entry points to the specification name `fn-frame-digest` in their
hypotheses. An integrity trailer detects the classes of damage covered by that
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

## Composed adapter and completion ownership

The current adapter sends allocator file/replace/directory, transaction
file/link/directory, and recovery-barrier observations to the executable
`fn-sn` composition through `host/store-node-host.lisp`. Reopening uses
`fn-sn-open-observed`, with decoded records and the observed frontier, followed
by five real barriers. Refusal and known prepublication abort call the proved
resolution operations; the host does not reconstruct node semantics.

The host closes its mutation gate before uncertain callbacks. A successful
transaction-directory observation grants one local completion opportunity.
`Store.finish` consumes it before calling actual `fn-sn-finish`; a rejected or
lost reply cannot be retried to bypass recovery, even when the core has already
completed. A lost directory callback grants no completion opportunity. Recovery
and closing the owner clear it. This is effect-delivery bookkeeping, not a
substitute for the core's pending-record binding or completion decision.

Fault tests exercise lost callbacks at allocator start/file/replacement/directory
and record file/link/directory, repeated completion rejection, and actual replay
before later mutation. Process deaths remain distinct from hardware power loss.
