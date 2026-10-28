# fn2 execution model: round-2 specification

Build **one semantic executor over bounded, resumable machines**. The reference semantics takes one transition at a time; the host calls a bounded turn that implements a sequence of those transitions. Machine lifetime, I/O lifetime, and commit-batch lifetime remain independent.

The main additional decisions are:

- Use a concrete struct-of-arrays state with one authority for bytes, reservations, and outstanding operations.
- Make the scheduler part of the reference semantics. “Some permitted sequence” must include its fairness rules.
- Reserve completion capacity when issuing an operation.
- Publish a committed root atomically; distribute replies and wake notifications incrementally afterward.
- Treat storage uncertainty as persistent uncertainty until recovery establishes an outcome. A timeout does not establish refusal.
- Page persistent namespaces through bounded caches. Resident capacity must not determine how many objects the store can retain.

All `fn2-*` names below are proposed definitions and obligations, not existing certified functions. The inspected checkout is `3a937ebc3`; [INTERFACES-TODAY.md](build/coordinator/fn2/INTERFACES-TODAY.md) describes `3bbfc4dca`. Its runtime-contract inventory is therefore a revision-scoped source, not a claim about files present in this checkout.

## A. ACL2 realization and proof obligations

### A.1 State and transition granularity

**Yes to a top-level stobj with nested tables by machine kind; no to a separately allocated stobj for every machine instance.**

Use a foundational `fn2-core$c` containing:

- connection, upload, transaction, cursor, commit, wait, TLS-job, and maintenance tables;
- principal accounts and scheduling state;
- pool metadata and the byte array;
- cache metadata;
- outstanding-operation records;
- bounded event/action storage;
- persistent-root references and recovery state.

Each machine table is a struct of arrays. A machine instance is a row identified by `(kind, slot, generation)`. Nested stobjs provide modular access to tables; their nesting is not the logical decomposition of the server.

Access children through `stobj-let`. Cross-table transitions bind all required children together and pass scalar root information explicitly. They must not reach back into the parent while borrowed children are live. This follows the restrictions and examples in [03-modelling-data.md, §3.8](~/dev/acl2aiguide/humans/03-modelling-data.md:1178).

Place an abstract interface over this foundation where it simplifies invariant reasoning. Its logical state contains maps, sequences, and octet-list views; the executable state contains the columns and pool. The logical view is never materialized on the served path.

There are three distinct functions:

| Function | Meaning |
|---|---|
| `fn2-transition` | One enabled semantic transition: consume one observation, run one bounded machine continuation, or perform one scheduler/service transition. |
| `fn2-reference-turn` | Deterministically select and execute transitions until the turn’s budgets are exhausted or no eligible work remains. |
| `fn2-turn` | The host-called concrete implementation, with fixed arrays and optional fused loops. |

A transition need not mean “one byte.” A parser transition may process up to a fixed byte quantum; a query transition may examine a bounded number of entries. Its state records the exact continuation position. The bound covers everything performed by that transition.

Initially, `fn2-turn` should be a straightforward bounded loop over concrete transitions. Optimize this same dispatcher afterward. Do not create a second server to obtain vectorization.

### A.2 What the refinement must say

Let `R(C,S)` relate concrete state `C` to reference state `S`. Include scheduler position, pending actions, reservations, ownership, and operation phases in this relation.

The turn theorem is:

```text
R(C, S) ∧ Inv(S) ∧ BoundaryCompatible(E)
  ⇒
    let (C', A, status) = fn2-turn(C, E)

    there exists a finite transition sequence σ such that:
      σ follows the specified scheduler and observation order
      reference-run(S, E, σ) = (S', Aref, statusref)
      R(C', S')
      Inv(S')
      A = encode-actions(Aref)
      status = statusref
      Cost(fn2-turn) ≤ Qturn(profile)
      emitted-actions ≤ Aturn
```

“Follows the specified scheduler” matters. An arbitrary enabled sequence could preserve safety while starving a principal forever.

The supporting obligations are:

| Obligation | Required content |
|---|---|
| Initialization | The creator establishes the representation relation and a nonempty, useful invariant. |
| Transition preservation | Each transition preserves ownership, resource conservation, pending dependencies, and semantic invariants. |
| Frame property | A transition changes only its declared rows, shared structures, and transferred resources. |
| Guard safety | Every concrete access is in bounds; arithmetic is checked before overflow; arbitrary client octets require no well-formedness premise. |
| Output correspondence | Replies, submissions, cancellations, and posture changes agree, including their order and resource effects. |
| Progress | Budget exhaustion leaves a resumable continuation; dependency blockage records what can make it runnable. |
| Fusion | A fused loop implements the same scheduled transitions, or a proved observationally equivalent permutation of independent transitions. |
| Crash composition | Every submitted action prefix and process-death cut has a corresponding environment execution and recovery state. |

The byte-fill boundary requires its own theorem: an input completion exposes exactly the initialized range written under the corresponding exclusive loan. The adapter cannot mutate other pool bytes or make a still-borrowed range readable.

An abstract-stobj export that performs multiple updates requires the appropriate protection discipline. `:protect t` protects ACL2’s abstraction machinery against interrupted execution; it does **not** prove disk crash consistency. See [03-modelling-data.md, §3.9](~/dev/acl2aiguide/humans/03-modelling-data.md:1312).

These are boundary proofs, not instructions to hand-write a logical twin of every helper. The representation history shows why that distinction matters: efficient islands repeatedly landed while the list paths remained executable. [REPRESENTATION-HISTORY-20261028.md, §§2–4](build/coordinator/REPRESENTATION-HISTORY-20261028.md:53)

### A.3 ATC is an explicit lowering boundary

**Ordinary stobj code is not automatically ATC input.** The inspected ATC interface expects its shallow C representation: C integer recognizers and operations, supported arrays/structures, guard-verified functions, and restricted recursive loop forms. `(unsigned-byte-p 32 x)` alone is not the C type declaration ATC expects. [05-high-performance.md, §5.8](~/dev/acl2aiguide/humans/05-high-performance.md:985), [ATC reference](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php?xkey=C____ATC)

Use the same machine/column declarations to generate:

1. the ACL2 stobj realization;
2. a flat ATC-compatible representation and dispatcher;
3. their representation and transition correspondence obligations.

For the C realization, use flat structures containing integer arrays, or distinct array arguments. Do not depend on arbitrary nested-stobj translation. The relevant demonstrated forms are in [ATC arrays.lisp](~/tools/acl2-fn/acl2-8.7/books/kestrel/c/atc/tests/arrays.lisp) and [ATC structs.lisp](~/tools/acl2-fn/acl2-8.7/books/kestrel/c/atc/tests/structs.lisp).

Additional requirements:

- Loops are singly recursive with explicit decreasing fuel.
- Dispatch uses finite tags, not function-valued continuations.
- Persistent references are integers, never C pointers.
- Pass the byte pool once with offsets; do not pass overlapping slices as supposedly independent objects.
- Establish the target ABI’s widths and alignment.
- Preserve checked arithmetic, action ordering, and ownership through lowering.

ATC’s generated correctness theorem relates its input function to generated C semantics; it does not establish the preceding lowering or the adapter’s behavior. Its pointer theorem also assumes non-overlapping objects. [ATC doc.lisp](~/tools/acl2-fn/acl2-8.7/books/kestrel/c/atc/doc.lisp:1536)

The guide explicitly says ATC’s closure was not certified locally. The upstream test drivers also request tooling trust tags. Thus ATC is a concrete proposed route with a qualification task, not an already established extraction claim under fn’s current no-trust-tag rule.

The first extraction experiment should contain the real ingredients: two machine tables, the shared pool, a reserved action, completion matching, and a budgeted dispatcher. A scalar arithmetic example would not resolve this design question.

## B. Machine catalogue for the first slice

### B.1 Types and capacities

These are **initial simulator-profile values**, not permanent storage ceilings.

| Symbol | Initial capacity |
|---|---:|
| `C` — live connections | 256 |
| `P` — active principal accounts, including the anonymous class | 64 |
| `U` — upload machines | 128 |
| `T` — transaction machines | 128 |
| `X` — query cursors | 256 |
| `W` — parked waits | 256 |
| `Esub` — subscription edges | 4,096 |
| `B` — commit-batch machines | 2 |
| Batch membership/packing | 1,024 records and 4 MiB per batch |
| Large-upload windows | 16, each with two 256 KiB chunks |
| `Jread`, `Jwrite` — storage jobs | 64, 16 |
| `Ltls` — active handshake jobs | 16 |
| `O` — outstanding external operations | 1,024 |
| `Ncancel` — outstanding cancellation requests | 32 |
| Listener accept credits | 8 |
| Cleaning/checkpoint/recovery machines | One each |

Upload rows, large-upload windows, transaction rows, and TAKETHIS credits are distinct resources. A 64-record peer window does not entitle that peer to 64 large-upload windows or 64 records in the next batch.

Common encodings:

| Type | Representation |
|---|---|
| Machine reference `MRef` | `kind:u8, slot:u32, generation:u64` |
| Pool range `Range` | `slot:u32, generation:u64, offset:u32, length:u32` |
| Operation reference `OpRef` | `slot:u32, generation:u64`, scoped to a process incarnation |
| Persistent identity / position | Two `u64` words, with a distinct semantic type for each namespace |
| Disk address and length | `u64`, checked against the opened storage domain |
| Digest | Algorithm tag plus four `u64` words for the initial 256-bit profile |
| Enum / flags | `u8` / `u16` |
| Resource quantities | `u64` per resource dimension |

Finite encodings have explicit exhaustion behavior. No counter wraps into a previously valid identity. Process-local slots may be retired; persistent namespace exhaustion requires an explicit namespace transition or named refusal. These widths do not create resident arrays indexed by all possible identities.

Every machine row also contains:

```text
phase:u8, generation:u64, principal-slot:u16,
account-ref:u32, ready-prev:u32, ready-next:u32,
wait-reason:u8, deadline:u64
```

Persistent registrations and principals are paged records. `P` and `W` limit active execution state, not the number of durable accounts or consumer registrations.

### B.2 State and retained resources

| Machine kind | State enum | Additional retained fields | Account entries |
|---|---|---|---|
| **Listener/connection** | `accepting, greeting, command, article-input, reply, upgrading, closing, draining` | Capability token; RX/TX `Range`; parser offset `u32`; command ordinal and selected view; authentication/configuration references; active request references; outstanding-use count `u32` | Connection, RX/TX bytes, operation credits, reply window, parser work, anonymous admission |
| **TLS admission/job** | `requested, reserved, running, result-ready, cancelling, draining, done` | Connection `MRef`; configuration generation; job `OpRef`; evidence range; negotiated flags; channel-binding digest | Handshake slot, bounded worker memory/work, session-memory reservation, operation and completion credits |
| **Upload** | `head, identity, receiving, validating, discard, sealed, aborting, draining` | Connection/request; source and stored lengths `u64`; scan/hash continuation; two chunk ranges; manifest cursor; Message-ID range; transaction reference; TAKETHIS ordinal | Upload row, chunks, temporary disk extents, hash/scan work, peer-window credit |
| **Transaction** | `admit, lookup, reserve, prepare, ready, batched, accepted, refused, uncertain, draining` | Operation identity; authority/configuration version; identity reservation; membership cursor; dependency-manifest root; proposed index root; batch reference; outcome | Transaction row, identity reservation, storage, index work, commit capacity, retained obligations |
| **Query cursor** | `select, seek, need-page, inspect, render, send, finish, failed` | Request kind; pinned view/root; article/group references; index position; source offset `u64`; render offset `u32`; framing state; pending ranges | Cursor, snapshot obligation, cache pins, output window, read slots, scan/render work |
| **Consumer wait** | `registering, checking, parked, eligible, polling, replying, cancelling` | Consumer/history/incarnation IDs; registration epoch; principal/query/view versions; acknowledged and scanned positions; subscription-edge head/count; pending-wake bit | Wait row, subscription edges, control-output reservation; no worker while parked |
| **Cache/storage job** | `reserve, issue, waiting, verify, ready, failed, cancelling, draining` | Expected block identity/address/digest; pool range; `OpRef`; verification offset; owner/waiter references | Cache bytes/pins, read/write slot, operation credits, verification work |
| **Commit batch** | `collect, seal, dependencies, log-write, fence, durable, install, publish, notify, uncertain, draining` | Batch identity; predecessor head; member list; dependency cursor/count; outstanding counts; packed ranges; proposed root; fence `OpRef`; publication cursor | Batch row, packing bytes, member records, write/fence credits, publication/notification debt |
| **Cleaner** | `choose, inspect, copy, move-commit, retire, reclaim, blocked` | Victim extent/generation; scan/copy offsets; old/new block references; MOVE transaction; retirement frontier | Maintenance work, relocation reserve, cache/I/O, retained old extents |
| **Checkpoint** | `capture, walk, write, seal, install-commit, retire, blocked` | Captured root/frontier; page-walk cursor; new checkpoint root; dependency cursor; installation transaction | Maintenance work, checkpoint space, I/O, old/new root retention |
| **Recovery** | `roots, select, scan, verify, classify, repair, install, serving, damaged, unknown` | Root candidates; selected lineage/frontier; replay and dependency cursors; fault range; evidence reference | Protected recovery memory, I/O, verification work, repair space |
| **Timer/grant/wake services** | `idle, scanning, dispatching, pending` | Bounded heap/list cursors; resource-wait heads; dirty-subscription cursors; latest clock observation | Protected service work; subscription/grant work charged to its originating account where applicable |

Principal accounts are shared ledger rows, not a second executor. They contain limits, protected reservations, current holdings, maintenance debt, runnable-list heads, and scheduling weight. Authentication changes attribution according to a core transition; it does not erase prior costs.

A subscription edge is a separate row:

```text
wait:MRef, stream-id:128 bits,
stream-prev:u32, stream-next:u32,
wait-prev:u32, wait-next:u32, observed-frontier:128 bits
```

One connection link cannot represent membership in several stream lists.

### B.3 Events, actions, and continuation budgets

The following limits are simultaneous limits. Work stops when **any** applicable limit is reached.

| Machine | Consumes | Emits externally | Continuation and maximum work per run |
|---|---|---|---|
| Listener/connection | Accept, receive, send, close results; internal request/outcome notifications | `Accept`, `Receive`, `Send`, `Close`, `Cancel` | At most 4 KiB parsed/rendered, 32 structural transitions, 4 action descriptors |
| TLS | Admission request, TLS result, clock/cancel/release observations | `TlsStart`, `Cancel`, possibly `Close` | At most 32 metadata operations; handshake computation runs in its reserved adapter/worker |
| Upload | Received ranges, identity result, storage result, transaction outcome | Through storage jobs; receive demand goes to connection | At most 4 KiB scanned/hashed/copied and 32 manifest entries |
| Transaction | Sealed upload or consumer mutation; index/dependency results | Through storage/commit machines | At most 32 index entries, comparisons, or preparation units; long byte comparisons also stop at 4 KiB |
| Query cursor | Request, page-ready, send progress/release | `Send`; reads through storage jobs | At most 32 examined entries and 4 KiB inspected/rendered; retain partial row/framing state |
| Consumer wait | Wait/poll/ack request; publication hint; clock; view change | Reply through connection; ack through transaction | At most 32 subscription edges or scan entries and 4 KiB output |
| Cache/storage job | Read/write result, cancel/release result | `Read`, `Write`, `Cancel` | At most 4 KiB verification/copy, 32 metadata operations, 4 descriptors |
| Commit batch | Ready transactions; write/fence results | `Write`, `Fence`; outcomes handed internally | At most 32 members/dependencies or 4 KiB packing/hash work, 4 descriptors |
| Cleaner | Maintenance grant; page/result; MOVE outcome; pin release | Through storage/commit machines | At most 32 entries or 4 KiB copied/verified |
| Checkpoint | Trigger; page/result; installation outcome | Through storage/commit machines | At most 32 entries or 4 KiB encoded/verified |
| Recovery | Root/block results; evidence; repair outcome | `Read`, repair `Write`/`Fence`, service posture | At most 32 entries or 4 KiB verified/replayed |
| Services | Clock observation; resource release; publication | Usually none; timer-arm information if required | At most 32 timers, grants, or subscription edges |

These caps define loop bounds. They are not yet a CPU-cost theorem. Each run must also have a cost certificate covering its scalar work, queue updates, hashing, and descriptor construction.

A 64 KiB I/O window can require sixteen 4 KiB verification runs before it becomes readable. Buffer size and execution quantum need not coincide.

The existing runtime contract supplies useful ownership vocabulary, but its reported served instances are only echo and host leases. The catalogue above must become the actual composed execution path. [INTERFACES-TODAY.md, §9](build/coordinator/fn2/INTERFACES-TODAY.md:612)

## C. Deterministic scheduler

### C.1 Runnable sets

Maintain intrusive FIFO runnable lists per principal. A machine appears at most once.

A machine is eligible when:

1. it has a continuation capable of progress;
2. its prerequisite observations have arrived;
3. the next bounded operation has its necessary resource/output reservation.

Blocked machines sit on indexed dependency or resource-wait lists. The scheduler does not repeatedly inspect every blocked row.

Use four protected service classes:

- commit/publication;
- timers and resource grants;
- subscription notification;
- maintenance/recovery.

These receive execution opportunities independently of client demand. Client-generated work performed there still carries accounting; a system queue is not a way to obtain unlimited service.

### C.2 Selection rule

For the initial equal-share profile, use a fixed calendar of 80 entries:

```text
principal slots  0..15, commit, timer/grant, wake, maintenance
principal slots 16..31, commit, timer/grant, wake, maintenance
principal slots 32..47, commit, timer/grant, wake, maintenance
principal slots 48..63, commit, timer/grant, wake, maintenance
```

An empty entry costs a bounded calendar visit and advances the cursor.

At a principal entry:

1. remove the head eligible machine;
2. execute one bounded run;
3. append it to the tail if still runnable;
4. otherwise put it on its appropriate wait list or retire it.

Newly runnable machines enter at the tail. Repeated wake notifications do not move an already queued machine forward. All unauthenticated connections share the anonymous principal slot.

Weights can later be represented by repeated calendar entries, with a bound on total calendar length. Weight changes are explicit core configuration transitions.

### C.3 Turn bounds and starvation property

Initial turn limits:

```text
H = 128 external observations
K = 64 calendar visits
Aturn = 256 new action descriptors
```

Observation handling does only bounded validation, completion bookkeeping, ownership transfer, and runnable marking. Payload parsing and verification occur in scheduled runs.

Let `qmax` bound a machine run, `cevent` bound observation bookkeeping, and `csched` bound a calendar visit:

```text
Cost(turn) ≤ H·cevent + K·(csched + qmax) + creturn
```

The implementation must account for any additional loop under one of those terms.

For calendar length `L`:

- A continuously eligible principal receives a service opportunity within `L` visits.
- With at most `m` runnable machines in that principal’s account, a continuously eligible machine receives a run within `L·m` visits.
- In full turns, a conservative bound is `1 + ceil(L·m/K)` turns.

This guarantees scheduling opportunities. Request completion additionally requires finite remaining work and available dependencies. Disk completions, network consumption, and clock observations need explicit environment progress assumptions.

Protected I/O, memory, and commit reservations are also necessary: CPU fairness cannot overcome a peer holding every disk slot or every non-reclaimable buffer.

### C.4 Fusion and dependencies

Start with **order-preserving fusion**: combine consecutive scheduled runs of the same machine kind, preserving their selection and effects. Re-evaluate eligibility and scheduling effects at each logical boundary.

Reordering nonconsecutive runs requires a commutation theorem covering:

- shared rows;
- resource acquisition;
- action order;
- scheduler updates;
- newly runnable machines;
- visibility and authority versions.

Commit completion cannot jump ahead merely because “commit” is processed before “read.” Publication can enable a waiter; that dependency is represented in state.

The executor may wait externally only when no eligible internal continuation remains. Machines waiting solely for adapter submission capacity allow an external wait; machines with remaining parsing, expiry, recovery, or notification work do not.

The distinction between safety and this progress claim is already explicit in [04-modelling-systems.md, §4.4](~/dev/acl2aiguide/humans/04-modelling-systems.md:516).

## D. Event and action vocabulary, with capacities

### D.1 Queue contract

Use one bounded outstanding-operation table and persistent action outbox.

An operation reservation includes:

- one operation slot;
- one pending action descriptor;
- the physical resource/window it uses;
- sufficient completion storage for its permitted lifecycle;
- any eventual buffer-release notification.

For the first slice, use single-shot accepts, receives, reads, and sends. Each submission produces at most:

1. one terminal/result observation;
2. one separate release observation, when required.

A short send terminates that submission. Sending the remainder requires a new core-issued action. This avoids an unbounded stream of progress events under one reservation.

Capacities:

| Storage | Capacity | Rule |
|---|---:|---|
| Outstanding operations `Qop` | `O = 1,024` | Includes issued operations and operations still awaiting physical release |
| Pending action outbox `Qa` | 1,024 descriptors | At most one unsubmitted descriptor per reserved operation |
| Reserved result storage `Qr` | `2O = 2,048` observations | Credits reserved before submission |
| Unsolicited control inbox `Qc` | 32 descriptors | Bounded input ranges separately reserved |
| Clock observation mailbox | 1 | Coalesced observation with explicit semantics |
| Diagnostic queue | 64 bounded records | Best effort; drops counted |
| Internal runnable membership | One link per machine | No duplicated enqueue records |
| Wait registrations / subscription edges | `W / Esub` | Reserved before registration |

Malformed or duplicate observations cannot steal the credits reserved for genuine operation completion. Their validation and reporting must themselves be bounded. Liveness does not assume an adapter may inject an infinite hostile stream while withholding all real completions.

The kernel ring, worker queues, and TLS adapter have additional physical capacities. Each backend must prove its mapping to this contract. `CQ = 2 × SQ` alone is not that proof.

### D.2 Events

All operation-associated events carry the process incarnation, `OpRef`, and appropriate machine/range generation. These common fields are omitted below.

| Event | Fields beyond common token | Permitted producer | Reservation / queue | At exhaustion |
|---|---|---|---|---|
| `AcceptResult` | Status; connection capability; fixed-width peer address/credentials | Network adapter, in response to `Accept` | Reserved connection/accept credit; `Qr` | Stop issuing accepts; no unreserved accepted connection enters the core |
| `ConnectResult` | Status; capability | Network adapter | Connection and operation credit; `Qr` | New attempts wait for admission |
| `ReceiveResult` | Status; initialized range; byte count | Network/TLS adapter | RX bytes and operation credit; `Qr` | No further receive issued |
| `SendResult` | Consumed prefix length; status; release-pending flag | Network/TLS adapter | TX borrow and operation credit; `Qr` | Further sends wait; bytes remain borrowed as required |
| `BorrowReleased` | Borrow identity and range generation | Adapter after physical access ends | Second result credit; `Qr` | Must be deliverable from its reserved credit |
| `ReadResult` | Status; initialized range; actual count | Storage adapter | Read slot, input range; `Qr` | New reads wait |
| `WriteResult` | Status; known progress, if meaningful; uncertainty classification | Storage adapter | Write slot, immutable range; `Qr` | New writes wait; failure does not imply rollback |
| `FenceResult` | Storage domain; fence identity; status | Storage adapter | Fence slot; `Qr` | No further fence issued until slot available |
| `CancelResult` | Target `OpRef`; cancelled/not-found/not-cancellable status | Adapter | Separate cancel operation credit; `Qr` | Cancellation requests remain pending in core state |
| `CloseResult` | Capability; status | Network adapter | Close operation credit; `Qr` | Connection remains closing/draining |
| `TlsResult` | Status; protocol attributes; peer-evidence reference; channel binding | TLS adapter | TLS job, evidence bytes, `Qr` | Admission waits; no executor-blocking handshake |
| `EntropyResult` | Initialized range; status | Entropy adapter | Reserved entropy operation/range; `Qr` | Consumers of fresh entropy remain blocked |
| `ClockObserved` | Monotonic value; realtime value; validity flags | Clock adapter | One mailbox | Coalesce according to the declared observation rule; expiry work remains budgeted |
| `ControlObserved` | Kind; caller capability; bounded payload reference | Local control/signal adapter | `Qc` and input-byte credit | Backpressure; shutdown may use a sticky bit; configuration updates are not silently discarded |
| `EvidenceObserved` | Witness identity/scope and bounded encoded evidence | Authorized control/client ingress | `Qc` or ordinary request resources | Wait/backpressure; core verifies evidence before relying on it |

`ClockObserved` records time; it does not select a machine. Backward or malformed readings are classified by core policy. Wall time never determines commit order.

`Run`, `PageReady`, `TransactionOutcome`, `ResourceAvailable`, and `SubscriptionDirty` are internal notifications. Implement them as durable-in-memory state bits or reserved links, not an unbounded message queue.

### D.3 Actions

Only the core emits these actions.

| Action | Fields | Reservation consumed / capacity | At exhaustion |
|---|---|---|---|
| `Accept` | Listener capability | One of 8 accept credits, reserved connection slot, `Qop/Qa/Qr` | Listener continuation waits |
| `Connect` | Bounded address; connection reference | Connection, network-operation credit | Connection continuation waits |
| `Receive` | Capability; writable `Range` | RX window; one receive per connection initially | Stop reading that connection |
| `Send` | Capability; at most 4 immutable ranges; transport mode | TX window; one send per connection initially; release credit if needed | Retain reply continuation and borrowed bytes |
| `Close` | Capability; close mode | Close operation credit | Retain closing state; do not recycle slot |
| `Read` | Storage domain; offset; writable range | `Jread = 64`; aligned bytes | Cache/query/recovery continuation waits |
| `Write` | Domain; offset; immutable range; durability flags | `Jwrite = 16`; maximum 256 KiB per submission | Write continuation waits |
| `Fence` | Domain; dependency/fence token | One fence in flight for the initial storage domain | Commit machine waits |
| `Cancel` | Target `OpRef` | `Ncancel = 32`; separate operation/result credit | Mark cancellation owed; retain target resources |
| `TlsStart` | Capability; config generation; bounded identity inputs | `Ltls = 16`, worker/session-memory reservation | TLS admission waits or refuses before undertaking work |
| `Entropy` | Writable reserved range | One outstanding request initially | Entropy-dependent continuation waits |
| `ArmWake` | Observation-generation token; deadline | One replaceable wake request | Coalesce; no lost requirement to wake by the earliest active deadline |
| `Trace` | Kind; bounded fields/range | 64 diagnostic records | Drop/count; never drop semantic evidence |
| `ServicePosture` | Serving/read-only/damaged/unknown/stopping; reason and scope | Fixed state/mailbox | Replace with current posture; preserve durable reasons in the store where required |

`Commit`, `AcceptPost`, `WakeConsumer`, `GrantBuffer`, and `RefuseCommand` are not host primitives.

Actions already emitted remain represented until consumed by the adapter. A full outbox is ordinary backpressure. The core must reserve output space before a transition requiring an action, or retain a bounded pending-action continuation.

## E. Repaired durability protocol

### E.1 Batch authority

The initial implementation has one ordered commit stream per storage domain. Two batch slots allow preparation beside an in-flight batch; they do not permit a later batch to publish past an unresolved predecessor.

A sealed batch identifies:

- history and storage incarnation;
- batch identity and predecessor head;
- ordered transaction identities;
- exact dependency references, lengths, and digests;
- the resulting committed-root reference;
- format and integrity information.

The dependency manifest is paged. Its size does not require the complete dependency graph to reside in memory.

Identity reservations and tentative numbering are core state. Unfinished uploads are excluded from sealing a ready batch. A stalled uploader cannot hold completed transactions out of a batch merely by arriving first.

### E.2 Commit-batch state machine

| Phase | Work and exit condition | Failure/cancellation meaning |
|---|---|---|
| `collect` | Accept ready transactions with reserved capacity; close promptly when the preceding batch permits progress | Unbatched requests may still be refused if no committing record can exist |
| `seal` | Fix membership, order, predecessor, manifest, and proposed root incrementally | Release only reservations proven not externally borrowed or durably authoritative |
| `dependencies` | Issue/finish body, manifest, and required index-page writes; verify every result belongs to the expected operation | Ambiguous writes retain extents and accounting; no success |
| `log-write` | Write immutable batch records and sealing metadata to fresh reachable locations | Once a recoverable commit record may exist, abandonment is potentially uncertain |
| `fence` | Submit the backend-specific durability sequence only after its required dependency completions | Failure or timeout enters uncertainty; it is not “nothing stored” |
| `durable` | Record successful durability evidence for this exact dependency set | A lost client connection does not undo commitment |
| `install` | Finish bounded preparation of the new visible root; old root remains authoritative meanwhile | No partial visible membership or partially advanced consumer position |
| `publish` | One transition installs the committed root/frontier | Publication is the visibility point |
| `notify` | Incrementally deliver request outcomes and mark/walk affected subscriptions | Output pressure delays notification, not the committed fact |
| `draining` | Retain rows/ranges still needed by notifications or external borrows | Recycle only after all obligations end |
| `uncertain` | Fence mutation in the affected storage scope; preserve operation identities and recovery information | Resolve through recovery, not a later generic success observation |

The success theorem refers to the durable transaction and published root. It must not require that all other replies or wake notifications from the batch have been sent.

A waiter registering during delayed wake processing compares its cursor against the published frontier. It therefore does not depend on catching a particular notification.

### E.3 Backend barrier sequences

| Backend | Required sequence |
|---|---|
| **File backend, buffered or direct I/O** | Finish all dependency and batch writes, then successfully complete the specified file durability barrier covering them. File creation/extension metadata requires its own stated contract. |
| **Raw block backend, baseline** | Finish all dependency and batch writes, then successfully complete a device flush covering them. |
| **Raw block backend, preflush/FUA optimization** | Finish every preceding dependency, including earlier log sectors; issue the final sealing write with a primitive whose contract is preflush followed by FUA persistence of that write. |
| **Every dependency individually durable** | Finish every independently durable write, then persist the sealing record; no omitted volatile dependency is permitted. |
| **Power-loss-protected device** | Keep the same semantic contract; barrier elision requires an explicit platform refinement, not a device-class label. |

FUA makes its own request durable. Preflush persists previously completed writes before the flagged write starts. Thus FUA on the final sector alone cannot replace the baseline flush. [Linux writeback-cache control documentation](https://www.kernel.org/doc/html/latest/block/writeback_cache_control.html)

Do not identify `RWF_DSYNC`, raw-device FUA, and preflush-plus-FUA merely because all are called “durable write.” Their adapter contracts must establish the exact dependency guarantee needed above.

A single semantic executor still permits many outstanding device operations and worker syscalls. The storage model must admit their concurrent, reordered effects.

### E.4 Recovery classification and policy

Recovery is a bounded machine over observations, not a checksum loop with a truncation rule.

| State | What establishes it | Policy |
|---|---|---|
| **Intact** | A valid lineage/root and valid required replay/dependency evidence, consistent with any available independent frontier evidence | Recover the committed prefix; adopt complete surviving unacknowledged batches when permitted; resume service after installation |
| **Torn tail** | Evidence plus the declared crash-only fault profile establishes that the incomplete suffix could not contain acknowledged history | Ignore/quarantine only that suffix; reclaim its extents through the allocator protocol |
| **Damaged** | A required committed block/record is missing, corrupt, misdirected, or conflicts with surviving authoritative evidence | Preserve evidence; stop mutation in the affected domain; repair from an independently validated source or report an explicit unavailable range |
| **Unknown** | Observations cannot distinguish harmless incompleteness from loss of accepted history, or cannot establish which lineage/frontier is authoritative | Do not silently choose a shorter history; enter recovery-required posture and request evidence/repair |

“Intact” is scoped to what was checked. If checkpointed payloads are verified lazily, recovery does not claim every old payload was read. Each block must pass integrity and identity checks before its bytes are served.

A malformed tail under the broader corruption profile is **unknown or damaged**, unless additional evidence establishes the torn-tail classification. Checksums alone do not establish that it was unacknowledged.

Recovery may discover a complete batch whose client never received success. That is a legitimate recovered commitment. Retry uses exact identity and the recorded operation semantics.

After a failed barrier, reopening and reading the same bytes does not by itself prove durability: the platform may still expose volatile cached data. Recovery must use a backend procedure that re-establishes the required persistence evidence before renewed acceptance. The underlying failure distinction is documented in the [paper survey’s crash-model table, rows 8–9](~/paperbin/README-fn2-20261028.md:383).

### E.5 Independent evidence and claim profiles

Name these assumptions separately:

- **`A-PERSISTENCE-FENCE`**: a successful backend barrier has its stated persistence effect.
- **`A-INTEGRITY-EVIDENCE`**: surviving trusted integrity references detect the modeled corruption, subject to the named checksum/collision assumption.
- **`A-INDEPENDENT-FRONTIER`**: an independently surviving witness binds the history incarnation to a frontier/head that recovery must not silently precede or contradict.

`A-INDEPENDENT-FRONTIER` must state its coverage. A client receipt proves something when that receipt survives and is presented. It is not an always-available monotonic anchor.

Consequently:

| Fault profile | Claim |
|---|---|
| Honest barriers; no later destruction of durable data | Acknowledged transactions survive permitted crashes and repeated recovery crashes, until authorized release |
| Corruption with surviving integrity evidence | Corrupt/unavailable content is detected before being served; repair requires a source |
| Rollback with a surviving independent frontier witness | A contradictory older image is detected |
| Loss of the suffix and every independent witness | No unconditional local rollback-detection claim |

Four local superblock copies do not establish the final missing premise.

### E.6 Cleaning and checkpoints participate in this protocol

A cleaner writes replacements, commits a MOVE/root update, and retires old extents only after:

1. the replacement is durable;
2. current and recoverable roots no longer require the old locations;
3. reader pins and external borrows have ended;
4. allocator state makes reuse crash-safe.

A checkpoint writes a captured root’s pages and installs its descriptor through the commit protocol. Its fold must equal replay of the captured prefix. Installing it does not automatically authorize dropping identity history, consumer progress, or retention evidence.

The “never rewrite an acknowledged sector” rule therefore means **never overwrite a still-required sector**. Permanent prohibition would prevent reclamation.

These requirements preserve the client distinction between transport acknowledgement, durable consumer acknowledgement, and evidence authorizing retention release. [CLIENTS-AND-DATA-MODELS.md, §§1.1, 2.1–2.2](build/coordinator/fn2/CLIENTS-AND-DATA-MODELS.md:77)

## F. First slice as simulator acceptance scenarios

### F.1 Harness and checkers

Run the same concrete core against the simulator and native adapter. The simulator records the initial profile, seed, observation order, fault choices, and software revision.

Use both:

- a tiny profile for exhaustive bounded schedules and process-death cuts;
- the concrete profile above for composition, sustained backpressure, and resource measurements.

The reference transition runner checks dispatcher refinement. Independent semantic checkers examine history, bytes, ownership, and outcomes; merely running the implementation twice is insufficient.

| Checker | Assertion |
|---|---|
| **TRACE** | Concrete turns match scheduled reference transitions and ordered actions |
| **WORK** | Every ingress pass, machine run, service pass, and turn stays within its declared work/output limits |
| **OWN** | No read of uninitialized/lent input; immutable output borrows; no premature reuse; generations match |
| **ACCOUNT** | Reservations and holdings conserve capacity; one principal cannot spend another’s protected allocation |
| **FAIR** | Continuously eligible principals/machines meet the calendar-visit bound |
| **HISTORY** | Accepted outcomes have the required durable transaction; refused operations contribute no committed mutation; uncertain operations remain unresolved/fenced |
| **IDENTITY** | Exact Message-ID/source bindings, duplicate/conflict behavior, numbering, and manifest content survive concurrency and recovery |
| **WIRE** | Replies have correct bytes, framing, ordering, and incomplete-stream behavior |
| **CONSUMER** | Cursor scope/version checks, forward-only durable ack, redelivery before ack, and no lost-wake registration race |
| **RECOVERY** | Classification and action agree with the fault profile and available evidence |
| **RECLAIM** | No extent required by a live or recoverable root, pin, borrow, identity record, or obligation is reused |

### F.2 Scenario list

| Scenario | Schedule/fault variation | Required checkers and pass condition |
|---|---|---|
| **1. Full composition** | Streaming upload commits beside a cold 16 MiB BODY, sparse XOVER, TAKETHIS traffic, and a parked authenticated consumer | All checkers; unrelated eligible machines keep progressing while each path repeatedly yields |
| **2. Cold BODY and stalled reader** | Partial sends, zero-byte progress conditions, delayed release notifications, then reader stops | OWN, ACCOUNT, FAIR, WIRE; only the reserved window remains held, other readers and commits progress |
| **3. Late BODY corruption** | First blocks pass; a later block fails after the success line has been sent | WIRE, RECOVERY; corrupted bytes never leave, stream terminates incomplete, no fresh refusal is inserted into the body |
| **4. Streaming upload failure** | Arbitrary fragmentation; missing terminator; oversized input; late admission refusal; disconnected sender | WORK, OWN, HISTORY; bounded discard or close, temporary extents accounted for, no false durable refusal |
| **5. TAKETHIS window** | Fill 64 peer credits; stall one body; complete others; lose outcomes and retry | ACCOUNT, FAIR, HISTORY, IDENTITY; completed eligible transfers commit without waiting for the stalled member |
| **6. Sparse XOVER** | Very large numeric range, few matching entries, cold index pages, one unusually large overview row | WORK, WIRE, FAIR; indexed/resumable progress, no numeric-range walk or omitted row at quantum exhaustion |
| **7. Wait registration race** | Commit immediately before, during the registration sequence, and after parking; delay wake fan-out | CONSUMER, TRACE; registration’s final frontier check prevents lost wake; wake is only a hint |
| **8. Multi-stream wait** | One wait watches room, DM, and mention streams; commits touch several; timeout and view change race with notification | CONSUMER, ACCOUNT, WORK; edge accounting is exact, notifications coalesce, authorization is rechecked |
| **9. Consumer crash/redelivery** | Crash before client processing, after client transaction but before ack, and around every ack persistence boundary | CONSUMER, HISTORY; unacked delivery may repeat; acknowledged progress survives the honest-barrier profile |
| **10. Unfinished cancellation** | Cancel returns not-found or completes before target; target/release arrives late; connection already closed | OWN, ACCOUNT; cancel never releases target bytes or recycles its incarnation |
| **11. Principal exhaustion** | One principal exhausts upload, output, cache-pin, TLS, and transaction credits; many anonymous connections | ACCOUNT, FAIR; protected peers retain their reservations/share; connection count creates no new entitlement |
| **12. Queue exhaustion** | Fill action outbox, delay adapter submission, deliver every reserved terminal/release notification | WORK, OWN, TRACE; no required result is dropped; no irreversible transition lacks a retained action |
| **13. Every commit death cut** | Reorder writes; tear pending sectors; crash before/after each dependency, fence, publication, and reply | HISTORY, RECOVERY, IDENTITY; accepted history survives within the honest-fence profile |
| **14. Failed/slow barrier** | Timeout followed by late success; partial write; `EIO`; `ENOSPC`; failed barrier with readable cached bytes | HISTORY, RECOVERY, ACCOUNT; uncertainty never becomes “nothing stored” merely due to time or readback |
| **15. Damage versus tail** | Corrupt a previously committed middle batch; corrupt a tail; misdirect a read/write; present an older consistent image | RECOVERY; classification follows evidence, not checksum position |
| **16. Independent witness** | Repeat rollback with a covering receipt/anchor, then without it | RECOVERY; covering evidence detects rollback; the unwitnessed case is not credited as successful detection |
| **17. Cleaning/checkpoint cuts** | Clean beside pinned BODY; crash around MOVE, checkpoint installation, retirement, and reuse; crash again during recovery | RECLAIM, HISTORY, IDENTITY; recovery selects usable state and never resurrects a duplicate identity |
| **18. TLS and time pressure** | Handshake flood, worker stall, STARTTLS boundary fragments, mass deadline expiry after a clock jump | WORK, ACCOUNT, FAIR, WIRE; bounded admission/expiry work, correct protocol handoff |
| **19. Counter exhaustion and stale events** | Initialize generations/positions near their encoding limits; inject stale and duplicate completions | OWN, IDENTITY, TRACE; no wraparound alias and no stale state mutation |
| **20. Dispatcher differential** | Run scalar and fused dispatch with the same observations; vary harvest/turn boundaries under corresponding schedules | TRACE, WIRE, HISTORY; equivalent semantic observations without demanding identical batch packing |

For liveness tests, stop injecting faults and supply a declared bounded-completion environment. Then check a bound derived from remaining work, scheduler service, and dependency latency. “All requests eventually finish” is not a valid acceptance criterion while a device or peer may remain unresponsive forever.

For performance, report wake latency, per-turn CPU, throughput, retained memory, and copy volume beside the actual profile and workload. The envelope’s arithmetic is a hypothesis to measure, not a simulator success criterion.

## G. Disagreements with the bounds table

The table should distinguish **execution capacity**, **admission policy**, **format geometry**, and **fault-model assumptions**. Putting all four under “hard-code these bounds” hides consequential design choices.

The governing requirement remains [D27](~/dev/fn/planning/decisions.md:1182): data limits belong to the supported operator profile; concrete representation and bounded execution must not introduce smaller accidental limits.

### G.1 Storage choices masquerading as execution bounds

| Envelope bound/choice | Disagreement | Replacement |
|---|---|---|
| `max_articles = 2^32−1`, resident ID table sized from `T` | Couples retained history to RAM and a u32 row identifier | Paged identity/index structures, bounded caches, explicit disk admission and namespace exhaustion |
| `max_groups = 65,536`, u16 membership IDs | A permanent namespace choice presented as a scheduling necessity | Persistent group IDs distinct from resident group-cache slots; paged summaries and membership indexes |
| `max_consumers = 65,536` | Durable registrations are stored data, not simultaneously running machines | Paged consumer records; separate limits for active cursor machines, parked waits, and subscription edges |
| 16 MiB compile-time article ceiling | Streaming work does not require it; it also fixes manifest shape | Operator admission limit, paged manifests, bounded parser/hash/I/O windows |
| One blob-index block per article | Makes block fan-out an implicit article-size ceiling | Multi-page manifest/tree with a bounded traversal continuation |
| Head fixed at 16 KiB, 64 fields, 256 lines | These may be profile defaults, but whole-head residency makes them implementation ceilings | Profile-controlled admission with incremental parsing and paged/spooled field metadata where supported |
| Injected headers fixed at 4 KiB | “Typical” group-name length is not a worst-case bound | Compute exact encoded size before commitment; stream injection or apply an explicit admission policy |
| 32 groups per article justified by `O(32)` POST work | Conflates membership count with work per turn | Profile-controlled membership count, incremental preparation, atomic publication of the complete result |
| Resident per-group number arrays and membership pool | Memory remains proportional to retained data despite paged article rows | Page these structures too; keep bounded hot caches |
| Rebuild the entire ID index at open | Replaces incremental checkpoint cost with an ever-growing recovery cost | Persist a pageable index or maintain a bounded replay overlay; full rebuild remains a repair option |
| Preallocated single file of fixed size | Reasonable initial storage backend, but a substantive store-capacity choice | State its capacity and full-store behavior explicitly; later extension is a core storage operation with a persistence contract |

Increasing integer width alone does not solve these problems. The important separation is persistent identity versus resident slot, together with a deliberate exhaustion policy.

### G.2 Bounds that are useful but need corrected meaning

| Envelope row | Required correction |
|---|---|
| **4 KiB sector** | Separate I/O alignment, logical block size, and possible tear granularity. Discover backend requirements; do not infer atomicity from alignment. |
| **64 KiB grid block** | A format/cache geometry choice, not a universal execution quantum. Sub-block reads and verification coverage must agree with the checksum layout. |
| **1 MiB cleaning extent** | Bounds bytes in one victim, not work in one run. Victim search, liveness inspection, relocation, and reference retirement all yield. |
| **Four superblocks, quorum two** | Requires a complete update/selection protocol and fault budget. It is not independent rollback evidence. |
| **Checkpoint every 64 MiB/65,536 records** | A trigger does not bound replay if checkpoint production falls behind. Reserve throughput/space or apply admission backpressure; account separately for blob-dependency verification. |
| **Waiters equal connections** | Reasonable for one wait per connection, but each multi-stream wait needs separately reserved edges and notification work. |
| **TAKETHIS window 64** | Independent of commit-batch size. It bounds the peer’s outstanding lifecycles. |
| **Batch 1,024 records / 4 MiB** | Bounds packing and membership, not the number of all external body dependencies; manifests must be resumable. |
| **Two batches** | Reasonable initial pipeline depth, provided a full batch is not held indefinitely by notification or unrelated upload lifetimes. |
| **64 disk reads / 16 writes** | Useful execution capacities, with protected recovery/maintenance shares and per-principal reservations. |
| **SQ/CQ 4,096/8,192** | Must derive from actual backend operations and notification multiplicities, including cancellations and zero-copy releases. Multishot operations invalidate simple operation-count arithmetic. |
| **1,024 completions per iteration** | Bounds descriptor count only. Completion handling must not perform unbounded verification, publication, or wake fan-out. |
| **64 KiB rendered or 1,024 rows scanned** | Need simultaneous limits on bytes, examined entries, probes, hash work, metadata, and emitted actions. |
| **16 TLS handshakes, 5 s deadline** | Bounds admitted jobs and waiting policy; neither bounds executor stall nor proves worker memory is reclaimable at five seconds. |
| **10 ms tick** | An observation/wakeup granularity, not the scheduler’s fairness mechanism. Expiring all due timers still requires a continuation. |
| **Article duration from line rate** | Gives a transfer-time floor under stated bandwidth, not an upper bound. A sender can stop indefinitely. |
| **No allocation after startup** | Must include TLS, adapter queues, runtime stacks, and foreign libraries, or explicitly scope the claim to the core. |
| **All profile values fixed for process life** | Separate structural capacities from live policy limits. A policy change can take effect within allocated capacity without rebuilding the process. |

The proposed 4 KiB execution quantum, two-batch pipeline, bounded operation table, and fixed active-machine tables are reasonable starting points. The article, group, consumer, and history namespaces should remain storage abstractions that those bounded machines traverse.