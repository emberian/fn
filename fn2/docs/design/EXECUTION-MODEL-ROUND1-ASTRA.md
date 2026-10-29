# fn2 execution model: put the whole server inside the semantic boundary

I would build a **single-executor network of bounded, resumable machines**, with one concrete byte pool, explicit resource reservations, and bulk dispatch and I/O. Its logical interface can be `step(state, events) → (state', actions)`. Its implementation should mutate fixed storage in place.

That is close to the proposal’s intended realization, but differs at two decisive points:

1. **Parsing, connection state, scheduling, buffer ownership, and admission belong inside the semantic core.** Already-validated commands are an internal interface, not the boundary of the server whose robustness we intend to establish.
2. **An execution turn, a transport batch, and a persistence batch are different objects.** None should define the other’s lifetime.

Pure semantics does not require copying state, allocating effect lists, dispatching through a heavyweight boundary per byte, or finishing a request before yielding. The representation investigation identifies actual costs: repeated conversions, reconstruction, and work under the owner mutex. It does not establish that functional semantics caused them. Conversely, replacing cons tuples with stobjs does not by itself establish bounded work, isolation, or an efficient persistence layout. [build/coordinator/REPRESENTATION-HISTORY-20261028.md, §§2–4](/Users/ember/dev/fn/build/coordinator/REPRESENTATION-HISTORY-20261028.md)

## 1. Where the proposal fails, and what “the batch is the step” misses

### C1–C8 need more than a batch interface

| Constraint | Assessment of the opening proposal |
|---|---|
| **C1: determinism** | Achievable, but “same commands” is insufficient. Completion order, time observations, entropy, transport state, scheduling decisions, and resource availability must be represented. Sorting events by kind needs specified dependency rules. |
| **C2: boundedness and isolation** | Not established. Fixed arrays bound memory capacity; they do not prevent one principal exhausting shared pins, disk slots, handshake slots, or commit reservations. Bounded event counts also do not bound work per event. |
| **C3: batching** | Compatible with the design, but there are several independent batches. Homogeneous processing must preserve causal dependencies and fairness. A batch must not become a barrier that waits for its slowest connection. |
| **C4: one byte representation** | Achievable with pool ranges and extent references. It does not mean one physical address forever or literally zero copies. Alignment, TLS, header insertion, and packing small records may require bounded copies within the same representation. |
| **C5: trace semantics** | The proposed database core has trace semantics, but excludes the machinery that turns arbitrary client bytes into its inputs. The whole-server refinement would still require a substantial composition theorem. Enlarge the semantic boundary now. |
| **C6: small, portable host** | Plausible if policy really leaves the host. The envelope instead puts ownership tables, pool arbitration, and timer machinery there. Those are semantically consequential. TLS and kernel adaptation remain explicit trusted components regardless of their source-line count. |
| **C7: per-principal accounting** | A principal table is not enough. Every resource acquisition, including pre-authentication work and deferred maintenance debt, needs an accountable owner and an admission rule. |
| **C8: resumability** | Explicit continuations are right, but must cover parsing, hashing, collision walks, wake fan-out, recovery, cleaning, and checkpointing as well as rendering and scans. |

These objections address the specific proposal in [build/coordinator/fn2/EXECUTION-MODEL-ROUND1.md](/Users/ember/dev/fn/build/coordinator/fn2/EXECUTION-MODEL-ROUND1.md) and executor in [build/coordinator/fn2/ENVELOPE-AND-HOST.md, §§1.8, 2.1–2.3](/Users/ember/dev/fn/build/coordinator/fn2/ENVELOPE-AND-HOST.md).

**C2 also needs a precise isolation promise.** Taken literally, “a client cannot exhaust anything another client needs” is impossible for arbitrary clients competing for finite public resources. We can guarantee that one principal cannot consume another admitted principal’s reserved capacity or minimum scheduling share. Best-effort capacity can run out. Unauthenticated connections must share a bounded admission class; opening more connections must not manufacture more entitlement.

Likewise, static working memory must not quietly become a permanent store-size restriction. The envelope’s resident table sized to `max_articles`, u16 group namespace, and compile-time article ceiling are substantive storage choices, not consequences of bounded execution. Page persistent indexes through bounded caches; make supported admission limits explicit; handle namespace exhaustion deliberately. Startup resource ceilings can coexist with live policy changes within those ceilings. This respects both bounded execution and the objections to arbitrary data ceilings and compiled-in configuration in [build/coordinator/fn2/EMBER-ARCHITECTURE-WORDS.md, §14, sentences 3, 4, 7–9](/Users/ember/dev/fn/build/coordinator/fn2/EMBER-ARCHITECTURE-WORDS.md:448).

### Three different meanings of “batch”

I would name these separately:

- **Harvest batch:** a bounded vector of externally observed completions.
- **Execution turn:** bounded work distributed among runnable machines.
- **Commit batch:** records whose dependencies share a durability barrier.

A commit batch lives across many execution turns. A response can span many commit batches. A harvest batch can contain partial progress on hundreds of unrelated requests.

Calling the execution turn a “batch step” is harmless. Calling a batch of complete commands the fundamental step is restrictive, and calling a persistence batch the step is wrong for an interactive server.

Consider the concrete NNTP cases.

**Streaming replies.** A command produces a reply continuation: selected view, current position, framing state, and pending output ranges. It does not produce the complete reply. Sending part of a range advances a transport offset; it does not rerun the command. Other connections run while that response is blocked. A later command’s response must not interleave into the unfinished multiline response on the same connection.

**A 16 MiB BODY.** With a 64 KiB output quantum, this requires at least 256 payload quanta, plus framing and possibly more turns for short sends or cold reads. Retained working memory stays bounded by the configured window, including every buffer still externally borrowed. The continuation pins the necessary logical content/version and a bounded physical window; it does not pin all 16 MiB in cache.

The core should verify each cold block before releasing its bytes to the transport. If a later block is unreadable after the success line and some body bytes have gone out, a fresh NNTP refusal line cannot repair that response. The core must terminate the incomplete stream and record the fault. Internally typed failure does not imply that every failure can be rendered as a fresh wire-level refusal.

**TAKETHIS windows.** This requires several simultaneous record lifecycles per connection: receiving one article, validating another, waiting for durability on several, and emitting outcomes for completed transfers. Each accepted transfer consumes a window reservation. Parsing advances in wire order, but persistence completion is not the parser’s clock.

A window is a bound on outstanding work, not an instruction to wait until all its members arrive. A stalled upload must not hold unrelated completed articles out of the next commit batch. Rejected article input must either be drained under a bounded discard continuation or cause connection closure; an unlimited “drain until terminator” call is an attack.

**XOVER ranges.** `XOVER 1-1000000000` is a cursor over an indexed, pinned selection, not a billion-iteration command. Bound both rows examined and bytes emitted per turn. Sparse ranges need an index successor operation, not repeated numerical increments. The cursor retains its snapshot semantics across yields and cold reads.

These examples also show why “already parsed, already validated” is an unstable boundary. Syntax can be checked incrementally; authority, duplicate identity, and resource admission depend on evolving shared state. A validation result must name the state or reservation that makes it valid. Two commands validated independently against the same old state cannot both acquire the same supposedly absent identity.

### The proposed executor contains several specific traps

The envelope’s pseudocode is useful precisely because it makes these visible.

- `timer_wheel.expire`, `signals.drain`, pool grants, and wake fan-out need budgets too. Bounding only reaped completions does not bound a loop iteration.
- The loop must not wait for another external completion while internal continuations remain runnable.
- Processing “all commits, then all reads, then all sends” can starve classes and can change semantics across batch boundaries. Preserve dependency order; batch independent work selected by a fair scheduler.
- Fixed-width operation and incarnation counters need exhaustion behavior. “Never reused” is not implemented by incrementing a u32 forever.
- A cancellation request does **not** establish a deadline for physical buffer release. If the operation remains outstanding, its buffers remain borrowed. Timeouts bound the core’s decision to stop waiting; they do not make an unresponsive device relinquish memory.
- A zero-copy send may report send progress before a later notification permits buffer reuse. Those are different facts. The proposed `uses.take(c.op)` on the first completion cannot implement that lifecycle unchanged. [liburing’s `io_uring_prep_send_zc` documentation](https://www.man7.org/linux/man-pages/man3/io_uring_prep_send_zc.3.html)

The memory arithmetic also needs aggregate pin reservations: 1,024 connections each entitled to pin 64 KiB can consume 64 MiB before accounting for block rounding, metadata, or outstanding transport borrows. “Inside the block cache” does not make this capacity free.

### The durability argument needs repair before implementation

The ordinary rule—finish all dependency writes, then flush, then authorize success—is a good starting point. Three surrounding claims are too strong.

**FUA on the final sector is insufficient.** Earlier ordinary writes may have completed into volatile cache. Making only the final sector durable does not persist those dependencies. Keep the flush, make every dependency independently durable, or use an explicitly specified ordering-and-persistence primitive. Linux distinguishes FUA, which persists its own request, from preflush, which persists previously completed writes. [Linux block-layer documentation](https://www.kernel.org/doc/html/v6.6/block/writeback_cache_control.html)

**A bad checksum does not establish an unacknowledged tail.** Under corruption-at-rest or misdirected-write faults, the damaged batch may have been acknowledged long ago. “Stop at the first bad batch; everything later was never acknowledged” is valid only under a narrower crash-only model with intact previously durable data. The broader model needs a damaged/unknown state and a recovery policy that does not silently reinterpret lost history as a harmless tail.

**A checksum chain cannot always detect rollback.** Suppose a lying device loses an acknowledged suffix and all newer superblock copies, returning a complete, self-consistent older image. Local recovery cannot distinguish that image from a world in which the suffix was never accepted. Detection requires surviving independent evidence—a trusted monotonic anchor, client receipt, or peer—or a fault-budget assumption that preserves such evidence. Four copies alone do not resolve correlated loss.

These are counterexamples to the envelope’s stated arguments, not objections to checksums or group commit. They follow directly from the stronger fault classes in [/Users/ember/paperbin/README-fn2-20261028.md, crash-model table, rows 1–6, 11–15, 20](/Users/ember/paperbin/README-fn2-20261028.md:383).

## 2. The core/host boundary I would implement

### One semantic core, several internal interfaces

The outer core includes:

- transport-independent connection and protocol machines;
- parsers, framing, authentication policy, and reply rendering;
- scheduling, admission, resource accounting, and buffer ownership;
- catalog, indexes, cache policy, persistence, recovery, and maintenance;
- consumers, subscriptions, peering, BP obligations, and the built-in web interface.

It does not manipulate OS socket objects. It does manipulate connection capabilities and their lifecycle. “The core never sees a socket” is useful only if it means no file descriptors or kernel APIs, not no connection semantics.

The database operation interface remains valuable **inside** this core. NNTP, the web reader, remote consumers, and BP submit typed operations through it. They share identity, authorization, persistence, and accounting rules. This follows the shared-contract direction in [build/coordinator/fn2/CLIENTS-AND-DATA-MODELS.md, §§1–3](/Users/ember/dev/fn/build/coordinator/fn2/CLIENTS-AND-DATA-MODELS.md).

### Events entering the core

Every asynchronous observation carries the relevant operation ID, instance incarnation, and buffer generation. The event vocabulary should distinguish:

| Input kind | Meaning |
|---|---|
| `Accepted`, `Connected`, `Closed` | Transport lifecycle result, opaque connection capability, bounded peer/credential observations. |
| `ReceiveResult` | A submitted receive produced an initialized plaintext range, EOF, or failure. Arbitrary client octets are valid input. |
| `SendProgress` | A prefix was consumed by the transport, or the send failed. This is not proof of peer receipt. |
| `BorrowReleased` | External access to specified buffers has ended. Can coincide with ordinary completion; need not coincide for zero-copy output. |
| `ReadResult`, `WriteResult`, `FlushResult` | Storage operation outcome, including exact progress where meaningful and uncertain failure where necessary. |
| `CancelResult` | Result of asking to cancel; separate from the target operation’s terminal result. |
| `TlsResult` | Handshake/transport transition result, negotiated attributes, channel binding, and authenticated peer evidence supplied by the TLS adapter. |
| `ClockObserved`, `EntropyProvided` | Explicit external observations; no hidden clock or randomness inside transitions. |
| `ControlObserved` | Shutdown/reload request or bounded configuration input, still subject to core validation and authorization. |

A capability-based local client can use a typed request port. It is not a privileged escape hatch: the request still carries caller authority and undergoes core admission.

`Run` is an internal continuation event, selected by the core scheduler. Consumer wake-ups and pool grants are likewise internal transitions, not facts supplied by the host.

A process crash is an environment transition in the composed model. The crashed process does not conveniently receive and handle a `Crash` event before dying.

### Outputs leaving the core

Use fixed-capacity descriptor arrays containing:

- transport `Accept`, `Connect`, `Receive`, `SendRanges`, `Close`;
- storage `ReadBlocks`, `WriteBlocks`, `Flush`;
- `Cancel`;
- admitted TLS/crypto work requests where execution is asynchronous;
- timer-arm or next-wake information;
- bounded diagnostics and explicit service-posture changes.

Protocol replies are byte ranges selected or produced by the core. There is no host operation called `AcceptPost`, `Commit`, `WakeConsumer`, or `RefuseXover`. Those are core decisions.

Output-capacity exhaustion must be an ordinary continuation condition. Reserve space before making a transition that requires an output, or retain the pending output in bounded core state. Never mutate irreversibly and then discover there is nowhere to describe the required effect.

### The byte pool: core authority, host physical access

The host allocates and registers the region at startup. **The core owns its allocation policy, ownership metadata, generations, leases, and accounting.** The host holds the OS registrations and executes the exact permissions conveyed by descriptors.

A handle names a pool slot, generation, offset, and length. A receive or disk read lends a writable range to the environment; the core cannot inspect it until completion transfers it back. A send or write lends immutable bytes; reuse waits until every external borrow ends.

Logical semantics includes the bytes delivered by input operations. The optimized implementation lets the host write directly into the lent region and then reports completion. That splice is an explicit refinement boundary, not an unmodeled mutation hidden behind a handle.

One representation permits several physical uses: receive chunks, aligned batch packing, cache blocks, and bounded render buffers. Persistent references name extents/blocks, not process addresses. Pool slots can then be reused without pretending an entire article remains resident.

This is substantially the ownership structure already described in [build/coordinator/fn2/INTERFACES-TODAY.md, §9](/Users/ember/dev/fn/build/coordinator/fn2/INTERFACES-TODAY.md:588). That document also records the important limitation: today’s general runtime contract is not the execution path for most of the served product. Reusing its vocabulary does not inherit whole-server assurance.

### TLS and expensive foreign computation

TLS protocol execution, certificate parsing, and record cryptography remain in the TLS implementation below the core. The core owns:

- permission to begin or upgrade;
- handshake admission and resource reservations;
- deadlines and cancellation decisions;
- interpretation of authenticated identity;
- STARTTLS’s protocol-state transition;
- authorization policy.

The adapter reports plaintext through bounded pool ranges. It must expose or conservatively reserve its buffers, session state, and outstanding work. The envelope’s estimated TLS memory is not yet a no-allocation guarantee.

A non-preemptible handshake or signature verification cannot simply be called inside a tiny execution quantum and then charged afterward. Either its supported worst-case cost fits that quantum, or it runs on a bounded worker/component with reserved capacity. Workers return results; they do not mutate semantic state.

This keeps one semantic executor without making “one OS thread” a religious requirement. It also prevents the host-size estimate from hiding an unbounded TLS subsystem.

### Consumer wait/wake

Waiting lives in core connection/subscription state. No thread or control worker is held while parked.

A wait records its cursor scope, query/view version, principal, deadline, and subscribed streams. Registration checks the committed frontier and installs the wait atomically relative to commit publication, avoiding a lost wake between “nothing available” and “start waiting.”

A commit marks affected subscriptions eligible. Actual wake processing is budgeted, coalesced, and resumable. A connection watching several groups needs several bounded subscription edges; a single intrusive link per connection cannot inhabit all those group lists.

A wake is a hint to reconsider the durable predicate, not the delivery authority. Reconnect and poll recover from a lost notification. An ack advances durable consumer progress only through the persistence machine. This preserves the consumer-owned inbox/outbox semantics documented in [build/coordinator/fn2/CLIENTS-AND-DATA-MODELS.md, §§1.1–1.2, 2.1](/Users/ember/dev/fn/build/coordinator/fn2/CLIENTS-AND-DATA-MODELS.md).

### Per-principal accounting

The core maintains reservations and charges for connections, TLS jobs, receive/output windows, cache pins, I/O slots, scan/hash work, commit capacity, storage, subscriptions, and retained obligations.

Reserve before issuing work; settle on completion. Disconnecting does not erase charges for outstanding work or durable obligations. Authentication transfers attribution from the pre-authentication class without laundering already incurred cost.

Shared costs need an explicit allocation rule: batch padding, flushes, shared cache occupancy, and cleaning/checkpoint work cannot disappear into “system overhead.” A system reserve covers indispensable recovery and control work; principal reservations protect admitted service. Borrowed spare capacity must not compromise guarantees when it becomes non-reclaimable.

## 3. What assurance should prove first—and what is not about `step` alone

There is a naming discrepancy worth fixing. Round 1 names five targets: no crash, bounded work, isolation, durable acceptance, exact identity. The actual [specs/node-functionality.md, §3](/Users/ember/dev/fn/specs/node-functionality.md:563) lists totality, work, memory, typed failures, and reply semantics, then adds connection isolation in §3.6. We should preserve both sets of obligations.

### First prove the executable transition’s ownership and resource invariant

The first substantial theorem should concern the function actually called by the executor:

```text
Inv(S) ∧ BoundaryObservation(E)
    ⇒ Inv(S')
       ∧ ActionsAuthorized(S, E, A)
       ∧ ResourceConservation(S, E, S', A)
       ∧ Work(step) ≤ Q(profile)
       ∧ |A| ≤ action_capacity
```

Here `Inv` includes initialized readable ranges, exclusive write ownership, outstanding borrows, generation validity, accounting, pending-operation dependencies, and commit/publication phases.

There must be **no “client bytes are well formed” premise**. Boundary premises describe the host’s physical delivery contract, not successful NNTP parsing. Malformed input and stale or invalid descriptors must be handled before unsafe access.

Prove the concrete arrays’ abstraction relation at this boundary and carry it through execution. Do not revalidate the whole state every turn or create an independently callable list implementation of every helper. The history of representation twins is a direct warning against that approach. [build/coordinator/REPRESENTATION-HISTORY-20261028.md, §§3.1, 4](/Users/ember/dev/fn/build/coordinator/REPRESENTATION-HISTORY-20261028.md)

Then establish the trace refinement: internal turns can stutter, requests span turns, and externally visible actions correspond to the abstract node’s behavior.

### The five requested claims

| Claim | What can be proved about the core | Is the complete claim about `step` alone? |
|---|---|---|
| **No crash from client input** | Guard-safe execution, valid accesses, bounded state, typed outcomes, and invariant preservation for arbitrary input octets. | **Only the core claim.** Whole-process safety also depends on the adapter, TLS/crypto libraries, compiler/runtime, and OS contract. A trusted parser outside the core would leave a particularly large hole. |
| **Bounded work** | A fixed upper bound per turn, covering scheduler bookkeeping, parsing, probes, hashing, rendering, wakes, and output construction. Fixed retained storage and reservation conservation. | **Yes for modeled core work.** Wall-clock latency needs bounds or assumptions for foreign calls, scheduling, and hardware. Termination alone is insufficient. |
| **Isolation** | Other principals cannot alter private state, consume protected reservations, or invalidate a pinned read’s selected content except through explicitly allowed shared events. | **A trace property of repeated `step`.** Service guarantees additionally need scheduler fairness and resource/environment availability. Timing noninterference is a stronger, separate claim. |
| **Durable acceptance** | A success output requires the correct transaction’s completed dependency set and durability evidence; uncertainty fences the relevant mutation scope. | **No.** Recovery after crashes is a property of core plus storage environment and host refinement. A forged success observation cannot be made true by a pure transition. |
| **Exact identity** | Lookup confirms exact Message-ID bytes; concurrent pending inserts serialize/reserve that identity; hash collisions cannot become equality; recovery and reclaim preserve bindings. | **The decision theorem can be internal.** End-to-end byte preservation and corruption detection depend on storage/host contracts; digest-based integrity has explicit collision assumptions. |

For identity, keep Message-ID equality, authored-source equality, content identity, and stored projection distinct. Injected headers mean “the bytes” is not a sufficient theorem subject. Hash tables also need a worst-case path: keyed hashing improves expected behavior but does not prove a hard probe bound. Resume collision work or use a bounded worst-case structure; never report “absent” because a probe budget expired.

For durability, publish separate theorems for separate fault profiles:

- Under an honest persistence fence, acknowledged records survive permitted crashes and repeated recovery crashes, until authorized release.
- Under corruption with stated surviving evidence and checksum assumptions, invalid data is detected before being served.
- Under arbitrary loss of every witness, unconditional recovery or detection is impossible.

Likewise, a timed-out commit may later prove durable. Once persistence has become ambiguous, “refused, nothing stored” is not a safe outcome merely because a deadline passed.

### Batching changes some theorem statements

The old refusal statement—“a refused step changes no committed history”—cannot be copied to a batch step. One turn may refuse principal A’s request while committing principal B’s. The new statement must be **request-indexed**: the refused operation contributes no committed mutation.

Accepted/refused/uncertain are terminal operation outcomes, not an exhaustive classification of every execution turn. Most turns are pending progress. Fencing must name its scope; a storage-domain fence need not forbid every safe read or unrelated computation.

Partition independence also needs care. Different TCP fragmentation should preserve protocol meaning when semantic observation points are held fixed. Different batching may legitimately change flush grouping, latency, admission timing, and physical log packing. Prove equivalence of the relevant observations under corresponding schedules, not equality of every internal state after arbitrary regrouping.

## 4. The strongest counter-model, and which I would build

The strongest alternative to the proposal is **a deterministic cooperative machine network**, physically implemented with arrays and bounded queues:

```text
observe bounded external completions
    → make affected machines runnable
    → choose principals and machines using core scheduling state
    → run bounded homogeneous groups of continuations
    → emit bounded action descriptors
    → submit in bulk
```

The executor waits only when no eligible internal work remains.

Each machine has a small state enum, typed fields, a resource account, and explicit continuations. Internal handoff transfers handles or references. Parsing, queries, commits, consumer waits, BP forwarding, and maintenance are instances of the same execution discipline. A global turn budget bounds their composition; individual budgets prevent any one machine consuming the turn.

The reference semantics can select one transition at a time. The executable dispatcher can fuse compatible transitions into loops over columns. Its later refinement obligation is to show that the fused execution implements an allowed reference schedule, including resource and output effects. **Logical decomposition does not require runtime dispatch overhead at every logical transition.**

This model offers three advantages over a public `prepare(batch)/commit(batch)` interface:

1. It represents interaction and backpressure directly, without introducing a second server beside the “core.”
2. It gives resource accounting and ownership one place to live.
3. It allows batching wherever useful without making command completion or persistence completion the scheduling quantum.

The genuine alternative worth keeping in view is a partitioned, multi-executor version. It can retain deterministic semantics by recording merge order and giving each partition the same bounded machinery. But crossposts, global identity, account budgets, configuration generations, and retention obligations then need cross-partition protocols. Partitioning by connection does not partition those decisions. I would preserve transferable handles and explicit message boundaries so that this remains possible, but would not introduce those protocols before a demonstrated need.

I would therefore build the cooperative network first: **one semantic executor, bounded asynchronous adapters, and batching inside the implementation.** This is closer to A’s complete semantic boundary with B’s bulk execution than to B’s command-only core.

The first running slice should deliberately exercise composition: a streaming upload committing beside a cold 16 MiB BODY, a resumable XOVER, a TAKETHIS window, and a parked remote consumer. Run that same core with deterministic storage/network faults and the native host. Include a stalled reader, an unfinished cancellation, a principal exhausting its own quota, and crashes between dependency writes and publication.

That slice would answer the important design question: whether fn2 can keep unrelated work moving while preserving its bytes, promises, and resource guarantees. “The batch is the step” does not answer it; the ownership, continuation, scheduling, and persistence rules do.