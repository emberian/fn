# fn as the correspondence substrate of the dregg OS

Status: source-grounded architectural proposal, 2026-09-23. This note proposes
implementation packets; it does not alter the selected release gates, claim a
new proof result, or authorize changes outside fn. The external repositories
were read only. The [selected E1/E2 exchange](experiments/e1-e2-agent-exchange.md),
[consumer contract](../specs/consumer-progress.md), [decisions](decisions.md), and
[takeover](takeover-2026-09-23.md) remain authoritative.

## Recommendation

Make fn central to how independently administered dregg nodes remember and
exchange work: durable authored requests, reports, evidence, dependencies and
replies remain available while an agent or its execution host sleeps. Build the
first integration against **Mini's existing native resource receiver**, using
Bread's implemented mailbox, workflow and federation paths as compatibility
references. Mini is the selected construction home; Bread's latest
[continuity record](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/HORIZONLOG.md#september-19--mini-core-cycle-1-complete-hosted-runtime-remains-next)
and [Mini handoff](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/HANDOFF.md)
both say so.

The most useful first artifact is an actual Mini native operation and its
original accepted-prefix receipt, carried in an fn report and independently
checked by a second Mini consumer. A second artifact is that consumer's durable
decision and reply. This directly advances the existing OS: task resources,
content publication, current policy, exact retry and sleeping workers. It does
not require inventing a new agent platform before the correspondence works.

Topics can become autonomous application histories with their own authority
and execution rules. An fn group is initially the transport/routing projection
of such a topic. A topic's causal history, policy lineage and any consensus
must have their own portable identities. Local article numbers and fn Store
positions cannot provide those identities or consensus. This distinction lets
fn support many kinds of autonomous topic without forcing all topics into one
execution or agreement model.

## Inspected source and evidence scope

| Repository | Inspected revision | Scope |
| --- | --- | --- |
| fn | `11b8d53bb4ab764220f4db087cc762623993e470` | Guide, architecture, decisions, trajectory/takeover, E1/E2, consumer kernel and documented native owner/Store boundary. Active implementation lanes continue independently. |
| Bread | `c93404d81c013d4c5b304a852d26f190d0aab19f` | Actual mailbox, silo, consensus execution cursor, dependent-turn scheduler, workflow, World bridge and merge call paths. |
| Mini | `dd1360d774e802900e3063e397ee29af073994b2` | Native host/client, resource transaction and policy interfaces, receipt/replay, SQLite CAS, grain model, causal history and delivery/finality models. |

Links below use those revisions. Source inspection establishes the described
call paths, not their execution in this investigation. External trees contain
unrelated work; no untracked Python platform/build drafts are treated as an
accepted implementation route. The Mini handoff distinguishes its complete
fresh native journey from a later source-matched build and targeted replay;
those older results are not new tests of these checkouts. This lane runs no
remote build and consumes no certification seats.

## What the actual systems do

### Mini: signed admission, exact publication, original receipt

The Rust [resource client](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/native/resource-client/src/main.rs)
owns custody, invokes Lean for semantic authoring, signs the returned exact
headers, and retains `call.bin` for retry. Its
[interface](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/native/resource-client/README.md)
already exposes submit, authorized query and exact retained-call lookup. It is
a local process client, not a remote fn consumer or hosted Hermes service.

[Host/Main.lean](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Host/Main.lean#L110)
dispatches bounded stdio operations to `NativeHost.prepare`, `submit`, `lookup`,
`challenge` and `query`. `serve` loops over frames, but
[NativeHost.openExisting](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/NativeHost.lean#L29)
reloads and verifies history on operations. A persistent stdio process therefore
does not yet mean a retained verified session. Preserve the separately planned
verified-prefix session work; do not build a network wrapper that hides its cost.

The real mutation path is:

```text
Rust mini: retained canonical signed call
  -> Host.Main dispatch/CLI -> NativeHost.submit -> openExisting
  -> NativeHostReplay.verifyLoaded
  -> submitLoaded -> operation-specific native receiver
  -> DurableReceiverIO.receiveLoaded
  -> opaque Rust SQLite exact-byte compare_exchange
  -> exact-intent readback -> NativeHost.historicalReceipt
```

[ResourceTransaction.Command](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/ResourceTransaction.lean#L36)
contains subject, expected authority root, nonce and distinct resource targets.
Each target has an exact old root, capability, schema version and source-owned
scalar/content operation. Multi-target commands also require observation
authority before another resource's law can inspect a participant's state.
The [operation marker](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/ResourceTransaction.lean#L143)
binds domain, semantics, subject and nonce; changing the payload is not a new
operation. This is the right place to join consumer deduplication to an
application transition, rather than a Rust table that independently decides
whether a task may run.

[DurableReceiverIO.receiveLoaded](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Compiler/DurableReceiverIO.lean#L153)
publishes against exactly the loaded image whose authority and height were
checked. It makes one CAS attempt and does not silently rebase. Contention
requires fresh admission. Ambiguous CAS results require readback; they do not
become semantic refusals. The
[SQLite helper](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/native/hyperdocument-link-sqlite-store/src/lib.rs#L472)
compares opaque byte images and does not interpret intent.

[NativeHostCodec.Receipt](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Compiler/NativeHostCodec.lean#L169)
contains transaction ID, event ID, accepted-prefix count and image boundary.
It contains neither a signature nor a succinct execution proof. `confirmed`
readback and `historicalReceipt` return the original accepted prefix even if
later events have committed. `lookupLoaded` checks exact historical ingress;
it does not submit an absent call. A transported receipt is therefore useful
evidence to check, not by itself proof of a foreign state transition.

There is already a strong verification entry point:
[NativeHostReplay.verifyBytes](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/NativeHostReplay.lean#L189).
It starts at an operator-pinned genesis, re-admits the retained original signed
ingress at each historical prefix, compares full canonical intents, and checks
the exact final image. It calls no storage publication. The first E1 receiver
can use this to verify a small public fixture's history without installing that
foreign image as its own Store. A read-only export/verify CLI and bounded package
codec still need implementation; the current host command set does not expose
this as a portable evidence operation.

### Mini: task lifecycle and current authority are already resource law

[AgentGrain.State](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/AgentGrain.lean#L23)
has execution generation, status, remaining allowance and unresolved reservation.
Its [transition policy](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/AgentGrain.lean#L82)
reserves before dispatch, preserves unresolved allowance through hard stop, and
fences stale worker generations. One paid attempt is in flight per task;
independent parallel tasks have independent resource identities and budgets.
`Operation.command` packages a task transition with other resource publications
through the generic transaction receiver. No separate agent transaction engine
is needed to publish a task result and its outgoing reply together.

These fields are not Book balances, policy revisions or grant revocation
generations. A stopped resource establishes admission fencing, not actual
termination of a provider call or child process. The source and handoff explicitly
leave the hosted supervisor and physical interruption join open.

[CredentialAuthorityPolicyRegistry](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Compiler/CredentialAuthorityPolicyRegistry.lean#L88)
loads the current policy revision from committed authority state. Existing
grants face current law; revising law and revoking a grant are distinct. An fn
article signed by yesterday's authorized worker can remain valid historical
authorship evidence while a new Mini invocation by that worker is refused.
Conversely, an exact retry of a historically accepted operation can recover its
old receipt after revocation without authorizing a new event.

### Bread: the mailbox is a deferred owner-authorized execution adapter

The actual [MailboxCrank](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/dregg-sdk-net/src/mailbox.rs#L299)
drains hosted relay messages, verifies a dequeue proof and payload binding,
checks an allowed sender set against the inbox cell's live commitment, decrypts
the payload, decodes `MailboxTurnIntent`, and calls the owner's normal
`.turn().on(...).method(...).effects(...).sign().submit()` path.

Three implementation details matter for fn integration:

* `MailboxTransport::drain` returns already-dequeued messages. The crank has no
  post-transaction durable cursor/ack operation equivalent to E2.
* `MailboxTurnIntent` carries target, method and effects; the recipient owner
  signs the resulting turn. The outer sender's authenticity does not preserve
  the sender as the authority exercising the action.
* The crank appends `CustodyReceipt` to an in-memory `Vec`; it does not atomically
  record a durable provenance inbox, unique operation index and reply outbox.

Consequently, implementing `MailboxTransport` on top of fn by synthesizing a
dequeue proof would assert evidence fn never issued. Feeding arbitrary fn
articles into `submit_intent` would also confer ambient owner authority. A future
Bread adapter should consume a distinct fn evidence type and pass through a
selected application admission gate. Its existing crank remains a reference
for the execution boundary, not the E2 implementation.

### Bread: scheduling and agreement are separate from message arrival

[private_dependent_turns](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/node/src/private_dependent_turns.rs#L1)
stores a prevalidated signed turn under a node custody key. A durable Ready row
is destructively claimed before ordinary SignedTurn ingress. Its explicit
at-most-once contract permits a crash to strand a claimed item. This is not E2's
retry-until-settled operation contract. An fn reply can eventually supply a
validated trigger, but article arrival must not create a Ready row without the
promise/authority checks or reinterpret a claimed item as completed execution.

[node startup](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/node/src/lib.rs#L3010)
starts blocklace even in solo mode. The
[ExecutionCursor](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/node/src/execution_cursor.rs#L59)
tracks executed block identities, and advances only for committed or durable
deterministic rejection outcomes. Operational retry and integrity failure keep
the item pending. This is an application/finality cursor, distinct from fn's
scan of a committed local Store prefix. Neither can replace the other.

The [silo server](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/wire/src/server.rs#L209)
has its own proof verifier, revocation authorities, federation roots, freshness
policy and connection bounds. An inbound `AttestedRootPush` is queued after a
known-federation check for **node-side quorum verification**; fn authorship
cannot take that verifier's place. The
[SiloClient](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/dregg-sdk-net/src/client.rs#L20)
already distinguishes verified non-revocation from an unverified server claim.
Carry that distinction across an fn report rather than reducing it to a generic
successful-delivery flag.

### Bread: workflow and World interfaces have narrower contracts

[durable-workflow](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/durable-workflow/src/lib.rs#L253)
registers separate RunStep and MeterTick activities, drives a duroxide workflow
over SQLite, and exposes a `StepRunner` for execution. Its standalone
[admission](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/durable-workflow/src/admission.rs#L32)
uses a MAC-authenticated lease budget and expiry. That is not Mini's native
capability/current-policy receiver. Its completed-activity replay and metering
must not be promoted into exactly-once arbitrary external effects; the call to
the runner and recording of its result need their own crash reconciliation.

The [Hermes World bridge](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/deos-hermes/src/world_bridge.rs#L143)
dispatches ledger reads and `FireEffects` to a WorldSink on the owning thread.
Its Unix socket peer trust rests on a private containing directory. A successful
local bridge test is not a cross-silo authenticated fn execution service.

Finally, [dregg-merge](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/dregg-merge/src/runtime.rs#L68)
really classifies free merges versus settlement and emits a chained merge
receipt. Its own [gate](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/dregg-merge/src/gate.rs#L24)
names the Rust/Lean refinement gap. The existence of that API supports a mixed
coordination architecture; it is not evidence that every topic can merge
arbitrary operations safely.
