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

## Topic autonomy with concrete, separate meanings

The user's autonomous-topic direction fits these repositories when a topic is
a named application history with a rule for admitting events. It does not
require every topic to be a BFT blockchain. The following objects need separate
types in an integration, even if an early fixture uses the same small integers
for several of them.

| Object | Authority and meaning | What it cannot establish |
| --- | --- | --- |
| fn group and local article number | This Store's membership/routing projection and locally allocated number. | A portable topic ID, a causal predecessor, or a global execution order. |
| fn committed position | Prefix scanned in one history/incarnation under one consumer/query/view/registration. | Application processing, a topic tip, or finality. |
| Authored source identity | Exact preserved bytes under fn's selected identity contract. | Correctness of a contained receipt, current capability, or agreement. |
| Application operation ID | Stable retry/conflict key in its declared domain. Mini already binds a native operation to domain/semantics/subject/nonce. | A BP attempt, fn Message-ID, or permission to execute again. |
| Causal event/dependency | A typed reference to admitted parent evidence in a semantic history. | Total order or permission to ignore missing evidence. |
| Policy revision | Which source-authored law applies at a selected authority snapshot. | Grant revocation, execution generation, or rewriting historical admission. |
| Consensus/finality evidence | A chosen domain's rule establishes a canonical candidate/position under named membership and failure assumptions. | Delivery, storage durability or a universal topic merge rule. |
| Application execution receipt | A named receiver/verifier's result over exact request and state evidence. | fn retention release or physical completion of unrelated external effects. |

Mini's [CausalVersionDag](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Theory/CausalVersionDag.lean#L258)
already separates generic causal validity from optional parent admission:
`anyAdmitted` permits an offline sibling with an admitted parent, whereas
`currentTips` adds a frontier restriction. A topic can use either as part of its
application contract without making fn reinterpret article order as causality.
Several fn nodes can receive the same valid sibling events in different orders
and preserve all of them. Whether application state merges, forks, or waits is
the topic's decision.

Mini's [HyperedgeTier](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/HyperedgeTier.lean#L1)
describes a commit tier at least as strong as each participating leg and
explicitly leaves its per-cell tier field and admission-gate join open. Its
[authenticated settlement](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/AuthenticatedSettlementFinality.lean#L1)
also names key-directory, issuance discipline, quorum and cryptographic premises.
These are substantive design resources, not an already deployed per-topic
consensus switch. A new adapter must not claim to activate them by selecting
a `bft` string in an article.

A proposed portable topic descriptor should name: application/codec identity;
genesis or authority anchor; policy-source lineage; admissible authors and
delegation scheme; parent rule; conflict/merge rule; required execution/finality
evidence; and resource/retention terms. Its identity must be derived in the
owning semantic implementation from exact canonical bytes. A local NNTP group
is then an alias for a descriptor identity/version. Two stores may offer
different aliases or refuse the same descriptor. This is a proposal for D11,
not an implemented fn group-control format.

The descriptor has two interpretations with different owners. fn's ACL2 policy
owns article read/post/transit/release admission and storage charges. Mini's Lean
policy owns resource observation, mutation, delegation and execution. The
intersection is explicit: an article must be visible to the consumer, then its
claimed action must be admissible at the current application authority. Do not
translate Mini predicates into a second ACL2 execution policy, and do not let
Mini execute or replace fn's retention decisions.

This gives swarms a concrete composition model. A worker can consume public
reports from several topics, but any resulting multi-resource Mini mutation
still needs the actual observation and action grants of all participants. A
single local Mini image can commit those incidences atomically. A transaction
spanning independent Mini stores cannot inherit that atomicity merely because
its reports share an fn article or topic. It needs an explicit settlement,
reservation/compensation or distributed commit contract. Under disconnection,
monotone evidence collection can proceed while spending, revocation-sensitive
actions and agreed finalization wait for their chosen authority protocol.

## Proposed integration contract

### 1. A typed evidence envelope outside fn semantics

Keep E1's application body opaque to fn. Implement a bounded Mini-owned codec
for `report-receipt` and `reply` with application/version/operation/correlation
and typed dependency fields, matching the selected E1 logical envelope. For
the first fixture add a precise payload kind, `mini-native-prefix-v1`, naming:

* the Mini domain, semantics profile and independently selected genesis pin;
* exact native signed call bytes and exact original receipt bytes;
* a bounded public retained history through the reported accepted prefix;
* the source/evidence identity of the operation to which a reply refers.

The pin carried in the package is a claim to compare against local configured
trust, never a replacement trust root supplied by the sender. The consumer
verifier runs `NativeHostReplay.verifyBytes` under its selected configuration,
then finds the exact call and recomputes/matches the original receipt. It checks
that the prefix is the one reported, rather than treating some later image
containing the call as byte-identical evidence. Reusing this entry point keeps
Mini's semantics in Lean and avoids a Rust or ACL2 receipt verifier twin.

The current Mini client uses Ed25519 custody. fn's selected mandatory Ed25519
**and** ML-DSA-65 outer authorship remains a separate cryptographic layer.
Putting a Mini Ed25519 call inside a hybrid-signed fn article does not upgrade
the security of Mini's original authority chain. Neither does changing the fn
signature profile change Mini's call codec. Record both verification results
with their own profile and trust anchors.

Measure the complete retained-prefix package, signed article and resulting BP
ADU before freezing a payload limit. Whole-history replay can outgrow the active
receive envelope quickly. Begin with a fresh synthetic public genesis and one
small real accepted operation. If even that exceeds a current bound, record a
bounded refusal and prioritize a bounded prefix-witness/manifest design. Do not
silently truncate required authority history, split one application operation,
increase BP bounds, or use a live private authority database as a fixture.
The wrapper must bound bytes, retained events, dependency count, canonical
integer widths and verification work before invoking the existing decoder and
replay entry point on external input. A maximum article length alone is not a
demonstration that a nested application verifier has bounded work. No such
portable-verifier resource bound was established by this source survey.

### 2. A Mini-owned processing transaction

E2's provenance key and operation key solve different problems. The consumer
records provenance under `(fn history, incarnation, source identity,
application, operation)` while an independent unique `(application, operation)`
binding decides new/repeat/conflict. A topic/application domain must make that
operation namespace unambiguous across multiple authors; the declared mapping
to Mini's domain/semantics/subject/nonce is source-owned and versioned.

For a new valid report, one native resource transaction installs the provenance
record, unique operation binding, application decision/task update and immutable
reply outbox payload. For an exact repeat, it recovers the prior decision and
reply. For changed source under the same operation, it preserves conflict
evidence without a second application transition or reply. Mini's
existing transaction-conflict refusal alone is insufficient: a separately
identified, authorized evidence-recording transaction is needed to retain the
conflict, without reallocating the original operation's application effect.

The current scalar/content resource primitives supply atomic publication, but
there is no inspected deployed fn consumer index or special inbox primitive.
The implementation packet must choose a bounded resource representation and
prove its uniqueness and provenance semantics through the actual native
receiver. A generic content atom containing a key string is not a uniqueness
constraint. Rust may frame I/O and retain bytes; it must not decide a second
copy of operation admission. Required observation capabilities for the joint
inbox/task/outbox transaction remain part of the contract.

After that transaction is confirmed, the consumer acknowledges the fn scan
cursor. Uncertain Mini publication is settled with exact native lookup;
uncertain fn ack is settled with fn position lookup. The two databases do not
share a transaction and need no distributed commit to obtain this ordering.
Repeated polling is harmless only after the Mini operation binding is durable.
fn ack creates neither an article pin nor a release of an existing obligation.

The outbox first stores immutable reply application bytes. Before attempting fn
publication, it durably stores the exact final authored source, Message-ID and
carrier returned by the selected native signer. Only that persisted posting
artifact may be submitted or retried. This extra step matters if signing or
article construction is nondeterministic: a crash before durable artifact
storage must have made no post, and a crash after it must reuse the same source.
The fn identity algorithm remains ACL2-owned; the Mini adapter can retain fn's
returned identity but must not implement an alternative identity derivation.

There is already a concrete fn producer seam:
[`fnn-command-hybrid-sign-carrier`](../host/native/signature-command.lisp)
calls the ACL2 preimage/render functions, verifies both signatures, and writes
the rendered portable article to a new output file. Its current source-read
limit is 32768 octets, a relevant early bound for P0 in addition to the BP
limits. The output writer closes the file but does not itself establish the
consumer database's crash-safe outbox commit. P2 must import/sync that exact
artifact through its durable outbox publication before sending it; command
exit success alone is not the outbox durability witness. T10's durable received
carrier/verdict join remains the active authorship lane's separate obligation.

### 3. Distinct receipts at each boundary

| Evidence | What its successful verification means | Allowed consumer action |
| --- | --- | --- |
| TCPCL transfer ACK | The selected durable receive boundary for that transfer was satisfied. | Update that transport attempt under the BP machine's rules. |
| fn retention receipt | Exact matching content/undertaking/issuer terms permit the particular retention transition. | Ask fn's release authority to decide the named obligation; preserve unrelated pins. |
| fn authorship verdict | Exact authored source satisfied the recorded profile/key context. | Attribute those bytes; still check application evidence and present authority. |
| Mini historical native receipt plus verified prefix | This accepted operation belongs to the independently verified historical image prefix. | Record an application observation; separately decide any new local action. |
| Consumer fn ack | Consumer declared its transaction finished through this scoped scanned prefix. | Advance only that consumer's durable recorded position. |
| Application reply | The named author/consumer reports its decision about the exact correlated operation/source. | Apply only the topic's verified reply policy. |

Mini's existing
[OutboxDelivery.checkAck](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/OutboxDelivery.lean#L227)
requires the **current attempt number**, rejecting acknowledgements for older
attempts. E1's logical application reply can remain valid after several BP
attempts. Those are different protocols. Do not map a delayed E1 reply directly
to this attempt-specific Ack or weaken the existing theorem incidentally.
Either implement a separately typed stable-operation acknowledgement, or
reconcile a reply with the named attempt according to an explicit policy.
`OutboxDelivery.receive` is a logical, noncomputable receiver model and
`ProgressRefinement` supplies scheduler/network ceilings as assumptions; it is
not a ready-made native queue.

### 4. Scheduling is triggered by a durable decision

Polling is initially an explicit bounded consumer action. Wake hints may later
reduce latency, but lost/duplicated hints must change neither admission nor
durable progress. A supervisor can wake because a topic has unread evidence;
it dispatches a worker only after its normal Mini authority check and any
AgentGrain reservation commit. A hard stop increments execution generation;
late results can still be retained as evidence while stale mutation is refused
and unresolved external charges remain reserved until reconciled.

Thus fn is central even before a general scheduler exists: it is the place a
restarted or relocated worker retrieves the exact request, dependencies and
prior replies. The scheduler remains replaceable without losing that history.
No notification or subscription grants a spending capability.

## Implementation packets and acceptance boundaries

These are proposed work units after, or independent of, the active T8b, T10,
BP A1/A2/A3 and consumer Store changes. They are not new v0 gates. Proposed new
paths below are explicitly labeled; existing paths identify concrete extension
points, not permission for overlapping edits during this lane.

| Packet | Concrete target paths | Complete outcome and decisive evidence |
| --- | --- | --- |
| P0 — portable native evidence | Mini: proposed `Compiler/FnEvidenceCodec.lean`, `Kernel/FnEvidence.lean`, `Assurance/FnEvidence.lean`; extend `Host/Main.lean`, `Host/Json.lean`, `native/resource-client/src/main.rs`. fn: proposed `tests/fixtures/dregg-e1/` public vectors and `planning/evidence/dregg-e1-payload-budget.md`. | Export a small actually accepted native prefix and independently verify it read-only. Canonical decoder/encoder and exact call/receipt/pin binding; altered call, receipt, prefix, profile or genesis fails. Measure all nested byte/work limits before choosing transport parameters. |
| P1 — durable application consumer | Mini: proposed `Kernel/FnConsumer.lean`, `Compiler/FnConsumerCodec.lean`, `Assurance/FnConsumer.lean`; compose `Kernel/ResourceTransaction.lean`, `Kernel/ContentResource.lean` and the existing native receiver. fn: consume the active lane's future Store/owner interface, do not fork it. | One real native consumer transaction installs provenance, a unique operation binding, local result and reply. Exact replay returns same result; changed-source conflict is durably retained without another transition. Actual receiver theorem and native crash/readback witnesses, including two competing consumers of one operation. |
| P2 — native correspondence driver | Mini: proposed Rust `native/fn-consumer/` for bounded transport and custody only; use the P0/P1 Lean entry points. fn: existing `host/native/owner.lisp`, `host/owner-host.lisp`, `specs/consumer-progress.md` under the consumer lane's ownership; proposed `tests/campaign/dregg_exchange.py` as test orchestration only. | A sleeping B consumes A's report, commits its native transaction, acks, then publishes the persisted signed reply. Kill each side between every named boundary; all three outcomes remain distinct. Restart settles both databases and reuses exact source. No Python runtime dependency. |
| P3 — topic policy experiment | Mini: proposed `Kernel/TopicDescriptor.lean`, `Compiler/TopicDescriptorCodec.lean`, `Assurance/TopicDescriptor.lean`, consuming existing `Theory/CausalVersionDag.lean` and current resource authority. fn: future D11/S4/S5 policy/membership integration, with proposed scenario added alongside its contract. | Two topic descriptors use different sender/action laws and parent policies; same reports remain evidence while resulting actions differ. Change law while B sleeps, preserve historical validity and apply current action authority. No implicit grant revocation and no owner repair bypass. |
| P4 — hosted task join | Mini: `Kernel/AgentGrain.lean` and the suite's planned host/supervisor work, with proposed native fn consumer hooks. Bread reference tests: `deos-hermes/tests/world_bridge_e2e.rs`, `node/src/private_dependent_turns.rs`, `durable-workflow/tests/crash_resume.rs`. | A real supervised task reserves before dispatch; pause/cancel/restart fences stale workers and retains uncertain effects. Delayed results are preserved, not executed under expired generation. Measure physical interruption separately from kernel refusal. |
| P5 — Bread compatibility adapter | Bread: proposed `dregg-sdk-net/src/fn_evidence.rs` and `dregg-sdk-net/tests/fn_evidence.rs`; optional consumer call site beside `src/mailbox.rs`, not a fabricated `MailboxTransport::drain` proof. `node/src/mailbox_crank_e2e.rs` supplies the existing executor fixture. | An fn report reaches an explicit application verifier and normal turn ingress without synthesizing relay custody or granting ambient owner authority. Durable inbox/outbox and operation dedup are prerequisites to an E2 claim. Initially report-only compatibility can exercise an actual Bread receipt verifier without execution. |

P0 and bounded public vectors are the best independent next packet: they expose
whether actual OS evidence fits the current fn/BP acceptance unit and make
application verification concrete. P1 and P2 then close the two-database seam.
P3 can be designed concurrently, but portable topic governance is not a
dependency of a configured public experimental group. P4 should join the
existing persistent-host/Hermes work; it should not revive the rejected Python
platform. P5 is useful for preserving Bread interoperability, not a prerequisite
for Mini's selected path.

The active consumer lane reports `fnce` bootstrap/register/ack/rebase/unregister/
rollover events and a replayed scoped position projection under development.
That is lane coordination information, not certification or a served API at
this note's base. P2 must wait for the actual bounded poll and authenticated
owner caller, with certified Store publication/recovery and runtime evidence.

## Experiments that discriminate between working infrastructure and arrival

1. **Historical receipt, current law.** A publishes a small Mini content or task
   operation and its original receipt. B sleeps through fn/BP transfer. B then
   verifies the prefix with an independently pinned genesis, records one result
   and replies. Change B's current resource law before waking: the old report
   remains historically verifiable, while an unauthorized new local action is
   refused. A raw fn signature, old grant or arrived receipt must not bypass it.

2. **Opposite arrival order.** A and B author sibling topic reports naming the
   same admitted parent. C and D receive them in opposite orders and with
   duplicates. fn local numbers/positions may differ. Application causal
   identities, preserved conflicts and any selected confluent observation must
   agree; a nonconfluent spending proposal must remain pending/refused until
   its own settlement rule is satisfied. A missing parent stays bounded pending
   evidence instead of triggering recursive network fetch without a budget.

3. **Durable conflict and lost reply.** Deliver one operation/source twice,
   then a different source with the same application operation. Kill B after
   its Mini commit, after fn ack, and after Q submission but before its result.
   Inspect Mini's provenance and unique-operation state, reply bytes, fn's
   recorded position, and A's application result independently. There must be
   one original effect/reply plus retained conflict evidence; outbox recovery
   cannot depend on another delivery of R.

4. **Worker migration without history confusion.** Stop one consumer process
   and resume it elsewhere with the same authorized durable Mini history and
   stable consumer binding. Separately restore/clone fn under a new incarnation:
   its old cursor must be refused and explicitly rebased, while the consumer
   operation index prevents re-execution. A deliberate fork of the **consumer's**
   Mini database is a different problem: two writable futures need an execution
   lease/authority protocol before claiming one live worker or exactly-once
   external dispatch. fn incarnation checks alone cannot prevent that fork.

5. **Retention and capacity remain independent.** Keep an unrelated archive
   pin, deliver R and its application reply, and acknowledge both consumers.
   None releases that pin. Only the matching authorized fn retention evidence
   can release its named obligation. Fill the consumer metadata and article
   budgets independently; refusal occurs before any promise, and a reclaimed
   visible article yields the E2 explicit unavailable gap rather than a cursor
   silently skipping it.

6. **Real execution generation.** Start a supervised task from an admitted
   report, reserve allowance, disconnect hard and deliver an old worker result
   after a replacement generation exists. Verify that the result is retained
   as evidence, the stale mutation refuses, the live worker stays unaffected,
   and physical process/provider reconciliation accounts for the held allowance.
   This belongs after P4; a model status transition is not its physical witness.

Each experiment uses isolated stores and public synthetic inputs, records exact
source/toolchain/image hashes, and reports verification/runtime/physical scopes
separately. Existing archived Mini journey evidence supplies regression cases;
it does not replace the new two-store run. fn keystones must name the actual
host caller and carry nondegenerate witnesses and hypothesis counterexamples.
Mini proof/build checks follow its own native closure and named-theorem rules.
Every process kill must correspond to a stated model crash event; bytes crossing
a socket and an in-memory result never substitute for the two durable records.

## Decisions to bring forward when their packet reaches them

No new answer is needed to finish the active fn gates or inspect a public fixture.
The following become real choices at a specific implementation boundary:

| Choice | Recommended experimental position | When a user-facing decision matters |
| --- | --- | --- |
| Portable topic authority | A configured topic descriptor anchored to an explicit application domain/genesis, with NNTP names as local aliases. | Before D11/S4/S5 creates interoperable topic-control semantics; naming, delegation, succession and legitimate forks are product policy. |
| First foreign Mini trust | Independently pin the synthetic peer's genesis and semantics profile; verify its bounded retained prefix with the real native verifier. | Before accepting an unfamiliar silo, exporting private history or replacing replay with an attested/succinct claim. |
| Cross-topic mutation | Local atomic Mini transaction only when all targets are in one native image and grants admit the joint observation/action. | Before promising atomic operations across separately administered stores; choose settlement/escrow/compensation explicitly. |
| Background work while the human sleeps | Preserve AgentGrain's explicit hard/soft modes, generation and allowance; fn only wakes and supplies evidence. | Before a real provider can spend or perform external effects unattended; custody, budget allocation and reconciliation need a concrete hosted profile. |
| Delayed authority information | Historical verification uses the acceptance prefix; new execution uses current locally authoritative law. | Before disconnected untrusted peers may issue revocation-sensitive actions; decide required freshness/agreement, rather than wall-clock last-writer-wins. |
| Confidential topics | Public synthetic reports for E1; no private-authority database in payloads. | Before private groups or confidential capabilities travel; fn's private-group cryptosystem remains unselected. |

The architectural direction is ambitious and implementable in complete steps:
fn holds durable correspondence and undertakings; Mini admits and commits
resource transitions; topic policy states which evidence can authorize which
action; a supervisor performs physical work and returns reconcilable evidence.
The first useful join is already identifiable in the source. Its missing pieces
are a bounded portable evidence codec, a real durable consumer transaction and
the tested publication/ack sequence, rather than a new universal OS abstraction.

## Validation of this note

`make check` passed on the isolated lane based on `11b8d53b`, after the two
documentation checkpoints `e89517e4` and `22edf932`. It emitted the repository's
existing assurance/hygiene reports; its success is scaffolding validation only.
`git diff --check` passed. A local source-link audit loaded every linked
Bread/Mini file with `git show <pinned-revision>:<path>` and compared its bytes
with the inspected working file; all matched. Thus unrelated external WIP is
not silently represented by the pinned citations. No external tests, builds,
network deployment, certification run or end-to-end exchange was performed by
this design lane. No requirement/proof registry status changes follow from it.
