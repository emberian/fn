# Next implementation slices

First pass: 2026-10-03, Codex coordinator, at source `8fa6b902b`.

This is the durable queue for carrying the remaining initiatives through their
actual consumers. It preserves the full destination in the
[architecture](docs/architecture.md) and [decisions](planning/decisions.md);
an overnight window does not reduce that destination. Start from existing
implementations and finish their integration, rather than build replacement
prototypes without consumers.

The [active plan](planning/overnight-2026-10-03.md) coordinates current work.
The [repair ledger](planning/repair/STATUS.md),
[requirements](planning/requirements.json), and [proof registry](planning/proofs.json)
remain authoritative for individual obligations. This file groups related work
into executable slices; its headings are navigation anchors, not new requirement
IDs. Linked findings are starting points, not an exhaustive mapping or a claim
that their recorded state is current at every later revision.

## Using the queue

- **Active** means an owner has work underway; **next** means a concrete
  continuation is identified; **queued** means implementation ownership still
  needs dispatch. A coordinating owner is not an assertion that another agent
  is running. Check actual agent state and explicitly resume a completed agent.
- Dependencies below name the interface or evidence needed for a particular
  consumer. They do not serialize entire initiatives. Source reading, disjoint
  implementation and fixture preparation can proceed alongside them.
- Each slice ends in a usable behavior, with appropriate invariant/proof and
  scenario evidence. Update its linked obligations and record the integrated
  source and evidence when closing it. Source, certification, executable-image
  checks and deployment remain separate coordinates; a passing prototype or
  the first consumer does not complete a family.
- Push coherent source to public `origin/dev` promptly, before verification, as
  ember explicitly directed on 2026-10-03. One assembler composes overlapping
  code as needed; review, focused checks, certification and reports follow
  asynchronously. Fix forward and retain pending proof/image status. This queue
  adds no review, report, certification or image gate before source push.
- Each coherent packet names its actual runnable consumer, minimum kernel
  dependencies and next owner. An unresolved component proof is a separate
  workitem from an enabled capability; do not call an unpriced profile funded.
- Route the first candidate failure to one precise leaf owner immediately.
  Keep a matching minimal repair candidate moving alongside the coherent next
  capability wave. Use the last good image only for its valid baseline scope.
  Reuse an exact published artifact set instead of repeating acquisition or
  checks; do not wait for a whole subsystem or repeat unchanged polls.
- Keep completed slices here with their receipts; update the remaining work in
  place. Split a slice when it has independently useful consumers. The list is
  an initial coverage map, not a claim that all remaining defects are enumerated.

## Worker consolidation at 08:00 America/New_York

Ember caps running subagents at ten, excluding the root coordinator, from
08:00 on 2026-10-03; the 10:00 capability mission continues. Handoffs preserve
current source, warm-session coordinates, concrete consumers and pending claims.
The continuing owners are Integration (including source assembly), Runtime
(including HM), Served (including matcher/catalog availability), Foundations,
History (including carrier/pages/checkpoint), BP transport (including the completed
Tools fair-round packet), Access (including Operator and the S011 journal consumer),
Tools for shared structured and opt-in allocation tracing, Web, and Groundwork for
the actual application-consumer/E1–E2 boundary. Empirical completed its archive
and watch handoff; Integration owns the pending candidate watch. Helpers complete their current
coherent packet or transfer it before stopping; a passive assignment does not
count as active work. No Luna wave resumes. These are ownership transfers, not
capability completion claims.
The convergence lieutenant is explicitly excluded from this implementation cap
and owns routine coordination; Groundwork remains the application consumer owner.

## Dispatch next

| Slice | Current position | Coordination / implementation | Next useful result |
| --- | --- | --- | --- |
| [Safe completion and actor rollout](#safe-completion-and-actor-rollout) | Active | Runtime; completed source-tracer packets retained | Escapes preserve actual outcomes, fence the service when required, and settle custody through the real consumer |
| [Output allocation and funding](#output-allocation-and-funding) | Active | Foundations + Served | Actual bounded serializer/selector allocation is funded before creation |
| [Paged catalog in the service](#paged-catalog-in-the-service) | Active, execution dependency | Served; completed paged-store packet retained; Integration schedules | Existing paged attachment serves POST/read/navigation/withdrawal/reopen |
| [Reclaim and physical release](#reclaim-and-physical-release) | Active bounded builder and publication work | History; completed Astra relocation packet retained | Remove observed whole-history-copy credit obstruction and release resources safely |
| [Fair feed and pull rounds](#fair-feed-and-pull-rounds) | Active repairs; broader continuation next | BP transport + Runtime | Credential fixes and phase outcomes compose with bounded rounds and queue progress |
| [Runtime/model correspondence](#runtimemodel-correspondence) | Active | Runtime + consumer owners; Integration schedules evidence | Real ordered lock/pin/I/O labels drive the same model transitions |

The repaired candidate `1a946582c` produced a developer image on 2026-10-03,
and its actual raw/counterpart POST, duplicate and readback check passed.
That is an earlier candidate, not runtime evidence for all source at this
file's revision. New funded-worker and cursor consumers need matching selected
runtime checks. Image construction itself is no longer the first open result.

## Execution and resources

### Safe completion and actor rollout

**Active — Runtime; completed source-tracer packets retained.** Finish
post-launch completion custody, committer escape fencing and shutdown; then
carry the generated lifecycle through publisher, reclaim, feed, cold-I/O,
mux and web families. Physical return and consumed operation outcome remain
separate receipts. Trace the actual generated/native callers and their leaves,
including setup failure, raw throws, cleanup failure and late return.

Done for each family: its real failure schedules preserve accepted/uncertain/
refused outcomes, retained jobs and exactly-once settlement, with no active
service whose required actor has silently died. Remove displaced hand recipes
when consumers move. Connect the tracer's completion-escape repair, not just
its fixture. Anchors: [HOST-COORDINATION](planning/repair/items/HOST-COORDINATION.json),
[lifecycle](specs/lifecycle.md), [TCB design](planning/design/tcb-shrink-2026-10-03.md).

### Output allocation and funding

**Active — Foundations + Served.** Connect indexed serialization, incremental
selection and output custody to a real connection/operation funding producer.
The first actual producer/serializer probe charges a per-CID generational draw
before serialization and retains worker output until both output completion and
physical join. Runtime activation and full matcher/outer-copy tariffs remain
open; the probe is not complete NEWNEWS accounting.
Count temporary cons/copy windows, retained continuation and failed/refused
work; a wire-byte reservation is not a dynamic-heap allocation budget.

Depends on actual serializer/selector interfaces and supported profile
representation. Done: admission precedes materialization; suspend/resume,
disconnect, refusal and completion account for actual retained memory without
leaks or double refunds. Native allocation probes and logical tariffs must refer
to the same implementation. Anchors: [RESOURCE-OPERATIONS](planning/repair/items/RESOURCE-OPERATIONS.json),
[DE-R2](planning/repair/items/DE-R2.json), [resource specification](specs/resource-vector.md).

### Resource accounting across operations

**Next — Foundations owns the accounting direction; consumer owners assemble.**
Extend the consumed worker ledger to user subbanks, owner/maintenance reserves,
refusal costs, retained outputs and other allocating entry points. Install each
funding producer before enabling its admission gate; use actual profile capacity
instead of assuming spare workers or a universal maintenance allowance.

Done: the intended allocating families draw before effects and settle once,
including cancellation with physically outstanding I/O and drain-before-destroy.
Per-family executable correspondence, guards and scenarios accompany rollout.
Anchors: [RESOURCE-OPERATIONS](planning/repair/items/RESOURCE-OPERATIONS.json),
[resource contract](docs/resource-contract.md), [resource specification](specs/resource-vector.md).

### Owner carrier and removal of whole-state revalidation

**Active continuation — History owns the carrier and native authority consumer.
The completed proof packet is retained; the focused export helper hands back to History.**
Resume the existing carrier transformation safely, using current signatures and
actual native dispatch. Complete the POST bridge and the named owner-writer
preservation obligations, then carry the invariant through other live writers.
Private actors can continue against serialized shared sections meanwhile.

Done per batch: actual callers use the established carrier boundary, refused and
aborted operations avoid whole-store revalidation, and the corresponding
temporary trust debt is removed by real preservation evidence. Never use the
old destructive replay script as the migration procedure. Anchors:
[NIGHT-CARRIER-REPLAY](planning/repair/items/NIGHT-CARRIER-REPLAY.json),
[PGO-REFUSE-ABORT](planning/repair/items/PGO-REFUSE-ABORT.json),
[owner writer obligations](planning/repair/items/PGO-OWED-OWNER-HOST.json),
[store design](planning/design-store-representation-2026-10-01.md).

## Served commands and storage

### Complete bounded discovery and view policy

**Active/next — Served + command helper.** Finish the incremental group/membership
selector and matcher funding in the actual NEWNEWS factory/plan. Connect the
decided completed discovery snapshot to LIST variants, NEWGROUPS and NEWNEWS;
preserve the by-Message-ID pin followed by completed-view boundary.

Done: sparse/tombstoned data, long identifiers, small byte/visit budgets,
concurrent maintenance and cache churn all produce the correct complete reply
and make progress. Initialization and one-candidate work are bounded too.
Anchors: [GEN-CURSOR](planning/repair/items/GEN-CURSOR.json),
[DC05](planning/repair/items/DC05.json), [SCL4](planning/repair/items/SCL4.json),
[view policy](planning/design/command-view-policy-2026-10-03.md).

### Finish streaming and restricted command families

**Next — Served.** Carry the shared cursor/dependency machinery through OVER,
HDR/XHDR, XPAT, LISTGROUP and the restricted route. Complete table-generated
dispatch, preserving current session and access semantics; remove the remaining
hand fallbacks only as their consumers are covered.

Depends on stable continuation/capture/output interfaces, not completion of all
storage work. Done: cold ranges larger than the payload cache terminate with
exact replies, bounded per-quantum work and independent reader progress; restricted
sessions use the same bounded implementation. Anchors:
[DC02](planning/repair/items/DC02.json), [DC03](planning/repair/items/DC03.json),
[DC04](planning/repair/items/DC04.json), [SCL3](planning/repair/items/SCL3.json),
[cold-line work](planning/repair/items/sl-cold-line-quanta.json), [NNTP](specs/nntp.md).

### Paged catalog in the service

**Active — Served owns the concrete command consumer; Integration owns runtime capacity.
The paged-store helper has completed its source handoff.**
Use the existing paged catalog attachment and image route. Resolve the actual
creator/attachment question and run the prepared generic service scenario;
failure to acquire compatible certificates is not evidence of an attachment bug.
The actual cached attachment/creator and live/fresh generic probes passed; the
distinct paged executable consumer remains with Integration and the selected consumer owner.

Done: socket POST, GROUP, NEXT/LAST, exact retrieval, withdrawal, missing-article
replies and reopen work through the paged consumer with its representation
boundary and supported-profile costs. This completes a catalog slice, not all
page-backed state. Anchors: [STORE-PAGES](planning/repair/items/STORE-PAGES.json),
[store representation](planning/design-store-representation-2026-10-01.md).

### Dense groups, overview and reclaim-aware navigation

**Active availability implementation — Served owns the adapter and carried relation;
the paged-store helper source is complete.** Connect dense group-number and overview
representations to actual GROUP/LISTGROUP/LIST/OVER and navigation consumers.
Complete available-article counts and movement past reclaimed articles.

Done: counts agree with the selected view, NEXT/LAST progress past tombstones,
and maintained indexes remain correct across POST, withdrawal, reclaim and
restart. Representation changes retain named refinement boundaries.
Anchors: [STORE-PAGES](planning/repair/items/STORE-PAGES.json),
[SCL2](planning/repair/items/SCL2.json), [S042](planning/repair/items/S042.json),
[group-count design](planning/design/group-count-after-reclaim-2026-10-03.md).

### Page-backed history and node roots

**Active — History owns native authority, roots and builder; Astra completed the
page relocation continuation and handed its packet to History.** Extend
the existing page representation to history and node roots, with actual open,
tail replay, checkpoint and retained-view consumers. The first connected packet replaces the three publication callers’ whole suffix construction with a bounded append/flush builder; it does not yet establish effective reclaim. Keep progress and
allocation bounded per step without truncating admitted data.

Done: supported store growth does not force whole-history materialization on
the intended served/startup paths; exact content, local numbering and retained
roots survive replay and restart. Work can proceed beside carrier migration
where interfaces are independent. Anchors: [STORE-PAGES](planning/repair/items/STORE-PAGES.json),
[S147](planning/repair/items/S147.json), [store design](planning/design-store-representation-2026-10-01.md).

The private builder continuation now separates page readiness/copy/zero/header/mark
ticks from explicit flat-array growth (`history-pages-relocate-step`, SCN-1101).
Completed concrete equality and finite progress are component obligations;
flat-array resize, whole-event encoding, commit work and native root attachment
remain open and must not be described as bounded by a row yield.

### Reclaim and physical release

**Active — History owns native authority, bounded history/root, publication and
reclaim consumers; Runtime owns physical custody. Completed Astra packets remain inputs.**
Replace the observed whole-history-copy allocation with a bounded captured
page/history path, using real funding. Compose retention roots, holder/name
counts, caches, reader views, pending/fenced work and durable BP obligations.
Complete arena-forget, publication capture, swap and physical last-close.

Done: reclaim progresses under the supported profile while readers and accepts
continue; all kept bytes survive reopen, forgotten content does not resurrect,
and disk/memory release follows actual holder termination without needing another
POST. Logical invalidation alone does not establish physical release.
Anchors: [X04](planning/repair/items/X04.json), [S038](planning/repair/items/S038.json),
[S046](planning/repair/items/S046.json), [S114](planning/repair/items/S114.json),
[arena-forget design](planning/design/arena-forget-2026-10-03.md), [retention](specs/retention.md).

### Checkpoint, recovery and bounded store utilities

**Active — History owns staged history-image readback and storage continuation;
Access owns the operator journal. Astra is complete and is not an active owner.**
Group the existing repairs by actual log/checkpoint/import/journal path:
publication/read-back before dropping covered data, interrupted repair recovery,
txid/lineage preservation, bounded header/tail processing, and descriptor lifetime.
Stream offline work instead of assembling the entire input/history in memory.

Done per batch: original corruption/crash/refusal scenarios pass through the real
store, every prior accepted record remains recoverable, and partial operations
have accurate outcomes and bounded allocation. Anchors:
[S011](planning/repair/items/S011.json), [S013](planning/repair/items/S013.json),
[S039](planning/repair/items/S039.json), [S040](planning/repair/items/S040.json),
[S045](planning/repair/items/S045.json), [S047](planning/repair/items/S047.json),
[S048](planning/repair/items/S048.json), [S076](planning/repair/items/S076.json).

## Transport, access and operations

### Fair feed and pull rounds

**Active continuation — BP transport + Runtime.** Credential, durable journal
phase, fragment uncertainty and removed-peer cache/schedule source batches are
consumed. Tools handed the resumable pull/catch-up round context and ACL2
selection to BP transport; Runtime retains feed actor/idle ownership. Finish queue-head
progress, bounded rounds, streaming large transfers and captured peer config.
Connect phase-aware durable journal outcomes and close removed-peer resources.

Done: one slow/broken peer cannot starve others; reconnect/reconfiguration and
large articles make progress; pre-attempt refusal, durable uncertainty and host
fault remain distinct. Anchors: [S035](planning/repair/items/S035.json),
[S053](planning/repair/items/S053.json), [S067](planning/repair/items/S067.json),
[S106](planning/repair/items/S106.json), [S107](planning/repair/items/S107.json),
[S110](planning/repair/items/S110.json), [S112](planning/repair/items/S112.json),
[peering](specs/peering.md).

### BP custody, retained work and restart

**Active — BP transport owns the canonical producer and transport boundaries;
Groundwork owns application composition; Integration schedules the prepared real scenario.** Current source tracing found
that the record-log route never invoked the identity-grant producer required by
retention preparation. Source `7c6d135f3` and reviewed outcome validation restore
that connection; actual current-image undertaking/release/reopen remains the
next check. The historical refused workload is archived separately. Complete
real producer-to-Store custody, exact application
receipts, release/waiver, retry and restart across the BP workflow.

Done: accepted obligations survive outages; only the correct durable evidence
releases them; admission evidence agrees with the final application outcome;
tombstones are never transported as payload. Anchors:
[S024](planning/repair/items/S024.json), [S052](planning/repair/items/S052.json),
[S098](planning/repair/items/S098.json), [S099](planning/repair/items/S099.json),
[X12](planning/repair/items/X12.json), [BP workflow](specs/bp-workflow.md),
[BP path](specs/bp-path.md).

### Bounded BP/TCPCL scheduling and reassembly

**Active — BP transport owns continuing TCPCL sessions/reassembly and the
completed Tools fair pull/catch-up packet.**

Source now connects funded incoming/outgoing retained node sessions, asynchronous
forwarding/receipt continuation and same-token fragment socket rearm. Raw actual
consumer discrimination passes a live first peer, second acceptance and every
service phase. Matching DTN image and full tariff/refinement remain open.
Make session service, reassembly and forwarding genuinely resumable. Complete
ACL2-owned budget parsing and outcome decisions; retain custody correctly on
both inbound and outbound sessions.

Done: a keepalive peer or large fragmented family cannot monopolize the node;
other contacts, receipt delivery, expiry and forwarding progress between quanta.
Connection-local failures stay local where the contract permits.
Anchors: [S006](planning/repair/items/S006.json), [S025](planning/repair/items/S025.json),
[S026](planning/repair/items/S026.json), [S068](planning/repair/items/S068.json),
[S146](planning/repair/items/S146.json), [BP node](specs/bp-node-machine.md).

### ION and external transport outcomes

**Active — BP transport owns actual ION route/lifetime/outcome continuation;
Integration schedules the prepared native receipt consumers.**
Finish explicit-route submission, representable lifetime validation and durable
observation binding using the existing ION integration. Preserve refusal before
attempt, uncertain attempted work and acceptance through reopen.

Done: the original explicit-route and lifetime scenarios pass through the real
adapter; a helper/transport acknowledgment never substitutes for application
durability. Anchors: [X10A](planning/repair/items/X10A.json),
[X10B](planning/repair/items/X10B.json), [S097](planning/repair/items/S097.json),
[BP workflow host](specs/bp-workflow-host.md).

### Authentication, TLS, access and reconfiguration

**Active — Access owns authentication/TLS/access/reconfiguration, coordinating shared lifecycle with Runtime.** Complete authentication throttling,
TLS identity transitions, credential/secret publication cleanup, reader access
for peer roles, and resource charges around accepted/refused reconfiguration.

Done: exact access policy survives role and TLS transitions; malformed or
partially published credentials fail in the right scope; accepted config changes
update charges and retained historical context consistently. Anchors:
[S044](planning/repair/items/S044.json), [S085](planning/repair/items/S085.json),
[S092](planning/repair/items/S092.json), [S113](planning/repair/items/S113.json),
[S119](planning/repair/items/S119.json), [S120](planning/repair/items/S120.json),
[S121](planning/repair/items/S121.json), [reconfiguration](specs/reconfiguration.md).

### Concurrent web service

**Active — deputy_web (GPT-6.1 Sol), Runtime owns shared interfaces.** The
source packet 934b416cb and lifetime followups through 8e37db4f2 connect a bounded
HTTP I/O actor plus one fixed semantic worker to generated actor lifecycle,
shared commit await/cold consumers and per-CID flow leases. The assembled
consumer raw fixture passes exact partial windows and cancellation custody,
including a held whole-disposal receipt. Matching web/POST native-image cases
are pending Integration. Full NNTP/HTML materialization funding and incremental
core rendering remain open; bounded socket windows alone do not complete that
contract (WEB-006, SCN-1099). Preserve session cleanup and distinguish store
faults, uncertainty, refusal and disappearance.

Web source through the sole semantic-disposal receipt is integrated; raw held
cleanup and repeated finish schedules pass. Page cursor source 0d04c4a59 now
counts and emits validated segments outside O through the fixed worker, with
no full HTML OUT (SCN-1105 raw passes). PRF-1277 remains planned/program mode;
matching image use and full NNTP input/plan/job funding remain open. Owner
admission/session decisions/segment construction can still hold the I/O actor.
Web remains a separate continuing owner through 10:00 after Ember revised the
08:00 cap to ten. Exact captured reply plans now build on the fixed worker
without O/live-table access; source equivalence PRF-1279 awaits admission.
Root/Foundations own the full output funding seam.

Done: a slow client does not block every web client; POST composes with a
pipelined native batch; replies stream within accounted limits; faults fence or
close the correct scope. Anchors: [S003](planning/repair/items/S003.json),
[S030](planning/repair/items/S030.json), [S031](planning/repair/items/S031.json),
[S032](planning/repair/items/S032.json), [S037](planning/repair/items/S037.json),
[web interface](docs/web.md).

### Operator commands and trustworthy diagnostics

**Active — Operator owns bounded retire/drain, diagnostic classification and ACL2 initialization compatibility. S012 direct probe/selector source is integrated; its saved-image boundary remains a selected check.** Finish
bounded retire/drain, accurate heap/profile/startup diagnostics, safe fixture
separation, command outcome classes and interrupted administrative operations.
Explain retained resources and pending obligations using real state.

Done: fault/refusal/uncertainty are distinct in CLI status and exit codes; a
refused operation does not silently mutate unrelated state; diagnostic commands
do not manufacture success. Anchors: [S012](planning/repair/items/S012.json),
[S072](planning/repair/items/S072.json), [S074](planning/repair/items/S074.json),
[S090](planning/repair/items/S090.json), [S132](planning/repair/items/S132.json),
[S138](planning/repair/items/S138.json), [S151](planning/repair/items/S151.json),
[native configuration](specs/native-config.md).

## Assurance, shared machinery and use

### Runtime/model correspondence

**Active — Runtime + consumer owners; Integration schedules evidence.** Connect actual ordered section,
pin, I/O, physical-return and settlement observations to the executable host
model. Cancel, pin/capture/drain and physical-return preservation have matching
certificates. Complete issue/settle preservation and the all-schedules argument;
finite passing schedules alone do not establish it.

Done for the selected boundary: real traces replay against the exact corresponding
model, the claimed invariants cover reachable behavior, and assumptions and
unobserved branches remain explicit. Extend funded and direct paths deliberately.
Anchors: [HM02](planning/repair/items/HM02.json),
[whole-system design](planning/design/whole-system-correctness-astra-2026-10-03.md).

### Carried reads, crash cuts and historical evidence

**Next — Runtime, History and Access own their actual subsystem consumers;
the convergence lieutenant coordinates seams.** Finish carried
read statements under pinned/historical configuration and connect crash theorems
to the actual open/recovery program. Keep identity, exact authored bytes,
acceptance-time provenance and durable outcomes connected through the affected
storage/transport changes.

Done: the host-called subjects and representation boundaries support the stated
read/recovery guarantees; every process-death cut is represented; unreachable
old per-file branches stop serving as evidence. Anchors:
[HM01](planning/repair/items/HM01.json), [HM03](planning/repair/items/HM03.json),
[identity](specs/identity.md), [historical reader](specs/history-auth-reader.md).

### Finish shared generators through their consumers

**Active/next — Foundations and consumer owners.** Finish carried-view/keyset,
cost/entry/operation and teeth machinery by replacing actual repeated recipes.
Batch related consumer migrations; library existence is not completion.

Done per family: emitted declarations, guards, keystones and witnesses match the
actual caller; old hand machinery is removed where replaced; unknown costs and
remaining consumers stay visible. Anchors:
[GEN-CARRIED-VIEW](planning/repair/items/GEN-CARRIED-VIEW.json),
[GEN-KEYSET](planning/repair/items/GEN-KEYSET.json),
[GEN-TEETH](planning/repair/items/GEN-TEETH.json), [DE-R2](planning/repair/items/DE-R2.json).

### Shared structured tracing and allocation feedback

**Active — Tools owns the shared mechanism; Runtime and face owners connect actual phases.**
Use one span macro for parent/scope identity, lifetime, timing, outcome, unwind
cleanup and multiple values. Disabled tracing stays cheap; allocation tracing is
opt-in and states its measured scope. Reuse existing actor/operation machinery
rather than a different logging recipe per lane. The next usable consumer is a
real owner/mux scenario whose trace and analysis expose phase cost and allocation.
Metrics do not supply an allocation tariff or prove physical funding.

### Proof simplification, tooling and historical implementations

**Broad sweep paused — four Luna helpers stopped; validated packets retained,
unfinished experiments parked. The Sol now implements the owner carrier slice.**
Tools now implements shared structured tracing; source assembly is absorbed by
Integration after the helper’s completed handoff. Deliver related proof
simplifications in warm batches. Preserve statements and semantics; benchmark
representative or uncertain changes, not every cleanup. Keep corpus coverage
and tested/untested scope durable. Continue targeted checker repairs and harvest
useful prior implementations directly into the capability slices above.

Done per batch: reviewed source is integrated with necessary proof/consumer
checks and honest scope; a numeric speed claim has supporting measurements.
No proof-count or recommendation quota, repeated census, or broad audit gate.
Anchors: [proof guidance](docs/proofs.md),
[HARVEST-WORK](planning/repair/items/HARVEST-WORK.json),
[X17](planning/repair/items/X17.json). The new `PROOF-SWEEP-20261003` repair item
and archived coverage checkpoint are in the proof deputy's integration batch.

### Combined empirical behavior and operational convergence

**Active and recurring — Integration, with actual consumer owners. Empirical
completed the failed-candidate archive and handed off the watch; explicitly resume
a focused empirical task when a matching executable is ready.** Run
selected matching-image workloads for funded POST/stop, cold/slow readers,
maintenance, crash recovery and peer interruption as their slices land. Then
combine them and measure supported-profile scale, fairness and resource use.

Done at convergence: the packaged executable has matching behavior, proof and
scenario evidence for its claims, with accurate capability/limitation records.
Historical-image evidence does not validate new code. Source integration keeps
moving; full qualification is for a meaningful convergence or operational claim.
Live rollout remains a separate authorized task.
Anchors: [empirical matrix](planning/empirical-workloads.md),
[current capability evidence](planning/current.md), [active plan](planning/overnight-2026-10-03.md).

### Sleeping-agent exchange

**Active — Groundwork owns the existing native/CLI consumer and durable client
inbox/outbox; Integration schedules the matching executable.** Implement the chosen consumer-owned durable
inbox/outbox exchange between separately administered stores: report while the
peer sleeps, verify exact source after delivery, commit processing and reply,
then acknowledge the consumer cursor.

Depends on the experiment's authorship/verdict and BP joins having their own
evidence. Done: outages, retries and restart preserve authored bytes and the
application's correlation/conflict semantics; external effects are not claimed
exactly-once merely because a message was accepted.
Anchor: [E1/E2 experiment contract](planning/experiments/e1-e2-agent-exchange.md).


### Web ARTICLE collector continuation — GPT-6.1 Sol active

Source packet: virtual metadata scan/replay page source (PRF-1283, SCN-1113),
actual native consumer, final pin through count/emit/socket suffix and cold
replay. Raw reference/IN-bound/pin witnesses pass; program refinement and image
pending. LIST/OVER collector removal continues; qualified Web tariff/repeated
read/working/job funding coordinated with Root/Foundations/Runtime. No borrowed
native output grant or universal allocation claim.


Web OVER follow-on (PRF-1284 planned, SCN-1114): the actual native shared
stream/replay provider scans the existing100-number OVER request into at most
100 rows of four virtual spans. Number/subject/From/date text is read from the
same capture for count/emit, in the reference's newest-first order. Long fields
are not copied into the row metadata. A101st generated row fails the invariant
instead of returning truncated data. Raw exact-reference, generic native
cold/count/partial-write/IN-bound/final-pin witnesses pass. Source programs still
await guard/refinement and matching image; repeated backward seeks and physical
reads require qualified Web funding. LIST ACTIVE remains the full collector to
remove next; no blanket output grant or complete fairness/warranty claim.


Web LIST dynamic row source (PRF-1285 planned, SCN-1115): all three large read
routes now share captured-plan replay; LIST retains nine scanner entries and
one generated row segment plan, independent of group count. Actual native
empty/one/1003-group exact reference/cold/count/window/pin raw PASS. Source
program/refinement/profile arithmetic/image pending. Original NNTP ARTICLE
payload/block, LIST complete reply and some OVER full NOV/projection replies
remain upstream materialization frontiers. Served owns LIST producer; Root
owns shared payload/section producer; Web owns these connected consumers and
qualified consumer tariff coordination. No full producer funding claim.
BP-TRANSPORT S068 continuation (2026-10-03): production concrete framing cursor
and actual retained :read/:buffer consumer source ready; PRF1289 local4096-copy
quantum and codec composition fixtures. Full-frame conversion/decode, initial
reserve/GC latency and public received-source issuer remain open. No image
claim transferred from657; matching SCN1110 continues with Integration.
