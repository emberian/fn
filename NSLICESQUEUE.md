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
- Owners continue through their entire capability areas and the outstanding
  backlog. A landed commit, completed slice or passing check triggers the next
  useful connected change without waiting for assignment. Root retains the full
  scope; root and Integration clear dependencies and integration flow without
  selecting a smaller finishable subset.
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
  Use scoped coherent loaded-world checks and actual source-loaded host consumers
  as primary integration feedback while capability work continues. Fresh
  source-loaded processes can exercise restart and recovery. Record exact loaded
  source/interface identities and never mix obsolete stobj layouts. Saved-image
  production is not a development dependency; eventual packaging/startup
  qualification retains its own coordinate. Use historical images only for
  their valid baseline scope.
  Reuse an exact published artifact set instead of repeating acquisition or
  checks; do not wait for a whole subsystem or repeat unchanged polls.
- Keep completed slices here with their receipts; update the remaining work in
  place. Split a slice when it has independently useful consumers. The list is
  an initial coverage map, not a claim that all remaining defects are enumerated.

## Current engineering and source-tracing wave — 2026-10-03

Ember authorized Integration, History, Runtime, BP, Foundations, Served, Access,
Tools, Operator and Empirical, plus horse_entries, horse_exits,
horse_consistency and horse_bounds for complete source-path tracing and the
shared consumer .spw corpus. Root coordinates and supplies the reusable decoded
core; Operator, Foundations and Runtime compose the actual DEFAULT pool startup
producer. No lieutenant or Luna resumed. Integration owns public
assembly, current execution and planning; History storage/P3/reclaim; Runtime
ARTICLE/Web/decoded lifecycle; BP transport and signed application joins;
Foundations accounting/banks/tariffs; Served query/serializer families; Access
ARTICLE/header representation; Tools developer/tracing/allocation; Operator
policy/control/journal; Empirical system scenarios and defect discovery.
These are full-domain implementation/invariant/assurance obligations, not
finite end-tidying. Groundwork and other former helpers remain stopped.

The earlier ten-worker roster described the pre-usage-limit wave. That earlier wave
wound down before the explicit resumptions above; a retained warm handle does not imply an active owner or a
working current-union native process. History now owns one fresh current
source-world initialization. The alleged11-versus10 read-pool field difference
was false: :inline is an option, and both declarations have10 fields. Missing
current decoded methods and early P3 attachment remain actual assembly work.

## Dispatch next

| Slice | Current position | Coordination / implementation | Next useful result |
| --- | --- | --- | --- |
| [Safe completion and actor rollout](#safe-completion-and-actor-rollout) | Active | Runtime; completed source-tracer packets retained | Escapes preserve actual outcomes, fence the service when required, and settle custody through the real consumer |
| [Output allocation and funding](#output-allocation-and-funding) | Active partial producer and wider accounting | Foundations + Root + Runtime; Served serializers | Actual bounded serializer/selector allocation is funded before creation |
| [Paged catalog in the service](#paged-catalog-in-the-service) | Active shared execution dependency | History + Served + Runtime | Existing paged attachment serves POST/read/navigation/withdrawal/reopen |
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

**Active accounting/selector owners — Foundations + Served; Runtime consumes the current producer.** Connect indexed serialization, incremental
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

**Connected partial accounting source — Foundations; Operator/Bounds/Consistency assemble.**
Independent peer flight/work rows now have an explicit binary operator allowance
and a whole-native-machine startup recheck. DEFAULT protects the actual fixed
process collector trigger, and backing extensions account for trigger growth.
Live Store growth transfers only spare pool resident authority under the sealed
owner/extent publication join, preserving every issued row and ready marker.
Whole-current nonempty startup, protected recovery workspace transfer, init/run
affordability and complete physical/native allocation tariffs remain open.
Scoped source/guard/fixture evidence does not close those consumer obligations.
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
The completed proof packet is retained; the stopped export helper handed its
source and warm world back to History.**
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

**Paused — Served; command-helper source retained.** Finish the incremental group/membership
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

Access owns the continuing shared ARTICLE/HEAD/BODY producer and its NNTP/Web
consumers. Retained numeric/current/withdrawn selection, framing preflight and
lazy Xref now yield in bounded steps; READY commits selection once and replays
without authority changes. Source fixtures and exact normal source admission
pass. Complete actual parsed factory/socket/physical decoded-window/Web browser
composition, initial authorization setup bounds, renderer/owner guards and
universal owner/reference refinement remain open (PRF-1286, SCN-1116). The
retained source-execution process/inputs and precise mixed ABI frontier are in
LANEDUMP; no certificate, current image or full funded operation follows from
those checks. Numeric/current/Message-ID selector guards and exact fuel split now
normal-certify at73a0; direct server capture boundary certifies at39d72. These
component certificates do not certify the whole owner/physical path. Access owns
shared arbitrary HDR/XPAT span backing (PRF-1304/SCN-1135); Served owns the actual
command consumer. Captured span bounds and exact state/USED scheduling/source
bridge now normal-certify;237330 actual header source checks pass. Generic actual
header-byte grammar control and full-run original grammar phase prove independent
of requested names; whole arbitrary-field value/query correspondence remains open.
ARTICLE Xref iterator now guardT total with numbered-pair theorem and selected
normal certificate. Renderer/owner guards, selector termination/reference and
full session/reply refinement stay owned/open. Runtime + History own the current
compressed endpoint join; no image/physical transfer. Operator resumes non-ARTICLE
operator work; Access keeps the general journal bridge. Root S132 strict native
ten MiB acceptance/readback now passes on the named initialized-source cache with
its supported128MiB history profile; current-kernel/funding qualification separate.

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

**Active shared execution — History/Runtime consume the committed Served command adapter; Integration owns assembly.
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

**Paused availability implementation — Served owns the adapter and carried relation;
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

**Paused — Access owns authentication/TLS/access/reconfiguration; Runtime consumes the shared lifecycle.** Complete authentication throttling,
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

**Active execution — Runtime consumes Web source and owns shared interfaces; the Web deputy is paused.** The
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

**Operator’s pre-open DEFAULT partial pool startup and startup-failure custody source batch is complete; its nonempty native endpoint remains pending the current world. Foundations owns the numerical producer and Runtime its persistent executor. Access retains the earlier retire, diagnostic, init and journal continuation.**
The new native startup consumer installs an admitted plan before Store open,
and joins orphan workers before releasing run authority. SCN-1130's actual
source ordering, refusal/fault and escaping-join cases pass; coherent physical
owner open/read/stop remains the next consumer in History's retained world.
Complete cold profiles stay refused and full allocation refinement stays open.
S012 direct probe/selector source is integrated; its saved-image boundary
remains a selected check. Finish
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

**Paused generator owner — Foundations; active consumer owners integrate committed interfaces.** Finish carried-view/keyset,
cost/entry/operation and teeth machinery by replacing actual repeated recipes.
Batch related consumer migrations; library existence is not completion.

Done per family: emitted declarations, guards, keystones and witnesses match the
actual caller; old hand machinery is removed where replaced; unknown costs and
remaining consumers stay visible. Anchors:
[GEN-CARRIED-VIEW](planning/repair/items/GEN-CARRIED-VIEW.json),
[GEN-KEYSET](planning/repair/items/GEN-KEYSET.json),
[GEN-TEETH](planning/repair/items/GEN-TEETH.json), [DE-R2](planning/repair/items/DE-R2.json).

### Shared structured tracing and allocation feedback

**Paused — Tools owns the shared mechanism; Runtime connects actual consumer phases.**
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

**Paused — Groundwork owns the existing native/CLI consumer and durable client
inbox/outbox; Integration schedules the matching executable.** Implement the chosen consumer-owned durable
inbox/outbox exchange between separately administered stores: report while the
peer sleeps, verify exact source after delivery, commit processing and reply,
then acknowledge the consumer cursor.

Depends on the experiment's authorship/verdict and BP joins having their own
evidence. Done: outages, retries and restart preserve authored bytes and the
application's correlation/conflict semantics; external effects are not claimed
exactly-once merely because a message was accepted.
Anchor: [E1/E2 experiment contract](planning/experiments/e1-e2-agent-exchange.md).


### Web ARTICLE collector continuation — source retained; Runtime owns current execution

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
S068 production followthrough: actual passive node binds a private incoming-grant
received operation. Chain materialization uses64-action turns and incarnation
checks; END ACK waits for exactly one existing durable delivery callback. Raw
actual constructor/callback stale-generation and publication-cut cases pass.
Public SAMEPRS provider/source issuer remains separate; final semantic decode,
source-driver guards/refinement and complete GC/work tariff stay open. Fresh
source-loaded SCN1110 composition requested; saved images are off critical path.


Captured POST/remove BEGIN (PRF-1290 planned, SCN-1119) now looks up/touches
its session and handles expiry in the owner section, then returns a core-selected
private-begin action for the existing fixed semantic worker. That worker runs
the exact same-site/session/CSRF gate and authored POST/cancel preparation
outside O. Source equivalence/witness admission and matching image remain
pending; raw classifier/held-worker scheduling passes with a healthy owner
event progressing. Body preparation still runs to completion on one worker;
full body/working/capture allocation is unpriced, and stateful owner admission
can still delay events. No second worker or full fairness warranty.


Web private source checkpoint49dc6fa5e: complete web-session-keystones fresh
ACL2 source replay admits, plus full existing123-form session witness range and
private reply/POST/remove positive and predicate-removal witnesses pass.
Evidence planning/evidence/web-private-source-2026-10-03.md archives final
source hashes, clean world log and earlier proof/refusal repair log. This is
source admission; no certification/composed native browser/funding claim.
Missing-session POST/remove stays immediate refusal; captured body preparation
remains one full private worker operation. Integration owns coherent source
launcher; Web drives actual endpoint once that execution route is available.


Streaming Web command and await plans enter a fixed-worker `:ready` phase before
replay capture. `fnn-owner-ready-plan-step` resolves one shared ARTICLE framing
preflight quantum; yielded/raw and cold continuations are retained without
publication. Only READY stores the immutable original plan for both HTML passes.
No preflight/selection scan is replayed during count or emit. The consumer pairs
with Access source e7624ab8a/e41b22c21 and Served a3bd4513f; its raw adversarial
owner adapter checks cold/yield/READY capture custody, not producer semantics.
Actual composed source execution and complete Web tariff remain pending.


Shared ARTICLE producer/native Web composition: Access2a0f46790 byte-window
entry now supplies exact-W parts, with immutable pending dot fragments. The
actual shared producer bodies plus native Web scan/replay/count/write consumer
pass5,000 dot-leading lines, cold replay, partial drain and exact HTML/count/pin
receipt. The old work-only producer fails this same fixture with5,408 output
bytes for W4,096. Recording arena/owner/cold/I/O seams remain; full native
source-loaded browser execution and qualified Web funding are not established.


The host-reached ARTICLE/OVER/LIST program functions and Web window wrappers
now admit and execute in the same actual ACL2 source stobj world as the private
reply/gate functions. tests/acl2/web-stream-consumer-source-tests.lisp compares
complete reference page plans with virtual scan/count/emit under chunk1/2/7/4096
fixtures. Guard/refinement and complete endpoint/funding qualification remain
open; concrete-fill invariant-risk warnings are retained in the source receipt.


### Operator/developer remaining scope at the 2026-10-03 usage pause

S132 now passes strict native ten MiB NNTP/operator acceptance and exact
readback: one test, zero skips, 28.443s, supported 128 MiB history/16 MiB
article/64 transactions. The named ad8 initialized cache plus ordinary observer
overlay is the execution coordinate; whole current-kernel/funding qualification
and completion under every overloaded deadline remain open. Earlier scratch
refusals were oversize or underfunded, not timeouts. S083 actual partial-publication/restart/retry now passes: one test, zero skips,
10.444s on the named historical cache plus current formatter/consumer overlay.
The CLI preserves named uncertainty, durable authorization survives restart,
and accepted retry withdraws the target. Whole current-union qualification
remains separate. Current authority/generation interactions
remain an investigation item, not an established security defect or an inferred
atomicity requirement: the trusted local control route does not use login for
withdrawal, and the published row authorizes a cause rather than completing
target withdrawal.

The developer REPL now has actual native-owner admission/refusal/cleanup/fence
coverage on its named cache coordinate. Ordinary ACL2 proof admission now uses with-prover-step-limit: default200000
steps per perform, explicit override or NIL ordinary allowance. Actual ACL2
worker/socket tests cover zero-allowance refusal, stopping later batch forms,
unchanged global allowance and following valid proof/Lisp progress. This closes
the explicit prover-allowance gap. Actual native initialized-cache proof-limit
refusal/recovery and hot-reload hook deduplication also pass; wall time, arbitrary
Lisp evaluation and full current-owner composition remain unbounded or pending. Broad command access does
not establish complete internal observability or allocation accounting. Preserve
source/proof/cache/image distinctions when completing these domains.

2026-10-03 BP continuation: source-execution fixture provenance now compares
explicit launcher/manifest hashes and every actually loaded execution input,
separately from published-image qualification. Eight positive/refusal checks
PASS locally; SCN1110 still unexecuted. History owns the current TEN-field
ordinary pool/earlyP3 bootstrap; Integration will supply exact manifest/launcher.
BP owner continues actual keepalive/second canonical request and signed R/Q
Store/FNRJ/reopen join. Oldad8 cache is diagnostic only, not current-union proof.

SCN-1125 prepared BP/application join: signed binary R and immutable Q cross
actual ACL2-authored request, Store/FNRJ publication, reopened native return
receipt and matching pin release, then independent consumer source/signature
verification and correlation. No NNTP inter-node peer route. Compile-only
source state; native execution remains pending current initialized world.

BP owner source repaired missing RFC9174§4.1 Contact Header timeout: actual
retained begin captures core60s deadline, turn closes protocol only before
header completion; established source/END ACK unaffected. Raw controller and
source-control/custody composition PASS,14 warm literal assertions PASS. PRF-1295
proposed composed boundary remains planned; direct definition helpers not cited.
SCN-1126 real-time silent-contact/canonical request/reopen prepared, unexecuted.
SESS_INIT stalls/full admission, whole decode/GC and physical-cut refinement
remain owned open work. Exact two-root certification pending.

Ordinary live-session abort followthrough (PRF-1296): the single writer first
removes every future TURN/FINISH invocation. ACL2 permits retirement of an
ordinary context only without pending source/root/token/source-held/fence. The
host discards held ACK before TCP-closed and drops volatile input/output aliases;
durable Store/FNBS/FNRJ facts remain. Context release and observed physical close
are independent receipts. Fenced or unknown publishing debt stays discoverable,
and an unobserved close still holds the bank/root Store. Actual raw four-way
ordinary/fenced × observed/unobserved-close matrix PASS; no native or composed
refinement claim. This fixes normal shutdown of a live accepted peer, which
otherwise stranded the bank despite its disabled continuation. SCN1110/1125/1126
remain actual source-process consumers to execute on the current initialized
world. Matching profile/teeth certification pending.

SESS_INIT reception followthrough (PRF-1297, SCN-1127): entering messaging
captures one ACL2 sixty-second local deadline; further partial input does not
renew it. Already captured finite framing/materialization finishes before an
expiration decision; established sessions clear the setup deadline. Actual
retained driver consumes timeout as TCP-closed, never physical return or custody
settlement. RFC9174§4.6 requires negotiation before transfer; the sixty-second
SESS_INIT bound is fn local policy, distinct from §4.1 Contact Header requirement
and §5.1.1 negotiated idle behavior. Actual raw driver/source-control/custody
composition PASS; real two-peer durable request + setup expiry + reopen selector
prepared UNEXECUTED. Early announced-EID/channel admission and concurrent control
input during held-source work remain next connected work.

Early passive session admission (PRF-1299, SCN-1128): actual fnn-tcl-apply
invokes an optional BP-only admission callback once, at the decoded established
transition and before this frame's events or another buffered frame. The live
owner calls ACL2 fn-bpaj-session-admission on kernel-observed channel and decoded
announced URI, reusing durable ingress's principal policy. Refusal discards
unflushed messages and protocol-closes only that connection, records its exact
policy reason, and cannot install a received-source job or publish a Store/FNBS
record. The sender observes interruption before any transfer ACK; its pin stays.
Pre-transfer refusal has no bundle wire to persist as receive evidence. Existing
per-transfer admission/evidence remains for transfers actually consumed, and
outbound on-ready keeps its physical-write ordering. Unknown admission results
remain faults. Actual apply/flush raw matrix PASS; current native SCN1128 and
updated absent-trust request/receipt selectors remain UNEXECUTED. Full config
traversal, host correspondence and semantic allocation/GC costs stay open.

Held-source control ingress (PRF-1300, SCN-1131): the actual retained driver
alternates64-action source quanta with one existing bounded control read/frame
turn. ACL2 permits only fixed-size control headers2..6; new XFER/SESS_INIT stays
parked in the same at-most4096-byte socket vector until source terminal. No new
buffer, source issuer or bank is admitted. Incoming KEEPALIVE uses the original
session transition, advances actual last-RX and leaves the inbound record and
host source root/END ACK held. Outgoing timer KEEPALIVE still never fabricates
reception. EOF/close drains the existing private source before declaring context
terminal; one publication occurs, and a broken socket cannot flush its ACK.
Actual raw framing/private operation/session transition/delivery-plan/custody
composition PASS with recorded decoder/socket/durable callback. Normal source
book guards and13 assertions PASS; step preservation/reception lemmas1599/1482
steps. Matching roots pending, complete native caller correspondence open.
Real canonical sender-pump/encoded coalesced-control/reopen selector prepared
UNEXECUTED. PRF1273 citation now names only its real physical range keystone;
selected action IF-arm corollaries stay regressions, not completion evidence.

Empty offer host composition: supplied-p distinguishes an explicit empty payload
from omitted offer through begin/session. CLI optional absent paths and BP
receive absent reply omit the bundle keyword, while real empty files retain a
CONS tag/NIL offer for the consistency owner's zero START|END/ACK machine repair.
Actual begin raw cases PASS. Latest tcpcl-session source must precede native use;
no native zero-file verdict is claimed. Full semantic decoder/CRC/publication and
GC/working tariffs still require connected bounded consumers, beyond this step.

BP served owner startup SCN1134: source connects bp-node serve and bp-app receive
to independent captured DEFAULT installation before Store recovery, preserves
constructor/physical/Store-close debt through owner authority and attempts all
root cleanup. Actual command/helper recorded-seam fixture PASS; complete tariff
and current source-native worker/Store/multi-peer/RQ composition remain UNDONE.

BP actual parser correspondence PRF1303: universal complete KEEP/remainder source
driver/session equality and inbound/reception preservation warm PASS (311/4513
steps) with full positive/hypothesis-removal teeth; exact certificate pending.
Concrete control-parser boundary only; full framing, private source/END ACK
aliases and bounded semantic decode/CRC/publication remain UNDONE.

BP launcher profile PRF1306/SCN1137 source connects exact ACL2 Store/concurrency
projection and named refusal to actual heap consumer seventh normalized-root
value. Producer guards/grammar literals and recorded actual consumer PASS;
Operator DEFAULT extension composition/certificate/current native remain open.
Received-source alpha tracked at distinct claimed PRF1305, preserving PRF1292
owner readout; current union receiver/refinement certificate refresh pending.

BP consumed interface/cleanup followthrough: actual scheduler, grant, source,
framing and deadline leaves declared with their genuine guarded logical class
and scalar kinds. Host input probe and segment-MRU wrappers now explicitly
guard-verified (normal warm ACL2 admission), not relabeled PROGRAM. IF-arm
restatements removed from curated retained-turn citations. Global arena return
must be :closed after executor join before BP served ownership can settle;
constructor-without-Store debt retains authority too. Actual startup source
fixture passes nine helper outcomes plus command failures. Depends on shared
fnn-arena-return-observation physical seam; current native joins remain pending.
Exact four-root2674541 certificate refresh certifies PRF1305 receiver boundary;
PRF1306 full launcher reservation correspondence remains planned.

Root PRF1309 single-candidate BP allocator actual consumer connected: native
bank retains independent incoming/outgoing ACL2 cursor positions and exact
ledger results, one candidate call per attempt. Yield materializes no grant,
socket or context; forwarding explicitly retains a pending retry and receipt
cursor remains owed across --once drain. Actual bank/loop recording-boundary
fixture passes two yields, complete service rotation and terminal settlement.
Root owns actual stobj/guard/draw correspondence and typed producer fixtures;
no whole-ledger scan allegation (WFP is17 header/length checks). Current native
multi-peer/RQ durability remains unexecuted pending shared current entry.

BP S068/SCN1138 decoder prefix cost: actual fn-bpc-dec text/bytes and
fn-bpb-take-bytes execute existing guarded at-least prefix predicate through
MBE, original logical outputs unchanged. Normal decoder guards PASS110313steps,
bounded bytes reader guards PASS4806steps. Actual-body matched4-byte item plus
65536 untouched octets preserves complete result and replaces65540 LEN visits
with4 prefix visits. Affected two-root certificate submitted; full primary
prefix extraction, semantic decode/CRC/canonical/publication continuation and
current source-native multi-peer/RQ remain open. No arbitrary ceiling added.

BP convergence: allocator consumer and prefix availability cost source ready;
current shared source-world entry not available, so native multi-peer/RQ/drain
durability remains UNEXECUTED. Warm proof worlds stopped, no owned native
process. Full remaining decode/integrity/publication/RAM authority/app retained
session/tariff and custody composition obligations remain in BP LANEDUMP; no
closure claim from source fixtures. Continue via sealed current manifest, not
old ad8 diagnostic cache.

BP prefix certificate2794821 PASSED4/0 archived/indexed; actual source cost
receipt scoped to item availability and complete decoder results. Current
native endpoint and whole semantic decode/publication remain unexecuted/open.
