# Development workstreams — 2026-10-03

Revised by Codex after ember asked for deeper first-hand reading. This replaces
this file's initial pilot-oriented plan. The objective is to complete and connect
the outstanding initiatives and repairs, with a serving system along the way.
An overnight run is a period of work, not a smaller product scope or a stopping
point after one macro consumer. Use GPT-6.1-Sol for the former Luna assignments.

The repair ledger is the shared queue. Designs define the destination; an item's
acceptance scenario defines whether its replacement actually closes it. Existing
source, unmerged implementations and proof libraries are material to integrate
and finish. Keeping a branch is not completion.

## What the deeper reading changes

The [store design](design-store-representation-2026-10-01.md) makes pages and
prepaid resource accounting foundational. They need active implementation
ownership alongside served behavior and coordination. The existing resource
vector/tree and typed executable are a starting point, not a served accounting
implementation: [the specification](../specs/resource-vector.md) still owes the
operation layer, representation correspondence and real producers/consumers.
The paged catalog already has an attachment and a separate image route; the next
work starts there, not with another catalog prototype.

The [whole-system decision](design/whole-system-correctness-2026-10-03.md#decision-coordinator-2026-10-03-recorded-by-codex-liaison-11-ember-may-overturn)
explicitly orders lifecycle generation, the host model and off-lock work in
parallel. The [TCB design](design/tcb-shrink-2026-10-03.md) moves coordination
into ACL2; wrapping the existing host program alone does not finish it.
The committer already has its own thread and enters serialized sections in
`host/native/owner.lisp`. Private actor coordination can be developed and
installed against those sections while the owner carrier migration proceeds.
A blanket carrier-before-any-actor dependency was too strong.

The generator continuations describe implemented libraries and waiting consumers:
`def-command`'s generated dispatcher is not yet the served dispatcher;
`def-holder`'s accounting does not itself license forget/close; `def-cost` has no
served operation accounting; carried-view and keyset have implementations to
finish connecting. A first consumer validates a contract. Its owner then keeps
going across the intended consumers, replacing the repeated hand machinery.

The late update in [the prior plan](plan-2026-10-03.md#update-at-the-end-of-the-session-2026-10-03-late)
authorizes direct integration onto dev while stabilizing it. Source integration
does not wait behind the old next-to-dev image gate. Qualification still belongs
to one immutable candidate and never transfers a verdict to changed bytes.

## Reorientation after compaction or takeover

A summary is a locator, not sufficient reorientation. Recover the actual
top-level user **and assistant** exchanges with `cv prompts 01a0fe41`, then
`cv show 01a0fe41 --around N --context K`. Useful prompts are 317 (ambition),
362 (team/design), 640 (correction to serial/preservation advice), 830 (Sol
deputies), 967 (context deputy), 1009 (integration/shipping), 1037 (skeptical
external reviews), 1058 (empirical/helpers), 1189/1245/1256 (speed/batching),
1273 (trajectory) and 1312 (recovery). Read surrounding responses and latest
corrections, advancing beyond long tool stretches through the assistant final
response. These three verified windows include the correction, subsequent
batching discussion and complete promised trajectory/capability answer:

```sh
cv show 01a0fe41 --around 640 --context 5
cv show 01a0fe41 --around 1273 --context 8
cv show 01a0fe41 --range 1295..1307
```

If output truncates, continue at the range printed by `cv`. Do not count
repeated forked history as independent evidence or commit transcript dumps or
personal context.

Before substantive decisions, read the complete needed governing files:
`docs/README.md`, `docs/architecture.md`, `planning/decisions.md`, this active
plan, `planning/now.md`, `planning/current.md`, and applicable complete subsystem
designs/specifications. If output truncates, read the remaining chunks. Confirm
live ownership and the frozen candidate with Groundwork and Integration;
authoritative `origin/dev` may differ from the protected, untouched shared
checkout. Agent summaries/reports are leads to source and conversations, not
reading substitutes. This is a working routine, not an installed runtime hook.

Summaries and recovery notes locate prior reading; they do not replace first-time
understanding. After a compaction, check file revisions before rereading. Retain a
concise note of already-read file/revision, conclusions and unresolved questions;
read complete changed documents and the complete documents needed for the current
consequential decision, in bounded non-overlapping chunks. Recovery does not
require rereading the whole corpus every time. Recover the actual exchange and
latest corrections even when the governing files are unchanged.

## Execution roster and ownership

The first groundwork wave is active: Integration, Runtime coordination, Served
commands, Generators and accounting, and Tools and harvest have GPT-6.1-Sol
deputies. Approved helpers feed existing consumers: empirical native scenarios,
typed owner-ledger proofs followed by paged catalog closure, command-table rows,
and a source semantic-review/conflict-staging helper. Integration remains the
sole dev writer; source review proceeds alongside executable debugging. A
GPT-6.1-Sol groundwork deputy owns detailed cross-lane coordination, composition
and representation contracts alongside the strategic coordinator. Corrected:
these are active workers, not a prepared launch. The wider roster below remains
a target; composition, storage, representation and transport owners have not
been launched separately. Start additional lanes only for useful independent
work after agreement with the coordinator. Sol lays the integrated foundation
first; Astra composition remains a later option rather than an active claim.

| Owner | Model | Continuing responsibility |
|---|---|---|
| Coordinator | this session | System design, priorities, shared contracts, overlap resolution and following every workstream through use |
| Integration | GPT-6.1-Sol | Sole dev writer; harvest running builds, source/evidence reconciliation, review assembly and candidate qualification |
| Source assembly helper | GPT-6.1-Sol | Concrete READY batch semantic review and isolated conflict staging for Integration; no independent dev push or global audit |
| Runtime coordination | GPT-6.1-Sol | Section/actor generator, lifecycle, committer and queued work, then mux/cold/service conversion and web concurrency |
| Composition | GPT-6-Astra | HM actions and capability contracts; real runtime linkage, schedule harness, carried read and crash composition; initial implementation as well as review |
| Served commands | GPT-6.1-Sol | NEWNEWS/OVER/HDR/XPAT and remaining streaming commands, view policy, reclaim-aware navigation, generated command switch |
| Storage and lifetime | GPT-6.1-Sol | Holder/root accounting, arena forget and release, reclaim/retention, checkpoint/recovery and bounded store operations |
| Representation | GPT-6.1-Sol | Owner carrier/dispatch and POST cost; paged catalog to dense groups/history/node roots; resource-ledger concrete representation |
| Generators and accounting | GPT-6.1-Sol | Cost/entry/operation contract, resource charges and settlement, carried-view/keyset/teeth/representation library completion and consumer rollout |
| Transport and operations | GPT-6.1-Sol | NNTP feeds, pull, BP/ION/TCPCL, authentication/configuration/operator repairs and bounded peer work |
| Tools and harvest | GPT-6.1-Sol | Repair/checker correctness and speed; mine useful historical implementations into current subsystem owners' work |

Active worker sessions are `deputy_integration`, `deputy_runtime`,
`deputy_served`, `deputy_foundations`, `deputy_tools`, `deputy_groundwork`,
`deputy_empirical`, `helper_resource_exec` and `helper_command_rows`: nine Sol
workers plus the strategic coordinator. The resource helper feeds Foundations
and Runtime; the command helper feeds Served. Empirical designs actual-image
workloads and replayable fault schedules, with Integration budgeting runs.
The groundwork deputy routes routine findings and READY source directly to peers
and Integration; only consequential decisions and user outcomes reach the
strategic coordinator. Integration alone pushes dev and coordinates expensive
builds. All workers use isolated trees under `build/lanes/`.

Existing ledger owner names remain historical workstream labels; the table
assigns continuing responsibility without asserting every future lane is active. The
coverage is: composition -> Composition; wrapper/failure-scope/host-lifecycle/
owner-offlock/host-deputy -> Runtime; served-catalog-live/def-command/liaison ->
Served; arena-forget/def-holder/reclaim-retention/sweep-store -> Storage;
stage-5b/cost-gate -> Representation; generators/def-entry/served-deputy's
NIGHT-COST items -> Generators; sweep-peer/sweep-ops/sweep-ops-cfg -> Transport;
sweep-gates/burndown/branch mining -> Tools; runner/dev-serves/integration ->
Integration. Cross-area entries are routed by their actual effect: for example
ION to Transport, owner-lock work to Runtime, reclaim credit to Storage.

Every owner reads the actual subject, its callers and continuation. They own the
whole workstream, choose complete landing slices and keep moving while checks
run. Two unlanded slices is a useful starting WIP bound, not an instruction to
sit idle until an image finishes. An obstruction gets a collaborator or a
revised implementation, not another permanent handoff. No unbounded child swarms.

Shared files are assembled by an agreed owner: Runtime for actor/section and
committer parts of owner/mux; Served for command/cursor parts; Storage for
reclaim/release; Representation for carrier signatures/dispatch. Agree on the
specific function boundary before concurrent edits. This does not serialize
whole subsystems because they share owner.lisp.

## Active consumer closure (groundwork wave, 2026-10-03)

These records describe the current executed boundary and the next acceptance
scenario; declarations and unused libraries do not close an initiative. Each
implementation owner follows its wiring, displaced-path removal and failures
through dev. Before starting another independent slice/lane, reduce orphaned READY
or integration-blocked work; useful preparation may continue beside a running
check. Integration owns the first combined candidate and its scoped host-prefix,
image and native checks. That candidate proceeds with runnable slices and does
not wait for completion of the actor/cursor/resource frameworks.

| Initiative | Actual producer and host consumer | First acceptance and continuing owner | Dependency owner / present evidence |
|---|---|---|---|
| Physical actor lifecycle | `fnn-owner-spawn-syncer` -> `fnn-owner-start-syncer` -> pipeline parent `fnn-owner-actor-join`; actual captured job is retained custody | Stop with held batch cleanup, failed/timed-out join and post-create latch failure retain the child/job until physical end; Runtime wires families and removes hand registration/failure recipes | Runtime model scoped certificate and native SBCL schedules; source READY `3bda776c6` to Integration, combined image pending |
| Owner worker accounting | Existing capacity input at `fnn-mux-budget-install` -> typed `fn-rl` owner worker account -> Runtime syncer draw and join/completion consumer | One worker draw before spawn remains held until physical join AND operation settlement, returns reusable projection exactly once; Foundations owns concrete producer/correspondence, Runtime wiring | Foundations/Runtime; real typed startup/issue/physical/outcome and actual fn-oqw receipt execute in the native fixture. Matching-image mux/profile acceptance remains pending. Flat owner accounting does not claim user subbanks/refunds or full rescue funding. Historical fixed12 'two spare' is stale: committer/syncer already consume them |
| Served metadata and continuation | `fn-nntp-newnews-response-cat` -> `fn-scr-command` -> owner handle chunk -> mux reply drain | `native_newnews_wildmat` with 1,000 articles and second reader, cold dependency deadline, maintenance alongside acceptance; Served owns command/cursor wiring and removes displaced response paths | Metadata/capture source landed; generated command caller and cursor shell assembled in `bb0b20203`, warm composition/drain checks pass. Combined native verdict and Foundations output funding remain pending |
| Typed worker ledger execution | Existing `fn-rl` draw/settle implementation -> Foundations `resource-syncer` producer -> Runtime syncer consumer | Preserve guards/abstraction, exhaustion refusal and exactly-once reusable return with pending receipt scalars; Resource exec helper owns book/tests, Foundations assembles | Stable receipt `e3412f1dc`; helper guards/preservation and bank correspondence `724b8e92c` assembled by Foundations. Bootstrap guard and matching certification follow, no tree/refund expansion |
| Command table continuation | NEXT/LAST/LISTGROUP and ARTICLE/HEAD/BODY/STAT rows -> `fn-proto-archive-command-cat` -> Served DC02 switch | Literal dispatch behavior and teeth preserve pinned-view policy; Command rows helper owns rows/tests, Served assembles and removes old switch paths | Seven rows consumed by Served actual switch; helper continues LIST/NEWGROUPS/DATE. NEWNEWS/OVER/HDR/XPAT remain Served |
| Empirical mixed workload | Actual qualified fn image -> concurrent posts/cold-slow readers/checkpoint-reclaim harness, then peer and late-return schedules | Seeded replay, four outcomes, latency/throughput/fairness and peak resident/disk/FD under matched profiles; Empirical owns harness/matrix, Integration budgets isolated-node runs | Active executable smoke on explicitly historical image coordinate while combined candidate builds; measurements never imply proof or current-image qualification |
| Publication capability | Arena plus generation pin captured in owner quantum -> `fnn-owner-publish-captured` -> checkpoint walk/write/release | Publication while accepts/readers proceed uses captured capability without off-section protected getters; Served carries capture through reclaim/export, Runtime later converts actor lifecycle | Publication actual graph+mutation checks passed at source merge; reclaim/export capture source READY `cb941ede3` with31 narrow checks, combined-image verdict pending |
| Host schedule composition | Actual `fn-pio-direct-admit/cancel/settle/quiet-p` outputs -> `fn-hmc-*` direct labels carrying holder effects | Cancellation, retirement, late physical return, fd/CID/worker reuse and stale receipts through same direct subjects; Groundwork owns machine, proof continuation and native label linkage | Actual admit/settle machine and finite witnesses certified; literal `:READ` witness certified in `fa21382ab`. All-schedules and actual HM/native realization remain owed. Funded sites require distinct transitions |
| Verifier and checker | Current unittest harness transplanted unchanged to base/head -> structured assertion observations; host graph -> stable source identities | Exact base assertion fails/head same IDs pass; shifted callback line numbers preserve debt rather than hiding new paths; Tools owns checker/fixture consumers and historical implementation routing | NIGHT-VERIFY 19 fixtures+archived witness source integrated; selector fixture READY, lock identity repair under narrow verification |
| Candidate assembly | Reviewed source -> Integration's immutable assembled candidate -> actual loaded host world and native modules | Host-prefix normal/DTN, real NEWNEWS/cold/publication and syncer custody scenario; Integration owns builds and source/evidence coordinates | dev contains integrated physical actors, publication capture, dispatcher source, model and checker/tool slices. Frozen `37f501197` certification234/0+784cached; host-prefix/images pending. No new image green or deployment claim |

The current coherent source queue (refresh the state, do not create another
tracker):

| Slice / grouped obligations | Producer -> consumer; assembler | Shared prerequisite | Next discriminating check | Source state / actual blocker |
|---|---|---|---|---|
| Frozen first candidate | Captured capabilities and physical actors -> real native service; Integration | Exact declared loaded world and normal/DTN host guards | sol1 host-prefix, then saved images and affected native modules | Immutable `37f501197`: certification234 passed/0 failed,784 matching cached; normal/DTN host LD failed/time-limited, no images/native verdict. Groundwork fixes file/window wrapper hints613/841; Integration reuses unchanged certificates/artifacts for repaired full LD |
| Direct HM boundary (HM02, PRF-1254, SCN-1082) | Actual direct read entries -> machine/literal checker -> actual observation packets; Integration assembles, Groundwork/Runtime/Empirical own consumers | Exact machine and direct dependency bytes; native event order/identity produced at primitive boundary | Actual extent normal/:READ packet with O/E/pins and completion/physical-return order | Main cancel/pin/capture/drain and physical return certified at matching source in074717/080416 manifests. Actual generated actor/shared section O-only packets replay with prefix invariants. Issue/settle/all-schedules, full extent/pin realization and funded pool remain owed |
| Funded syncer custody (resource exec and PRF-1252) | Actual mux capacity hold -> typed owner ledger -> syncer draw/physical/outcome; Foundations assembles Runtime and resource helper | Validated private creator, opaque token plus independent operation generation; two receipts before refund | Matching-image actual mux POST/stop, held cleanup, timeout and after-release starter failure | Creator repaired; actual start-syncer, typed methods, physical join and fn-oqw completion fixture passes0.26s, supplied local12-thread/1MiB projection. Helper bank/bootstrap guards consumed by Foundations final source59d46c3ff; Runtime342c7f153 READY. Matching combined certificate/image closure follows. Runtime owns production wire/late-fault path |
| Command rows into switch (DC03 -> DC02) | Seven table rows -> `fn-proto-archive-command-cat` -> actual `fn-scr-command`; Served assembles helper | Stable session/archive/index/verdict/env/view/arena/catalog inputs, pinned-view policy | Actual generated dispatch/chain replay and selected native command cases | DC03 consumed in Served `38f75aaa9`; generated caller installed. Helper continues LIST/NEWGROUPS/DATE, then available for a stable next seam; undeclared hand fallback removal remains Served debt |
| Metadata cursor and output custody (GEN-CURSOR) | One-candidate metadata step -> plan continuation -> mux drain; Served assembles Foundations projection | Exact wire residual; bounded initialization/working bytes; admitted connection draw precedes materialization | Actual plan drain equality at byte/visit budgets1 and256, then native sparse/cache-churn output | Served `bb0b20203` includes source shell/switch; composition residual and actual plan drain pass warm checks, source repair being committed. Foundations owns pre-materialization funding; reply wire bytes alone do not fund cons/copy heap windows. Capture/completed-view and allocation debt remain |
| Actual empirical scenarios (SCN-1083) | Matching actual image -> mixed posts/readers/checkpoint/reclaim and restart; Empirical owns, Integration assembles/runs | Exact image/host/profile and seeded trace, four outcomes distinct | Current-image mixed smoke; literal direct I/O trace only with grounded locks/pins | Historical `147c8f2a0`:48 exact records recover; reclaim refuses credit. Diagnostics `e76d5bc72` image execution pending. No current-image reclaim progress or HM trace claim; Groundwork owns bounded reclaim follow-through |
| Short feedback tooling | Changed books -> scoped exact hash/evidence audit; Tools owns, Integration assembles | Full final audit remains available; indexed bytes verified | Same scoped verdict and immutable-tree acquisition without repeated Git lookup | Scoped source/evidence audit reduced one installed-evidence query180s->4s; frozen-root negative/commondir memo `19decc5f8` READY. Integration owns actual next acquisition measure; no duplicate build |
| Transport credential boundary (S107/108/109) | `fnn-feed-auth-profile` -> push dial and `fnn-pull-profile` -> pull/catch-up; Tools owns, Integration assembles | Nonblocking descriptor capture/regular-file authority; ACL2-owned named outcome; Runtime retains feed actor/idle scope | FIFO/missing/insecure profile refuses before TCP, Store/core fault reaches service guard | Assigned Tools on current open dev items; investigate existing decode fault conversion as part of same consumer change. Native selected execution follows source; no broad audit |
| Carrier/pages and reclaim | Existing paged state/captured history -> checkpoint/reclaim/service; Groundwork owns, helper retask when current seam closes | Source-bound signatures, safe capture and actual allocating consumer; no invented maintenance grant | Refute whole-history-copy credit obstruction under same supported profile, then bounded captured-page replacement | Resource helper now owns existing paged-catalog attachment and real generic POST/reader/withdraw/reopen closure, Groundwork assembles. Groundwork removes whole-history-copy reclaim obstruction through that page/history seam; same-profile credit refusal16680640 remains. Command helper continues remaining rows; no new worker |

An assembler consumes READY promptly or names the concrete blocked-on owner in
this table/LANEDUMP. A helper can prepare a disjoint continuation while waiting;
it retains responsibility for consumer failures. Shared reports/evidence may
follow source integration with explicit pending status. One owner runs each
expensive check and reuses matching evidence; no new incoming READY moves the
frozen candidate.

Temporary raw-dispatch trust is a native realization facility with explicit owed
writers, not an `encapsulate` theorem assumption. The seven entries' actual
loaded-world guard bridges and matched raw/counterpart POST must pass before an
execution claim. The carrier migration owns eliminating that exception; source
integration does not retire its debt.

## Work that starts together

### Integrate the existing work and keep dev usable

Harvest ov1 and the other runs below before spending on replacement builds.
Finish integrating served-live, post-guard-off, wrapper and burndown-3 at current
dev, repairing actual conflicts and regressions. File matching manifests; an old
run can establish unchanged book bytes without establishing a new image verdict.
Keep native/proof remainders open after source landing.

Tools fixes NIGHT-VERIFY and the checker residuals, and starts HARVEST-WORK from
[branch archaeology](design/branch-archaeology-2026-10-03.md): atomic init,
stranded journal/barrier/control-capacity/reclaim work, useful proof/runtime
slices and matching historical evidence. Route recovered implementations to the
owner who will connect them. Check current applicability; a historical MINE-A
label is not a merge verdict. Do not delete branches or other sessions' files.

### Move coordination into ACL2, with the model alongside it

Finish the existing wrapper and its native failure behavior, repair the actor
join/spawn contract, and implement the committer as the first full ACL2 actor.
Reuse `books/owner-queued-work.lisp` and the existing `fn-hx-*` operation drivers;
do not create a second competing primitive vocabulary. Continue through the
remaining actor families in the TCB design. Pure decision transfers can proceed
alongside actor work from the start.

The interface decision is one declaration family for sections and actors, one
action vocabulary consumed by primitive dispatch, HM labels and checker data.
Each receipt carries its operation identity, outcome and surviving resource
custody. The model owner and Runtime agree on these shapes before incompatible
emitters spread; model and implementation then advance together.

A failed or timed-out join never proves physical termination. Reserve identity
before spawn (or latch start); keep ownership through terminal cleanup. Test
early exit, failed spawn/join, stop with held cleanup, closed-inbox offers,
duplicate/stale receipt and uncertain completion. Migrate families fully enough
to remove their repeated registration, failure and handoff recipes.

Carrier work proceeds concurrently. Existing shared globals remain accessible
only through the established serialized sections during migration. Off-section
ACL2 steps need private state, an appropriate catch context and reviewed raw
exports: no shared live-state access, unsafe hons/memoize or racing process-wide
`:protect` bookkeeping. A torn step faults; it is not retried. Those are real
runtime dependencies; completing every carrier proof first is not one.

Complete the off-lock consumers too: F8 maintenance capability capture, F7 mux
continuations, F4 file leases/pread, statement barriers and inline paths. S014's
current off-owner batch job is progress, but per-member FNFD fsync is still there:
coalesce the journal phase with its durable order preserved. Do not solve a
blocking callback by wrapping a whole maintenance operation in the owner lock.

### Finish served commands and their common continuation mechanism

Land the metadata NEWNEWS repair and command declaration; retain the dependency
deadline as containment while replacing whole-command retries. Finish GEN-CURSOR
across NEWNEWS and OVER, then cold HDR/XHDR/XPAT and other whole-response arms.
The generator owns preservation, response residual, progress, visits, working and
output bytes, and suspension/settlement; actual command declarations own policy.

Persist progress or retain a funded dependency until consumption. Fewer than
eight rows per quantum cannot guarantee progress in a shared eight-entry cache.
Exercise more than eight candidates, sparse results, cache churn, partial writes,
cancellation/late physical return and faults after multiline output starts.
The terminator must never turn omitted rows into an apparently complete reply.

Finish SCL2/S042 together across GROUP/LISTGROUP/NEXT/LAST/OVER: available count,
first/last and allocation watermark are distinct. Keeping 1 and 34 gives
`211 2 1 34`; an empty group gives `211 0 watermark+1 watermark`. Reclaim changes
root identity even where a count/version shortcut appears unchanged.

Implement the settled completed-view discovery and pin-first Message-ID policy,
including config-backed LIST forms; preserve the connection pin. Complete all
DC03 rows, install DC02's generated dispatcher and DC04's restricted dispatch,
and reduce view-policy debt through real consumers. Restricted streaming is work
to finish, not an indefinite reference-path exception. DATE freshness alone
does not establish discovery publication order.

### Complete storage lifetime and the page/resource foundation

Storage first finishes the deferred-seal and retention repairs, then carries the
per-handle name count over every reachable root through rebuild/swap. Compose
`def-holder` accounting with physical custody and durable ordering; counts alone
never license release. Cover BP workflow/bound-store roots, caches, reader views,
response cursors, pending/fenced members and whole-arena leases.

Complete arena-forget's actual read/reseat/crash paths: named forgotten-payload
fault, no resurrection, distinct staged-copy release, retained due work across
yields, and eventual release after holders end without requiring another POST.
Use [the revised design](design/arena-forget-2026-10-03.md), especially the final
name-count decision and eight native refutation phases. Logical invalidation,
file unlink and physical last-close are different effects. The native acceptance
must check exact kept bytes and recovery as well as disk/RSS. Behavior-first
allows exact proof debt; it does not justify wiring a release with unknown roots.

Representation repairs and replays the carrier transformation safely on an
isolated frozen candidate, using current source-bound signatures and correct
`:instance` handling. The handed-off destructive redo.sh is not the migration
procedure. Complete the seven-entry POST bridge and its owed writers, then remove
the assumption-backed escape as the carrier boundary is established. Measure
raw/counterpart on the same image, since-open and reopened fixtures.

STORE-PAGES resumes the implemented paged catalog/attachment, establishes its
actual served image behavior and matched costs, and advances dense group numbers,
overview pools, history and node roots. Use the existing page/representation
libraries; do not restart from the October 1 inventory as though nothing landed.
The continuing destination is page-backed state, bounded startup/tail replay and
checkpoint work, not a paged catalog demo. Carrier and page work have distinct
consumers and may be split between workers when they are independently ready.

RESOURCE-OPERATIONS starts now as a joint Generators/Representation contract,
using the existing resource vector/tree, typed ledger and page/read ownership.
Finish executable correspondence/guards, derive tariffs through the cost layer,
install user-bank/owner-reserve producers, and connect charge-before-effect and
settle-once to real entry/actor receipts. Include refusal-path transient cost,
retained outputs and physical completion. A timeout does not return resources
still held by I/O. No admission gate is enabled before its funding producer.
Continue across the allocating served entries; the first row is a test of the
interface, not the accounting project's completion criterion.

### Finish reusable libraries and remaining protocol/operations work

Generators repairs both def-cost defects, keeps transitive unknown costs visible,
installs the real fn-reader-chunk row and completes stamped/allocation/outcome
contracts and def-entry/operation integration. Cost across a command is its actual
trace with repeated actions, not a sum of distinct callee names. Finish the
carried-view and keyset consumers already underway, teeth provenance/obligations,
and paged representation generation. Move helpers into shared libraries where
real consumers repeat them; remove the displaced hand implementation when its
replacement is connected.

Transport finishes queue-head progress, round deadlines, streaming replies,
credentials/TLS/authentication, BP custody/reassembly, ION outcome distinctions
and operator/configuration repairs. Runtime owns web/mux actor conversion;
Storage owns log/checkpoint/import/journal/reclaim bounds. Small local fixes keep
flowing on Sol while larger replacements develop. A DISSOLVES-IN finding remains
open until its original scenario passes through the replacement.

## Composition decisions for implementation

Codex adopts the corrected contracts from Astra's
[reconciliation](design/whole-system-correctness-astra-2026-10-03.md#round-2-astras-reconciliation-with-the-composition-deputys-answer-same-session-after-delivery-verbatim):

- Reply refinement compares the emitted prefix plus retained continuation/output
  state against a snapshot-aware reference. Literal equality with all planned
  reply bytes is false after a section and before the socket drains.
- Mutation sections determine mutation order; capture/command identities and
  pinned epochs survive multiple quanta. Invalid actions fault or are disabled
  explicitly; they are not silently successful no-ops.
- Physical settlement needs an I/O-return assumption. Fair scheduling alone
  bounds neither fsync nor client drain. Deadline observation and its named
  posture are distinct from successful completion or known refusal.
- Use narrow runtime/I/O assumptions and an explicit remaining realization
  obligation. A broad host-is-model assumption cannot discharge the result the
  generated coordination and model are meant to establish.
- Check a lock DAG and contextual capabilities, including released-lock wait
  returns and dispatch administration versus the called target. A missing lease
  declaration is not by itself proof of a reachable use-after-close.

HM02 must run real funded/direct transitions, leases, cancellation and fd reuse,
then prove its all-schedules statements and drive native holds from the same
labels. A seeded checker JSON or initialization test is not this connection.
HM03 needs a true carried/historical-config statement for P2/M6/P8, not a bridge
to a static relation that reconfiguration refutes. HM01/crash work follows the
actual log open and abstract effect prefixes. When a statement fails, implement
and connect the useful true replacement.

## Runtime validation triggers

Keep four loops distinct. Warm REPL/scoped certification and reviewed source
integration continue frequently; target under three minutes from reviewed
coherent source READY to dev when no concrete correctness blocker is found.
Build or load an executable candidate when a changed host consumer poses a
specific runtime question that existing matching artifacts cannot answer. Run
the selected dynamic scenarios that answer that question, reusing exact matching
image/dependency/profile evidence. Full qualification belongs to a scoped
operational claim or convergence, not every source batch.

The frozen sol1 candidate answers host-prefix and the first combined physical
actor/publication behavior. A subsequent executable candidate is warranted for
the actual funded mux POST/stop and generated cursor/dispatcher paths absent
from sol1, once those coherent slices are assembled. Source churn alone is no
trigger. Do not defer all cross-layer validation to the final release: small
real creator/method/thread fixtures already refuted and repaired a boundary
that logical admission missed. Those fixtures do not establish whole-image or
whole-profile behavior. Integration owns build capacity and picks the smallest
matching load/image/scenario set; reports and later READYs proceed alongside.

## Integration, evidence and resources

The Integration deputy merges reviewed source directly onto dev during
stabilization, including the authorized behavior-first work with exact
`category=proof-owed` entries. New lanes start from current dev. If next is kept
as an integration mirror it is not a qualification gate. Fix forward; a failure
blocks its affected claim/candidate, not unrelated development. No baseline
increase merely to hide a newly exposed lock or ownership path.

Lanes run the narrow refuting check and affected roots. Reviewers inspect the
result and add only a missing discriminating check. Batch expensive images and
composition tests on an immutable candidate while subsequent work continues.
Book closure changes can require natives without host Lisp changes. Reuse matching
evidence; never transfer green to changed bytes. The X13 assurance catch-up has
an owner and remains visible alongside behavior-first development.

Use both build boxes, warm caches, swarm-build on hbox and slot-controlled laptop
ACL2. The integrator inventories existing jobs before starting heavy work and
allocates memory from RSS/ARC and observed throughput. There is no permanent
project-wide two-job quota inferred from yesterday's runs, and no independent
per-lane multiplication of expensive image builds. Do not delete others' caches
or worktrees to relieve pressure.

A workstream is done when its intended consumers run, replaced machinery is
removed or explicitly justified, affected scenarios pass, and source/evidence/
proof debt are accurately recorded. Reports say what the user can now do, what
remains broken and who is fixing it. Runtime qualification and deployment stay
separate; this plan does not authorize live-node changes or outward messaging.

## Initial inspection snapshot (historical, before this revision)

The following observations belong to the initial orientation, not a current
build-status poll. Planning commit `8d17b09dd` subsequently reached dev and next.
Re-read job status and current dev at dispatch.


- Remote `dev`: `9af0cd1a9c5a7b6f9106c72d8312c04f0405b9fa`, verified against
  origin. The shared checkout was `31d645af9`; `origin/next` was `a35902812`.
  Both are stale starting points for new lanes. Re-anchor the train to current
  dev by an ordinary fast-forward/merge, with no reset or force push.
- Before reconciliation: 259 repair items: 108 open, 52 in-progress, 69 ready,
  13 landed, 2 refuted, 10 duplicate, 5 deferred. Most READY source is already
  on dev. All 69 were reconciled to source-landed by exact ancestor receipts
  (67 explicit SHAs, two SHAs recovered from item notes). Five newly scoped
  issues are now recorded: 264 total, 113 open, 52 in-progress, zero ready,
  82 source-landed. Source landing does not establish native/proof completion.
- Existing native run `ov1` builds source `4671ace0f` (BM10); the only later
  change at `9af0cd1a9` is the BM10 ledger receipt. Its image-root certification
  passed (32 passed, zero failed; `certify-20261003T043548Z-620519`). At this
  inspection it was still in host loading: no image/native verdict exists.
  Harvest it; do not launch a duplicate build. Cite the built source, not the
  later ledger-only SHA. Do not label known OVER failures as a green suite.
- Last handoff image set: `45e05c7fdfcd4f34539b45c241ec217acdd8d3c1` on hbox.
  This is a fallback, not qualification of current source. Deployment was
  not inspected or changed during this orientation.
- Unmerged: served-live `7b9ffe475`, post-guard-off `812082a53`, wrapper
  `4e0e11c78`, burndown-3 `2f7f5bda2`. Their worktrees were clean. The carrier
  transformation `fa32ac06f` is a broken draft, not a candidate to merge.
- Served-live fast checks: 12/13, new R1 at owner.lisp:6090. Source tracing
  reaches the existing publication worker's off-section `fnn-live-arena`
  access through the new maintenance path. Do not wrap the whole maintenance
  tick in a lock: its callees already have sections, and I/O stays outside.
  Capture a protected arena/root capability at the proper boundary and pass
  it to the worker, or defer that independent slice while retaining its code.
- Wrapper's old farm run `run-20261003T041004Z-fe23` finished with 561 passed,
  11 failed. These harvested manifests are not yet in dev's evidence index;
  archive/index before claiming filed evidence. The changed failure-scope
  book passed at matching bytes; old
  BM09/BM10 failures elsewhere prevent a whole-run green claim.
- Burndown-3 already contains CL08/09, BM08/CL20, CL10, CL12 and CL11 work.
  Read its verification, including the base failure reason, before redispatch.

The lasting post-foundation capability queue is [NSLICESQUEUE.md](../NSLICESQUEUE.md).
Primary implementation continues alongside the proof sweep: Served owns the
configured-group selector through actual NEWNEWS factory/plan; Foundations
owns explicit heap funding and Runtime the retained output drain/discard
consumer; Groundwork owns history/page-backed reclamation, with the page
helper answering the existing catalog attachment/creator/smoke question first.
Tools owns BP send/refusal boundaries; Groundwork owns canonical retention
reservation and Empirical the undertake/release/reopen delivery scenario.
Integration owns one exact executable candidate and its selected questions.
Host all-schedules assurance, later operator-path closure and unstarted
capabilities remain explicit queue work, not implications of POST smoke.

The first developer old-catalog executable at frozen `1a946582c` has actual
normal/DTN host-prefix passes and POST/duplicate/readback passes. It does not
contain every newer source slice. The retention producer repair `7c6d135f3`
restores ACL2's identity gate before log allocation; the reviewed aggregate
`56f97b4d3` is handed to Integration. Actual BP undertaking/release/reopen is
the next discriminating consumer, not another historical-image retry.
