# Swarm coordination

Implementation dispatched on 2026-09-23 from `df5097b6`.
The [takeover plan](takeover-2026-09-23.md) gives candidate work; the
[working loop](how-we-work.md) gives coordination and compute rules.

This board records intentions and agreements, not exclusive file claims.
Agents communicate directly; updating the board or waiting for root is not
a prerequisite to making an agreement with a peer. Root consolidates the
summary during convergence so it survives compaction.

For each active effort record:

- Agent/task name, intended result and current source/worktree.
- Expected shared functions/interfaces and collaborators to contact.
- What was agreed, the next useful action, and any real dependency.
- Existing proof/build run to reuse: host, absolute path, source/closure
  identity, toolchain, run ID and manifest when available.
- Who will assemble this particular change and check the combined evidence.

In the current Codex harness, use `collaboration.list_agents` and
`collaboration.send_message` for discovery and direct peer coordination.
Share discoveries and failed attempts as well as successful commits. Name
revision and theorem hypotheses when sharing a proof so its scope is clear.

## Current coordination — 2026-09-24

### Wind-down convergence — 07:16 UTC

All current implementation packets are on dev; the
[handoff](handoff-2026-09-24-winddown.md) supersedes the active assignments
below. Both BP guard lanes stopped after the bounded repair: lower helper
guards passed, while the outer debt helper needs a maintained-base invariant
through its inner report step. No new feature or proof search is running.
Only `native_qualification` remains active on exact `8a1b31f9`, hbox gate
`/tank/fn/gates/final-cut-8a1b31f9-20260924`, ordinary run
`run-20260924T070856Z-7ddd`, four jobs with a 300-second per-book bound.
Its full result or explicit bounded partial stop is the last handoff packet.
The exact source passed root's structural check; no image may be built around
the known failed guard root.

The [first](evidence/worktree-retirement-convergence-2026-09-24.md) and
[final](evidence/worktree-retirement-final-handoffs-2026-09-24.md) retirement
batches preserve and verify the completed lanes privately while retaining
branch references. No remote evidence gate or live service was removed.
The goal will be paused and the user-requested local `ALLDONE.marker` written
only after all workers and owned scratch jobs are quiescent.

### Complete capability wave — 06:06 UTC

The [capability plan](capability-wave-2026-09-24.md) supersedes earlier serial
implementation holds. Topic v2, local key lifecycle, pack retirement, human
drafts/outbox and the experimental ION observer are integrated. Root is
converging their source; `native_qualification` owns the next shared image pair
from an immutable checkout and the current b074 runtime evidence packet.

- `bp_foundation` and `bp_counterexample_completion` are joining dispatch,
  forwarding, session/MRU and cached journal debt on the actual native path.
- `consumer_contract` repairs configured-owner index rebuild and maintains the
  Store/topic/crash relation; `topic_metadata` supplies cooperating v2 witnesses.
- `storage_kernel_completion` owns retention record publication/cuts;
  `status_codec_proof` supplies the actual configured-owner retention entry.
- `assurance_review_followup` now extends the per-principal lifecycle proof
  through Store/replay. `retire_old_worktrees` owns preservation cut fidelity
  and mixed topic/pack native tests, not further housekeeping.
- `mini_reply_join` shares the qualifier's two protected Stores for the actual
  report/ACK/reply experiment. Mini changes stay in its isolated evidence lane.
- `review_branch_inventory` has transferred from human client work to the
  ION observation/current-attempt/receipt join. `stamp_review` completed its
  bounded Astra handoff; further transport implementation is Sol work.

The root's `ca68b5a1` fixes the native BP identity vector/string comparison.
Its raw actual-function test passed; both N03 and interrupted-fragment native
retests need the next image. The configured-owner missing consumer index is a
distinct runtime defect, owned by `consumer_contract`. Existing failed logs
are evidence, not discarded fixture noise. Combined proof capacity remains
four jobs, scoped runs coordinated separately; agents reuse matching caches.

At 06:17 UTC the immutable `863c2141` combined run is active on hbox as
`run-20260924T061318Z-cd11`, gate
`/tank/fn/gates/capability-863c2141-20260924`. The revised work distribution is:
`topic_metadata` implements shared NNTP/BP verified incoming authorship with
`assurance_review_followup`; `consumer_contract` continues the integrated
partial maintained topic bridge. `mini_reply_join` adds A-side durable reply
consumption while retaining the failed old-image two-Store preflight. The
preservation agent extends the isolated block-error campaign in addition to
running its pack/mixed-history subset when the shared image exists. The
qualifier hands independent native test subsets to those agents instead of
serializing every test through one worker. No new duplicate build is needed.

### Recovery repair, BP prerequisites and complete exchanges — 05:28 UTC

Root integrated pure BP debt and dispatch codec prerequisites through
`a2357594`; generated ledger/static convergence follows. These do not activate
forwarding. `native_qualification` owns the next one ordinary combined run
at four jobs with a 300-second discovery bound after the finite byte-store
conditional repair lands, then one shared image pair. The stronger topic
bridge continues alongside native qualification; its missing proof is stated
explicitly rather than assumed away.

- `storage_kernel_completion`: finish the conditional byte reopen theorem and
  exact physical counterexample, then resume served storage correspondence.
- `topic_metadata` with `consumer_contract`: maintain topic validity through
  actual Store transitions/crash/replay, reusing the qualified candidate-sequence
  helper. Versioned topic migration stays separate.
- `bp_foundation` with `bp_counterexample_completion`: complete codec guards and
  typed inverse, and implement/prove cached used/debt updates of the actual
  outer progress machine. Coordinate shared slots and durable callback deltas;
  no per-command full-history reconstruction or sibling semantic reducer.
- `mini_reply_join`: extend the separate qualified E2/B3 legs to two Stores
  with explicit durable application/ACK/reply cuts. Mini remains isolated;
  share existing images and scratch ports with the qualifier.
- `review_branch_inventory`: opt-in durable local web-client submission outbox,
  exact frozen source before network, no automatic repost after ambiguity,
  restart/read-only settlement tests; no proof farm or native server changes.
- `assurance_review_followup`: delivered the current pinned assurance snapshot.
- `status_codec_proof`: available for concrete combined-gate findings.

The Mini candidate's same-fixture clean read-only reopen median is 26.65 seconds
versus 29.72 baseline across three interleaved pairs; full native B3 evidence
still belongs to the original binary. Neither measurement establishes general
replay throughput. The earlier active-reader reclaim fixture remains in the
next shared-image campaign. No live service change is authorized by this board.

### Converging consumer/topic, BP progress and Store interface — 04:52 UTC

Root integrated source through `2b3a8d31`; ledger regeneration and static check
precede the next single combined hbox run. The previously red consumer theorem
and its new mixed-topic witness have scoped certification. BP's engine and
actual-called selection/obligation theorem plus recovery teeth are integrated.
The Store export-interface packet is also scoped-certified; its wider reverse
closure is deliberately part of this batch. `native_qualification` owns the
four-job run and matching image pair; no parallel image build is authorized by
this board.

- `consumer_contract` measures indexed native poll after that image builds.
- `bp_foundation` and `bp_counterexample_completion` support the N03 native
  fixture and then continue the declared remaining selection/session/debt work.
- `status_codec_proof` supports any concrete downstream interface proof finding.
- `storage_kernel_completion` extends owner/byte correspondence through failed
  directory barriers, distinguishing applied and dropped physical outcomes.
- `mini_reply_join` profiles compiled historical admission before optimizing;
  its already qualified B3 artifacts remain separate and preserved.
- `review_branch_inventory` adds actual offline reclaim exclusion while an
  owner serves a pinned reader, then exact retained-source recovery evidence.
- `assurance_review_followup` supplied the consumer/topic fixture and its
  evidence; `topic_metadata` refreshed the assurance snapshot at `f277823d`.
- `retire_old_worktrees` archived six further landed lanes, retaining branches,
  ignored logs and per-tree restore manifests outside the checkout.

The `67d026ad` combined run is terminal failed: 263 passed, four actual
failed theorem events and seven dependent failures; no image exists. The
[manifest/cause record](evidence/wide-combined-67d026ad-red-2026-09-24.md)
is retained. `consumer_contract` repairs acceptance-stamp; `status_codec_proof`
repairs Store prepare (including the owner-prepare cascade); `bp_foundation`
repairs BP observed-reopen premises; `storage_kernel_completion` finishes exact
EIO counterexamples then repairs byte-model reopen. `assurance_review_followup`
fixes live farm reporting: exited processes are not certified books. The
qualifier waits for a coherent repaired cut and will use the 300-second bound.
BP debt/dispatch and topic-v2 migration implementation proceed on separate
branches; neither is silently folded into this repair cutoff.

The older sections below describe their own checkpoints, not current image
qualification. The live node remains protected.

### Resumed wide Sol cycle — 03:31 UTC

The user requested wide forward implementation, mostly GPT-6-Sol. Root
integrated topic/index at `f9f809b2`; frozen `8c61c098` adds the final Luna
trial record. The following intentions supersede older lane checkpoints.
They do not grant exclusive ownership.

| Agent | Intended result and direct collaborators |
| --- | --- |
| `native_qualification` | One combined closure and production/developer image pair at `8c61c098`; topic admission/reopen and indexed consumer/status compatibility. Shares the fixture with `mini_reply_join`. |
| `topic_metadata` | Repair concrete topic/index integration findings with the qualifier and consumer lane; no duplicate qualification run. |
| `bp_foundation` | Transplant the qualified fragment/expiry activation packet onto current Store state, then interrupted-fragment/restart runtime qualification. Coordinates foundation changes with BP counterexample lane. |
| `storage_kernel_completion` | Integrate allocator pair-12/pair-14 relation proofs and advance the actual served entry/crash correspondence. Shares physical publisher facts with BP lanes. |
| `consumer_contract` | Complete the actual indexed-poll correspondence's missing premise witnesses and measure served polling with the qualifier. |
| `mini_reply_join` | Complete native B3 durable hybrid reply preparation, retry, post and reopened readback in the isolated Mini evidence worktree. |
| `bp_counterexample_completion` | Ground N03/N04/N05 suite gaps in the implemented host path; implement a coherent missing progress slice with its witnesses where required. |
| `status_codec_proof` | Prove the general kind-9 status codec roundtrip with concrete full-antecedent and premise witnesses. |
| `assurance_review_followup` | Reuse existing event/digest/closure checks to warn about unsupported certified registry claims; no proof farm required. |

The first shared qualification at `8c61c098` failed; its original manifest
and finite failure classification are [preserved](evidence/topic-index-8c61-full-gate-red-2026-09-24.md).
All seven independent causes now have scoped source repairs integrated,
including the newly exposed K7 dependent proof. Root also landed the BP
activation/live-selection, consumer relation, status codec and allocator
packets. The next combined freeze follows generated-ledger/static convergence;
`native_qualification` owns its one four-job hbox run and shared image pair.

Active follow-on work: `storage_kernel_completion` joins the shared owner
callback chain; the two BP lanes cooperate on actual foundation progress and
its N03/N04/N05 contracts; `consumer_contract` prepares real indexed-poll
measurements; `mini_reply_join` repairs and exercises B3 on the existing
qualified e160 image; `assurance_review_followup` aggregates current proof-cost
evidence. Root keeps native qualification distinct from lane certificates.
The general status codec proof and the earlier idle/replay and K6 cost fixes
are now integrated; their old open notes below are historical.

Lane runs stay within shared pools, at most two jobs each; combined runs use
four. Live `.active.json` and per-book logs now identify actual work before
completion. Native tests use disposable stores, never `/tank/fn/node`.

### Following the repaired freeze — 04:12 UTC

`f0d67034` passed the main static check and is the sole combined hbox run
`run-20260924T041225Z-7481` at
`/tank/fn/gates/topic-index-repaired-f0d67034-20260924`: 521 cached/kept,
97 to certify, four jobs. No image verdict follows from submission.
Root released the verified idle `cstatus` REPL with its normal stop command;
it had held a shared slot after its codec work completed.

The next packets proceed alongside that fixed test subject:

- `bp_foundation` and `bp_counterexample_completion`: the actual outer
  progress caller, route waits and an older-unrouted/younger-local trace;
  forwarding/session policy and durable journal debt remain separate gaps.
- `topic_metadata`: exact historical report retry as a distinct replayed
  success without another event or charge; the current host incorrectly
  refuses the ACL2 historical-success result.
- `storage_kernel_completion`: shared owner callback correspondence beyond
  the already landed inner Store callback result.
- `mini_reply_join`: preserve definite refusal, uncertainty and transport
  fault through the real reply signer, then complete the B3 exchange.
- `consumer_contract`: native indexed-poll cost measurement on the shared
  image when available.
- `status_codec_proof` and `review_branch_inventory`: bounded peer-inbound
  and Store-cluster proof-cost repairs, preserving theorem statements.
- `assurance_review_followup`: identify and close a substantive guard gap
  on an actual runtime caller, avoiding theorem-only guard-count work.

The cost-history packet is integrated at `af47c79a`, with the aggregate
summary correction at `7caa9a03`; eight focused tests and the integrated
static check pass. None changes the frozen server/proof source.

### Previous cycle checkpoint

Root recovered the two accidental main-checkout operations; see
[recovery](worktree-recovery-2026-09-24.md). ADVANCE, OVER, allocator frontier
entry, consumer-index foundations, web paging and offline cursor inspection
are integrated. Combined `a785ae03` source and its selected native gates are
recorded in [the native evidence](evidence/native-a785-selected-gate-2026-09-24.md).
The later D1b selector repair awaits the next shared image. The live
`da5fd8cb` node is protected.

- The [GPT-6-Luna feature trial](experiments/luna-feature-trial-2026-09-24.md)
  is source-integrated at `e160442f`. Its four-job hbox run
  `run-20260924T031246Z-1771` passed all default, DTN and ACL2 test roots.
  The [one source-matched image pair](evidence/native-luna-e160-selected-2026-09-24.md)
  has passed native web paging, cursor inspection and local consumer status.
  General status codec roundtrip
  `PRF-068` remains open; Sol repaired the decoder guard and ACL2 fixtures.
  The trial record separates Luna implementation, Sol review/proof work,
  root assistance and the measured session-cost proxy. Future bounded Luna
  fn lanes leave proof development and certification failures with Sol.
- `native_qualification` also passed the D1b report cut on that same image
  after a test-only ordering fix `7c1215d6`: the first driver had queried
  the sender's Store while its live process held the lock. This is separate
  from the three Luna features.
- `consumer_contract` has scoped certificates for the topic/index Store
  relation, observed reopen and actual indexed owner poll; it assembles a
  finite source/evidence packet. `topic_metadata` joins its native topic tail
  to that packet in an explicit isolated worktree. They coordinate the poll
  scope helper with the Luna status lane. This next packet does not block
  the smaller trial image.
- BP fragment activation and persisted expiry-safe replacement are qualified
  on `fix/bp-union-proof` at `3d1a461e`; native interrupted-contact execution
  and the remaining recovery decoder guards are open. Root has the packet.
- Allocator pair-12 and pair-14 relation proofs are qualified on
  `implement/byte-store-k568` at `af679760`; they await integration. They do
  not establish the entire physical recovery argument.
- Mini's isolated `fn-evidence` branch has live poll/transaction/reopen/ACK
  evidence and B3 durable reply preparation/signing source. B3 signed native
  post/readback remains unrun and needs coordinated fixture startup.
- `retire_old_worktrees` completed verified archival of 101 inactive or landed
  trees. Active trees and branch tips remain available.

The entries below are historical checkpoints.

## Wide implementation cycle — revised goal, 2026-09-23

The user replaced the goal with concurrent v0/v1 development grounded in
`/Users/ember/dev/breadstuffs` and `/Users/ember/dev/minidregg`. Image cuts
identify reproducible experiments; they are not a project-wide implementation
freeze. Preserve the live `da5fd8cb` node and existing shared compute pools.

Current coordination snapshot: `bc9be7ec` passed full source qualification
(run `run-20260923T230009Z-f41e`, original manifest
`certify-20260923T230027Z-407330.json`) and both shared native builds at
`/tank/fn/gates/reader-clone-poll-native-bc9-20260923`. INN and selected
peering passed. Poll and live-created-group posting exposed host composition
bugs; the source-matched image stays immutable while the fixes land. Live node unchanged.
Root has integrated later K0 argument/preparation bridges, Mini read-only
projection (current-source guard/dependency correction pending), poll CLI fix,
peering harness/evidence, and owner proof-cost hints.

| Agent | Current substantive result and coordination |
| --- | --- |
| `acceptance_stamp` | READ relation qualified on earlier source; investigates actual ADVANCE success/refusal and config-pin preservation on the E2/T17 port. |
| `store_invariants` | Ports historical READ relation to current E2/T17, sharing source with acceptance lane. |
| `consumer_contract` | Poll integrated; adds derived sequence index with carried correspondence to remove prefix traversal. Coordinates Store slot13 after topic slot12. |
| `crash_differential` | Pair-10 full byte relation integrated; proves actual served framing/name call-argument bridge and names remaining physical entry invariant. |
| `authorship_carrier` | Clone and auxiliary replay integrated; advancing-ACK four-cut driver ready; reviews actual clone recovery/outcomes. |
| `feed_replay` | T17 and source-only native driver integrated; proof-cost repairs integrated. No redundant build. |
| `bp_foundation` | Assembles fragments, observed-channel admission, K6 v3 and D1b into one source; closes actual fragment wrapper guards. |
| `status_codec` | Durable kind10 deletion retains exact report intent across crash; joins actual native publisher and admin report queue. |
| `fragment_refinement` | K6 v3 raw/projected intent and recovered Message-ID binding qualified; consolidates raw EID parsing/admission/FNBS ingress in one ACL2 called wrapper. |
| `stamp_review` | Shared a8e4 developer/production image and reader/E2/clone qualification; exports exact public poll bytes for Mini. |
| `mini_evidence_bridge` | Portable inbox and exact-sharing replay optimizations complete in isolated Mini worktree; implements Store-report/cursor durable join with consumer lane. |
| `topic_metadata` | Actual Store topic slot12 projection scoped certified; reverse invariants and native anchor/admission caller underway. |

Root integrates finite source commits, regenerates ledgers, checks concrete
proof/runtime regressions and maintains evidence. No lane is a permanent file
owner. Announce interface changes and coordinate combined patches directly.
The specialized Astra OS study is complete in
[dregg-os-integration-2026-09-23.md](dregg-os-integration-2026-09-23.md).
It grounds P0/P1/P2 in Mini's real resource receiver and distinguishes Bread's destructive mailbox and ambient owner authority from the selected E2 contract.
The Mini evidence implementation continues in its isolated integration worktree.

## Qualification underway alongside implementation

Frozen `329a51a2` certified from scratch and all four native profiles built.
Its scoped runtime campaign passed migration (including selected old checkpoint),
checkpoint/admin, protected peering and raw/served process-death tests. Corrected
OpenSSL harness selection passed both real hybrid author tests. The NEWNEWS
harness was corrected to the conservative no-clock legacy policy. The receipt
fault selector repair passed the rebuilt developer image's unchanged BP suite.

Copying that image to persvati exposed an actual portability defect: the saved
core retained the hbox OpenSSL absolute path. The source fix now passes on isolated `1836ed01` production/developer images:
copied-image TLS/hybrid, missing-bundle refusal and actual two-host protected
exchange. The earlier failed attempt remains recorded separately.

Root's BP merge qualification passed and landed as `a093a6b2`: `run-20260923T184236Z-0991` on hbox,
`/tank/fn/gates/integrate-bp-a2-2009-current`, twenty changed/dependent roots,
two jobs and the existing pool, 33.293 seconds. The lane's source certificate set differed in
shared dependency bytes from current dev, so this is a real integration check.
T8b and authorship have their own announced coherent/affected runs; do not
start duplicate runs merely because a wait expired.

Root integrated native A2/contact and the TCPCL coalesced-output repair at
`66bf9e55`. Current-Store dependency roots passed in hbox
`run-20260923T190525Z-2d0f`; all six changed roots have current evidence.
Foundation assembles one image with its exact kind-5 payload inspection
regression, then exercises restart/integrity/contacts. Do not substitute
file size or logged payload length for retained byte equality.

The295 developer image qualifies T8 live configuration and T10a durable
authorship/reopen; HDR/index joins remain pending. Current BP image passes
its repaired native suite, while actual monotonic expiry exposed a persisted
process-clock defect. Foundation and feed cooperate on a boot-domain record
and restart/legacy compatibility decisions before claiming reboot support.
E2 completion now needs an explicit carried projection/replay invariant,
not merely an extra assumed recovery predicate; its lane is proving that
while stamp_review builds the native publication adapter.

## Current union and next cooperating packets

- Root qualification: `536ca577`, hbox `run-20260923T201700Z-0e13`,
  gate `/tank/fn/gates/integrate-reader-bp-topic-20260923`, four jobs,
  existing w28/cache/pools, default+DTN+ACL2 test roots.
  `stamp_review` owns the next developer image and native reader, entire
  hybrid-author suite (including peering/restart), and topic inspection.
- `store_invariants` and `acceptance_stamp` compose historical wire/index/
  verdict preservation. Indexed-open cost packet `84ddec61` is separate
  from the already integrated TLS-prefix pin repair.
- `bp_foundation` and `status_codec` compose A3 same-owner app delivery and
  receipt outbox; exact handoff-trigger and payload/peer binding are required.
- `consumer_contract` repairs the completed-prefix/pending-event invariant
  before native E2 qualification. `authorship_carrier` has a qualified
  component preservation/fenced-clone packet at `0a56254c`; its native
  clone fault campaign awaits that E2 image.
- `crash_differential` has a modeled final-link/decoder crash packet at
  `52bf0ad7`; whole scanner membership and K0 still need composition.
- Mini P1 fixture `026e18da` landed. `mini_evidence_bridge` now joins actual
  portable authored-source verification without inventing Store admission
  evidence or an unimplemented E2 endpoint.
- Topic metadata packet is in the frozen union; `topic_metadata` continues
  general codec/source-binding assurance. Governance choices remain proposals.
- Certificate compatibility selector now serves incremental certification
  and image acquisition. Measured default 202-book candidate selection on
  `e4f62e7c` took 1.56s, with no recertification or cache writes.

## Findings during the combined qualification

The `536ca577` union finished with three failed proof roots plus their tests;
[the original failed manifest and diagnosis](evidence/reader-bp-topic-union-2026-09-23.md)
are preserved. Reader-context repair `80da2a65` landed as `088050ff`;
`fragment_refinement` is fixing the pinned auth/agent theorem chain and its
163-second expansion. Root will qualify the repaired full Makefile root set
incrementally, including the previously omitted ideal/replay invariant roots.

The separate A3 image `5930f4f2` built and passed existing receive/recovery
suites. Its first actual request test exposed an endpoint record/string
caller mismatch; `status_codec` repairs it before the next image. Its test
must still observe actual application acceptance and receipt production.

Mini's next shared-image consumer uses a versioned portable verification
line with exact source and full principal/Ed25519/ML-DSA-65 key pins. This is
portable authorship, not Store admission evidence. `stamp_review` will include
that native verb when root cuts the repaired shared image; no duplicate Mini
fn image is being built.

`authorship_carrier` now investigates the open no-posters served-fold claim
while its preservation packet awaits E2. Initial source inspection shows the
old no-any-submission formulation fails when AUTHINFO grants a transit peer
role. The meaningful local-POST safety property must allow authorized transit;
a reachable witness and explicit corrected contract are required.

## Native checkpoint and continuing work

`884e4816` has a built developer image with passed full hybrid-author, indexed
reader/restart and topic-inspection suites. Evidence is
[native-reader-884e4816](evidence/native-reader-884e4816-2026-09-23.md).
Mini P2 portable authorship passed on the same image; its archive is forthcoming.
`stamp_review` reuses it for isolated INN/live-config and applicable native
matrix coverage. Do not rebuild for that campaign or disturb the live node.

Indexed-open source through `ceed4b9e` separately passed all Makefile roots
in hbox `run-20260923T203850Z-16b5`, 29 certified / 483 cached; the earlier
image excludes that cost optimization. Root static check is recorded under
`build/launch-20260923/indexed-open-check.log`.

Next integration packets remain active: K6 source `14d08cdb` adds actual
pair-10 crash/decoder provenance and fixes the typed Store-event sequence
accessor; T8/T17 colleagues compose exact pin cleanup and historical read
preservation; E2 colleagues close a runaway resolution proof before the
consumer crash-prefix relation; A3's native return receipt peer mismatch is
fixed in `7e62af7c` and awaits its combined image. A3's five fault tests passed
on the preceding image, which still refuses the happy-path receipt.

P3 will add folded field rendering/decoding and coherent signed-envelope
bounds for its full maximum roster, rather than silently reducing the profile.
Current 998-octet physical line and 8192-octet header limits do not fit every
maximal codec value after the mandatory hybrid carrier. The short-duplicate
native witness now reaches actual topic rejection; the earlier oversize
negative remains recorded separately.

Current convergence checkpoint (root `b9bf596d`):

- K6 through `aedf696f` integrated, including typed Store-event sequence and
  conditional pair-10 whole-list scanner bridge. General K0 actual-call
  relation establishment continues in `crash_differential`.
- Topic proof packet `9ff82359` integrated; folded maximum signed-envelope
  source and its broad dependent qualification are next.
- Auth handled-command correspondence `cdedd176` integrated. Authorship lane
  proves the full no-local-POST fold while preserving authorized transit.
- Historical T8/T17 relation union continues. Archive/pin domain witnesses
  are certified; actual read bounds and full relation composition remain.
- A3 native source through `7ad230b5` and fault evidence are integrated at
  `7c25183d` and followups. Foundation/status finish effective handoff projection.
  Fragment review found missing observed-channel principal admission and an
  outbox ambiguity-to-refusal error; repair them before claiming those seams.
- Mini P2 bounded-output twelve-case evidence integrated `0d411186`; lane
  joins actual portable authentication to Mini P1 durable operation/reply.
- E2 phase-aware completed-prefix/crash relation remains in progress; native
  fetch/ack and preservation-clone campaign depend on this coherent packet.
- Frozen884 broader INN/live-config/matrix evidence integrated `b9bf596d`.
  Stamp fixes the wildcard-config matrix's usage expectation without changing
  native accepted/refused/uncertain meanings.
- Latest root full Makefile-root proof run: hbox `run-20260923T205921Z-411b`,
  `/tank/fn/gates/integrate-a3-scanner-20260923`, four jobs, existing pool/cache: passed, 493 cached, 28 newly
  certified, 27.353 seconds, manifest `certify-20260923T205938Z-120445`.
  Prior `2234c1f3` run passed (496 cached, 17 certified, 15.164 seconds).

## Current cooperation checkpoint — 23:16 UTC

- `stamp_review`: integrated poll CLI fix `e1b4eeb8` → root `59cfdc25`;
  repairs live configuration observer caches and current-owner group-code
  projection, with raw and saved-image regression. New-group post refusal
  followed by BUSY is an observed defect, not dismissed as a fixture issue.
- `fragment_refinement`: INN/peering evidence integrated (`d81ff4fb`,
  `a5fdc44a`); now repairs shared completion handling when a commit callback
  refuses after the owner took a control request. Coordinates owner.lisp
  edits with stamp; preserves uncertain/fault fences.
- `store_invariants` and `mini_evidence_bridge`: cursor decoder guards were
  already verified; the Mini projection came from an older dependency and
  calls removed `fn-cp-at-mostp`. Adapt it to current bounded primitive and
  close actual projection guards. Mini getter packet `36869776` removes
  duplicated host preflight constants. One final current-source run is owed.
- `bp_foundation`: coherent root-based union in `build/lanes/bp-current-union`
  includes fragment/expiry/K6 v3/D1b/composed admission, plus new actual BP
  owner-event relation lemmas (`9a5b3898`) and owner cost hints (`cb21c4d6`).
  Final selected owner/dependent run `run-20260923T231510Z-0e00` is active;
  status lane closes actual report wrapper guards. No separate image build.
- `topic_metadata` and `consumer_contract`: cooperate from full P3 ancestry
  (c43aa989,66f81e7a,15f4fb19,6055b4a5,b8101d94,702d6ef1), not an isolated
  last commit. Topic slot12 and derived sequence-index slot13 share an updater
  that preserves untouched fields; physical config reopen must retain both.
  Pure index `2c82adaf` is qualified, actual called poll join is in progress.
- `acceptance_stamp`: actual ADVANCE outcome avoids repinning refused rebuilds;
  a certified duplicate-ID counterexample shows historical relation needs
  unique connection IDs. Carried uniqueness/ADVANCE preservation and dependent
  reader union qualify together; no root landing yet.
- `crash_differential`: continues actual P-FRONTIER successful reserved-entry
  relation from prior related state. Root suggested public checked-attachment
  frontier codec interfaces for host wrappers, rather than a new abstract/
  concrete equality assumption. Hardware and general trace scope remain open.
- `feed_replay`: efficient OVER range through existing group bucket and trie;
  proves reachable number/ID/article correspondence instead of introducing
  a disposable per-request full-archive projection.
- `authorship_carrier`: owner proof-cost packet `c922852d` integrated as
  `762c8ee2`; closed unrelated definitions in two theorem-local hints, no
  theorem statement/runtime changes. Store/projection and BP lanes reuse it.

The next small repaired poll/clone/Mini-projection image should not wait for
all later P3 or BP work. Keep each source and test-driver identity explicit.

### Storage topic/reopen handoff — 2026-09-24 05:25 UTC

- `storage_kernel_completion` on isolated `fix/byte-store-topic-reopen`:
  byte K4 and sweep reopen statements carry the exact scanned observed-topic
  replay premise required by Store v6. A physically framed topic-anchor image
  after a consumer bootstrap satisfies the old consumer/byte/crash/identity
  premises and refuses at `fn-sn-open-observed` because topic replay fails.
  Persvati selected book/test `run-20260924T052420Z-2a40` passed at two jobs;
  evidence `planning/evidence/byte-k4-topic-reopen-2026-09-24.md`. The packet
  is conditional; topic_metadata owns the maintained actual Store topic/crash
  bridge and BP foundation uses that shared interface. No native or full
  closure run was duplicated.


### Root checkpoint — 2026-09-23 23:33 UTC

- `1d26e01f` repair source full ACL2 PASS, 36.027 seconds; shared production
  and developer images built. Signed poll, lost advancing-ACK reply/reopen,
  historical live-group reader, clone rollover tests pass in the image lane;
  original negative driver assertions and corrected test hashes are retained
  separately. Mini is consuming the exact exported event and cursor.
- BP source `48425e4e` full run `run-20260923T232555Z-a3c1` FAILED:
  `bp-node-fragment-guards` timed out; `bp-report-guards` is its dependent;
  `bp-fnbs-replay-invariants` and its test failed. Acceptance lane repairs the
  fragment guard from its log, BP foundation repairs replay; status lane
  maintains report campaign. No new unrelated behavior lands before these
  batch regressions are repaired.
- Ready subsequent packets: actual ADVANCE historical-reader relation
  through `b8a1a02b`; allocator file-fence K0 through `f82213a3` with later
  record-list proof in progress. Topic and consumer index lanes cooperate
  on the shared Store configuration updater. Indexed OVER/XOVER closes its
  affected owner proof set. The protected live service remains untouched.
