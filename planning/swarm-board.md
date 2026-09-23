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

## Wide implementation cycle — revised goal, 2026-09-23

The user replaced the goal with concurrent v0/v1 development grounded in
`/Users/ember/dev/breadstuffs` and `/Users/ember/dev/minidregg`. Image cuts
identify reproducible experiments; they are not a project-wide implementation
freeze. Preserve the live `da5fd8cb` node and existing shared compute pools.

Current coordination snapshot at source `0143f87e`; the later notes retain
earlier evidence. Root's full incremental run is `run-20260923T221336Z-48f3`
on hbox at `/tank/fn/gates/consumer-topic-bp-20260923`, four shared-pool jobs.
Do not duplicate it; image preparation follows its result.

| Agent | Current substantive result and coordination |
| --- | --- |
| `acceptance_stamp` | Composes the full historical reader relation using certified survivor/pin lemmas from `store_invariants`. |
| `store_invariants` | E2 constructor repair integrated; historical helper packet qualified on E2, final full relation shared with `acceptance_stamp`. |
| `consumer_contract` | Production local commands, peer credentials and bootstrap integrated; implements actual bounded poll/fetch without advancing ack or skipping omitted matches. |
| `crash_differential` | Nonempty physical consumer-reopen teeth integrated; continues K0 actual new-inode known/fenced provenance. |
| `authorship_carrier` | Actual served auth-fold proof ready; ports preservation/restore/clone to current E2/T10 and prepares four-cut image witnesses. |
| `feed_replay` | Actual per-group LISTGROUP bucket packet qualified on lane source; reconciles E2/current owner constructors and historical-reader overlap. |
| `bp_foundation` | Functional kind-18 atomic fragment service/replay qualified; closes actual wrapper guards before combined image. |
| `status_codec` | Held-bundle expiry packet qualified; joins durable deletion/status reporting to foundation's single ordered replay. |
| `fragment_refinement` | Channel admission integrated; fixes live config-check/lock gap and joins shared transit policy to raw-request/projected-Store v3 intent. |
| `stamp_review` | Prepares the root-qualified combined developer/production image and native consumer/BP/topic tests; no duplicate certification. |
| `mini_evidence_bridge` | Exact-carrier inbox shares the real Mini signed transaction; profiles costly native replay and proves optimizations against existing semantics. |
| `topic_metadata` | Topic authorship integrated; Store envelope component qualified; adds explicit durable local administrator binding before actual anchor/admission. |

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
