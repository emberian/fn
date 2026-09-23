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

| Agent | Current substantive result and coordination |
| --- | --- |
| `acceptance_stamp` | Historical configuration replay, phase-aware Store/owner relation and actual live adoption; coordinate Store shape with consumer and authored records, reader pins with reader lanes. |
| `authorship_carrier` | T10a and native295 qualification landed; now preservation/restore, selected-pack and consumer incarnation contracts with consumer/reader lanes. |
| `stamp_review` | Historical recorded-verdict pin threaded through served NNTP and HDR; coordinate carried reader shape with index lane. |
| `store_invariants` | Actual served Message-ID index and maintained correspondence; share reader view shape with verdict lane rather than waiting for all reader work. |
| `consumer_contract` | Durable consumer bootstrap/events/Store projection, registration/ack/recovery and restore fencing; coordinate shared Store constructors with historical config and authored records. |
| `bp_foundation` | One native FNBS service authority, typed receive/publish/recovery and actual caller switch; native A2/contact/TCPCL packet integrated at `66bf9e55`; qualify one coherent saved image. |
| `feed_replay` | TCPCL drive and clock-domain codec/gate certified; foundation qualifies native clock join. Now repairs missing authored NNTP injection projection found by actual carrier peering. |
| `status_codec` | Native contact planning, interruption/expiry/backpressure and receipt progression through that same service; do not import the old scheduler's assumed durable completion. |
| `crash_differential` | Corrected K8 model crash-scan theorem landed; K6 actual framed-write trace provenance and K0 establishment next. |
| `fragment_refinement` | Device-EIO campaign landed. Now fixes cache composition using actual ACL2 certificate hash compatibility: same source/toolchain can carry different portcullis/expansion hashes. |
| `store_semantics` | Reader/composer and exact retry handling integrated; browser and native POST/readback passed; bounded in-memory submission registry, no durable client spool. |
| `mini_evidence_bridge` | P0 native export/verify and signed fixture complete; P1 durable operation binding, provenance/conflict evidence and immutable reply transaction in Mini. |
| `topic_metadata` | P3 bounded canonical metadata codec, exact-authored-source field projection and native inspection; coordinate T10 binding without claiming topic admission or Mini action authority. |

Root integrates finite source commits, regenerates ledgers, checks concrete
proof/runtime regressions and maintains evidence. No lane is a permanent file
owner. Announce interface changes and coordinate combined patches directly.
The specialized Astra OS study is complete in
[dregg-os-integration-2026-09-23.md](dregg-os-integration-2026-09-23.md).
It grounds P0/P1/P2 in Mini's real resource receiver and distinguishes Bread's destructive mailbox and ambient owner authority from the selected E2 contract.
The P0 implementation now occupies that free parallel slot.

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

Ready next convergence packets (not yet integrated into root):

- K6 `d2a66dce` through `14d08cdb` and earlier link/crash refinements;
  includes typed Store-event sequence fix. Original manifests are in lane.
- Topic proof packet `9ff82359`; native fixture `1da3801f` already landed.
  Topic lane continues coherent folded signed-envelope work.
- Auth handled-command correspondence `cdedd176`; arbitrary index/verdicts,
  no index hypothesis, excludes delegated reader commands by explicit scope.
- Historical T8/T17 open/read relation union is still being composed with
  pin cleanup; do not claim full read preservation from its conditional pieces.
- A3 combined source `7ad230b5` passed the two-carrier request/receipt/pin-release
  happy path. Five fault cases passed preceding `4e7dd362`; preserve separate
  image attribution. Effective handoff-state projection is still being built.
- Mini P2 evidence `cc84eb67` landed `f3b22b8c`; Mini now repairs the subprocess
  stdout allocation bound (cap before accumulating) and reruns the matrix.
- E2 completed-prefix/crash relation remains in progress; resolution theory
  explosion was repaired from a 5210-way split to a 3.16-second certificate.
