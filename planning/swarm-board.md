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
| `feed_replay` | TCPCL drive correspondence landed; now durable clock-domain compatibility/codec/migration, coordinating native clock observations with foundation. |
| `status_codec` | Native contact planning, interruption/expiry/backpressure and receipt progression through that same service; do not import the old scheduler's assumed durable completion. |
| `crash_differential` | Corrected K8 model crash-scan theorem landed; K6 actual framed-write trace provenance and K0 establishment next. |
| `fragment_refinement` | Isolated device-EIO campaign and strict process/device ownership checks landed; ext4-only scope, no power-loss/ZFS claim. |
| `store_semantics` | Reader/composer and exact retry handling integrated; browser and native POST/readback passed; bounded in-memory submission registry, no durable client spool. |
| `mini_evidence_bridge` | P0 native export/verify and signed fixture complete; P1 durable operation binding, provenance/conflict evidence and immutable reply transaction in Mini. |

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
