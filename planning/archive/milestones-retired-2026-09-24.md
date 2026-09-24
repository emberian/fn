# Milestones: retired sections, 2026-09-24

> Archived on 2026-09-24 from [milestones.md](../milestones.md) at dev `46f2660d`, superseded by [now.md](../now.md) and the [wind-down handoff](../handoff-2026-09-24-winddown.md). Text verbatim except relative links, rewritten to resolve from this directory.

## Former status and current-task paragraphs (milestones.md lines 1 to 107)

Current state is the [wind-down handoff](../handoff-2026-09-24-winddown.md), with
qualification tracked in [now.md](../now.md). All current fn packets are on dev;
the exact `863c2141` combined closure and image builds passed, while the final
`8a1b31f9` source still has a known BP guard/build obligation. Neither is a
release declaration. The [two-Store preflight](../evidence/e160-two-store-preflight-gap-2026-09-24.md)
identified missing receiver-side durable native verdicts after peering. Shared
NNTP/BP verified transit is now implemented with scoped proof/component tests;
the new receiver restart and consumer projection fixture awaits its matching
image. Mini's A-side durable reply consumer is committed in its isolated
branch, without a complete two-Store run. The dated evidence below retains the
scope of earlier demonstrated legs.

Previously demonstrated selected-v1 join: native fn poll feeds Mini's signed durable
transaction and immutable Q; after reopen Mini ACKs, and fn returns the durable
position and no repeat article. The [live synthetic evidence](../evidence/native-mini-live-join-2026-09-24.md)
uses the earlier `1d26e01f` image. A separately pinned [B3 reply experiment](../evidence/mini-b3-e160-native-join-2026-09-24.md)
now durably prepares and signs a Mini reply, reuses that signed slot in another
process without the private keys, posts through the qualified `e160442f`
native image, and verifies exact source and both public keys after cold reopen.
These are two demonstrated exchange legs, not the complete two-store crash
trace. Mini replay cost remains material. The maintained event index and its actual
Store/owner poll join are integrated at `8c61c098`; combined certification,
source-matched runtime qualification and the outer correspondence's remaining
premise witnesses are in progress. CNS-001, PRF-064 and SCN-033 track this work;
E2 is not a v0 gate.

Current task (2026-09-23): concurrent v0/v1 development grounded in the actual
Mini/Bread OS interfaces. [Current work](../now.md) names integrated source,
qualified image scope and remaining release obligations; the
[swarm board](../swarm-board.md) names cooperating implementation lanes. Frozen
`329a51a2` passed scoped native migration, storage, peering and process-death
tests; the saved-library relocation defect it exposed is repaired and
`1836ed01` passed protected hbox–persvati exchange. It is not the final v0
release freeze. The live node remains
`da5fd8cb`. Native BP/TCPCL/contact integration, durable author and consumer
bindings, historical live configuration, pinned reader verdicts, served
indexes, byte-level durability and a human client advance concurrently.
The [OS integration study](../dregg-os-integration-2026-09-23.md) proposes the
next real Mini evidence and consumer experiments; P0's native export/verify
and signed public fixture are complete. P1's isolated native durable reply,
stale-submission refusal and reopen fixture passed; its production fn
provenance and E2 cursor/ack join remain open. The conditional K5 prefix
and corrected K8 issued-link crash-scan theorems have landed; K0/K6 and
physical qualification retain their documented open scope. The `295bbe35` native
image passed historical live configuration and T10a author/reopen tests;
the wider `884e4816` image passed indexed-reader, historical HDR, signed
peering/restart, topic inspection, INN interoperability and live configuration.
The P3 codec now has general constructor bounds/inverse and host-called
authored-field binding proofs. Canonical folding and a bounded larger header
envelope accommodate the maximum topic profile in ACL2; the exact maximum
profile passed native inspection on frozen `86323c89`. The historical
candidate selector binds controller and keyset to the exact schema-1 T10
source and enrollment snapshot. The experimental root-only Store projection
now completes administrator installation, root anchors and roster/parent/quota
gated report events and replays them separately on reopen. Its source-level
native owner caller is present; a combined saved-image admission/reopen run
and physical qualification remain open. No succession or fork policy follows.
K6 now carries exact typed Store-event frames
through the modeled surviving-link crash. The ordered whole-list scanner
join now holds under the actual pair-10 byte/kernel relation; general K0 must
establish that relation along every supported served trace. The successful
allocator P-FRONTIER pair-12 root fence and pair-14 callback now reestablish
the full byte/kernel relation from a related ready input with a typed
successor frame and fresh staging name. Its Store-node and shared-owner
callback projections are certified; served call-entry establishment, error
outcomes and physical barrier qualification remain open.
Release gates remain the [trajectory](../plan-2026-09-22-trajectory.md), and
image qualification proceeds alongside implementation under
[how we work](../how-we-work.md).


Earlier current task (2026-09-21): repair and qualify the wider native service batch
under the source-pinned progression in [current work](../now.md), alongside the
durable identity, bounded Store-record, compaction, and authenticated peering
joins. The earlier
frozen `03eb3ba3` certification, default/DTN builds and scoped runtime gate
passed. Native authentication startup, the shared-owner prepare refinement,
shared BP publication and bounded checkpoint namespace are now integrated.
Native control/posting, orderly shutdown and control resource bounds have
also landed, with separate component/runtime evidence. Transaction namespace,
native credential administration and the outbound-feed component are
integrated. The current service-composition source joins connection fault
isolation and public administration, routes accepted IPv4/loopback addresses through
the ACL2 peer/open decision, and activates the existing outbound feed through
the public owner's lifecycle hooks. An older frozen repair has source-matched native two-node exchange evidence;
the wider combined source still awaits its own image and qualification. STARTTLS and public credential/group/capacity/peer administration
are joined in source. The next frozen qualification batch will exercise their
composition. Parallel implementation extends authoritative Store history for
BP obligations and identity/key snapshots, live administration, checkpoint
compaction and physical crash correspondence; the full release scope remains.

The two-peer native release remains unqualified. The packaged Python service
is development infrastructure; component certificates and tests do not complete
v0. See [current work](../now.md), [assignments](swarm-cycles.md), and the
[consolidation audit](../duplication-audit-2026-09-21.md).

The W18 prepare correspondences now cover both the standalone wrapper and the
actual configured owner. Exact equality under the maintained store/owner
relations removes repeated appended-history replay from prepare. Recovery still
replays authoritative history. The [owner evidence](../evidence/native-owner-prepare-correspondence-w18-2026-09-21.md)
records certification and native runtime tests; the earlier [standalone probe](../evidence/store-prepare-correspondence-w18-2026-09-21.md)
does not establish concurrent-service scaling. Complete physical correspondence
and measured shared-owner service cost remain open.

The following dated landing notes preserve their original evidence and gaps;
their phrases “current task” and “nearest gaps” refer to those earlier batches.

## Retired: the six-wave shape and its checklist (2026-09-20 to 2026-09-22)

Retired by decision 3 of 2026-09-22; kept as history; the fiber records under
`planning/evidence/fiber-*` are evidence for the dates they name and define
nothing.

## Earlier landing notes

Current stage: the proof-style realignment and the four server waves have
landed (`0bd0b5c`..`c8886ee`); twenty-one of the fifty requirements are
`implemented` against named keystones certified on the farm gates of `dev`
`7a9e89a` (210 of 213 roots) and `dev` `bdd59d2` (213 of 216). The evidence
record for that batch, with the measured numbers, the gate table, the defects
and the open list, is
[wave-realignment-2026-09-19](../evidence/wave-realignment-2026-09-19.md). No full
implementation/proof milestone is complete.

**`books/owner` certifies** as of 2026-09-20 --- persvati
`run-20260920T224103Z-7c59` (w10/owner-relation) and again in
`run-20260920T234122Z-7687` (w11/snt-guards, 1.77 s), with
`books/owner-invariants`, `books/served`, `books/nntp-auth`,
`books/peer-inbound`, `books/provenance-codec` and `tests/acl2/owner-tests`
(166 of 166 assertions) beside it. What that unblocks has not been re-measured
against the packaged service: the claim that `fn run` cannot start because
ACL2 refuses `(include-book "books/owner")`
([live-52eb0db](../evidence/live-52eb0db-2026-09-20.md)) was true at `52eb0db`
and is no longer the reason, so **the current task is to re-run the live unit
and both gates on current `dev` and say what is actually missing now.**

**`books/owner-config` certifies** as of 2026-09-20 (w11/owner-config,
persvati `run-20260921T001423Z-0f98`, 74 of 74 roots), with its new test root
`tests/acl2/owner-config-tests` beside it, so the owner cluster has no red
root. Its two keystones that were false as stated each gained the hypothesis
`(fn-ocfg-statep oc)`, and the first needed one new conjunct of
`fn-own-relation` --- `fn-own-ids-below-next-p`, already true of every
reachable owner state and merely unstated
([handoff](../lanes/HANDOFF-w11-owner-config.md)). What is still open there is
the WIRE, not the model: no host line calls any `fn-ocfg-` function, so the
served port still answers LIST ACTIVE from the allocation domain and every
PRF-028 owner-side event carries a `pending_subject`.

**AUTHINFO works on a running server** as of 2026-09-21 (w11/auth-live). It
did not, and the model was never the reason: `fn-served-open-peer` pinned the
empty AUTHINFO profile where `fn-served-open` pinned the operator's, and the
owner resolves a connection to a peer by source address alone, so on a box
where a configured peer answers on loopback every client was opened with no
credential --- which is every two-node harness fn has. `AUTHINFO PASS`
answered 481 with the secret the CLI had just written, no AUTHINFO label was
advertised and POST was never gated (v0 matrix `c3b99f8`, eight F-AUTH rows).
The before-and-after measurement is
[auth-live](../evidence/auth-live-2026-09-21.md), PRF-039 carries the
theorems, and the boundary test that would have caught it --- `bin/fn run`
over an `fn.toml`, with a peer record, logging in with a credential written
in the same test --- is `tests/test_auth.py ServedCredentialTests`. `fn init`
gains `--auth-required`, so the policy is reachable from the operator surface
for the first time; `fn principal list` now reads the one registry the server
reads. **Open and on the board**: `[auth] required = true` also gates a
transit peer's `IHAVE`, so a node cannot yet both require a reader login and
take a feed. The v0 matrix at `6fb30ca` records six of the eight F-AUTH
rows moving (F-AUTH 15 accepted / 2 refused / 2 disagreements, from 9 / 8 /
8), and `nntplib 3.12.13` --- not fn's client --- logged in to both nodes.

**The checkpoint validator refused nothing about its prefix.** The one root
of the 2026-09-21 persvati gate of `dev` `e4fb8bc` (272 of 275) that no lane
owned, `tests/acl2/checkpoint-codec-tests`, failed a true assertion:
`fn-cpc-validp` accepted a record prefix whose recorded generation is not its
transaction id, which `fn-checkpoint-capture` refuses as `:history`.
`fn-replay` never compares those two fields, so the replay of the corrupt
prefix is EQUAL to the replay of the sound one and a validator comparing only
replay results could not see it. The recognizer carries the journal-interval
clause now and the refusal is PRF-037, with teeth
([handoff](../lanes/HANDOFF-w11-checkpoint-validator.md),
[evidence](../evidence/checkpoint-validator-2026-09-21.md)). The four roots that
transitively include `books/checkpoint-codec` all certify. The other two
failures of that gate are `books/bp-node` and its test book, owned by
`w11/bp-node`. Still open at that seam: no host line calls `fn-cpc-validp`,
so its keystones carry a `pending_subject` and cover no served path.

**A connection posts repeatedly.** The one-durable-post-per-connection defect
was fixed by `w5/clock-seam` (merge `7d8eff8`, the per-submission injection
clock) and the board line was never closed; measured live on persvati at
`dev` `5ae226f`, `tests.test_post.StorePostTests.test_a_reader_pinned_before_a_post_keeps_its_view`
and `tests.test_owner.OwnerTests.test_clock_and_group_facts_go_through_the_owner`
both pass. What remained at that seam, and is closed by
[D10-a](../decisions.md)/PRF-033 (w11/clock-seam), is that a REFUSED clock
observation froze the owner's clock and the resulting duplicate identity
reached the poster as `441 posting failed; the article was refused` -- an
article verdict for a clock fault.

The nearest known gaps behind the live re-run are, in order: the owner's three
one-line `host/owner-host.lisp` edits from w5-config-groups;
the `NNT-001` capability/dispatch mismatch;
and `books/stx-verify` at one printability lemma. See
[the board](../deputies/BOARD.md) for each item's exact form, and the [v0
checklist](#v0-checklist-every-item-its-status-its-evidence) below for where
each sits.

The [three-cycle work plan](swarm-cycles.md) maps 34 planned packets to
dependencies, owners, stable IDs and finite exits. [Current work](../now.md)
retains the completed baseline; the [decision workbook](../decisions.md) records
the remaining product choices.

### Release shape: v0 and v1

D07 clarification (2026-09-21): all six v0 waves must run through the native Lisp
node and operator CLI without Python runtime dependencies. Native component tests
or a Python service with a native subprocess do not close this gate. See the
[runtime contract](../../specs/host.md#selected-production-runtime) and SCN-015.
The existing Python matrix remains useful development evidence; its node launch
and dependency checks must adopt the native deployment before establishing v0.

Agreed 2026-09-20. **v0 is every feature usable between two peered fn nodes.**
Not every feature designed, and not a mission profile: the test of v0 is that
two fn nodes, peered, can do everything fn claims to do, with the assurance
rules of [`AGENTS.md`](../../AGENTS.md) holding for each claim. Six waves, in
dependency order, each ending with an evidence record:

| Wave | Content | Gate |
| --- | --- | --- |
| v0.1 server | The owner certifies and runs; POST is durable end to end; capabilities match dispatch; concurrent sessions | A deploy gate with owner-served evidence and a second reader live across another connection's POST |
| v0.2 peering | K1 to K7 of [the peering design](../lanes/DESIGN-peering-summary.md): transit refines acceptance, loop freedom, merge convergence, duplicate suppression, exactly-once feed | Two fn nodes exchanging articles both ways and converging |
| v0.3 DTN | The BP path from queued work to receipt across a real contact outage, with the receiver evolving-Store seam closed | An interrupted relay and contact-plan run with expiry and staging exhaustion |
| v0.4 substrate transport | TCPCLv4 C1 to C4 certified and hosted; the LTP question decided on the feasibility study | A two-node transfer over fn's own convergence layer |
| v0.5 reconfiguration and storage | Live reconfiguration as an owner event; the byte-level crash model ([K1 to K11](../lanes/DESIGN-crash-model-v2-summary.md)); persisted checkpoints; index adoption | Every crash point in the cut table is a transition the model expresses |
| v0.6 convergence and release | Identity and authority (D01, OBJ-003, OBJ-007), the include-hygiene backlog, one gate over every root on one machine | Every requirement either `implemented`/`validated` with keystones, or `deferred` with a reason |

**The gate over all six waves is one executable matrix.** `tools/v0_matrix.py`
stands up two peered fn nodes on a farm box, drives every feature between them,
and writes a separate matrix and report under `planning/evidence/v0-runs/`
for each run. Root uses `--publish-current` to select a non-overlaid,
non-simulated measurement of the checkout's HEAD as
[`planning/v0-matrix.json`](../v0-matrix.json). An older run cannot replace a newer
selected run. Publication records an observation; it does not declare a pass.
The matrix carries one row per feature observation with five
verdicts that are never collapsed into pass/fail: `accepted`, `refused` and
`uncertain` are D13's three outcomes and each is a real observation, so a
refusal row that draws its refusal is the feature working; `not-exercised` names
what blocked the row, and `not-built` names the lane that owns the missing
feature. Whether a row did what it was designed to do is the separate `agrees`
bit. Every row names its exact invocation, the revision, its log and what it
does not show, and the counts come from the tool, never from typing:
`make check` recomputes the rows' digest and refuses a hand-edited verdict.
`python3 tools/v0_matrix.py --list` prints the inventory and runs nothing. v0 is
reached when every row reads one of the three outcomes and agrees with its
expectation; the wave gates below say what each wave contributes to that.

The v0.4 wave has two halves that share a name. The convergence layer is
TCPCLv4 (C1 to C4). The statement layer is
[substrate transport](../../specs/substrate-transport.md), whose packets run in
dependency order: **S0** prefixes and registry (the `fn-stx-` tag, SUB-001 to
SUB-006, PRF-019 to PRF-026, SCN-019, the `FN-Statement` reservation); **S1**
the field codec; **S2** the verdict and its evidence values; **S3** the lace
projection, the bridge lemma and the carried index; **S4** policy on inbound
transit; **S5** membership epochs across a partition; **S6** the reader's
`:fn-verified` exposure. S1 and S2 can start now; S3 needs the peering transit
path, S4 and S5 need S3, S6 needs S2 and the reader profile. Owners,
deliverables and acceptance are
[the design's packet table](../../specs/substrate-transport.md#8-packets); no
theorem in §6 of that design exists yet.

### v0 checklist: every item, its status, its evidence

**Historical snapshot:** this checklist records the cited `52eb0db` gate and
its dated followups. It is not a current-main status table. In particular, the
old owner-certification/startup blockers are superseded by the native integrated
gate linked in the [recovery matrix](recovery-2026-09-21.md). Preserve its negative
evidence; use the recovery matrix for present integration priorities.

Generated-from-evidence, not from intent. A row is `done` only where a named
keystone certified in a farm gate this table cites, or a harness run in the
cited evidence file exercised it. `open` and `blocked` rows name what stops
them. The per-wave record is `planning/evidence/fiber-<wave>-2026-09-20.md`;
the whole-tree run behind these statuses is
[verdict-52eb0db](../evidence/verdict-52eb0db-2026-09-20.md).

### v0.1 server -- fiber record: [fiber-server](../evidence/fiber-server-2026-09-20.md)

| Item | Status | Evidence |
| --- | --- | --- |
| The owner certifies | **blocked** | `books/owner` has no certificate; ACL2 refuses `(include-book "books/owner")`, which is why `fn run` cannot start at all ([live-52eb0db](../evidence/live-52eb0db-2026-09-20.md)) |
| The owner runs as a service | **blocked** | the installed unit falls back to `tools/run_reader.py`, the same second choice `tools/deploy_gate.py` makes ([live-52eb0db](../evidence/live-52eb0db-2026-09-20.md)) |
| POST is durable end to end | **partial** | a post is durable and rereads byte-for-byte after a kill ([deploy-cce4b11](../evidence/deploy-cce4b11-2026-09-20.md) rows 23 to 28), and a connection now posts REPEATEDLY: `test_a_reader_pinned_before_a_post_keeps_its_view` passes live on persvati at `dev` `5ae226f` (w5/clock-seam's per-submission injection clock, merge `7d8eff8`). Open: two submissions inside one millisecond still share a generated Message-ID ([D10-a](../decisions.md), PRF-033) |
| Capabilities match dispatch | **open** | refuted by counterexample: POST answers 340 while CAPABILITIES omits POST, against RFC 3977 5.2.2 (NNT-001 note, `planning/requirements.json`) |
| Concurrent sessions | **open** | `tools/run_reader.py` is `listen(1)` and serves one connection to completion; the owner is the only concurrent server ([BOARD](../deputies/BOARD.md), w5-deploy-gate) |
| Three outcomes distinct at the CLI | **done** | accepted 0, refused 1, uncertain 3 ([deploy-cce4b11](../evidence/deploy-cce4b11-2026-09-20.md) rows 11 to 13) |

### v0.2 peering -- fiber record: [fiber-peering](../evidence/fiber-peering-2026-09-20.md)

| Item | Status | Evidence |
| --- | --- | --- |
| K1 transit refines acceptance | **done** | `fn-peer-transfer-is-the-post-path`, `fn-peer-transfer-stages-only-scope-groups` ([BOARD](../deputies/BOARD.md), w6/peering-inbound) |
| K2 loop freedom | **partial, and inert in any deployment until now** | `fn-peer-loop-is-refused` (inbound) reads `fn-peer-local-identity`, the `path-identity` policy slot, and NOTHING on this tree could write that slot, so it read the empty string and the check could never fire: both nodes in gate `bbd1f47` accepted an article whose Path named them. `fn policy set path-identity` writes it now. Outbound and RFC 5537 3.6 step 2 remain open. |
| K3 duplicate suppression | **done** | `fn-peer-history-is-refused-at-offer`/`-at-transfer`, `fn-peer-history-grows-under-transfer` |
| K4 restart | **the lost-reply half is witnessed live; the kill half is blocked on a named defect** | The tap cut a transfer after the article block and before the status line: node B served the article afterwards and node A observed ZERO accepted transfers ([twonode-a5c6792](../evidence/twonode-a5c6792-2026-09-21.md), `owner feed cut | CUT-TAKEN`). Two qualifications the corrected gate adds at `f49a844` ([twonode-f49a844](../evidence/twonode-f49a844-2026-09-21.md), w11/gate-verdicts): the octets node B serves are NOT byte-identical to node A's, and *exactly one copy* is **inconclusive** there rather than shown, because node B's GROUP line carried no count before the cut, so the claim rests on the reread alone. The `kill -9` half does not deliver because a lost connection never requeues the in-flight entry: `feed_drop` tells ACL2 only that the connection is gone and nothing applies `fn-feed-lost`, so the entry waits for the next `fn-own-reopen`, and separately node B answers every connection with an immediate close for the 90 s after that restart with no fault in its log -- **not exercised, both blockers named in the evidence**. The packet is in [HANDOFF-w11-twonode-feed](../lanes/HANDOFF-w11-twonode-feed.md). The general statement is recorded open in `specs/peering.md` status. |
| Peer records are configuration | **done** | `:set-peer` (9) and `:remove-peer` (10) in `books/config.lisp`; `books/peer-config.lisp` |
| Two nodes exchange both ways | **done (one host), by each node's own feed; the byte-identity half is WALKED BACK** | Both directions by the feed of `books/owner-feed.lisp`, by IHAVE and by RFC 4644 CHECK/TAKETHIS, with the offer commands on a wire tap; the second offer draws 435/438/439 each way ([twonode-feed-w11](../evidence/twonode-feed-w11-2026-09-20.md), run 5 = [twonode-a5c6792](../evidence/twonode-a5c6792-2026-09-21.md)). The row this replaces cited a 63-step green in which the feed steps were NOT EXERCISED and every transit offer drew `502`. **The receiver's octets are not the sender's**: the corrected gate measures `identical=False` for `<fed-ab@>`, `<fed-ba@>` and the streamed article at `f49a844` ([twonode-f49a844](../evidence/twonode-f49a844-2026-09-21.md), `feed-identical[ab]`, `[ba]`, `[stream-ab]` violated), where `a5c6792` measured `True` for all three. RFC 5537 3.6 permits a relaying agent to alter Path and Xref and nothing else, and no row here says which octets differ. |
| Two nodes exchange across boxes | **blocked** | `fn run` refuses a non-loopback listener, so the live peer records name addresses neither node can reach ([live-52eb0db](../evidence/live-52eb0db-2026-09-20.md)) |
| Real INN on the other end | **INN's side holds; the fn side of that run was the reader, not the owner** | INN 2.7.4, [inn-lab-f4e8272](../evidence/inn-lab-f4e8272-2026-09-20.md). The "75 steps, 0 failed" this row carried is what the gate family's missing verdict cost (w11/gate-verdicts): that run's own record says the owner entry point did not reach LISTENING and the lab fell back to `tools/run_reader.py --post`, and that 97 of 160 book pairs did not hash to the revision. Under the corrected lab it is `entry-point-listening` **violated** (exit 1) and `certificates-match` **inconclusive**. INN's own rows -- 435 on the duplicate, 437 on the Path loop, history surviving a SIGKILL -- all hold, and no fn transit surface was reached. |
| The owner carries the transit port | **done** | `tools/run_owner.py` resolves the source address through `fn-owner-peer-for-address` and opens with `fn-own-open-peer`; a configured peer draws `335` from `IHAVE` where a reader draws `502`. Unit evidence: `tests/test_owner.py::TransitPortTests`. `CAPABILITIES` still renders the reader block on a transit connection, which is open. |

### v0.3 DTN -- fiber record: [fiber-dtn](../evidence/fiber-dtn-2026-09-20.md)

| Item | Status | Evidence |
| --- | --- | --- |
| BP step and trace preserve the node | **done** | `fn-bp-step-preserves-node`, `fn-bp-trace-preserves-node` (REP-006 note) |
| Receipts distinguish the three kinds | **done** | RET-003 `implemented` |
| Durable scheduling with fairness | **done, with a caution** | REP-005 `implemented`; `fn-sched-conditional-progress-under-a-fairness` is conditional on a constrained assumption |
| The scheduler host writes valid records | **open** | `fn-sched-host-decision-octets` builds a `:bad` record ([BOARD](../deputies/BOARD.md), w3-scheduler) |
| Interrupted contact-plan run | **open** | no evidence file exists; the w9/dtn-e2e lane owns it |
| fn authors a BPv7 bundle another implementation accepts | **done** | `books/bp-node` certifies; dtn7-rs 0.21.0 decoded and delivered fn's 138-octet bundle, and fn decoded and re-encoded dtn7-rs's 132-octet one byte for byte ([bp-dtn7-w11](../evidence/bp-dtn7-w11-2026-09-21.md)) |
| The node's processing machine (`fn-bpn-step`, T1 to T6) | **open** | `books/bp-node` is the two ends of `specs/bp-design.md` §1.5, not the machine; §1.5.1 lists what is absent and nothing claims T1 to T6 |
| Received-held route-wait progress slice | **source and selected proof, native pending** | The actual BP service now calls `fn-bpnp-step` for `:progress`; a route-less older transit carrier records a volatile per-key wait and leaves a younger live local request selectable. [Scoped proof evidence](../evidence/bp-progress-route-wait-2026-09-24.md). Full N03 class fairness, N04 forwarding/MRU, N05 journal debt, and a source-matched native image remain open. |
| LTP | **open** | `planning/ltp-feasibility.md` is a study; REP-006 stays `specified` for that half |

### v0.4 substrate transport -- fiber record: [fiber-substrate-transport](../evidence/fiber-substrate-transport-2026-09-20.md)

| Item | Status | Evidence |
| --- | --- | --- |
| TCPCLv4 C1 to C4 certified | **done** | `books/tcpcl-octets`, `books/tcpcl-session`, `books/tcpcl-invariants` and `tests/acl2/tcpcl-tests` certified together on hbox with the served-path guard O(1) per chunk in BOTH directions, no prover step limit: 108.6 s, 64.6 s, 7.3 s, 0.3 s, `certify-20260921T005957Z-1365818` ([handoff](../lanes/HANDOFF-w11-tcpcl-outbound.md), w11/tcpcl-outbound, D20; the receive half is w11/tcpcl-theory's, which took the invariants book from 609.69 s to 7.25 s). Measured directly, the guard is 0.75 µs per call at 1 and at 20,000 unsent octets where it was 62.85 µs at 20,000 the day before |
| TCPCLv4 hosted, no Lisp-computed protocol value | **done in code, untested** | `host/tcpcl-host.lisp`, `host/native/tcpcl.lisp`; the image did not build and none of the five scenarios ran ([tcpcl-9cbf301](../evidence/tcpcl-9cbf301-2026-09-20.md)) |
| A two-node transfer over fn's own CL | **open** | the v0.4 gate condition; no run |
| S1 statement field codec | **partial** | `books/stx-carrier` certified; `books/stx-verify` open at `fn-stx-decimal-octets-are-printable` |
| S2 verdict | **open** | cascades off `stx-verify`; PRF-020's subject rule needs K1's transit path |
| S3 laces, index and equivocation | **partial** | `books/stx-lace`, `books/stx-index`, `books/stx-policy`, `books/stx-authority` and `books/stx-epochs` certify (w10/substrate-2). The index has a CARRIER and a HOST LINE since w11/sn-index (D21): `fn-sn-state` carries it and the keyring beside the node, `fn-sn-finish` grows it by one cons, `host/store-node-host.lisp` `fn-store-sn-statement` reads it, and `fn-sn-statement-lookup-is-the-lace-lookup` equates the called function to the projection. The identity lane now certifies bounded fn-e kind-2 verdict and kind-3 opaque keyring-snapshot definitions, a monotone-current-generation theorem for the ordered identity context, and kind-4 atomic article/verdict definitions with evaluated substitution witnesses. PRF-023 stays `in-progress`: the shared Store dispatcher/file recovery and native writer do not yet call those definitions, no acceptance/crash refinement theorem connects kind 4 to the physical commit, D09 provides no supported profile/current authority, `fn-stx-index-slots-agree` has no caller, and `fn-stx-transit-authority-ok` still walks the whole lace per article on the ADMISSION path with no caller |
| S4 to S6 | **open** | SUB-004 to SUB-006 `specified`; S6's reader verdict has no slot to read (see the design's section 10) |
| The LTP question decided | **open** | no decision recorded |

### v0.5 reconfiguration and storage -- fiber record: [fiber-reconfiguration-storage](../evidence/fiber-reconfiguration-storage-2026-09-20.md)

| Item | Status | Evidence |
| --- | --- | --- |
| Configuration is a replayed durable record | **done** | `books/config.lisp` ten delta kinds, `books/config-records.lisp`, `books/node-config.lisp` |
| Live reconfiguration as an owner event | **open** | `fn group create|retire` refuses while a service is live ([BOARD](../deputies/BOARD.md), w5-fn-cli) |
| Crash model K1 to K11 | **partial** | STO-004, STO-005, FLR-001, FLR-002 `implemented`. **K1 to K3 are proved and K4 is conditional** (PRF-041, `books/byte-store-scan.lisp` and `books/byte-store-keystones.lisp`): the scan of every byte-level crash image of a related store succeeds and is an image the file kernel admits, and the constructor reproduces it. The host reopen succeeds when the exact scanned identity and topic histories replay; consumer replay follows from the maintained E2 relation. A valid physical FNST topic-anchor image satisfies the earlier byte/consumer/identity conditions yet fails topic replay and actual reopen. A maintained actual Store topic/crash bridge is still open. K5's scan formula retains the durable decoded prefix and bounds any extension to one record (`books/byte-store-stable-prefix.lisp`). The corrected K8 theorem proves that every model crash image after a transaction-directory fence scans the exact old records plus the candidate when a related `:record-attempted` state has an issued pending link (`books/byte-store-record-fence.lisp`); a counterexample shows that phase and relation alone do not force that link. K6 now proves raw-frame equality at the actual P-RECORD file-fence and immutable-link cuts (`books/byte-store-record-provenance.lisp`); a surviving final name now reads the exact frame through every modeled crash image, while the actual `record-attempted` cut has the same byte state as the linked cut, while a related-input K0 slice derives both no-prior-operation and final-name absence through the actual file-cut prefix, including typed non-article Store events; a conditional actual pair-10 whole-list scanner bridge is proved when its byte/kernel relation holds, while a certified actual-trace K0 slice now derives the pair-10 logical file/link callback state from a related typed input with fresh staging; the actual pair-10 issued link, pending shape, and candidate decoding are derived, while actual pair-10 old durable-prefix preservation is now proved and full byte/kernel relation composition remains K0. General K0 and physical barrier qualification remain open; K0 must establish the issued-link/phase correspondence along the host program. K11 (truncation and resize never validate) is still a design |
| Every cut-table crash point is a transition | **open** | the deploy gate exercises one kill point and says so; `tests/campaign/cuts.py` is the table |
| Persisted checkpoints | **done** | STO-006 `implemented`, `books/checkpoint.lisp` |
| Index adoption | **partial** | STO-001 `implemented`; `books/index` certifies |
| The staging orphan has an owner | **open** | `recover` reports and leaves `staging-orphans=1` across two recoveries and a kill; no registry row ([deploy-cce4b11](../evidence/deploy-cce4b11-2026-09-20.md)) |
| Compaction and reclamation | **open** | STO-007, RET-005, RET-006; PRF-009 planned, no events |

### v0.6 convergence and release -- fiber record: [fiber-convergence-release](../evidence/fiber-convergence-release-2026-09-20.md)

| Item | Status | Evidence |
| --- | --- | --- |
| One gate over every root on one machine | **done** | `tools/verdict.py <commit> --host persvati`, one command, host-locked; [verdict-52eb0db](../evidence/verdict-52eb0db-2026-09-20.md) |
| One evidence record per fiber | **done** | the six `planning/evidence/fiber-*-2026-09-20.md` |
| fn runs as a service on two boxes | **partial** | installed, enabled and serving on both; the server is the reader, not the owner ([live-52eb0db](../evidence/live-52eb0db-2026-09-20.md)) |
| Identity and authority (D01, OBJ-003, OBJ-007) | **open** | `books/crypto-seam` and `books/statement` certify but are an abstract seam |
| The include-hygiene backlog | **open** | 47 names across eight host files resolve only by bridge load order ([BOARD](../deputies/BOARD.md), w5/host-lint) |
| Every requirement `implemented`/`validated` or `deferred` | **open** | 35 of 56 are still `specified`; no proof target is `certified` |

**v1 is M6 and beyond**: additional convergence-layer and deployment profiles,
long and asymmetric contacts, the human web interface, 9p projections, and the
mission-profile work that needs its own hardware, security and reliability
evidence. Nothing in v0 is a flight-readiness claim.
