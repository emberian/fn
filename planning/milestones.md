Current task (2026-09-24, 13:35 EDT): the hbox node runs `47bdb9a4`
([record](evidence/node-hbox-47bdb9a4-2026-09-24.md)), the plan's T0 for the
v0 push; the scoreboard says which of P1 to P11 hold on it. Earlier: the night's four judged items hold; the
[restart record](handoff-2026-09-24-night.md) has the numbers. Image
[`1a9dd747`](evidence/native-cut-1a9dd747-2026-09-24.md) is the last completed
shared image pair (BP N03 and interrupted-fragment cases pass); the
[two-Store join](evidence/two-store-join-1a9dd747-2026-09-24.md) completed
under four cut families; the ten-second baseline is at 19 books. Next: the
remaining cost books, the other native subsets on `1a9dd747`, and whether to
deploy it (a separate decision). [Now](now.md) names dev, the images and the
lanes. No v0/v1 release is declared. The earlier status and current-task
paragraphs, the retired six-wave checklist and the fiber records are in
[archive/milestones-retired-2026-09-24.md](archive/milestones-retired-2026-09-24.md).

## Earlier milestones

The release shape, v0 and v1, is the plan's §2.2; the steps are its §3.

## M0: design scaffold

- [x] Capture architecture, terminology, contracts, trust boundary, and sources.
- [x] Register requirements, proof targets, and scenario specifications.
- [x] Expose unresolved decisions with recommendations and consequences.
- [x] Record the user-facing choices needed by the first bounded M1 cycle.
- [x] Run structural checks and review for contradictions before handoff.

Scaffold validation on 2026-09-18: `make check` passed (see planning/ledger.md
for current document/requirement/proof-target/scenario counts, which have grown
since this milestone closed). Temporary-copy negative checks rejected a broken
document link, an unknown proof reference, and a certified status without
evidence. These are tooling checks only.

Exit: navigable scaffold and an accurate next-task list. M0 does not freeze all
later binary layouts. Decisions needing model/measurement evidence remain open
with named dependent milestones.

## M1: executable model

Before completing all of M1, finish the native-profile/D05 semantic details
(D01's source boundary and D02/D03/D04/D17 directions are selected),
D07, local D10/D11, D12's first handoff
terms, D13's initial history rule, resource bounds in D16, and proof scope D18.

- [x] Pin ACL2 and host Lisp versions, installation method, book dependencies, and
  clean certification invocation. Keep the initial book dependency set small.
- [x] Define octets/IDs, records, invariants, events/effects, one-transaction ownership,
  local acceptance, two-group allocation, duplicate suppression, and obligations.
- [x] Execute the logical portion of the letter lifecycle with lost replies and an
  explicit crash/commit-result abstraction.
- [x] Prove initial invariants, allocation/identity preservation, idempotent effects,
  and the first guard/correspondence obligations. Record actual theorem names.
- [x] Supply a deterministic simulator host; no network deployment is needed.

Evidence for the five above, 2026-09-20: ACL2 8.7 and SBCL 2.6.8 are pinned by
digest in every gate manifest, and `tools/certs.py` will not cache a
certificate pair except against a passed manifest, keyed on the book's whole
include closure. `OBJ-002`, `OBJ-005`, `STO-002`, `RET-001` and `FLR-002` in
[the requirement registry](requirements.json) carry the theorem names for
identity, allocation, one-transaction ownership, obligations and the three
outcomes; each is certified on the farm gate of `dev` `7a9e89a`
([the wave record](evidence/wave-realignment-2026-09-19.md)). M1's own exit
clause is **not** met: the boundary between proved logic and assumed commit
events is written, but provenance and signature modelling (`OBJ-003`,
`OBJ-007`, `PRF-013`, which has no events) is not, and `PRF-013` is what M3
and v0.6 close.

Incremental evidence: the acceptance and node components now have executable
traces and preservation work, and the deterministic simulator runs in ACL2.
Byte primitives, crash experiments, exchange, and a loopback reader are being
integrated in parallel. Guard verification, provenance/signature modeling,
system integration, and the remaining M1 contracts keep this milestone open.

The [article batch](../tests/evidence/2026-09-18-articles.md) also certifies
successful-parse exact source preservation and general retention-release
preservation. These are component theorems, not completion of M1's remaining
authorization, trace, or guard obligations.

Exit: admitted executable definitions, certified initial theorems, meaningful
scenario checks, and a written boundary between proved logic and assumed commit
events. An abstract commit event is not yet a disk recovery proof.

## M2: bytes and durable storage

Resolve D06, D08, D09's required byte profiles, D14, and measured layout choices.

- Freeze a versioned initial object/frame/checkpoint grammar with golden vectors.
  (Object and frame are frozen with vectors; no checkpoint codec exists.)
- [x] Implement bounded codecs and their round-trip/canonicality properties.
- Model torn/reordered writes, barriers, isolation, and uncertain failures.
  (Barriers, isolation and uncertainty are modelled and certified — `STO-004`,
  `FLR-001`, `FLR-002`. Crash images are record-granular; byte-level torn
  writes are [the v2 crash design](lanes/DESIGN-crash-model-v2-summary.md),
  which is review finding D4 and wave v0.5.)
- Implement segments, journal, recovery, and checkpoints against that model.
- Prove conditional recovery and checkpoint equivalence; implement a real adapter
  with explicit platform assumptions and fault-injection evidence.
  (Both proof halves are done — `STO-005` and `STO-006` — and the adapter runs
  on a farm box through [the deploy gate](evidence/deploy-cce4b11-2026-09-20.md)
  with one real kill cut. The platform assumptions are stated, not qualified.)
- Account for metadata and recovery/compaction headroom under no-space failures.

Codec evidence: `ENC-001` and `ENC-002` in [the requirement registry](requirements.json)
name the round-trip, canonicality and input-bound keystones for the CBOR
primitives, the schema-0 record and the BP ADU. The work ceiling they cite is
pessimistic by roughly 16,000x against the measured traversal cost of the same
parser on the same inputs, and it is an instrumented shadow, not a host
measurement.

Exit: acceptance survives the specified crash matrix; uncertain results force
recovery; no partial cross-post is published. Publish the exact supported fault
and platform profile. Compaction/expiry can remain disabled with bounded admission.

Incremental evidence: the [storage experiment](../specs/store-experiment.md) now
has complete record round-trip and typed replay proofs, real file/barrier/lock
operations, persistent allocation across abort/reopen, and failure-injection
tests. The [integrated record](../tests/evidence/2026-09-18-storage.md) includes a
maximum-profile reopen test. Actual immutable-file frame/byte and host refinement,
checkpoint publication/recovery, physical accounting, and platform qualification
keep M2 open; the isolated-slot journal is not the selected adapter model.

The [reader/storage batch](../tests/evidence/2026-09-18-wildmat-storage.md) adds a
dedicated immutable-file publication kernel with one-use allocator reservations,
crash choices, actual replay, and initial fence/gate proofs. The subsequent
[invariant book](../books/store-files-invariants.lisp) proves step/crash
preservation, stable-prefix retention, and one-crash success retention. The [assurance checkpoint](../tests/evidence/2026-09-18-assurance.md) extends
this to arbitrary finite file traces and actual live completion/replay
correspondence, with systematic fault/process testing. The subsequent [composed-store checkpoint](../tests/evidence/2026-09-18-composed-store.md)
passed mixed live/refusal/recovery traces and actual host adoption with a full
base-book guard batch (planning/ledger.md has current counts). Physical
refinement and platform qualification remain work.

## M3: first usable local news service

- Implement the complete selected NNTP profile, including article injection,
  range/wildmat/date semantics, overview, errors, and capability truthfulness.
- Integrate the same core definitions with the Common Lisp I/O adapter.
- Provide chosen provenance/signature and privacy features; the selected scope
  determines what may be called the first usable release.
- Specify local configuration, principal/authentication mapping, resource limits,
  startup, recovery, shutdown, and operator fault reporting.
- Run an independent newsreader, transcript corpus, concurrent-session cases,
  socket fragmentation, oversized input, crash/restart, and lost-response retries.

Exit: humans and agents can post/read through an actual client with documented
storage guarantees. Audit each advertised capability against RFC clauses. This
local-service milestone alone does not establish disconnected peering or remote
delivery; the active M4 path supplies its own concurrent evidence.

Incremental evidence: CLI-persisted articles can be reopened and served over
loopback NNTP. LISTGROUP ranges/cursors now have logical, socket, and independent
client checks; bounded UTF-8 wildmat and filtered listings are also integrated.
The [semantic field layer](../specs/article-fields.md) now adds bounded exact
Message-ID and Newsgroups checks over preserved article views. It remains a
narrow proto-article subset, separate from complete injection; live POST,
complete READER, overview, provenance, and signatures remain open.

Current M3 author-key task (2026-09-24): the selected both-required hybrid
signature path and historical kind-4 verdict binding have advanced beyond the
older checkpoint above. Operator-local per-principal rotation and revocation
now have ACL2 source and control/CLI fixtures. The completed kind-3 Store-node
path has a selector/replay projection theorem and a historical-verdict
preservation theorem. Successful recovery reconstructs both from durable
records; reachable A/B rotation/revocation/reopen and before/after-publication
crash traces exercise the path.
The frozen `863c2141` image passed the targeted author lifecycle native
subset on scratch Stores, including A/B-local authority, rotation,
revocation, restart inspection and exact carrier verification. A portable
succession/recovery policy, incoming signed-carrier admission and a full
crash-phase lifecycle relation remain open. See the
[author-key evidence](evidence/author-key-lifecycle-2026-09-24.md),
[identity](../specs/identity.md) and `PRF-069`.

The server waves (2026-09-20) move three of M3's five bullets without closing
any. `books/served` takes the framing and reply projection out of `:program`-mode
host Lisp, so the function the host calls per socket read is the one the
chunk-independence keystones are about (`NNT-003`). The session keystones
(`NNT-002`) carry every dispatched command unchanged; the legacy reader
commands (XOVER, HDR/XHDR, LIST HEADERS/ACTIVE.TIMES) have a board entry but
are **not** on `dev` — `books/nntp-legacy.lisp` does not exist here. Configuration, startup, recovery, shutdown and operator
fault reporting are specified and running: `bin/fn`, `docs/operator.md`,
`packaging/`. What is not moved: **the owner does not certify**, so there is no
concurrent server and no live POST read-back; the advertised capability bundle
does not match the dispatched one (`NNT-001`, an RFC 3977 §5.2.2 defect the
deploy gate found); principal and authentication mapping is unwritten; and no
newsreader has ever been run against fn. See
[the wave record](evidence/wave-realignment-2026-09-19.md).

## M4: disconnected exchange

- BPv7 is an active architectural path, developed alongside M3; it does not
  depend on completing M5 or M6. Use an existing pinned BPA for actual two-node
  queued delivery, restart, inbound staging and application receipt tests.
- Resolve portable D10/D11, D12 receipt details, and D15 batch behavior.
- Implement batches, bounded resumable ingestion, inventories, authorization,
  receipt regeneration, persistent transfer work, and restore/incarnation handling.
- Exercise duplicate, reordered, delayed, and carried-media exchanges among four
  simulated/real local nodes. Execute the multi-relay lifecycle.
- Prove fact-set merge/idempotence under stated validation hypotheses and the
  cooperative-peer obligation handoff argument.
- Add IHAVE or other peering capabilities only with their own conformance audit.

Exit: interrupted exchange and restart preserve accepted responsibilities;
application acceptance remains distinguishable from transport delivery.

Incremental evidence: the [object assembly experiment](../specs/transfer-experiment.md)
stages out-of-order fragments with declared-byte and metadata-slot reservations,
exact duplicates, missing ranges, conservative overlap conflicts, and explicit
unverified candidates. It now has general reserve/add preservation, exact accounting, candidate/gap
correctness, costed hot-path bounds and boundary vectors. The
[actual BP application exchange](../tests/evidence/2026-09-18-bp-exchange.md)
adds durable sender/receiver journals, explicit retry after uncertain BPA restart,
lost-receipt regeneration and return transport with independent archive retention.
Finite sender state/node and transport receipt preservation are certified.
Persistent fragmented transfer, complete dependency validation, portable batches,
authenticated handoff, multi-relay/carried-media contact plans and conditional
progress remain open. Next complete M4 steps are authenticated identity/receipt
design (D01/D09), FNWF/FNRJ byte/live/replay refinement and receiver/Store
evolution, and an interrupted relay/contact-plan experiment with expiry and
staging exhaustion. The [composition assurance batch](../tests/evidence/2026-09-18-bp-composition-assurance.md)
certifies joint pending/durable work binding and fixed-Store receiver replay,
with five actual receiver process-death cuts; it leaves those wider seams open.
On dev `1b734868` the native N08 case (death after a durable kind 8, one retried delivery, one copy held, no third attempt) passes on the default developer image but cannot run on the DTN image, and against dtn7-rs an fn-authored bundle survives a severed contact and a SIGKILLed carrier to be delivered once while the DTN image refuses every return bundle at its receive boundary ([record](evidence/m4-dtn-n08-2026-09-24.md)).

Durable scheduling is `implemented` (`REP-005`): all three scheduler roots
pass the farm gate of `dev` `bdd59d2`. Two cautions travel with that status —
both aging keystones were false as stated until `79e5227`, and conditional
progress holds only under the constrained `fn-assume-fairness-contact-index`.
TCPCLv4 arrived with `c8886ee` and no farm gate at all; C1 to C4 were then
closed by `w6/tcpcl-c4`, and `w9/dtn-e2e` gave the cluster its first **running**
evidence: `books/tcpcl-session` certifies with an O(1)-per-chunk served-path
guard, a native image carrying the layer builds, and `tools/tcpcl_lab.py`
passes six scenarios — including a bundle each way between two images on
loopback and one each way with dtn7-rs 0.21.0 over RFC 9174. That closes v0.4's
gate, "a two-node transfer over fn's own convergence layer", and nothing more:
the image is the DTN-only build list, there is no BP node behind the layer, and
`books/tcpcl-invariants` had no verdict against the new text when this was
written. **There is a BP node behind the layer as of 2026-09-21**:
`w11/bp-node` gave `books/bp-node` and `tests/acl2/bp-node-tests` their first
certificates, the DTN image carries the node, `tools/tcpcl_lab.py --scenario
adu` passes fn to fn with the bundle authored by `fn-bpn-send` at each end,
and the dtn7-rs exchange now has **one side authoring each way** rather than
dtn7 authoring both — with the octets kept in `tests/bp-dtn7/golden/` and the
dtn7-authored one inlined in a certified book
([the evidence](evidence/bp-dtn7-w11-2026-09-21.md)). It has one now: `w9/dtn-e2e` reverted that guard rather than leave
the invariants book timing out, and `w11/tcpcl-theory` re-landed it together
with the theory work the book needed to survive it, all three roots certified
together (`certify-20260921T000317Z-1324995`, the invariants book 609.69 s to
7.25 s). `w11/tcpcl-outbound` then took the other half, which that lane had
recorded open: the guard was still walking the unsent outbound suffix once
per socket chunk, so a *send* was still quadratic. It is not now (D20,
guard-total `fn-tcl-take`/`fn-tcl-drop` and `fn-tcl-outbound-cheapp`), and
four roots certify together with C1 to C4 byte-identical. The lab's `profile`
scenario, which times a send and would be the first end-to-end gate on that
work, has NOT run: `books/bp-node` is open on dev at one guard conjecture, so
no native image builds. See [the evidence](evidence/tcpcl-dtn-w9-2026-09-20.md),
[w11/tcpcl-theory's](evidence/tcpcl-theory-w11-2026-09-20.md),
[w11/tcpcl-outbound's](evidence/tcpcl-outbound-w11-2026-09-20.md) and
[the wave record](evidence/wave-realignment-2026-09-19.md) §1.

## M5: bounded long-lived operation

- Resolve history pruning, release, archive policy, and resurrection behavior.
- Implement GC and compaction with protected dependency closure and temporary
  space accounting. Prove preservation and crash behavior.
- Add justified disk indexes and checkpoints at realistic scale.
- Exercise corruption detection, repair policy, backup/restore, retained evidence,
  key/policy evolution, and format migration.

Exit: bounded admission/refusal and operational headroom are explicit and tested;
compaction does not weaken acceptance or replay guarantees. Retained history may
grow until admission refuses. Finite history pruning requires D13 and its own
duplicate/resurrection argument; indefinite acceptance is not promised.

Incremental evidence (2026-09-24, [m5-capacity](evidence/m5-capacity-2026-09-24.md)):
the transaction budget is ACL2's. The served article prepare
(`fn-sbud-prepare`, installed by `fn-owner-prepare`) refuses at the budget the
owner carries from the store's persisted profile, with the owner unchanged and
the word `:unaffordable` (`441 ... no capacity`); `operator status` prints
ACL2's headroom; `operator init --profile scale` reaches the 4096 budget.
Measured on a developer image: 128 POSTs accepted, the 129th and 130th
refused by name. Open: headroom of a running owner (the control channel has
no such query), an offline profile upgrade, and the reopen cost that makes
the 4096 budget admissible rather than usable.

Incremental evidence (2026-09-24, [m5-compaction](evidence/m5-compaction-2026-09-24.md)):
"compaction with its preservation proof" for the transaction prefix. A
selected lossless pack plus `pack-reclaim` already existed; PRF-073 now
proves, over the functions the reclaim and the next open call
(`fn-bs-pack-reclaim-plan`, `fn-profile-txn-observation`,
`fn-ccp-observe-framed`), that the open after a reclaim, at any cut, hands
replay the identical record list, and the plan's namespace bound is the
profile's (one owner). Natively on a developer image of the branch, GROUP,
ARTICLE by number and Message-ID, HDR and retention are identical across
the reclaim and each of its cuts, and the next POST gets high+1. Open:
no operator entry reaches compaction, the pack is bounded at 4096 events
and 4 MiB, and article-object closure and temporary space are unaddressed.

## M6: additional interfaces and mission profiles

- Extend the already exercised BP path with additional convergence-layer and
  deployment profiles. BP lifetime and fn obligation terms remain distinct;
  initial BP integration belongs to the active M3/M4 path.
- Simulate long/asymmetric contacts, interrupted transfers, clock uncertainty,
  quota pressure, and eventual-contact assumptions.
- After the selected NNTP/command-line-first path (D17), build the human web
  interface; explore 9p projections and submission
  files using the same acceptance rules. The read-only half of that exploration
  is now an experiment: [a 9P2000 view](../specs/views-9p.md) of one committed
  store, mounted by the Linux kernel client and served entirely from the
  reader's own projection functions. Private messaging follows D04's scope.
  The web interface ([the web reader](../docs/web.md)) now logs in over
  verified STARTTLS to a protected node, threads by References, replies with
  RFC 5537 References, keeps the three POST outcomes apart with the node's
  reason line, shows the node's `HDR :fn-verified` report as a badge, keeps
  client-only read marks, and resumes from (group, local number, Message-ID);
  exercised on a developer image ([record](evidence/m6-web-2026-09-24.md)),
  not yet against the deployed node.

Exit: demonstrate actual adapter interoperability and report its version/profile.
Operational mission qualification requires its own hardware, security, and
reliability work; it is not an automatic exit claim of M6.

## Handoff rule

After each task, update the current stage/next task, decision resolutions,
requirement status, proof status, and evidence references as applicable. Leave
future plans unchecked. A blocked dependency names the specific open decision
or missing evidence, rather than declaring the entire project blocked.

### `books/nntp-effects` is not a gap, and the old number is a warning

This list carried `books/nntp-effects` as open at
`FN-NNTP-HDR-LABELLED-LINE-IS-BLOCK-TEXT` after 2598.79 s and 1.47e9 prover
steps. It **certifies in 119.1 s**: persvati `run-20260921T005005Z-1235`,
manifest `status: passed`, `book_failures: {}`, 81 of 81 roots. The lane that
observed it changed nothing in that book and said it could not tell whether
the book was repaired by another lane's work or whether the original verdict
came from a contended box; neither can this note. What follows either way is
that **a wall-clock verdict taken while the box was loaded is not evidence
about a book**, and a 2598 s figure that becomes 119 s with no edit is the
shape of that mistake. Timings quoted as facts elsewhere in this tree should
name the box and its load, as the convergence-layer records now do.

## Retired: the six-wave shape and its checklist (2026-09-20 to 2026-09-22)

Retired by decision 3 of 2026-09-22. The section, the earlier landing notes,
the old release-shape text and the v0 checklist with its fiber records moved
to [archive/milestones-retired-2026-09-24.md](archive/milestones-retired-2026-09-24.md);
the release shape is [the trajectory plan](plan-2026-09-22-trajectory.md) §2.2.

Each milestone ends with a reviewable artifact and evidence. Sequence is a
dependency order, not a calendar estimate. Privacy/signature choices may expand
the first usable release. Interfaces can be explored without claiming completion
of a dependent guarantee.
