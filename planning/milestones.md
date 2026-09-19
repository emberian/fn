# Development milestones

Current stage: the BP composition assurance batch is complete for its named
scope; no full implementation/proof milestone is complete. The user requested
broader feature and assurance work in parallel. The [three-cycle work plan](swarm-cycles.md)
now maps 34 planned packets to dependencies, owners, stable IDs and finite exits:
a writable local pilot; signed disconnected exchange; then long-lived operation
and release assessment. Packet readiness controls sequencing, so independent
local service, identity, storage and DTN work can advance together.

The next launch is C1: BP guards/journal refinement and receiver/Store composition
alongside the mutable owner, injection/POST, complete reader/overview, resource
accounting, index adoption, checkpoint codec, source/authority design and an
early LTP feasibility experiment. These are planned artifacts, not evidence or
new decision resolutions. [Current work](now.md) retains the completed baseline;
the [decision workbook](decisions.md) records the remaining product choices.

Each milestone ends with a reviewable artifact and evidence. Sequence is a
dependency order, not a calendar estimate. Privacy/signature choices may expand
the first usable release. Interfaces can be explored without claiming completion
of a dependent guarantee.

## M0: design scaffold

- [x] Capture architecture, terminology, contracts, trust boundary, and sources.
- [x] Register requirements, proof targets, and scenario specifications.
- [x] Expose unresolved decisions with recommendations and consequences.
- [x] Record the user-facing choices needed by the first bounded M1 cycle.
- [x] Run structural checks and review for contradictions before handoff.

Scaffold validation on 2026-09-18: `make check` passed for 22 Markdown files,
49 requirements, 18 proof targets, and 18 scenario specifications. Temporary-copy
negative checks rejected a broken document link, an unknown proof reference,
and a certified status without evidence. These are tooling checks only.

Exit: navigable scaffold and an accurate next-task list. M0 does not freeze all
later binary layouts. Decisions needing model/measurement evidence remain open
with named dependent milestones.

## M1: executable model

Before completing all of M1, finish D01/D05's semantic details (D02/D03/D04 are selected),
D07, local D10/D11, D12's first handoff
terms, D13's initial history rule, resource bounds in D16, and proof scope D18.

- Pin ACL2 and host Lisp versions, installation method, book dependencies, and
  clean certification invocation. Keep the initial book dependency set small.
- Define octets/IDs, records, invariants, events/effects, one-transaction ownership,
  local acceptance, two-group allocation, duplicate suppression, and obligations.
- Execute the logical portion of the letter lifecycle with lost replies and an
  explicit crash/commit-result abstraction.
- Prove initial invariants, allocation/identity preservation, idempotent effects,
  and the first guard/correspondence obligations. Record actual theorem names.
- Supply a deterministic simulator host; no network deployment is needed.

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
- Implement bounded codecs and their round-trip/canonicality properties.
- Model torn/reordered writes, barriers, isolation, and uncertain failures.
- Implement segments, journal, recovery, and checkpoints against that model.
- Prove conditional recovery and checkpoint equivalence; implement a real adapter
  with explicit platform assumptions and fault-injection evidence.
- Account for metadata and recovery/compaction headroom under no-space failures.

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
passed mixed live/refusal/recovery traces, actual host adoption and 533 base
function guards in a 75-root/67-test batch. Physical refinement and platform
qualification remain work.

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

## M6: additional interfaces and mission profiles

- Extend the already exercised BP path with additional convergence-layer and
  deployment profiles. BP lifetime and fn obligation terms remain distinct;
  initial BP integration belongs to the active M3/M4 path.
- Simulate long/asymmetric contacts, interrupted transfers, clock uncertainty,
  quota pressure, and eventual-contact assumptions.
- Build the chosen human web interface; explore 9p projections and submission
  files using the same acceptance rules. Private messaging follows D04's scope.

Exit: demonstrate actual adapter interoperability and report its version/profile.
Operational mission qualification requires its own hardware, security, and
reliability work; it is not an automatic exit claim of M6.

## Handoff rule

After each task, update the current stage/next task, decision resolutions,
requirement status, proof status, and evidence references as applicable. Leave
future plans unchecked. A blocked dependency names the specific open decision
or missing evidence, rather than declaring the entire project blocked.
