# Development milestones

Current stage: parallel executable M1/M2 components, with implementation and batch
review authorized. Initial component books certify; no full implementation/proof
milestone is complete. See
[current work](now.md) for scope and ownership. Remaining decisions in the
[workbook](decisions.md) are a backlog; they do not all block this abstract model.

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
release does not yet claim disconnected peering or remote delivery.

## M4: disconnected exchange

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

## M5: bounded long-lived operation

- Resolve history pruning, release, archive policy, and resurrection behavior.
- Implement GC and compaction with protected dependency closure and temporary
  space accounting. Prove preservation and crash behavior.
- Add justified disk indexes and checkpoints at realistic scale.
- Exercise corruption detection, repair policy, backup/restore, retained evidence,
  key/policy evolution, and format migration.

Exit: finite-resource operation is explicit and tested; pruning/compaction do not
quietly weaken acceptance or replay guarantees.

## M6: additional interfaces and DTN

- Integrate portable batches with an existing BP implementation and selected
  convergence layers. Keep BP lifetime and fn obligation terms distinct.
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
