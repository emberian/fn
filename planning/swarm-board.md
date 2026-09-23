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

## Active efforts

All branches below start at `df5097b6`; worktrees are under `build/lanes/`.
This roster describes collaboration, not file reservations. Each lane has the
shared dispatch brief at `build/launch-20260923/BRIEF.md` and the relevant specs.

| Agent | Result being advanced | Immediate collaborators |
| --- | --- | --- |
| scholar_architect (Astra) | Reassess v0/v1 ambition for robust NNTP and agent/silo coordination; grounded recommendations and design changes | bp_foundation, authorship_carrier, root |
| image_upgrade (Sol) | Self-contained frozen artifacts and isolated preservation/rollback upgrade witnesses | entry_profiles, matrix_witnesses |
| entry_profiles (Sol) | Developer-only raw insertion and production DTN selector admission | image_upgrade, crash_differential, bp_foundation |
| crash_differential (Sol) | Served crash observations connected to ACL2 byte-model outcomes | entry_profiles, scholar_architect |
| feed_replay (Sol) | K5 actual feed/journal replay and protected restart witness | matrix_witnesses |
| bp_foundation (Sol) | Finite A1 schema/receive kernel and executable counterexamples | scholar_architect, status_codec, fragment_refinement |
| authorship_carrier (Sol) | Selected exact-source dual-signature carrier/profile | scholar_architect, root |
| fragment_refinement (Sol) | Fragment/reassembly reference correspondence and bounded admission | bp_foundation, status_codec |
| status_codec (Sol) | Bounded canonical BP status-report codec | bp_foundation, fragment_refinement |
| matrix_witnesses (Sol) | Actual native protected-exchange/queue observations and accurate test subjects | feed_replay, image_upgrade, crash_differential |
| iteration_tooling (Sol, landed) | Affected-root selection, measured proof-cost reporting, E1/E2 experiment proposal | all proof lanes |
| acceptance_stamp (Sol) and stamp_callers helper | T2a schema migration, caller and fixture correspondence | authorship_carrier (canonicality proof), crash_differential, BP lanes |

## Current agreements and discoveries

- Feed replay and matrix lanes share the protected two-node restart/queue
  exercise; do not independently build the same image for that witness.
- Iteration tooling repaired Makefile selection of host wrappers, preserving
  admission coverage through certifiable host-test roots. The proof-cost report
  is landed. Root also repaired the merge gate: `--changed-since --strict` now
  rejects moved dependency bytes as `stale`, distinct from a failed proof.
- Crash correspondence must account for physical inode renaming and invisible
  unreachable model inodes. Compare through an explicit observation relation;
  do not call scanner agreement full physical-state equality.
- The architect found that reader watermarks acknowledge output, not durable
  agent processing. The assessment and E1/E2 experiment proposal are landed.
  The user selected report/receipt plus reply, consumer-owned inbox/outbox and
  a cursor/ack contract, with separately administered stores and trusted peers
  first. These experiments do not widen the v0 gate.

## First convergence

- Native entry restrictions and four-profile packaging are landed and exercised
  on frozen `24a5df6b`; see its image evidence. Production normal submission,
  developer-only raw insertion and relocation passed their scoped gates.
- Broader no-skip suites exposed absent workflow constructors, an omitted
  reclaim-plan include, a Boolean predicate called as an action, and an admin
  fixture waiting forever after the CONTROL announcement. The latter three
  are repaired in source. Workflow undertake/receipt/release still need the
  actual ACL2 contract and caller join; rebuilding alone cannot supply them.
- Protected peering on the old image was not qualified. The corrected fixture
  observed a queued article with no offer. TLS zero-time reads never polled the
  socket; the host fix and real OpenSSL witness are landed. Matrix and feed
  agents share the new two-node restart/mid-transfer gate.
  That suite now passes on frozen `f0b8b166`, including reciprocal protected
  exchange, both restart cases and credential/anchor rejection controls;
  [the evidence](evidence/matrix-protected-f0b8b166-2026-09-23.md) records
  the exact journal observations and one recipient article after retry.
- The bounded feed-port replay theorem and served process-death visible-file
  relation are landed with exact manifests. Physical FNFD correspondence and
  the visible-relation-to-recovery theorem remain distinct open obligations.
- BP foundation is landed as an unhosted refinement. Review caught callback
  reuse and uncertainty fencing defects; the repaired model allocates operation
  IDs and ignores ordinary callbacks while uncertain. Guards and FNBS/native
  joins remain open.
- Hybrid carrier/profile source and its affected closure are landed. Store
  verdict and reader integration remain open; known profile alone grants no
  verified verdict. Its Sol agent now helps T2a reverse-parser canonicality.
- Fragment refinement and status-report codec proof work continue. T2a is
  checkpointed in its lane, not ready for integration.

## Runs and capacity

Frozen image `24a5df6b`: hbox run `run-20260923T142047Z-4e1a`, gate
`/tank/fn/gates/takeover-image-upgrade-24a5df6b`, w28 toolchain, all 174
closure books reused. Four cores and the no-skip suite outcomes are recorded
in [image evidence](evidence/four-profile-image-24a5df6b-2026-09-23.md).

Second frozen runtime source `f0b8b166`: hbox run `run-20260923T143814Z-b301`,
gate `/tank/fn/gates/takeover-image-upgrade-f0b8b166`, w28 toolchain. The
176-book image closure reused 174 and certifies two for the newly included
reclaim plan. Image_upgrade coordinates shared artifacts with matrix,
entry-profile and crash agents. Later harness commits are recorded separately.

Carrier affected closure: persvati run `run-20260923T143127Z-1770`, w25,
102 cached and 161 newly certified books, all passed. Fragment follows this
run; T2 will coordinate its broad migration batch when coherent. See the
individual evidence records for manifests and source digests.

Combining the fragment limits with the carrier exposed two stale include
closures despite each lane's own passing source. Root run
`run-20260923T144543Z-d324` in
`/home/ember/fn-gates/takeover-convergence` reused 70 dependencies and certified
`books/bp-limits` and its test at the combined bytes (w25, two jobs,
4.585 s certification wall). The
[manifest](evidence/manifests/certify-20260923T144550Z-772507.json) records
the source/closure digests and both passes. No unrelated roots were rebuilt.

Lanes begin with at most two jobs, then negotiate shared wider runs when
useful. Existing machine slot pools and hbox memory wrapper remain in force.
Release idle REPLs when peers need their slots. A runner that has not emitted
its first completed book may still be proving: the current farm progress
display can misleadingly show zero books/elapsed. Diagnose via its drivers,
version log and exact process before calling this a queue or resubmitting.
