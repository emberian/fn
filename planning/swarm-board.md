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
| iteration_tooling (Sol) | Affected-root selection defect and measured proof-cost reporting | all proof lanes |

## Current agreements and discoveries

- Feed replay and matrix lanes share the protected two-node restart/queue
  exercise; do not independently build the same image for that witness.
- Iteration tooling will repair Makefile/selection of host wrappers together,
  preserving their admission coverage through the appropriate host/image gate.
- Crash correspondence must account for physical inode renaming and invisible
  unreachable model inodes. Compare through an explicit observation relation;
  do not call scanner agreement full physical-state equality.
- The architect found that reader watermarks acknowledge output, not durable
  agent processing. Cursor/consumer semantics are under assessment, not new
  v0 promises.

## Runs and capacity

No certification run has been assigned by this board yet. Lanes start with
at most two jobs per submitted run, announce the run and matching cache work,
and negotiate larger shared runs. Existing machine slot pools and the hbox
memory wrapper remain in force. Do not change slot directories or pool limits
per lane. Root's initial read-only checks found the deployed node running and
no farm certification processes; this is a dispatch-time observation, not an
ongoing health claim.
