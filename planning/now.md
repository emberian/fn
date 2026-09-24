# Now — 2026-09-24

The one page a new agent reads first. It says where dev is, what the night
is for and who is working on what; everything else is linked. The previous
log that lived here is [archive/now-2026-09-24.md](archive/now-2026-09-24.md).

## Where things stand

- **dev** is `46f2660d`. All fn source packets from the 2026-09-24 wave are
  integrated; the [wind-down handoff](handoff-2026-09-24-winddown.md) is the
  restart record and the source for everything in this section.
- **Last completed shared image:** [`863c2141`](evidence/863-native-cut-2026-09-24.md),
  with the runtime scopes the handoff records. Later fixes (BP identity,
  pack namespace, signed receiver) are integrated but untested on an image.
- **Live node:** hbox `/tank/fn/node` on `da5fd8cb`
  ([node record](evidence/node-hbox-da5fd8cb-2026-09-23.md)). Nothing tonight
  replaces it.
- **Final cut:** source `8a1b31f9` failed combined certification on three
  roots, so no image was built ([final record](evidence/final-cut-8a1b31f9-2026-09-24.md);
  handoff, "Final cut"):

| Red root | Failure | Lane |
| --- | --- | --- |
| `books/bp-node-progress-guards` | guard of `fn-bpnp-issued-debt-delta` lacks the base-state premise | bp-progress-guards |
| `books/bp-node-progress-selection-invariants` | `fn-bpnp-step-progress-preserves-held-and-issued`, non-clock `:progress` Subgoal 40.2' | bp-selection-invariant |
| `tests/acl2/bp-node-machine-teeth-tests` | blocked by the uncertified selection include, not its own counterexample | follows bp-selection-invariant |

## Tonight's goal (set by ember; Claude took over at 07:25 UTC)

1. A frozen image past `863c2141`: the three roots above certified, and BP
   N03 plus the interrupted-fragment native cases passing on it.
2. Stretch: one end-to-end join, signed peering into Mini consumption across
   two Stores, run as one exchange (handoff, "Mini work is committed separately").
3. Proof cost down: books over 10 s from 30 to at most 20, and
   `tools/proof_cost.py` and `tools/certified_claims.py` failing `make check`
   against a baseline instead of warning.
4. Planning consolidated onto this page (this change).

Measure 3 with the tool, not prose: at `46f2660d`, `tools/proof_cost.py`
prints 45 over-10 s warning rows across 37 distinct roots, grouped per host
and toolchain. The check-ratchet lane fixes which figure the baseline counts.

## Active lanes (batch 1)

Lanes run on Claude Opus 5.5 in `build/lanes/<name>` on branch `lane/<name>`,
created from dev `46f2660d`; Claude Fable coordinates and merges. How lanes
coordinate is on the [swarm board](swarm-board.md).

| Lane | Intended result | Must cite |
| --- | --- | --- |
| plan-consolidate | done: this page, the archive moves, links repaired | merged, `make check` exit 0 |
| bp-progress-guards | guard closure of `books/bp-node-progress-guards` without whole-state revalidation on the served path | farm run id and manifest; theorem statements; `green_check` line |
| bp-selection-invariant | `fn-bpnp-step-progress-preserves-held-and-issued` certified, then the machine teeth book | farm run id and manifest; the subgoal repaired; teeth book result |
| proof-cost-regressions | `store-node-invariants`, `consumer-store-invariants`, `store-identity-sequence-invariants`, `store-node-traces`, `replay` under 10 s, statements unchanged | before/after per-book times from certify logs, same host and toolchain |
| check-ratchet | `proof_cost` and `certified_claims` fail `make check` against a committed baseline | the baseline file and the failing/passing `make check` runs |
| worktree-retire | done: 60 of 83 landed worktrees retired, 6 archive refs, [record](evidence/worktree-retirement-2026-09-24-claude.md) | merged `ec498722` |
| bp-codec-cost | `checkpoint-compaction`, `records-canonicality`, `bp-node-fragment-plan`, `bp-fnbs-codec-invariants`, `tcpcl-session`, `bp-fnbs-byte-invariants` under 10 s, statements unchanged | before/after per-book times, same host and toolchain |

## Where to read next

- [Wind-down handoff](handoff-2026-09-24-winddown.md): restart record, the
  integrated capabilities and their limits, the final cut.
- [How we work](how-we-work.md): the loop, the compute budget, convergence.
- [AGENTS.md](../AGENTS.md): the assurance rules. They apply in full.
- [Decisions](decisions.md): what ember has decided and when.
- [Trajectory plan](plan-2026-09-22-trajectory.md) §0 to §2 and §6: release
  scope, v0 and v1, and what v0 does not claim.
- Evidence: dated records in [`planning/evidence/`](evidence/) and certify
  manifests in [`planning/evidence/manifests/`](evidence/manifests/).
- [Milestones](milestones.md): M0 to M6 and the current-task line.
