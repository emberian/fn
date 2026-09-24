# Now — 2026-09-24

The one page a new agent reads first. It says where dev is, what the night
is for and who is working on what; everything else is linked. The previous
log that lived here is [archive/now-2026-09-24.md](archive/now-2026-09-24.md).

## Where things stand

- **dev** is `46f2660d`. All fn source packets from the 2026-09-24 wave are
  integrated; the [wind-down handoff](handoff-2026-09-24-winddown.md) is the
  restart record and the source for everything in this section.
- **Last completed shared image:** [`1a9dd747`](evidence/native-cut-1a9dd747-2026-09-24.md)
  (2026-09-24 06:10 EDT): closure green, image pair built, BP N03 and the
  interrupted-fragment case pass on it. Before it, [`863c2141`](evidence/863-native-cut-2026-09-24.md).
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

## The goal now: v0 (set 2026-09-24 ~08:00 EDT)

The night goal (image, join, cost, planning) is met; see the
[restart record](handoff-2026-09-24-night.md). ember's next goal is v0 itself,
as [plan §2.2](plan-2026-09-22-trajectory.md) defines it: P1 to P11 each held
as a theorem over the host-called function, with teeth, observed on the
deployed image; one matrix run on that image agreeing with every row it
reaches; the cut campaign passing on the production image. The scoreboard is
[v0-scoreboard.md](v0-scoreboard.md) (one row per P: theorem / host-called
subject / teeth / observed on image / obstruction); a P is DONE or names its
obstruction there. Deploying an image to the hbox node happens only after the
matrix and campaign pass on it, in place with the store kept and the previous
release retained. Proof cost stays a failing check.

## Active lanes

Lanes run on Claude Opus 5.5 in `build/lanes/<name>` on branch `lane/<name>`,
created from dev `46f2660d`; Claude Fable coordinates and merges. How lanes
coordinate is on the [swarm board](swarm-board.md).

| Lane | Intended result | Must cite |
| --- | --- | --- |
| plan-consolidate | done: this page, the archive moves, links repaired | merged, `make check` exit 0 |
| bp-progress-guards | guard closure of `books/bp-node-progress-guards` without whole-state revalidation on the served path | farm run id and manifest; theorem statements; `green_check` line |
| bp-selection-invariant | done: the old theorem was false after forwarding landed; split into `-preserves-held` and `-issued-unchanged-or-pending-dispatch` with routed witness and teeth | merged; hbox run-20260924T085624Z-626a |
| proof-cost-regressions | done: cause was `fn-th-topic-eventp` left enabled at export; withdrawn with a shape lemma plus four hint repairs. `replay` 58.1 to 2.5 s, `store-identity-sequence-invariants` 46.6 to 3.0, `consumer-store-invariants` 42.0 to 8.3, `store-node-invariants` 85.0 to 17.6, `store-node-traces` 50.5 to 20.3 (persvati, 2 jobs) | merged; [record](evidence/topic-recognizer-proof-cost-2026-09-24.md); persvati runs 084451Z, 090348Z, 090548Z |
| check-ratchet | done: both lints exit 1 on regression; baseline `planning/proof-cost-baseline.json` (37 books, slowest measurement per book) only shrinks | merged; `make check` exit 0 |
| worktree-retire | done: 60 of 83 landed worktrees retired, 6 archive refs, [record](evidence/worktree-retirement-2026-09-24-claude.md) | merged `ec498722` |
| bp-codec-cost | done: five of six under 10 s (`checkpoint-compaction` 67.8 to 1.8, `records-canonicality` 37.6 to 5.1, `bp-node-fragment-plan` 28.8 to 1.3, `bp-fnbs-codec-invariants` 26.5 to 4.4, `bp-fnbs-byte-invariants` 22.8 to 3.4); `tcpcl-session` 24.2 to 12.8, still over | merged; hbox runs 090646Z-5502, 091446Z-52b2 |
| two-store-join | done: harness `tools/runbooks/two_store_join.py`; dry run on 863c2141 stops at B's receiver verdict (REFUSED), which the ingress fix after 863 addresses; `a-accepted` cut held | merged; [record](evidence/two-store-join-harness-2026-09-24.md) |

## Where to read next

- [Restart record for the Claude night](handoff-2026-09-24-night.md): the
  numbers, the findings, what remains open, how to restart.
- [Wind-down handoff](handoff-2026-09-24-winddown.md): gpt-6's record of the
  integrated capabilities and their limits, and its final cut.
- [How we work](how-we-work.md): the loop, the compute budget, convergence.
- [AGENTS.md](../AGENTS.md): the assurance rules. They apply in full.
- [Decisions](decisions.md): what ember has decided and when.
- [Trajectory plan](plan-2026-09-22-trajectory.md) §0 to §2 and §6: release
  scope, v0 and v1, and what v0 does not claim.
- Evidence: dated records in [`planning/evidence/`](evidence/) and certify
  manifests in [`planning/evidence/manifests/`](evidence/manifests/).
- [Milestones](milestones.md): M0 to M6 and the current-task line.
