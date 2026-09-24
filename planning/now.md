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

## Tonight's goal (set by ember; Claude took over at 07:25 UTC)

1. A frozen image past `863c2141`: the three roots above certified, and BP
   N03 plus the interrupted-fragment native cases passing on it.
2. Stretch: one end-to-end join, signed peering into Mini consumption across
   two Stores, run as one exchange (handoff, "Mini work is committed separately").
3. Proof cost down: books over 10 s from 30 to at most 20, and
   `tools/proof_cost.py` and `tools/certified_claims.py` failing `make check`
   against a baseline instead of warning.
4. Planning consolidated onto this page (this change).

Measure 3 with the tool, not prose: the ratchet baseline counts 37 books
over 10 s at `46f2660d` (slowest measurement per book, any host); the
night's target in those terms is 27 or fewer, and a book leaves the
baseline only by a passing measurement under 10 s. At 06:45 EDT the
baseline holds 19 books.

## Active lanes (batch 1)

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
