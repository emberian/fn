# Swarm board

What each lane intends to do tonight, so peers can find shared work and
reuse each other's runs. The board records intentions, not exclusive claims:
two lanes may touch the same book, and they settle the combined change
between them (see [how we work](how-we-work.md)). The previous board, for the
2026-09-23/24 Codex swarm, is [archived](archive/swarm-board-2026-09-23-24.md).

## How lanes coordinate

The mechanism does not depend on the harness.

- Each lane works in its own worktree `build/lanes/<name>` on branch
  `lane/<name>`, from the dev revision named in [now.md](now.md).
- A lane keeps `LANEDUMP.md` at its worktree root: what it changed, the
  commits, the runs it submitted (host, run id, manifest), what it found
  that another lane needs, and what it could not resolve. Peers read it
  there. Its final report repeats the essentials.
- A lane that needs something from another lane says so in its LANEDUMP
  and its report. The coordinator relays it when that lane cannot read the
  other worktree in time.
- Lanes commit on their own branch and do not push. The coordinator merges
  coherent batches into dev, runs the convergence check in
  [how we work](how-we-work.md), and updates [now.md](now.md) and this board.
- A proof or build run is announced here (or in the LANEDUMP) before it is
  submitted, with its roots and source revision, so a matching run is reused
  rather than repeated.

## Batch 1 — 2026-09-24, from dev `46f2660d`

| Lane | Intends | Touches | Talk to |
| --- | --- | --- | --- |
| plan-consolidate | one current page; archive the stale plans; links resolve | `planning/*.md`, `AGENTS.md`, `docs/README.md` | everyone (the brief source changes) |
| bp-progress-guards | guard closure of `books/bp-node-progress-guards` | that book and the helpers its guards need | bp-selection-invariant (same machine) |
| bp-selection-invariant | `fn-bpnp-step-progress-preserves-held-and-issued`; then the machine teeth book | `books/bp-node-progress-selection-invariants`, `tests/acl2/bp-node-machine-teeth-tests` | bp-progress-guards |
| proof-cost-regressions | the five slow store/consumer/replay books under 10 s, statements unchanged | `store-node-invariants`, `consumer-store-invariants`, `store-identity-sequence-invariants`, `store-node-traces`, `replay` | check-ratchet (baseline) |
| check-ratchet | `proof_cost` and `certified_claims` fail `make check` against a baseline | `tools/proof_cost.py`, `tools/certified_claims.py`, `Makefile`, the baseline | proof-cost-regressions |
| worktree-retire | retire landed worktrees under `build/lanes/` | `build/lanes/*` (not active batch-1 trees) | coordinator |

Runs and results are recorded in each lane's LANEDUMP and, once merged, in
[now.md](now.md) and `planning/evidence/`.
