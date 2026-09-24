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

## Lanes

Lanes run on Claude Opus 5.5 in `build/lanes/<name>` on branch `lane/<name>`
from a named dev revision; Claude Fable coordinates, reviews and merges. How
lanes coordinate is on the [swarm board](swarm-board.md). The night lanes
(image, join, cost, planning) are in the [restart record](handoff-2026-09-24-night.md).

**v0 push, landed** (each row's evidence is in [the scoreboard](v0-scoreboard.md)
and the merge message):

| Lane | Result |
| --- | --- |
| audit-p1-p6, audit-p7-p9, audit-p10-p11 | every §2.1 cell re-verified; packets per P (`planning/v0-audit-*.md`) |
| matrix-1a9dd747 | 188 rows reached, 0 disagreed, 0 faulted, INN 33/33; three matrix-tool defects fixed ([record](evidence/matrix-1a9dd747-2026-09-24.md)) |
| campaign-1a9dd747 | 20/20 cuts pass on the developer twin; production refuses selectors; NNTP wire probe found W1, W2, W3 ([record](evidence/campaign-1a9dd747-2026-09-24.md)) |
| bp-d1b-disposition | every commit already on dev; worktree retired ([record](evidence/bp-d1b-disposition-2026-09-24.md)) |
| host-translate-check | `tools/host_shape_check.py` in `make check`; `make check-host-translate` |
| cost-4 | five more books under 10 s; baseline 5 |
| p9-retention | refusal and keep-until-release over the called prepare and finish; PRF-004 +6 |
| p6-reconfig | half-change theorem over the called publication path; delta constructor moved into ACL2 |
| p2-p3-p5-owner | 240 keystone over `fn-own-finish` (host must install it), T6 pinned view, open-at-bound and fault wrapper |
| p7-peering | loop freedom over `fn-own-submission-targets`; Path tail kept; PRF-029 +4, PRF-058 +2 |
| p8-verdict | kind-4 finish records its verdict; `HDR :fn-verified` over `fn-own-read`; PRF-026 has events |
| p1-auth | 480/483/posting allowance over `fn-auth-step-pinned` and `fn-served-dispatch`; PRF-031 +6 |
| p11-bridge | `fn-bpnp-step` refines `fn-bpn-step` on base events; no release without a receipt; counterexample suite started; recovery-clears-sessions bug found |

**In flight:**

| Lane | Intended result |
| --- | --- |
| p2-wire | W1, W2, W3 fixed in the host; `fn-owner-finish` installs `fn-own-finish`; probe rerun on a developer image |
| p10-k0 | general K0 (or its cut-coordinate restriction), K5/K8 registered, native transcription check, five missing cut selectors |
| campaign-production-kill | external SIGKILL campaign on the production image (P10's production evidence) |
| native-subsets-1a9dd747 | every remaining native module on the image, per-P observation cells |
| bp-recovery-sessions | the recovery arm clears sessions and the pending image; dependents re-certified |
| p6-crash-replay | crash headline over `fn-cpr-replay` as the host calls it |
| p3-p5-followups | local numbers never reused over the served path; owner-fault teeth |

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
