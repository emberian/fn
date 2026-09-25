# Now — 2026-09-24

The one page a new agent reads first. It says where dev is, what the night
is for and who is working on what; everything else is linked. The previous
log that lived here is [archive/now-2026-09-24.md](archive/now-2026-09-24.md).

## Where things stand

- **Read [the current view](current.md) first.** It is generated from the
  tree and a small sidecar, and gives each capability (P1 to P11, M4, M5, M6,
  T17) its contract, the host line that calls its subject, its keystone and
  certificate, the image that tested it, whether the live node carries it,
  and one line each for the latest result, the obstruction and the next
  gate. Superseded image records are listed there and stay in
  [`evidence/`](evidence/), immutable.
- **Live node:** hbox `/tank/fn/node` on `18c91321` since ~21:50 UTC
  ([node record](evidence/node-hbox-18c91321-2026-09-24.md),
  [qualification](evidence/qual-18c91321-2026-09-24.md)), upgraded in place
  with the store kept and its profile upgraded to scale (4096);
  `fn-47bdb9a4` and `fn-da5fd8cb` stay beside it for rollback.
- The [wind-down handoff](handoff-2026-09-24-winddown.md) is the restart
  record; [gpt-6's direction review](review-2026-09-24-gpt6-direction.md)
  names the next development cycle.

## The goal now: v0 deployed, then the milestones (re-pointed 2026-09-24 ~11:30 EDT)

ember's correction: the v0 push had become an audit of the present state.
The plan's forward work is what the lanes point at from here, with the
[scoreboard](v0-scoreboard.md) as the check, not the goal:

1. **T0, the deployed node: done.** It runs `18c91321` (above); which
   capabilities it carries is the "deployed" column of
   [the current view](current.md).
2. **M4, disconnected exchange.** The kind-8 retry policy (default adopted,
   pending ember), death-after-kind-8 exactly-once on a DTN image, an
   interrupted contact on a real BPA (dtn7-rs lab), the four-node lab.
3. **v1 (b), the Message-ID index on the served path** (T17) with its
   measured cost sentence.
4. **M6, the human web interface** ember, yue and tulip can use against the
   deployed node.
5. **M5, bounded long-lived operation**: headroom and refusal explicit and
   observed; compaction with its preservation proof.

Decisions for ember stay listed on the scoreboard; defaults are adopted where
the plan or the M4 evidence already implies one, and marked as such.

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

**Landed since:** each lane's result is in its record under
[`evidence/`](evidence/) and its merge message; what they add up to per
capability is in [the current view](current.md).

**Not merged, kept for a follow-up:** `lane/p11-machine-gaps` at `8b273f87`
(worktree `build/lanes/p11-machine-gaps`): N07 as a recovery-event boot-domain
gate and N11 as a kind-14 conflict record with its codec (certified), but the
keystone book `books/bp-node-machine-gaps.lisp` times out at the local lemma
`bpgap-conflict-held-under-hypotheses`, and the host must drive the new
`:persist-conflict` effect (bp-service.lisp `fnn-bps-drive-effects`, the
TCPCL receive callback, and the N07 gate at :75-114 / :752) before any image
carries the branch. Its LANEDUMP has the exact list.

**Stopped mid-flight by the laptop's OOM crash (2026-09-25 ~03:05 UTC),
each with its work committed in its worktree; resume by re-briefing from the
worktree's commits and LANEDUMP (the coordinator's SendMessage ids died with
the session):**

| Lane (worktree under build/lanes/) | State at the crash |
| --- | --- |
| rep-sha256 (Fable): SHA-256 on a word stobj | 0 commits; REPL work only; restart from the brief in the merge message of planning/design-2026-09-25-representation.md §5 |
| rep-records-2: records-concrete-2 and the trie | 2 commits ahead |
| rep-heap: the heap census and the payload holder | 1 commit ahead, 2 files modified (uncommitted) |
| bounds-p1-profile: the operator's profile (format 8) | 0 commits, 4 files modified (uncommitted) |
| bounds-p2-ceilings: data constants become codec ceilings | 3 commits ahead |
| bounds-p4-carrier: carrier v2 | 2 commits ahead; its persvati run (hybrid-* affected-by) was still certifying |
| control-c1: file control articles, never execute | 5 commits ahead |

Rule from the crash (cause and cap in
`planning/evidence/laptop-oom-2026-09-25.md`): ACL2 on the laptop only
through `tools/acl2` or `tools/proof_repl.py`, which now cap each process at
8,000 MB and pool six; never a bare `acl2 <`; images, owners and censuses on
hbox under `swarm-build` or a `systemd-run` memory cap, or on persvati.

## Where to read next

- [Current view](current.md): per capability, the four evidence
  coordinates and the next positive gate.
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
