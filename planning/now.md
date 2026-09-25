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

Push dev after every merge (ember, 2026-09-25): a merge certification
still runs and lands its manifest, but never gates the push.

Rule from the crash (cause and cap in
`planning/evidence/laptop-oom-2026-09-25.md`): ACL2 on the laptop only
through `tools/acl2` or `tools/proof_repl.py`, which now cap each process at
8,000 MB and pool six; never a bare `acl2 <`; images, owners and censuses on
hbox under `swarm-build` or a `systemd-run` memory cap, or on persvati.

**The megaspike (D28, from ~07:45 UTC 2026-09-25):** `spike/mega` from dev;
eight spike lanes on `spike/<name>` in build/lanes/spike-<name>: control (C2 to
C4 end to end), peering (invite/accept, succession, revocation, pull feeds,
INN stranger), mission (the four-node lab and demo on hbox), operator (one
`fn` command, upgrade/rollback/backup/restore, alerts, mission profiles),
storage (reclaim under D13, chained packs, rotation cleanup, 64-bit widths,
N=100k numbers), reader (threading, search, composer, a third-party client,
operator page), bp (routed queued jobs, fragmentation, multi-relay and ION,
production DTN labs, N16-F1), representation (waves B and C on the spike
for numbers). Dev lanes still running: bp-budgets-receipts (the connection-
local uncertain receipt transfer), bounds-p3-checkpoint, python-store-f8,
signed-path. The spike never merges into dev; each spike record lists its
deferrals for the proved re-implementation.

## State at the weekly API limit (2026-09-25 ~11:30 UTC; resets Sep 26 09:00 New York)

The night deputy and about a dozen of its lanes were terminated by the
account's weekly rate limit. Nothing was lost: every lane's commits are in
its worktree under build/lanes/, the deputy's state is in
build/coordinator/NIGHT-STATE.md and its routine in build/coordinator/
NIGHT.md, the backlog it swept is planning/backlog-2026-09-25.md. When the
limit resets, start a fresh deputy from those two files; it resumes each
terminated lane by re-briefing from the worktree (the agent ids are dead).

Landed on dev tonight by the deputy (18 merges, two merge certifications
green): bp-routing-2, peer-carriage, dtn-build, native-drift,
bounds-profile, k0-rest, operator-verdicts, path-and-login (D32: a
client-supplied Path accepted; login bound to principal), reclaim-d13 (the
proved half), bounds-blob, control-c3 (the decision), rep-octets-stobj,
carry-kind, k0-steps (K4 bridges), k0-cuts, live-status, marker-required,
plus the coordinator's own merges earlier (owner-checkpoint-open,
bp-budgets-receipts with the connection-local receipt transfer, control C2).
On spike/mega: operator, reader, peering, control, bp, representation; the
mission lab and the storage spike (a 100k-article run, 4 to 5 hours) were
still running on hbox when the limit hit.

Terminated mid-flight, worktrees intact, to resume: reader-surface, pbb-d32
(Fable), bounds-p5 native continuation (needs LD_LIBRARY_PATH for OpenSSL
on hbox), bp-n16-prod, control-c3b (the served withdrawal with K1 restated),
reclaim-host, peer-keys, peer-invite, status-join, rep-wave-c (Fable; its
correspondence chain was proving), checkpoint-cost, the bounds-p6 record-
ceiling fix. Held merges: bounds-p6 (the width half; blocked until the
record ceiling fix lands: a saved format-8 profile with R = 17,138,486
would fail validation), python-store-f8 (green but its quiet rerun of the
timed-out modules was pending), bounds-p5 (chained packs; one native test
red on packing nothing).

Dev's merged bytes are RED at four books (the deputy's third merge
certification, hbox run-20260925T102957Z-2118, manifest
certify-20260925T103038Z-3156842, 516 of 520 passed): books/poster-bytes-
buffer and tests/acl2/octets-stobj-tests (the octets-stobj consumer against
D32's supplied Path: the terminated Fable lane pbb-d32 was proving the
repaired chain), books/store-reclaim and its tests (the reclamation books
against the same merges). Both are join defects to fix first at the reset,
before any cut.

Not done tonight: no cut, qualification or deploy (dev never converged: P6
held, C3's served half and wave C in flight); segmented articles (P6's
second half) not started; the node is still on c3420013 with a format-7
store. What waits on ember: nothing new beyond the three decisions
recorded as D29 to D31 (all taken).

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
