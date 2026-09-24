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
  interrupted-fragment case pass on it; every other native module ran later
  ([native subsets](evidence/native-subsets-1a9dd747-2026-09-24.md)). Before it, [`863c2141`](evidence/863-native-cut-2026-09-24.md).
- **Live node:** hbox `/tank/fn/node` on `47bdb9a4` since 17:30 UTC
  ([node record](evidence/node-hbox-47bdb9a4-2026-09-24.md)), upgraded in
  place with the store kept; `fn-da5fd8cb` stays beside it for rollback.
- **Final cut:** source `8a1b31f9` failed combined certification on three
  roots, so no image was built ([final record](evidence/final-cut-8a1b31f9-2026-09-24.md);
  handoff, "Final cut"):

| Red root | Failure | Lane |
| --- | --- | --- |
| `books/bp-node-progress-guards` | guard of `fn-bpnp-issued-debt-delta` lacks the base-state premise | bp-progress-guards |
| `books/bp-node-progress-selection-invariants` | `fn-bpnp-step-progress-preserves-held-and-issued`, non-clock `:progress` Subgoal 40.2' | bp-selection-invariant |
| `tests/acl2/bp-node-machine-teeth-tests` | blocked by the uncertified selection include, not its own counterexample | follows bp-selection-invariant |

## The goal now: v0 deployed, then the milestones (re-pointed 2026-09-24 ~11:30 EDT)

ember's correction: the v0 push had become an audit of the present state.
The plan's forward work is what the lanes point at from here, with the
[scoreboard](v0-scoreboard.md) as the check, not the goal:

1. **T0, the deployed node: done with `47bdb9a4`.** (Earlier text:) Cut image `6c0626c5` (every fix of today:
   signed ingress, W1 to W3, reconfiguration in ACL2, retention, recovery),
   all four images (default and DTN, production and developer), run the
   matrix, the cut campaign, the production kill campaign and every native
   module on it, then upgrade the hbox node in place with the store kept and
   the previous release retained. The node's page says which of P1 to P11
   hold on it.
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

**Landed since (each with its record and merge message):** p10-k0 and
p10-k0-b (K0 at 18 of 25 cuts, transcription check, four new cut selectors),
p6-crash-replay, p3-p5-followups, bp-recovery-sessions, bp-app-txid,
group-name-validity and group-names-2 (NNT-009, PRF-071), p2-wire (W1 to W3,
`fn-own-finish` installed), campaign-production-kill (184 SIGKILLs, 0 torn),
t17-msgid-index (a whole-store guard check removed from every read), m6-web,
hybrid-feed-storm (an unenrolled author's 439, now logged), matrix-6c0626c5,
campaign-6c0626c5, native-subsets-6c0626c5. Second image `6c0626c5`: closure
green, all four images built, 25/25 cuts, probe 30/30 on the original rows,
matrix 123/32/2 with ONE regression that blocks deploy: a transit with a Path
identity is stored but answered 436 uncertain and the service exits
(`fn-own-completion-names-submission-p` compares the Path-prepended stored
payload with the offered octets). The DTN images cannot `store init`
(build-dtn.lisp never lds checkpoint-host.lisp).

Landed after that: transit-436 (the completion names the submission by the
stored octets; 235 with a Path identity), dtn-build-checkpoint (DTN images
`store init`; build-list check), m5-capacity (the transaction budget in ACL2,
headroom in `operator status`, `init --profile scale`; the deployed store's
budget is 128 with 7 used). Third cut `60862103` submitted with every fix.

Landed after that: bp-app-receive (the dropped ingress argument, a raw-arity
check that also caught `fn config check` exiting 4, refusal reasons logged,
`bp send` closes), matrix/campaign/native-subsets on `47bdb9a4` (all clean
for the server), and the deploy: **the hbox node runs `47bdb9a4`**
([record](evidence/node-hbox-47bdb9a4-2026-09-24.md)).

Landed after the deploy: m4-dtn-n08 (N08 exactly-once on the default
image; the DTN image lacks the node driver), stale-tests-2 (served crash
model against the stored octets; a refused start exits 5), commit-path-cost
(the POST commit's history search carried: commit CPU 20 -> 1 to 3 ms),
m5-profile-upgrade (offline development-to-scale upgrade with its byte
program and cuts, PRF-072), p8-signed-post (a signed POST over NNTP gets a
durable verdict through the transit classification).

**In flight:**

| Lane | Intended result |
| --- | --- |
| dtn-node-image | the DTN image runs the BP node (bp-node loaded), admits inbound bundles through the enrolled boundary, uncertain on a severed contact, same-identity retry |
| p10-k0-recovery | K0 over the seven recovery cuts (entry theorem from the scan) and the issued-link error arm |
| p11-machine-gaps | N07 (clock boot domain) and N11 (kind-14 conflict record) added to the machine with theorems and teeth |
| commit-path-2 | fn-sf-next-lower in prepare and the advance's node check carried; fn-ocl-relation across an article completion |
| second-count | the transaction file name from ACL2's sequence; the payload bound from the profile; the host counter and constant gone |

Next cut (the fifth) follows the DTN node lane; it carries everything since
`47bdb9a4` and is the image on which the deployed store's profile upgrade runs.

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
