# Restart record — Claude night of 2026-09-24

The successor to the [wind-down handoff](handoff-2026-09-24-winddown.md).
Claude took the checkout at 07:25 UTC (03:25 EDT) when gpt-6 wrote
`ALLDONE.marker` at dev `46f2660d`, and ran the night ember set as a goal on
Claude Opus 5.5 lanes (thirteen lanes, each in `build/lanes/<name>` from a
named revision; Claude Fable coordinated, reviewed and merged). Everything
below is on dev and pushed. [Now](now.md) is the entry page and carries the
lane table.

## What the night is judged by, and the numbers

1. **A frozen image past `863c2141`.** [`1a9dd747`](evidence/native-cut-1a9dd747-2026-09-24.md):
   combined closure of all 656 roots green at `9c344d1d` (books identical),
   315 newly certified and 343 installed at exact bytes, 0 failed, 348.9 s at
   four jobs (manifests `certify-20260924T094824Z-1155517`,
   `certify-20260924T100056Z-1167472`); production and developer image pair
   built; BP N03 PASS (log `81a7d9e2…`), interrupted fragment PASS
   (`ba9215f8…`), consumer E2 PASS (`081ab2d9…`). The three roots red at
   `8a1b31f9` are green. Gate `/tank/fn/gates/qual-1a9dd747-20260924`.
2. **The two-Store join** ([record](evidence/two-store-join-1a9dd747-2026-09-24.md)):
   signed peering into Mini consumption, report → ACK → signed reply →
   restart → read, EXCHANGE COMPLETE on that image with no cut and under all
   four cut families (`a-accepted`, `b-verdict`, `ack-response`, `reply-at-b`);
   the lost-ACK cut answered UNCERTAIN and settled. Harness
   `tools/runbooks/two_store_join.py`.
3. **Proof cost.** The ten-second baseline
   (`planning/proof-cost-baseline.json`) went from 37 books to 19; the five
   2x regressions (replay, store-identity-sequence-invariants,
   consumer-store-invariants, store-node-invariants, store-node-traces) are
   back under their earlier times, all from one leak, `fn-th-topic-eventp`
   left enabled at export ([record](evidence/topic-recognizer-proof-cost-2026-09-24.md));
   `tools/proof_cost.py` and `tools/certified_claims.py` exit 1 in `make check`
   on a regression, a missing citation or a moved closure.
4. **Planning.** [now.md](now.md) is the one entry page; the takeover, Codex
   handoff, workstream review, capability wave, assurance snapshot, evidence
   index and old board are in `archive/`; `decisions.md` has the 09-24
   entries; 62 landed lane worktrees were retired with every tip kept
   ([record](evidence/worktree-retirement-2026-09-24-claude.md)).

## Findings that were not slow proofs

- `fn-bpnp-step-progress-preserves-held-and-issued` was **false** after the
  forwarding packet: a `:progress` event that selects a routed held row
  installs a pending dispatch. Replaced by two exact theorems with a routed
  witness and must-fail teeth (merge `d8aec8f2`).
- Two guards in `books/bp-node-progress.lisp` were **false under guard `t`**
  (forward-scan's `mru`, start-one's held list); they are now guard premises,
  never runtime checks (merge `c97572ae`). The served step provably preserves
  its premises (`fn-bpnp-step-preserves-guard-premises`, merge `e078b0aa`).
- The `9c344d1d` image build failed on a **host translate error** from the
  02:19 signed-transit commits (`fn-owner-clock-observation`, an error
  triple, used as one value). `make check` does not `ld` the host, so the
  image build was the first check to see it. Fixed in `1a9dd747`; a
  host-translate check in `make check` is owed.
- The ratchet's `--allow-regression` rebuilt the baseline from measured books
  only and would have dropped 22 unmeasured defects; fixed and tested
  (`9c344d1d`).

## What remains open

- 19 books over 10 s (owner-invariants 25 s, bp-node-foundation 17,
  bp-primary-invariants 16, nntp-auth-fold 15, ...); two cost lanes were on
  them at 07:00 EDT (see the lane table). `fn-th-local-admin-eventp` is still
  enabled at export; `store-node-traces` at 9.9 s has no margin.
- The step-premise corollaries carry the full premise set; splitting them
  into single-property theorems with their own teeth is the next experiment.
- The two-Store join uses the retained Mini E1 source and the E2 identity,
  and its cuts are command-boundary process deaths plus the developer image's
  feed-stop selector. Mini's branch is not merged to Mini main.
- No other native subset (topic v2, author lifecycle, pack retirement,
  checkpoint, the matrix) ran on `1a9dd747`. Live node `da5fd8cb` untouched;
  deploying `1a9dd747` is a separate decision.
- `bp-d1b` (15 commits, "Join durable BP application delivery to FNBS
  foundation") and ten other kept worktrees hold commits no record covers.
- `specs/bp-node-machine.md` has grown 115 lines since review 3 without a
  review round.

## How to restart

Read [now.md](now.md). Lanes brief from it, `how-we-work.md` and this file.
The qualification recipe is the one used tonight: detached checkout at the
revision, `farm.py submit hbox <656 roots> --jobs 4 --timeout-seconds 300
--remote-root /tank/fn/gates/qual-<rev>-<date>`, one wait, then the stage-2
script (image pair, then the native cases with `FN_ACL2` exported for the BP
authoring bridge). Harvest a lane's gitignored manifests before removing its
worktree.
