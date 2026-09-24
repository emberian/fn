# Consolidation handoff — 2026-09-24

This is the restart entry point for the user-requested wind-down begun at
06:23 UTC. The full project goal remains unfinished. This record distinguishes
integrated source from the exact images exercised; the later final-cut section
will record the result of the last bounded convergence run.

## What to keep

The live hbox service at `/tank/fn/node` remains on `da5fd8cb`. Nothing in this
wave authorizes replacing it with an experimental image. Shared qualification
uses disposable Stores and immutable gates. Keep the gates, raw logs and
content-matched certificate caches on both hbox and persvati.

The last completed shared image at this checkpoint is
[`863c2141`](evidence/863-native-cut-2026-09-24.md). Its combined ACL2 closure
and production/developer builds passed. Native consumer lost-ACK/reopen,
local author lifecycle, and topic v1-to-v2 cases passed within their recorded
scope. It exposed two real caller defects: BP transit passed identity strings
to an octet-list conversion, and later pack publication still required a
gap-free namespace after retirement. Both have source fixes on dev; that
image does not qualify them.

## Integrated capabilities and their limits

- [Receiver-local signed ingress](evidence/peer-authored-ingress-2026-09-24.md)
  joins NNTP and BP through one acceptance helper. Present-invalid carriers
  cannot fall through to unsigned acceptance; fresh native acceptance binds
  exact source, current local enrollment and both primitive observations to a
  durable kind-4 record. Scoped ACL2, actual-function host regressions and real
  OpenSSL 3.5.8 component tests passed. A duplicate already held as legacy
  remains legacy: it does not acquire an invented acceptance-time verdict.
  Saved-image receiver restart and consumer projection are the next seam.
- [Local author lifecycle](evidence/author-key-lifecycle-2026-09-24.md) adds
  per-principal key rotation/revocation and preserves historical verdicts
  through the covered Store finish/recovery paths. This is not portable
  cross-administrator succession or an all-phase crash induction.
- [ION binding](evidence/ion-observation-binding-2026-09-24.md) persists an
  FNWF attempt and route before submission, then binds the helper's actual
  bundle observation to that attempt in ACL2. The parser, codecs and selected
  composite proofs passed. Native image execution, death/reopen testing and
  authenticated receipt return remain open. A local ION send observation is
  not a remote acceptance or release receipt.
- [Retention publication](evidence/k0-retention-record-directory-2026-09-24.md)
  uses the shared statement decoder and covers the typed record-directory
  EIO apply/drop cut, together with the actual owner preparation bridge.
  The served-entry byte relation, every publication/crash path and their
  physical correspondence are still separate obligations.
- [Maintained topic relation](evidence/topic-maintained-store-bridge-2026-09-24.md)
  now covers additional actual prepare/refusal transitions. Full outer
  transition/crash induction and the known-abort completion selector remain
  open; the partial theorem family must not be advertised as that induction.
- [Preservation](evidence/native-pack-retire-863-2026-09-24.md) has native
  retirement/active-reader evidence and a source repair for the later-pack
  namespace failure. The [private block campaign](evidence/t16-private-publication-profile-2026-09-24.md)
  exercised record-directory EIO, process death and simulated volatile-write
  loss. These bounded disposable-device observations do not establish every
  real power-loss outcome or every storage platform.
- The separate human client has durable drafts/outbox and lost-response
  handling exercised in the [b074 cut](evidence/b074-native-cut-2026-09-24.md).
  It remains separate from the native server process.

## Mini work is committed separately

Mini's isolated `implement/fn-evidence` branch at
`183cd3769a443dbefde67891f42186f12fa610d5` contains A-side durable reply
consumption, exact Q correlation, atomic inbox/result publication, reopen
export and ACK gating. Its checkout is
`/Users/ember/dev/minidregg-wt/fn-evidence`. `lake build minidregg-host` and the
retained negative-correlation check passed; the candidate executable digest is
`0cce4fbd02c5b5156fb061e2d96f2e25e12588c35b59d2fd2efe20acb202f286`.
It has not been merged to Mini main, pushed, or qualified by a complete
two-Store report/receipt/reply run. Its own
`docs/FN-E1E2-TWO-STORE-2026-09-24.md` is the detailed handoff.

The earlier preflight found a real missing receiver verdict, and Mini correctly
refused the legacy projection. Preserve that negative result. Once fresh
signed reception, restart and projection pass on fn, qualify the new Mini
binary through the complete exchange with explicit crash cuts; do not compose
two independently demonstrated legs into an end-to-end claim.

## How to restart

Read the final-cut result below before launching any test. Reuse its exact
source/toolchain evidence. Then prioritize the actual end-to-end joins:
fresh signed peering into Mini consumption; durable BP forwarding across a
contact loss and restart; and storage publication/recovery correspondence.
Keep stronger proofs paired with those called paths rather than accumulating
sibling helper theorems.

Proof cost remains a defect: the 863 run includes an 82-second consumer index
book, a 68-second checkpoint book and a 56-second identity sequence book.
Those are measured book times, not a reason to enlarge the timeout. Start
with their event logs and bounded REPL questions. Farm root selection stays
incremental, four combined jobs and at most two per lane within the shared
pools. Do not repeat an already successful closure.

The [worktree disposition](evidence/worktree-disposition-2026-09-24.md)
distinguishes pending current packets from historical adapted alternatives.
Positive `git cherry` output alone does not justify re-merging an old branch.
Unadmitted BP symbolic-cache work is a draft, not compiled assurance. Preserve
old drafts privately when archiving, keep branch/tip references and verify all
file bytes and symlink targets before removing a worktree.

## Final cut

Pending the finite BP packet and one shared convergence run. Until this section
is updated, `863c2141` is the latest completed shared image described here,
and later source must retain its unqualified boundaries.
