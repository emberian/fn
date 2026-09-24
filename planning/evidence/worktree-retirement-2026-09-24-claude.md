# Landed lane worktree retirement, 2026-09-24 (Claude lane)

Against `dev` `46f2660d`, 60 of 83 named candidate lane worktrees under
`build/lanes/` were removed with `git worktree remove` (never `--force`).
Every removed tip stays reachable from its own branch, from `dev`, or from a new
`archive/<name>` ref. No branch was deleted. This removes workspaces only; it
changes no model, native runtime, proof result or remote gate.

The disposition executed is the one in
[the disposition audit](worktree-disposition-2026-09-24.md),
[the convergence retirement](worktree-retirement-convergence-2026-09-24.md) and
[the final handoff retirement](worktree-retirement-final-handoffs-2026-09-24.md).
This lane did not re-decide it.

## Method

For each candidate, from the main repository:

- branch and tip from `git worktree list --porcelain`;
- dirt as the line count of `git -C <wt> status --porcelain --untracked-files=all`;
- reachability as `git merge-base --is-ancestor <tip> dev`. Otherwise
  `git cherry dev <tip>` gives the `+` (not patch-equivalent) and `-` counts,
  and each `+` commit's subject is looked up exactly in `git log --format=%s dev`.
  "Subject-unlanded" counts `+` commits whose subject is not on `dev`.

A worktree was removed only when it had no dirt at all, untracked files
included, and one of these held: its tip is an ancestor of `dev`; every `+`
commit is subject-landed (which includes having no `+` commit); or a disposition
record calls it integrated, adapted or superseded. Before removing a detached
worktree whose tip was not an ancestor of `dev`, `git branch archive/<name>
<tip>` was created. The tree was checked clean again immediately before
removal. After removal the branch or archive ref was resolved, and the tip was
checked to be its ancestor. `lsof` found no process with a working directory in
any candidate. The only processes were in the live lanes, which were not touched.

`git worktree remove` deletes ignored files, so they were copied first. Every
ignored file except ACL2 build products (`.cert`, `.port`, `.fasl`, `.out` and
similar) and `__pycache__` was copied: 6,865 files, about 93 MB.
Most of these are `build/acl2/certify-*` run directories, `build/farm`, raw
`build/*.log` files and 198 `planning/evidence/manifests/*.json` certification
manifests. Only 4 of them already existed byte-identically in the root checkout.
They were copied to the private local
`/Users/ember/dev/fn-worktree-archive/20260924/ignored-evidence-claude/<name>/`,
keeping their relative paths, and each file was then compared byte for byte
(0 mismatches). ACL2 certificates were not kept. They can be rebuilt, and native
freezes are qualified on hbox.

Records covering subject-unlanded commits: `byte-store-k568`,
`topic-store-base`, `topic-native-tail`, `topic-crash-bridge` and
`topic-maintained-bridge` are "adapted into dev or superseded by the active
successors". The audit says not to replay their positive `git cherry` commits.

## Table

| Worktree | Branch | Tip | Dirty | Reachability vs dev `46f2660d` | Disposition record | Action |
| --- | --- | --- | --- | --- | --- | --- |
| `assurance-review-followup` | `lane/assurance-review-followup` | `48b2133c` | 0 | 0 `+` (0 subject-unlanded), 2 `-` | not mentioned | removed; tip kept by `lane/assurance-review-followup`. Later ([kept branches](kept-worktrees-2026-09-24.md)): branch superseded |
| `assurance-status-refresh` | `docs/assurance-status-refresh` | `bcd7e607` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `docs/assurance-status-refresh` |
| `author-key-lifecycle` | `lane/author-key-lifecycle` | `a12f523e` | 0 | 3 `+` (0 subject-unlanded), 1 `-` | evidence tip patch-equivalent; source/proof in dev | removed; tip kept by `lane/author-key-lifecycle`. Later ([kept branches](kept-worktrees-2026-09-24.md)): branch superseded |
| `bp-a1-selection-assurance` | `DETACHED` | `f81f429b` | 0 | 4 `+` (0 subject-unlanded), 9 `-` | owner: integrated/superseded | removed; tip kept by `archive/bp-a1-selection-assurance` |
| `bp-counterexample-completion` | `DETACHED` | `24508145` | 0 | ancestor | not mentioned | removed; tip kept by `dev` |
| `bp-d1b` | `implement/bp-d1b` | `846b5d13` | 0 | 32 `+` (15 subject-unlanded), 2 `-` | not mentioned | kept: unlanded-uncovered |
| `bp-debt-cache-correspondence` | `DETACHED` | `ceb1895d` | 0 | 1 `+` (0 subject-unlanded), 11 `-` | handoff; untracked draft must not merge (draft since removed by owner) | removed; tip kept by `archive/bp-debt-cache-correspondence` |
| `bp-debt-n05` | `DETACHED` | `c4f5e921` | 0 | 1 `+` (0 subject-unlanded), 2 `-` | not mentioned | removed; tip kept by `archive/bp-debt-n05` |
| `bp-forward-dispatch` | `implement/bp-forward-dispatch` | `c6142184` | 0 | 3 `+` (0 subject-unlanded), 0 `-` | not mentioned | removed; tip kept by `implement/bp-forward-dispatch` |
| `bp-fragment-activate-current` | `implement/bp-fragment-activate-current` | `856274e1` | 0 | ancestor | not mentioned | removed; tip kept by `implement/bp-fragment-activate-current` |
| `bp-fragment-expiry-pure` | `implement/bp-fragment-expiry-pure` | `5c7f671c` | 0 | 1 `+` (0 subject-unlanded), 0 `-` | not mentioned | removed; tip kept by `implement/bp-fragment-expiry-pure` |
| `bp-fragment-native-trust` | `fix/bp-fragment-native-trust` | `5ad7b23e` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | owner: integrated/superseded | removed; tip kept by `fix/bp-fragment-native-trust` |
| `bp-progress-engine` | `implement/bp-progress-engine` | `55bb346c` | 0 | 2 `+` (0 subject-unlanded), 13 `-` | not mentioned | removed; tip kept by `implement/bp-progress-engine` |
| `bp-reopen-proof` | `fix/bp-observed-reopen` | `cc60c97f` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `fix/bp-observed-reopen` |
| `bp-union-proof` | `fix/bp-union-proof` | `3d1a461e` | 0 | 4 `+` (0 subject-unlanded), 2 `-` | BP union: adapted or superseded | removed; tip kept by `fix/bp-union-proof` |
| `byte-store-k568` | `implement/byte-store-k568` | `af679760` | 0 | 24 `+` (7 subject-unlanded), 3 `-` | adapted into dev or superseded | removed; tip kept by `implement/byte-store-k568` |
| `byte-store-k6-cost` | `fix/byte-store-k6-cost` | `8b71f6e6` | 0 | 1 `+` (0 subject-unlanded), 4 `-` | not mentioned | removed; tip kept by `fix/byte-store-k6-cost` |
| `byte-store-native-topic` | `fix/byte-store-native-topic` | `9c0b393e` | 0 | 2 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `fix/byte-store-native-topic` |
| `certified-claims-audit` | `lane/certified-claims-audit` | `ff81313e` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `lane/certified-claims-audit`. Later ([kept branches](kept-worktrees-2026-09-24.md)): branch superseded |
| `consumer-envelope` | `implement/consumer-envelope` | `f3428a7d` | 0 | 1 `+` (0 subject-unlanded), 0 `-` | f3428a7d integrated as eba44cb4 | removed; tip kept by `implement/consumer-envelope` |
| `consumer-finish-composed` | `fix/consumer-finish-composed` | `368bf7ee` | 0 | 1 `+` (0 subject-unlanded), 5 `-` | not mentioned | removed; tip kept by `fix/consumer-finish-composed` |
| `consumer-index-topic` | `implement/consumer-index-topic` | `5443e9b6` | 0 | 1 `+` (0 subject-unlanded), 0 `-` | consumer index: adapted or superseded | removed; tip kept by `implement/consumer-index-topic` |
| `consumer-kernel` | `implement/consumer-kernel` | `306f62d9` | 0 | 7 `+` (5 subject-unlanded), 5 `-` | not mentioned | kept: unlanded-uncovered |
| `consumer-poll-factor` | `fix/consumer-poll-factor` | `1579d3b7` | 0 | 0 `+` (0 subject-unlanded), 2 `-` | not mentioned | removed; tip kept by `fix/consumer-poll-factor` |
| `consumer-poll-host-fix` | `fix/consumer-poll-request` | `2ce86ca3` | 0 | 1 `+` (0 subject-unlanded), 10 `-` | not mentioned | removed; tip kept by `fix/consumer-poll-request` |
| `consumer-topic-trace` | `lane/consumer-topic-trace` | `45566a16` | 0 | 0 `+` (0 subject-unlanded), 4 `-` | not mentioned | removed; tip kept by `lane/consumer-topic-trace`. Later ([kept branches](kept-worktrees-2026-09-24.md)): branch superseded |
| `consumer-topic-trace-evidence` | `lane/consumer-topic-trace-evidence` | `f0abd74c` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `lane/consumer-topic-trace-evidence`. Later ([kept branches](kept-worktrees-2026-09-24.md)): branch superseded |
| `human-durable-outbox` | `feature/human-durable-outbox` | `13e7032d` | 0 | 1 `+` (0 subject-unlanded), 3 `-` | not mentioned | removed; tip kept by `feature/human-durable-outbox` |
| `image-0143-snapshot` | none | none | n/a | not a registered git worktree | not mentioned | kept: plain directory, outside `git worktree remove` |
| `image-1d26-snapshot` | none | none | n/a | not a registered git worktree | not mentioned | kept: plain directory, outside `git worktree remove` |
| `image-4f66-snapshot` | none | none | n/a | not a registered git worktree | not mentioned | kept: plain directory, outside `git worktree remove` |
| `image-a8e4-snapshot` | none | none | n/a | not a registered git worktree | not mentioned | kept: plain directory, outside `git worktree remove` |
| `image-bc9-snapshot` | none | none | n/a | not a registered git worktree | not mentioned | kept: plain directory, outside `git worktree remove` |
| `image-c1bb-snapshot` | none | none | n/a | not a registered git worktree | not mentioned | kept: plain directory, outside `git worktree remove` |
| `ion-observation-binding` | `feature/ion-observation-binding` | `7d49ce2c` | 0 | 1 `+` (0 subject-unlanded), 3 `-` | handoff | removed; tip kept by `feature/ion-observation-binding` |
| `luna-feature-consumer-status` | `implement/luna-consumer-status` | `e0066871` | 0 | 0 `+` (0 subject-unlanded), 6 `-` | not mentioned | removed; tip kept by `implement/luna-consumer-status` |
| `luna-feature-cursor-inspect` | `implement/luna-feature-cursor-inspect` | `28f49e0f` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `implement/luna-feature-cursor-inspect` |
| `luna-feature-review` | `lane/luna-feature-review` | `8ab153a4` | 0 | 2 `+` (1 subject-unlanded), 16 `-` | not mentioned | kept: unlanded-uncovered. Later ([kept branches](kept-worktrees-2026-09-24.md)): superseded; worktree to remove |
| `luna-feature-web-pages` | `luna-feature-web-pages` | `90fbe689` | 0 | 0 `+` (0 subject-unlanded), 5 `-` | not mentioned | removed; tip kept by `luna-feature-web-pages` |
| `luna-owner-config-cost` | `lane/luna-owner-config-cost` | `e548b15b` | 1 (planning/evidence/owner-config-proof-cost-luna-2026-09-24.md) | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | kept: dirty. Later ([kept branches](kept-worktrees-2026-09-24.md)): superseded, dirt saved; worktree to remove with `--force` |
| `luna-owner-config-cost-4b` | `lane/luna-owner-config-cost-4b` | `c332ed5d` | 0 | 0 `+` (0 subject-unlanded), 2 `-` | not mentioned | removed; tip kept by `lane/luna-owner-config-cost-4b`. Later ([kept branches](kept-worktrees-2026-09-24.md)): branch superseded |
| `luna-trial-docs` | `lane/luna-trial-docs` | `f3ec7227` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `lane/luna-trial-docs`. Later ([kept branches](kept-worktrees-2026-09-24.md)): branch superseded |
| `mini-p2-portable` | `implement/mini-p2-portable` | `36869776` | 0 | 4 `+` (2 subject-unlanded), 11 `-` | not mentioned | kept: unlanded-uncovered |
| `native-863-freeze` | `DETACHED` | `4764d923` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | owner: integrated/superseded | removed; tip kept by `archive/native-863-freeze` |
| `native-b074-freeze` | `DETACHED` | `564d0e6a` | 0 | 0 `+` (0 subject-unlanded), 2 `-` | owner: integrated/superseded | removed; tip kept by `archive/native-b074-freeze` |
| `native-block-profile` | `implement/native-block-profile` | `042c3fb0` | 0 | 0 `+` (0 subject-unlanded), 2 `-` | handoff (unmerged at 06:34 snapshot) | removed; tip kept by `implement/native-block-profile` |
| `native-consumer-e2` | `test/native-consumer-e2` | `7822ef44` | 0 | 7 `+` (5 subject-unlanded), 11 `-` | not mentioned | kept: unlanded-uncovered |
| `native-consumer-status-codec` | `prove/native-consumer-status-codec` | `7de34b36` | 0 | ancestor | not mentioned | removed; tip kept by `prove/native-consumer-status-codec` |
| `native-d1b-host-repair` | `fix/native-d1b-host-repair` | `e7475075` | 0 | 0 `+` (0 subject-unlanded), 2 `-` | not mentioned | removed; tip kept by `fix/native-d1b-host-repair` |
| `native-d1b-test-order` | `native-d1b-test-order` | `cbd67ffb` | 0 | 0 `+` (0 subject-unlanded), 2 `-` | not mentioned | removed; tip kept by `native-d1b-test-order` |
| `native-f0d-qual` | `native-f0d-qual` | `0a69ab6f` | 0 | 0 `+` (0 subject-unlanded), 4 `-` | not mentioned | removed; tip kept by `native-f0d-qual` |
| `native-final-freeze` | `DETACHED` | `c7a02278` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `archive/native-final-freeze` |
| `native-ltp-boundary` | `feature/native-ltp-boundary` | `d396a520` | 0 | 0 `+` (0 subject-unlanded), 2 `-` | patch-equivalent | removed; tip kept by `feature/native-ltp-boundary` |
| `native-opc-advance-repair` | `fix/native-opc-advance-repair` | `e4624ed6` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `fix/native-opc-advance-repair` |
| `native-topic-index-qual` | `native-topic-index-qual` | `855f5d30` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `native-topic-index-qual` |
| `owner-v6-cost` | `fix/owner-v6-cost` | `6e448ae9` | 0 | 0 `+` (0 subject-unlanded), 3 `-` | not mentioned | removed; tip kept by `fix/owner-v6-cost` |
| `pack-gap-publication` | `fix/pack-gap-publication` | `28d50703` | 0 | 1 `+` (0 subject-unlanded), 0 `-` | handoff (unmerged at 06:34 snapshot) | removed; tip kept by `fix/pack-gap-publication` |
| `preservation-recovery` | `implement/native-preservation-recovery` | `6855a7df` | 0 | 2 `+` (0 subject-unlanded), 1 `-` | owner: integrated/superseded | removed; tip kept by `implement/native-preservation-recovery` |
| `proof-cost-freshness-lint` | `agent/proof-cost-freshness-lint` | `608f02a5` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `agent/proof-cost-freshness-lint` |
| `proof-repl-composed` | `repair/topic-gate-8c61` | `006a75a2` | 0 | ancestor | not mentioned | removed; tip kept by `repair/topic-gate-8c61` |
| `reclaim-active-reader` | `test/reclaim-active-reader` | `970c4f85` | 0 | 2 `+` (0 subject-unlanded), 1 `-` | content-integrated (7326b70f, 970c4f85) | removed; tip kept by `test/reclaim-active-reader` |
| `storage-k0-completion` | `implement/storage-k0-completion` | `037355bf` | 2 (planning/ledger.json, planning/ledger.md) | 3 `+` (1 subject-unlanded), 17 `-` | not mentioned | kept: dirty |
| `storage-k0-failure` | `implement/storage-k0-failure` | `037419f8` | 0 | 0 `+` (0 subject-unlanded), 2 `-` | not mentioned | removed; tip kept by `implement/storage-k0-failure` |
| `storage-topic-reopen` | `fix/byte-store-topic-reopen` | `b4ec1807` | 0 | 1 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `fix/byte-store-topic-reopen` |
| `store-identity-topic-gate` | `fix/store-identity-topic-gate` | `05ab5f18` | 0 | 0 `+` (0 subject-unlanded), 1 `-` | not mentioned | removed; tip kept by `fix/store-identity-topic-gate` |
| `topic-admin-generation-v2` | `implement/topic-admin-generation-v2` | `6ffe9294` | 0 | 1 `+` (0 subject-unlanded), 2 `-` | owner: integrated/superseded (admin-generation adapted) | removed; tip kept by `implement/topic-admin-generation-v2` |
| `topic-assurance` | `implement/topic-assurance` | `76ecea41` | 0 | 2 `+` (1 subject-unlanded), 1 `-` | not mentioned | kept: unlanded-uncovered |
| `topic-candidate-sequence` | `prove/topic-candidate-sequence` | `838bcba9` | 0 | 1 `+` (1 subject-unlanded), 0 `-` | not mentioned | kept: unlanded-uncovered |
| `topic-crash-bridge` | `implement/topic-crash-bridge` | `2fd3d960` | 0 | 4 `+` (4 subject-unlanded), 0 `-` | adapted or superseded | removed; tip kept by `implement/topic-crash-bridge` |
| `topic-identity-disjoint` | `prove/topic-identity-disjoint` | `d412dfbb` | 0 | 5 `+` (3 subject-unlanded), 4 `-` | not mentioned | kept: unlanded-uncovered |
| `topic-index-native` | `integrate/topic-index-native` | `8ed5ec1b` | 0 | ancestor | not mentioned | removed; tip kept by `integrate/topic-index-native` |
| `topic-maintained-bridge` | `prove/topic-maintained-bridge` | `a409d238` | 0 | 12 `+` (12 subject-unlanded), 0 `-` | owner: integrated/superseded | removed; tip kept by `prove/topic-maintained-bridge` |
| `topic-native-tail` | `integrate/topic-native-tail` | `26278201` | 0 | 12 `+` (6 subject-unlanded), 9 `-` | adapted or superseded | removed; tip kept by `integrate/topic-native-tail` |
| `topic-next-slice` | `implement/topic-next-slice` | `5f202410` | 0 | 1 `+` (0 subject-unlanded), 4 `-` | content-integrated (c80d1113 guard in dev) | removed; tip kept by `implement/topic-next-slice` |
| `topic-recovery-selectors` | `prove/topic-recovery-selectors` | `41c95888` | 0 | 4 `+` (4 subject-unlanded), 0 `-` | not mentioned | kept: unlanded-uncovered |
| `topic-replay-proof` | `implement/topic-replay-proof` | `2d596500` | 0 | 3 `+` (2 subject-unlanded), 1 `-` | not mentioned | kept: unlanded-uncovered |
| `topic-store-base` | `integrate/topic-store-base` | `8c816cb6` | 0 | 8 `+` (5 subject-unlanded), 2 `-` | topic base: adapted or superseded | removed; tip kept by `integrate/topic-store-base` |
| `topic-store-join` | `implement/topic-store-join` | `4095511e` | 8 (planning/ledger.json, planning/ledger.md, planning/milestones.md, planning/proof-events.json, planning/proofs.json) | 7 `+` (3 subject-unlanded), 7 `-` | superseded old alternative; do not apply overlay without contract diff | kept: dirty |
| `topic-v2-crash-teeth` | `prove/topic-v2-crash-teeth` | `4f1222a5` | 0 | 11 `+` (11 subject-unlanded), 0 `-` | handoff to maintained-topic owner; root to review | kept: unlanded-uncovered |
| `w5-clock-seam` | none | none | n/a | not a registered git worktree | not mentioned | kept: plain directory, outside `git worktree remove` |
| `w9-reconfig` | none | none | n/a | not a registered git worktree | not mentioned | kept: plain directory, outside `git worktree remove` |
| `w9-server-polish` | none | none | n/a | not a registered git worktree | not mentioned | kept: plain directory, outside `git worktree remove` |
| `worktree-disposition-audit` | `audit/worktree-disposition-20260924` | `e83242e7` | 0 | 0 `+` (0 subject-unlanded), 3 `-` | not mentioned | removed; tip kept by `audit/worktree-disposition-20260924` |

## Outcome

- **Removed: 60.** 53 were preserved by their own branch, 1 by `dev`
  (detached `bp-counterexample-completion`, an ancestor of dev) and 6 by new
  archive refs.
- **Archive refs created (6):** `archive/bp-a1-selection-assurance` `f81f429b`,
  `archive/bp-debt-cache-correspondence` `ceb1895d`, `archive/bp-debt-n05`
  `c4f5e921`, `archive/native-863-freeze` `4764d923`,
  `archive/native-b074-freeze` `564d0e6a`, `archive/native-final-freeze`
  `c7a02278`. `bp-debt-cache-correspondence` was clean, so the unadmitted
  draft was already gone, as the convergence record says. The archive ref keeps
  its committed tip, and nothing from it was merged.
- **Kept: 23.**
  - 3 dirty: `luna-owner-config-cost` (1 line), `storage-k0-completion` (2),
    and `topic-store-join` (8 lines of planning/spec overlay, which must not
    be applied without a contract-level diff).
  - 11 clean but with subject-unlanded commits that no record covers:
    `bp-d1b` (15), `consumer-kernel` (5), `native-consumer-e2` (5),
    `topic-identity-disjoint` (3), `topic-recovery-selectors` (4),
    `topic-replay-proof` (2), `topic-v2-crash-teeth` (11; the records only
    say it was handed off), `mini-p2-portable` (2, ledger regeneration only),
    `luna-feature-review` (1, trial record), `topic-assurance` (1) and
    `topic-candidate-sequence` (1). Many of these topic commits are shared with
    the superseded topic lineage, but they were kept because no record names
    these trees.
  - 9 not registered as git worktrees, so `git worktree remove` does not apply:
    `image-{0143,1d26,4f66,a8e4,bc9,c1bb}-snapshot` (76 to 82 MB exported
    source trees without `.git`) and `w5-clock-seam`, `w9-reconfig`,
    `w9-server-polish` (empty `build/` skeletons under 8 KB).
- `git worktree prune` was run afterwards. `git worktree list | wc -l` gives
  **22**: the root, the 14 kept registered candidates, and the live lanes
  `bp-codec-cost`, `bp-progress-guards`, `bp-selection-invariant`,
  `check-ratchet`, `plan-consolidate`, `proof-cost-regressions` and
  `worktree-retire`. None of the live lanes was touched.

## Later status

The [kept-branch disposition](kept-worktrees-2026-09-24.md) (against `dev`
`00d291d0`) found that every commit on the fifteen `lane/*` branches still
ahead of `dev` is carried on `dev` by a cherry-picked commit with the same subject. The Action cells
above mark those rows. Of this table's kept worktrees, `luna-feature-review`
and `luna-owner-config-cost` are now ready to remove. The other kept trees were
outside that lane's scope.
