# Kept lane branches, disposition, 2026-09-24 (Claude lane)

Against `dev` `00d291d0`, each of the fifteen `lane/*` branches with commits
ahead of `dev` was checked three ways: `git cherry dev <branch>` for patch
equivalence; an exact subject lookup of every `dev..<branch>` commit in
`git log dev`; and a trial `git merge --no-commit --no-ff` into this lane,
aborted afterwards. Every branch commit has a same-subject commit on `dev`'s
first-parent line, so each change was landed by cherry-pick rather than by a
merge of the branch. That is why the branches still show commits ahead. The
trial merges add nothing: they are empty, or they conflict only where `dev` has
since moved on (archived `planning/*` files, regenerated ledgers, later edits
to `tools/proof_cost.py` and the Makefile). No branch needed landing, so this
lane merged nothing, changed no book and ran no farm job.

Where `git cherry` reports `+`, the difference was checked by hand:

- `author-key-lifecycle` `345dbdba`, `37730f4d` and `b3c4b0d3`: the `dev`
  commits `23173cf6`, `495e372a` and `6a410fe2` have the same file set, apart
  from `planning/ledger.{json,md}`. Those are generated, and `tools/ledger.py`
  regenerates them on `dev`. The only other difference is one `catalog.json`
  scope sentence and two evidence paths that `dev` holds in a newer form.
- `luna-feature-review` `8ab153a4`: its `dev` counterpart `99081da3` carries
  the same eight files. Its trial record is the rewritten final text, 181 lines
  where the branch has 152.
- `luna-feature-review` `eac1dfa3` ("Record web and cursor trial packets and
  review costs") has no same-subject commit. All but three of its added lines
  appear verbatim in `dev`'s `planning/experiments/luna-feature-trial-2026-09-24.md`.
  The three missing lines describe a navigation repair whose "result is
  pending"; the final record states that result.

## Table

| Branch | Ahead | `cherry +` | Worktree | Disposition | Carried on dev by | Merged here |
| --- | --- | --- | --- | --- | --- | --- |
| `lane/assurance-review-followup` | 2 | 0 | removed | superseded | `95a96d27`, `80f3ff31` | nothing |
| `lane/assurance-status-0924` | 1 | 0 | none | superseded | `99725808` (file since archived to `planning/archive/`) | nothing |
| `lane/author-key-lifecycle` | 4 | 3 | removed | superseded | `23173cf6`, `495e372a`, `6a410fe2`, `a4db1894` (differences are the regenerated ledger only) | nothing |
| `lane/certified-claims-audit` | 1 | 0 | removed | superseded | `0cae6df4` | nothing |
| `lane/certify-live-observability` | 1 | 0 | none | superseded | `6f616b13` (trial merge empty) | nothing |
| `lane/consumer-topic-trace` | 4 | 0 | removed | superseded | `9d888404`, `5a908e9e`, `83aa99ec`, `dfdefda8` (trial merge empty) | nothing |
| `lane/consumer-topic-trace-evidence` | 1 | 0 | removed | superseded | `e012529a` (trial merge empty) | nothing |
| `lane/dregg-os-architect` | 4 | 0 | none | design-only, already on dev | `bb729e5b`, `4c473b74`, `26f17986`, `275bdef7`; `dev` also updated the link to the archived takeover | nothing |
| `lane/farm-status-live` | 2 | 0 | none | superseded | `c3955777`, `0f3b9de5` (trial merge empty) | nothing |
| `lane/luna-feature-review` | 18 | 2 | **kept, clean** | superseded | 16 same-patch commits (for example `550b4faa`, `f3ca9007`, `c66f85e2`, `3dac710b`), `99081da3`; `eac1dfa3` absorbed into the final trial record | nothing |
| `lane/luna-owner-config-cost` | 1 | 0 | **kept, dirty (1 file)** | superseded | `5a947e25`; the uncommitted edit is an earlier draft of the text `eb2c55fd` landed | nothing |
| `lane/luna-owner-config-cost-4b` | 2 | 0 | removed | superseded | `dfc4c384` (book hint, certified in manifest `certify-20260924T010818Z-669581`), `eb2c55fd` | nothing |
| `lane/luna-trial-docs` | 1 | 0 | removed | superseded | `8c61c098` | nothing |
| `lane/proof-cost-history` | 1 | 0 | none | superseded | `af47c79a` | nothing |
| `lane/retention-prepare-guard` | 1 | 0 | none | superseded | `dac8a609` (trial merge empty) | nothing |

No branch is obsolete. Every change is on `dev`, so none needs archiving.

## The design-only branch

`lane/dregg-os-architect` wrote a single file,
[`planning/dregg-os-integration-2026-09-23.md`](../dregg-os-integration-2026-09-23.md).
It is already on `dev` and belongs there as a proposal. It is not a
requirement, so it does not go into the specs or the registries. It proposes
making fn the correspondence substrate for independently administered dregg
nodes: authored requests, reports, evidence, dependencies and replies stay
durable while an agent or its host sleeps. The first integration would target
Mini's existing native resource receiver, with Bread's mailbox, workflow and
federation paths serving as compatibility references. The first artifact would
be a real Mini native operation and its original accepted-prefix receipt,
carried in an fn report and checked independently by a second Mini consumer.
The second artifact is that consumer's durable decision and reply. The design
separates topics, which are autonomous application histories with their own
authority, policy lineage and portable identities, from fn groups, which are
only their transport and routing projection. Local article numbers and Store
positions are never topic identity or consensus. The contract has four parts:
a typed evidence envelope outside fn semantics, a Mini-owned processing
transaction, a distinct receipt at each boundary, and scheduling triggered by a
durable decision rather than by arrival. It lists implementation packets,
discriminating experiments and the decisions to raise when each packet is
reached. Nothing in it is scheduled in `planning/now.md`. Only archived records
and `planning/topic-history-p3-2026-09-23.md` link to it. Retiring the branch
loses nothing.

## Retirement commands (coordinator)

The uncommitted diff in `build/lanes/luna-owner-config-cost` was saved to
`/Users/ember/dev/fn-worktree-archive/20260924/dirty-kept-worktrees/luna-owner-config-cost.patch`
(89 lines, SHA-256 `379f616f559ac2d77fa51ea12836e1d7e227fa49562ff349a44c08fa904018e8`).
It is a pre-certification draft of the owner-config trial record, and the
certified version is on `dev`. Removing that worktree therefore needs
`--force`.

```sh
cd /Users/ember/dev/fn
git worktree remove build/lanes/luna-feature-review
git worktree remove --force build/lanes/luna-owner-config-cost
# Optional: keep the tips reachable before deleting branches.
for b in assurance-review-followup assurance-status-0924 author-key-lifecycle \
         certified-claims-audit certify-live-observability consumer-topic-trace \
         consumer-topic-trace-evidence dregg-os-architect farm-status-live \
         luna-feature-review luna-owner-config-cost luna-owner-config-cost-4b \
         luna-trial-docs proof-cost-history retention-prepare-guard; do
  git branch -f "archive/$b" "lane/$b" && git branch -D "lane/$b"
done
```

Drop the `git branch -f archive/...` half to delete outright. The patch
content of every branch is on `dev`. Only superseded drafts and ledger
regenerations would become unreachable.
