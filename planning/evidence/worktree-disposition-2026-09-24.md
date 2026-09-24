# fn worktree disposition at convergence

Read-only inventory against `dev` `4502f698` at 06:34 UTC, 2026-09-24. This
updates [the earlier workstream review](../workstream-review-2026-09-24.md)
and [worktree recovery record](../worktree-recovery-2026-09-24.md); it does not
authorize deleting any worktree or merging a historical branch. There were 82
attached fn worktrees at the snapshot. The 101 previously archived trees and
their retained branch refs are historical inventory, not 101 unmerged packets.
I used `git worktree list`, branch ancestry and `git cherry`, commit diffs and
current source comparison, without changing another lane's checkout. `git
cherry +` alone does not mean behavior is absent: root often adapted a patch
while integrating it.

## Current handoffs to reconcile with dev

These are the live substantive packets reported directly by their owners. Tips
and dirt can change during convergence; inspect the worktree before applying a
commit. Retain these trees until their owners and root report final integration.

| Lane | Snapshot / disposition |
| --- | --- |
| BP debt engine | `implement/bp-debt-engine` `d11239cf`, dirty native/proof edits. BP foundation owns final coherent forwarding/replay packet. |
| BP debt assurance | `bp-debt-cache-correspondence` `ceb1895d`; its untracked `books/bp-node-debt-cache-called-invariants.lisp` is an unadmitted draft and **must not be merged**. Peer-only committed work was handed to BP foundation for composition. |
| K0 retention publication | `implement/storage-k0-retention` `827b93b8`, dirty evidence/registry changes while final selected certification finishes. Storage owner will hand off a finite packet. |
| Maintained topic relation | `prove/topic-maintained-current` `8bec1384`, clean after scoped proof PASS; owner says root is integrating `fb1ef49a` and `8bec1384`. Its earlier baseline was already integrated as `d6f3caf4`. |
| Topic crash teeth | `prove/topic-v2-crash-teeth` `4f1222a5`, qualified test-only packet handed to the maintained-topic owner; root should review its exact test/evidence integration with that packet. |
| Peer authored acceptance | `implement/peer-authored-accept` `864e8f4a` plus dirty final tests; topic owner expects a finite handoff. |
| ION observation binding | `feature/ion-observation-binding` `0889f1f2` plus dirty parser/composite/native-caller work. Its owner expects to hand off by about 07:00 UTC. |
| Native physical campaign | `implement/native-block-profile` `e5f089f0`, clean committed packet; preservation owner says it is unmerged. |
| Pack gap publication | `fix/pack-gap-publication` `28d50703`, clean at this snapshot after its scoped run; preservation owner says it is unmerged. |

The live root checkout may already contain any item in this table by the time
this note is read. Compare final owner tips with the then-current `dev` before
integrating. The two BP lanes must be composed rather than merging the
unadmitted draft, and the topic crash test belongs with the maintained relation.

## Historical branches accounted for

The earlier review's ADVANCE, OVER, allocator and consumer-index foundation
backlog was integrated in the documented cleanup batch. Older `byte-store-k568`,
BP foundation/persistence/contact/union, consumer index/poll, and topic base,
native-tail, admin-generation, and crash-bridge branches were adapted into dev
or superseded by the active successors, according to their owners and the
[cleanup record](cleanup-integration-2026-09-24.md). Do not replay their
apparently positive `git cherry` commits onto the current state shape.

Concrete source checks resolve two misleading older branch tips. The
`topic-next-slice` commit `c80d1113` guards `:replayed-historical` by
`:report`; current `host/native/owner.lisp` has that exact guard and current
native tests include historical retry. The `reclaim-active-reader` commits
`7326b70f` and `970c4f85` have their retention command, active-reader fixture
and b074 image evidence in dev. Both are already content-integrated despite
non-ancestor tips. The native LTP boundary commits `899c8560` and `d396a520`
are patch-equivalent to dev (`git cherry -`), including their explicit
unbound-transport limitation. The author-key lifecycle evidence tip
`a12f523e` is patch-equivalent; its source and proof packets are in dev.

Owners also mark these clean trees as content-integrated or superseded:
`consumer-config-open-index`, `consumer-poll-teeth`, `topic-maintained-bridge`,
`topic-admin-generation-v2`, `bp-a1-selection-assurance`,
`native-b074-freeze`, `native-863-freeze`, `bp-fragment-native-trust`,
`preservation-recovery`, and `topic-preservation-native`. Their branch refs
may remain after safe archival. Keep the remote qualification gates, original
manifests and raw logs. `topic-store-join` is an old alternative with only
dirty planning/spec overlays at this snapshot; its owner says the active
maintained-topic branch supersedes it. Do not apply that older overlay without
a contract-level diff against the new topic relation.

This inventory found **no concrete overlooked older source commit** requiring
a blind merge. The nine live handoffs above are the remaining review queue.
The earlier review's Mini branches are in the separate Mini repository and
need their own final disposition; they are not fn worktrees.
