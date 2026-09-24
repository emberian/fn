# Worktree retirement and checkout recovery, 2026-09-24

97 inactive fn worktrees were archived and removed. All regular-file bytes
and symlink targets were compared with their archives before removal; tips
remain reachable through their original branches or three `archive/worktree-*`
refs. Seventeen lane trees remained at the cleanup checkpoint. These numbers
describe workspace disposition, not feature completion.

The private local archive is `/Users/ember/dev/fn-worktree-archive/20260924/`.
Its `README.md` and per-lane JSON manifests contain checksums, dirty status,
tips and restoration instructions. Original regular-file content totalled
9,714,746,545 bytes; compressed archives totalled 1,784,447,458 bytes. This is
not a measured physical-disk saving. The two dirty retired trees contained only
generated ledger changes, preserved as binary patches and complete archives.
No remote gate, cache, Mini tree or live service was removed.

After their source landed, four more clean worktrees were verified, archived
and retired: `live-advance-union`, `t17-over-range`, `luna-reader-verdict`, and
`consumer-index-foundation`. Their branch tips remain reachable. The archive
report now covers 101 retired worktrees; the byte totals above describe the
initial 97-tree checkpoint. Active storage and proof-cost lanes remain.

At 00:48:15 UTC an external Claude review accidentally reset the main checkout
from `92ad1b4d` to `origin/dev` (`6bfab467`). Root preserved
`recovery/pre-unexpected-reset-20260924` before investigating. The user confirmed
the reset was accidental, and root restored `dev` by fast-forwarding to that
recovery ref. The checkout then exactly matched `92ad1b4d` and was clean.

The three staged files Claude saw at 00:47:33 were a cherry-pick in progress:
`books/byte-store-record-provenance.lisp`,
`planning/evidence/k0-frontier-entry-2026-09-23.md`, and the original manifest
`planning/evidence/manifests/certify-20260923T233919Z-509059.json`.
They had already been committed in `565daf23` at 00:47:36, before the reset.
All fifteen displaced commits and all three named files were recovered;
no known uncommitted work was lost. The retired worktree archives and active
lane work were unaffected.

Reviews of another revision should use `git show`, `git diff`, or an isolated
worktree. A status observation can become stale while another agent is
committing; it never authorizes resetting a shared checkout.
