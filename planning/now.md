# Current work

The plan is [plan-2026-09-22-trajectory](plan-2026-09-22-trajectory.md);
the loop is [how-we-work](how-we-work.md). T0 landed on 2026-09-22: the deployed node is hbox at 192.168.50.39:1119
from the `dabebb84` image, its page is [docs/nodes/hbox.md](../docs/nodes/hbox.md)
and its record is [node-hbox-dabebb84](evidence/node-hbox-dabebb84-2026-09-22.md).
The current phase is 1. The hbox node runs the second image built from `dev`, `da5fd8cb`, upgraded
in place on 2026-09-23 with its store kept
([record](evidence/node-hbox-da5fd8cb-2026-09-23.md)); the image closure
certifies from scratch in 1 min 44 s and an incremental run of dev's head
in about a minute, after fifteen proof-cost lanes and the cache, runner
and incremental-mode tooling of 2026-09-23 (the numbers are the ITER
table of the [Codex handoff](handoff-to-codex-2026-09-23.md), whose State
section is the current state). The INN lab holds 33 of 33 on this image;
the cut campaign on it is the one lane still out. Everything else is in
the handoff; no Claude lane is live on any book. Landed since the node, 2026-09-22 to 23:
`t9b/role`, `t13/inn`, `t13/agents`, `t5/campaign`, `t12a/bp-rev2` (the
contract patched against [gpt-6's second review](review-2026-09-22-bp-node-machine-2.md);
[the third](review-2026-09-23-bp-node-machine-3.md) is answered and folded
into the [Codex handoff](handoff-to-codex-2026-09-23.md)), `t5/host` (one
startup gate for every developer selector, the owner armed for the cuts),
`t8c/live-rows` (the live rows were a dead owner, not two writers),
`t13/conform` (the operator's post injects, relayed articles served as fn's,
From a mailbox-list), `t6b/profile` (the log path works, the agent key
refused by name), `t5/sweep` (every crash orphan swept in bounded rounds).
None of it is on an image yet; the next freeze follows the seam. What an
hour of idle farm waiting taught is the last section of [how we work](how-we-work.md).
Earlier landings: `t8/reconfig` (the two headline theorems and two
live-path defects; the live domain adoption is T8b) and `t9c/feed-tls`
(the outbound feed's protected channel with teeth). T7, T11 and the T12a
design landed, revised against gpt-6's review; the release
replay the production build needs landed (2788d4cb); root ran T14 and T15
(5f7d0c2d, 3fa17fa5).  The dated narrative this file
carried is in [planning/archive/now-2026-09-22.md](archive/now-2026-09-22.md)
and in the evidence records it links.
