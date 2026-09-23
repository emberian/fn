# Current work

The plan is [plan-2026-09-22-trajectory](plan-2026-09-22-trajectory.md);
the loop is [how-we-work](how-we-work.md). T0 landed on 2026-09-22: the deployed node is hbox at 192.168.50.39:1119
from the `dabebb84` image, its page is [docs/nodes/hbox.md](../docs/nodes/hbox.md)
and its record is [node-hbox-dabebb84](evidence/node-hbox-dabebb84-2026-09-22.md).
The current phase is 1. Live lanes: `t1/codec-seam` (the codec boundary and the store cluster,
its final run being harvested) and `t4/snr` (why `store-node-resolution`
takes 1748 s, from its logs). Landed since the node, 2026-09-22 to 23:
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
