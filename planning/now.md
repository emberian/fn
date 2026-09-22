# Current work

The plan is [plan-2026-09-22-trajectory](plan-2026-09-22-trajectory.md);
the loop is [how-we-work](how-we-work.md). T0 landed on 2026-09-22: the deployed node is hbox at 192.168.50.39:1119
from the `dabebb84` image, its page is [docs/nodes/hbox.md](../docs/nodes/hbox.md)
and its record is [node-hbox-dabebb84](evidence/node-hbox-dabebb84-2026-09-22.md).
The current phase is 1. Live lanes: `t1/codec-seam` (the codec boundary and the store cluster),
`t6b/profile`, `t8c/live-rows`, `t12a/bp-rev2` (the contract patch against
[gpt-6's second review](review-2026-09-22-bp-node-machine-2.md)),
`t13/conform`, `t5/host` and `t5/sweep` (repairs from tonight's records:
[INN lab](evidence/inn-lab-dabebb84-2026-09-22.md),
[agents on hbox](evidence/agents-on-hbox-2026-09-22.md),
[the cut campaign](evidence/campaign-dabebb84-2026-09-22.md)). Landed since
the node: `t9b/role`, `t13/inn`, `t13/agents`, `t5/campaign`, `t8/reconfig` (the two headline theorems and two
live-path defects; the live domain adoption is T8b) and `t9c/feed-tls`
(the outbound feed's protected channel with teeth). T7, T11 and the T12a
design landed, revised against gpt-6's review; the release
replay the production build needs landed (2788d4cb); root ran T14 and T15
(5f7d0c2d, 3fa17fa5).  The dated narrative this file
carried is in [planning/archive/now-2026-09-22.md](archive/now-2026-09-22.md)
and in the evidence records it links.
