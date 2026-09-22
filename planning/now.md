# Current work

The plan is [plan-2026-09-22-trajectory](plan-2026-09-22-trajectory.md);
the loop is [how-we-work](how-we-work.md). T0 landed on 2026-09-22: the deployed node is hbox at 192.168.50.39:1119
from the `dabebb84` image, its page is [docs/nodes/hbox.md](../docs/nodes/hbox.md)
and its record is [node-hbox-dabebb84](evidence/node-hbox-dabebb84-2026-09-22.md).
The current phase is 1. Live lanes: `w31-freeze-3` (T0: the last two reds,
`checkpoint-codec` and `store-prepare-correspondence`, then the closure and
the images), `t12a/bp-design-2` (the design revised against
[gpt-6's review](review-2026-09-22-bp-node-machine.md)), and phase 1 begun
early on branches of their own: `t1/codec-seam` (the codec boundary and the
store cluster), and, landed since: `t8/reconfig` (the two headline theorems and two
live-path defects; the live domain adoption is T8b) and `t9c/feed-tls`
(the outbound feed's protected channel with teeth). T7, T11 and the T12a
design landed, revised against gpt-6's review; the release
replay the production build needs landed (2788d4cb); root ran T14 and T15
(5f7d0c2d, 3fa17fa5).  The dated narrative this file
carried is in [planning/archive/now-2026-09-22.md](archive/now-2026-09-22.md)
and in the evidence records it links.
