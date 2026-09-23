# A3 expired-held delivery checkpoint (2026-09-23)

The previous `bp-node` caller selected recovered kind-5 held requests before
observing their age. A request durably received and then left across process
death could reach Store after its lifetime. Moving the old `:clock` call
alone would not close this: that transition ages outbound base jobs, while
the received held row had no persisted arrival anchor.

This source checkpoint adds the receive observation to the ACL2
`:receive-bundle` event. New held rows persist slot-9 `(:wall)` or
`(:observed-age age-at-arrival monotonic-at-arrival)` in a versioned kind-5
frame. The old 11-field kind-5 frame remains byte-canonical with nil slot 9;
the A3 selector treats that legacy absence as uncertain and fences before
Store. The host asks `fn-bpah-pending-decision-at` with a current same-boot
observation, dispatches only `:ready`, and advances outbound clock before
dispatch. Definitively expired uncommitted held carriers are skipped; a
durable kind-7 handoff and FNRJ receipt/outbox obligation are selected
separately and are not deleted by this eligibility check.

Direct foundation, receive-boundary, kind-5 codec, guard and test roots
passed selected persvati ACL2 8.7 / SBCL 2.6.8 run
`run-20260923T212036Z-86ec`,
[manifest](manifests/certify-20260923T212039Z-295588.json).
The new anchored-frame witness passed selected run
`run-20260923T213320Z-b299`,
[manifest](manifests/certify-20260923T213325Z-424511.json).
The clocked handoff selector and its live/expired/legacy witnesses passed
`run-20260923T213420Z-9968`,
[manifest](manifests/certify-20260923T213423Z-434801.json).
All used `/home/ember/fn-gates/toolchains/w25/acl2-literal`, jobs 2,
90-second per-book cap and `/home/ember/fn-certcache`.

The affected dependent closure, source-matched native image, and process
death/reopen expiry test have not yet run at these bytes. The old four-field
logical receive event remains for proof fixtures but is rejected by the
native host event predicate; it is unreachable in composition. Expired held
retention/capacity reclamation is separate from the pre-Store safety decision
and remains open. The Bundle Age path uses `fn-clock-expiry-decision` under
its clock assumptions; the age estimate alone is a lower bound and this
checkpoint does not claim authentication or complete physical lifetime
soundness.
