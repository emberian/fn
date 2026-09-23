# D1b held-deletion kernel checkpoint (2026-09-23)

The native outbound machine authors bundles with status-request flags clear,
so its durable `:expired` job arm is not a reachable deletion-report source.
An inbound request for a deletion report can be received into FNBS kind 5,
but the present A3 clocked selector only skips an expired uncommitted carrier;
it does not persist deletion. No status assertion follows from that skip.

`books/bp-report-deletion.lisp` supplies the pure kind-10 prerequisite.
The candidate selector requires a current `:expired` decision on a held row
without a prior dispatch or deletion. The record binds epoch, operation ID,
arrival and exact primary-identity bytes to `:lifetime-expired`. Its apply
function marks held slot 14, preserving the received identity, kind-5 anchor
and any separate kind-7/FNRJ/outbox obligation; a wrong identity cannot
apply. A nil legacy age anchor gives no expiry candidate. The name
`fn-bpn-report-tombstone-not-pending` proves the resulting row cannot be
selected again for an uncommitted handoff. These are pure transition facts,
not yet a durable publication or host-reached report action.

The book and its exact/wrong-identity/legacy tests passed persvati ACL2 8.7
(SBCL 2.6.8) `run-20260923T220304Z-e47f`,
[manifest](manifests/certify-20260923T220308Z-737327.json), with jobs 2,
`/home/ember/fn-gates/toolchains/w25/acl2-literal`, a 90-second per-book
cap and `/home/ember/fn-certcache`. Kind-10 codec, ordered mixed replay,
live issue/publish callback, policy-gated administrative report authoring
and read-only remote-observation consumption remain open. No report or
application receipt is release authority for the other.

A follow-on pure planner now derives the RFC 9171 deletion assertion only
from the exact kind-10 record and its tombstoned held subject, with an
explicit reports-enabled input. It requires the subject's deletion-request
flag, suppresses administrative subjects and null report-to, uses reason
code 1 (lifetime expired), and uses the subject's status-time flag for an
optional assertion timestamp. Without a wall observation when time is
requested it emits no report. The exact requested-subject payload and
pre-commit/no-policy negative fixtures passed focused
`run-20260923T220946Z-acba`,
[manifest](manifests/certify-20260923T220950Z-806779.json); the book
including planner guard verification passed `run-20260923T220848Z-180d`,
[manifest](manifests/certify-20260923T220851Z-797062.json). The planner
is still not a host-called publisher or a completed D1b generation path.
