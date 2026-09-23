# E2 bounded poll: scoped source evidence

Source packet: `57907b8e` (`implement/consumer-poll`, based on
`22418c27` with the local-control, Linux peer-credential, and production
bootstrap packets). The exact source digests, cache origins, ACL2 executable
and toolchain identity are in the unmodified certification manifests below.
The ACL2 toolchain was `/tank/fn/toolchains/w28/acl2-literal-4g`
(ACL2 8.7, identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`).

| Exact original manifest | Scoped roots | Result |
| --- | --- | --- |
| [owner book](manifests/certify-20260923T221901Z-319533.json) | `books/consumer-owner-local` | Passed |
| [owner tests](manifests/certify-20260923T223119Z-355448.json) | `tests/acl2/consumer-owner-local-tests` | Passed |
| [control book and tests](manifests/certify-20260923T223604Z-363674.json) | `books/consumer-local-control`, `tests/acl2/consumer-local-control-tests` | Passed |

Local boundary check at this source:
`sbcl --noinform --script tests/native_owner_consumer_local_raw.lisp`
printed `native owner consumer local boundary passed`. `make check` passed
before the source commit. The raw test checks deployed native owner call order,
including that poll does not call the durable publisher; it is not a saved-image
socket test.

The ACL2 tests exercise a committed article after bootstrap/register, selection
and unchanged durable position, first-match stopping, nonmatching advances,
the 16-event scan limit, invalid sequence refusal, and bounded poll reply
round trips. This is a scoped source and boundary qualification. A coherent
integrated closure, source-matched native image, real socket poll/advancing ACK,
and Mini durable inbox/outbox join are separate follow-on evidence.
