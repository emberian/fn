# Combined topic/index source: first full-gate verdict

The frozen `8c61c098954e19396e2d0c529d097a1d8b2d33dc` source did **not**
qualify for an image. Its one four-job hbox incremental run was
`run-20260924T033100Z-4833` at
`/tank/fn/gates/topic-index-8c61c098-20260924`, using
`/tank/fn/toolchains/w28/acl2-literal-4g` and shared
`/tank/fn/certcache`. The 357 unique roots were all default, DTN and ACL2
test roots; there was no `--closure` or second diagnostic farm wave. The
original manifest is
`planning/evidence/manifests/certify-20260924T033144Z-795753.json`, SHA-256
`16d1ddac8e05bb93b1d473aea2d7958e2367582797f8d0d6db6d787166e9066f`.
Its toolchain identity is
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.

The cache provided 329 of 618 books; 289 were attempted. The run started at
03:31:44 UTC and finished at 03:43:47 UTC, with 701.381 seconds of
certification wall time. Recorded ACL2 slot wait totals 0.008 seconds across
book attempts (maximum 0.007 seconds). The failure map contains 41 books or
tests: the following seven have direct failures; 34 dependents failed because
a needed certificate was absent. Logs below are under the gate's
`build/acl2/certify-20260924T033144Z-795753/`.

| Direct red | Failed event or assertion | Scope |
| --- | --- | --- |
| `books/acceptance-stamp-invariants` | `FN-SN-FINISH-INSTALLS-THE-STAMP-THE-RECORD-CARRIES` | Topic state changed the relation; proof failed in 2.367 s. |
| `books/byte-store-native-correspondence` | `FN-BS-NATIVE-IO-IS-BYTE-OBSERVATION` | State-record selector proof failed in 2.578 s. |
| `books/store-identity-sequence-invariants` | `FN-SN-REFUSE-RESERVATION-PRESERVES-IDENTITY-NEXT` | State-record selector proof failed in 2.443 s. |
| `books/store-prepare-correspondence` | `FN-SPC-SET-KEYRING-PRESERVES-STATE` | State-record selector proof failed in 2.946 s. |
| `tests/acl2/store-events-tests` | Wrong-sequence-tag decode assertion expected `(:ERROR :VERSION)` | Assertion failed in 1.711 s. |
| `books/owner-invariants` | `FN-OWN-IDLE-NODE-IS-REPLAY` | The exact isolated ACL2 child was deliberately SIGTERM-bounded after more than 300 s; captured event time 398.14 s, with 0.01 s `prove` and no checkpoints. This is a bounded abort, not a proved counterexample. |
| `books/byte-store-record-provenance` | `FN-BS-K6-RELATED-STAGED-DURABLE-FINAL-NAME-ABSENT` | The exact isolated ACL2 child was deliberately SIGTERM-bounded after more than 300 s; captured event time 570.10 s, with 0.01 s `prove` and no checkpoints. This is a bounded abort, not a proved counterexample. |

Before signaling, the two long-lived children were revalidated by PID, parent
PID `795753`, `sbcl` command name, and exact gate working directory. Only
children `799079` and `802421` received SIGTERM. The farm runner continued,
recorded both logs and the dependent certificate failures, and exited 1. No
process group, shared slot service, or `/tank/fn/node` process was signaled.

Successful books above ten seconds include `store-node-invariants` (111.945
s), `consumer-event-index-store-invariants` (87.106 s), `store-node-traces`
(77.061 s), `peer-inbound` (55.432 s), and `replay` (45.195 s). These are
per-book wall times at this exact source and shared-cache condition, not
evidence of a speed regression against an otherwise identical run. The seven
direct red books require scoped repairs and a new combined qualification.
There is no `8c61c098` native image or topic/index runtime claim from this
attempt. A separately qualified `e160442f` image remains available for the
isolated Mini B3 reply fixture; it carries no topic/index claim.
