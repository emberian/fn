# T4: phase-aware Store journal sequence (2026-09-23)

`books/store-identity-sequence-invariants.lisp` introduces
`fn-sn-identity-sequencep`: in a ready state, the carried sequence cursor
equals the number of committed file records; during an enabled completion,
the committed file records lead the cursor by one. The book proves the
relation for initial state, preparation, I/O, refusal, known abort, recovery,
and every arm of the actual `fn-sn-finish`. The keystone
`fn-sn-finish-preserves-identity-sequence` has one hypothesis,
`fn-sn-identity-sequencep`; its test book gives a reachable enrollment,
composite acceptance, retention, burned transaction-id, and reopen trace,
and a `must-fail` bad-cursor counterexample without that hypothesis.

The host calls this theorem's subject at `host/store-node-host.lisp:551`,
inside `fn-store-sn-finish`. It is an ACL2 relation over the logical file
record list and carried cursor. It does not prove physical durability,
snapshot-to-article binding, or index agreement for accepted statement
records. Those remain separate PRF-050 and PRF-023 obligations.

Qualified persvati certification used ACL2 Version 8.7 through
`/home/ember/fn-gates/toolchains/w25/acl2-literal` (toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`),
cache `/home/ember/fn-certcache`, and two existing slots, without closure
recertification. The book and test root passed in
[`certify-20260923T170608Z-2002708.json`](manifests/certify-20260923T170608Z-2002708.json).
After adding the bad-cursor `must-fail` tooth, the test root passed in
[`certify-20260923T170852Z-2027792.json`](manifests/certify-20260923T170852Z-2027792.json).
That final manifest records source SHA-256
`f6ed9551a1811f6ec1f2bc88825aa21344edd307ef47d0d5417ee3a756c82127`
for the book and
`5d040ca8cc1188eacba5aa0741d634b6afad6be43ba597671703258a12fd780d`
for the test. `tools/green_check.py --changed-since b1a77f02 --strict`
reported both changed books green at the bytes this lane carries.
