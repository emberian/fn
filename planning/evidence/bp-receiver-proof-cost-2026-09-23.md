# BP receiver evolving Store proof cost, 2026-09-23

The 2026-09-23 integrated hbox full pass at
`/tank/fn/gates/consumer-topic-bp-20260923/build/acl2/certify-20260923T221404Z-303098`
spent 130.938 seconds on `books/bp-receiver-evolving-store-invariants` with
ACL2 8.7, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
source digest `1aeac8c1a9083ae4df91e2916080619b5ef497d5a3d53ed97e547b8ebd61a5d9`.
The log identifies `fn-bpr-live-receipt-regenerated-after-restart` as the
hotspot: 127.58 seconds and 82,377,715 prover steps. Its rules include the
open `fn-csi-full-relationp`, which unfolds the consumer and identity replay
predicates during a goal with large nested live-run and reopen terms.

The theorem statement and hypotheses are unchanged. A local lemma extracts
`fn-snt-relation` from `fn-csi-full-relationp` once. The final theorem's hint
keeps `fn-csi-full-relationp`, `fn-sn-observed-identity-okp`,
`fn-snt-consumerp` and `fn-replay-identity` closed; its existing explicit
`:use` instances still establish the crash/reopen and journal-replay facts.
The first bounded attempt with the closed predicates but no extraction lemma
failed in 1.08 seconds at a checkpoint needing `fn-snt-relation`; the local
lemma closes that exact obligation.

At source digest `c8e83fb3d2e65175eab50a680d47c16b47bac91c1d1f1d32b71e9ebe99051165`,
hbox incremental jobs-2 run `run-20260923T222432Z-aa32` passed the book in
3.971 seconds total; the formerly hot theorem took 1.03 seconds and 980,414
steps. Its manifest is
[`certify-20260923T222436Z-333899.json`](manifests/certify-20260923T222436Z-333899.json).
`run-20260923T222510Z-e581` passed the actual evolving-receiver test book in
3.78 seconds, manifest
[`certify-20260923T222514Z-336509.json`](manifests/certify-20260923T222514Z-336509.json).
This measures selected-book proof time at the same ACL2/toolchain identity;
it does not predict the next full gate's total wall time or change the runtime
machine. `make check` passed locally.

After the primary repair, the same baseline log showed
`fn-snt-ready-or-recovered-node-is-exact-replay` taking 25.00 seconds inside
`books/store-node-traces` (book 42.047 seconds, source digest
`64cfed61560bf81b1bc06ddf2e9ea45b3be3fc7d1d80c6a471fd05fd17b28a22`).
This is a definitional projection: its three permitted phases are all idle
phases. A local lemma states that membership implication, and the theorem
hint now opens only the relation while keeping replay and unrelated phase
machinery closed. Its statement is unchanged. At source digest
`057403478e37e930ddadc383ed9d20a820ac0fad458d8f84f6c6f22d4afeb668`,
the theorem took 0.01 seconds and 168 steps; the book passed in 15.226
seconds in `run-20260923T222909Z-a1ec`, manifest
[`certify-20260923T222913Z-348640.json`](manifests/certify-20260923T222913Z-348640.json).
The affected Store/receiver/test chain then passed in hbox jobs-2
`run-20260923T223015Z-ba16`, manifest
[`certify-20260923T223019Z-352053.json`](manifests/certify-20260923T223019Z-352053.json),
including the actual BP evolving-receiver book/test and
`tests/acl2/store-node-traces-tests`.
