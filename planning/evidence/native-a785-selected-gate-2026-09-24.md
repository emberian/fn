# Selected native qualification from frozen `a785ae03`, 2026-09-24

This is a synthetic local gate at
`/tank/fn/gates/cleanup-repaired-dfc4c384-20260924`. It did not touch the
live `/tank/fn/node` service. The exact source snapshot was `a785ae03`
(the `dfc4c384` behavior plus generated ledger); the full incremental ACL2
run `certify-20260924T010818Z-669581` passed with 16 newly certified and
581 matching cached books, no failures. Its manifest SHA-256 is
`0205d479eba40f3c4b2c83f880ceacac29c129b08c564b2d68a786e69bb92a41`.
Root's `make check` passed before the image build. The pinned w28 ACL2
executable SHA-256 was
`9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`;
the artifact acquire reported composed source digest
`c674aa8d4698e1a46e9ba3fdb20283b46e645cdd22e1741bb4ad4105d4dbd94e`,
251 books, and zero rejected candidates. Default validation loaded all 97
production roots. Both builds ran under the shared `swarm-build` wrapper with
`FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`; the OpenSSL CLI was
3.5.8, SHA-256
`dd70d8ae49ca0c08541c01ced7c74e310b49692e8a312185824e5ce06bdfd115`.

| Image | Launcher SHA-256 | Core SHA-256 |
| --- | --- | --- |
| Production `build/fn-host` | `d9f8a58d22fa301e2b97fcb0394310b500722a6be24a9d8ae0aee33bdbcec141` | `cb5bc63dd34667c5919eabaaedd7e060f2cc7a1102f7714081b59dc7e663ae12` |
| Developer `build/fn-host-developer` | `6e4e7f44d4cd0ce7057d13aac8ced2329c63175f053678ca1baf28ca75d7b937` | `044d6a9ac461f339cc3a71bd0f9e95cbc8e93ebe1a63a2d73d6683988da55a95` |

The developer image passed both tests in
`tests.test_native_consumer_project_bounds` (driver SHA-256
`fd4898a61ea403c7d78890b55dd1c48c7441a702a47b6415a6db29af280d2e02`):
overbound cursor/event files returned exit 1 and exact `limit` refusal; a
malformed within-bound pair returned exit 1 and exact `codec` refusal. Log
`build/freeze/test-consumer-project-bounds.log` SHA-256
`c34692e2aa6f5ff58d6163f1726d49a99a19dda38ae9d5ecc373ec1e7d79b414`.
A following separate CLI process accepted the archived valid 1d26
`continuation.fncu`/`accepted.fn-e` pair (exit 0); its exact line is in
`build/freeze/consumer-project-after-refusal.log`, SHA-256
`ac6dc5d8c9edfc9912536e1ff8d641947d638110811533ece72abc246e9998f6`.
Using `registered.fncu` instead correctly refused `binding`. This establishes
valid projection after earlier refusals across CLI invocations, not a
same-process mutation or owner recovery claim.

The production image passed
`NativeReaderIndexTest.test_over_xover_crosspost_sparse_range_historical_pin_and_restart`
with the frozen driver SHA-256
`247d885fdcfd29210e5a075ce60d655c2bc1684087f0771ed11ad4ca3db838f4`.
The test exercised indexed `OVER`/`XOVER`, crossposts, a sparse range,
historical pins and restart (one test, 0.810 s). Log
`build/freeze/test-reader-over-index.log` SHA-256
`58b090a6166c4c4201f8aa00222f25844aea97aed6db51f02e416668a87d8bc7`.
The `ADVANCE` relation was certified as an ACL2 configured-owner transition;
this record does not claim a native `ADVANCE` command or host caller.

The requested D1b native deletion-report scenario **did not pass** on these
images. The original driver SHA-256
`0e87b3bcca8542ba6f885eb0ac5ac77b582b98fc6be8a8d6efb1090bdee657a8`
stopped in setup because its request article had an `Xref` header, which the
ACL2 proto-article check intentionally refuses; `fn-bpi-host-message-id`
therefore returned NIL. Original log
`build/freeze/test-bp-deletion-report.log` SHA-256
`8d516ac863acc0ac674b5361ef7c85581f3ebbc56db06b50d8d034848b3e1588`.
A test-only follow-up driver removed only that `Xref` line (SHA-256
`4d026a151e7451ff3330fbfd1c35d87b649d4739ce4bc8d06bfdf991d9b2d919`).
It reached the kind-5 and kind-10 durable cuts and passed canonical report
decode/encode equality, then failed when `host/native/bp-node.lisp` called the
unregistered developer selector
`FN_BP_NODE_TEST_PAUSE_AFTER_REPORT_OUTBOX` (native exit 4). Follow-up log
`build/freeze/test-bp-deletion-report-followup.log` SHA-256
`c00174c695bc5e712f5551d26e0e7bcf6cd4b8be832e0e5c020f3c5232282e0b`.
Commit `57633aa4` registers that selector and repairs the proto-article test
fixture; `make check` passed in its isolated branch. The repaired source
requires a new frozen, qualified image before the rest of D1b can be tested.

This image predates BP fragment callback activation `3d1a461e`. No native
fragment admission or deletion-report return-contact claim follows from this
gate. The Mini B3 reply-post fixture was prepared but was not launched here.
