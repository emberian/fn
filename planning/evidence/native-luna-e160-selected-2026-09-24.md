# Frozen Luna trial: selected native qualification

The selected native cases ran on one shared production/developer image pair in
`/tank/fn/gates/luna-feature-e160442f`, copied from `e160442f`. This is a
bounded trial of the saved consumer cursor, consumer status, web paging, BP
deletion-report recovery, project bounds, and indexed reader paths. It is not a
deployment or a general BP fragment activation claim. `/tank/fn/node` was not
changed.

## Source, proof, and image identity

The four-job hbox ACL2 run `run-20260924T031246Z-1771` passed the combined
343-root default, DTN, and ACL2-test closure; 594 of 597 books matched the
cache and three certified in this run. The manifest is
`planning/evidence/manifests/certify-20260924T031327Z-785374.json` in the
gate, SHA-256 `0d74ea04d26daf5140ced0e7b2de553f3400b15699c6604e08a0d1833e707fe8`.
Toolchain identity is
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
The default artifact acquisition composed 251 books at source digest
`86de9a85de508caaa0562b33607f71eb0b1fcdd369a7feb19198aa70a95de8c5`,
with zero rejected artifacts, and validation loaded 97 production roots.
Their logs under `build/freeze/` are `acquire-default-native-qualification.log`
(SHA-256 `4d30f974068280caa53d388fa1f93201eb724e9e40e5866eb284ca918a964d55`)
and `validate-default-native-qualification.log`
(SHA-256 `394c96f1a2e3317b8e9a2949373d335900524c5e785fff880ad828b85ef4dac9`).

Both images used `/tank/fn/toolchains/w28/acl2-literal-4g` and
`/tank/fn/toolchains/openssl-3.5.8`, with that OpenSSL prefix's `lib` selected
from the outset. The production launcher `build/fn-host` has SHA-256
`2ca6ce83f5d8e9598e0af74f77b49130ed02738d79e828e6498909e6c0081e57`
and core `9a1cd1fb267878b1134166a77aab0081236e783a5d8ff2a3edafb33a38720a4e`.
The developer launcher `build/fn-host-developer` has SHA-256
`c46fe438a7b0efb69f5efe19a94e0ca83a737207c6fcfce453a3000cc8f5f553`
and core `883dc0db1067a5c9208463ed69a0fdd1e6cd2fda6fc1654de861d58721db2c7a`.
Build logs under `build/freeze/` are `native-build-production.log` SHA-256
`2869570447cc6d3e4e22f67ee7b992e1dbd5e3ef03162d91ad9b2d8e243da60a`
and `native-build-developer.log` SHA-256
`32caeda4908ad5752a13aab297e4ecf16c09403e65029d682f68b5694d599d02`.

## Native verdicts

`build/freeze/fn-luna-native-qualification.sh` (SHA-256
`50a995b35f8bc7eb89d8f29b1233c6472d2b8f393f222a461a484aeb0689f186`)
sets the source-matched image paths and pinned toolchain. From the gate it ran
the following selected `python3 -m unittest` cases. Each log below is under
`build/freeze/`.

| Case | Result and scope | Log SHA-256 |
| --- | --- | --- |
| `tests.test_native_consumer_inspect` | PASS, four cases: maximum and zero cursor positions, high-octet IDs, truncated/trailing/unknown-version and overbound refusal | `21c8017eb4b004db60b487cf1c047648f7e29c43c89f2c07be6fa08c0e45cd0c` |
| `tests.test_native_consumer_e2` selected durable-scope and signed-composite-poll cases | PASS, two cases: unknown-ID refusal, read-only status and ACK invariance, post frontier change, reopen and advancing ACK, lost positive ACK reply | `02061d44888b5e2405af2cb4d58d2fd2e4e1d082dd9187e984e02aa90ca06ccf` |
| `tests.test_fn_web_native.NativeWebClientTests.test_web_post_and_thread_read_use_the_native_owner` | PASS, two real native articles, exact one-number windows with Older/Newer links and HTML escaping | `b43673278fa47e20be2807d4934552c100faea4bfe500e868a3a93d16dbfd414` |
| `tests.test_native_consumer_project_bounds` | PASS, two cases: overbound cursor/event refusal without projection and malformed in-bound ACL2 codec refusal | `e29bf0207df8302f02217596f22834a35a93a2bc5516ca31519f01c89b22715e` |
| `tests.test_native_reader_index.NativeReaderIndexTest.test_over_xover_crosspost_sparse_range_historical_pin_and_restart` | PASS, production image indexed OVER/XOVER path | `18b2f5a37f6fedfab270fae4e38ed113ea6449c42731e3c46f017c9a1d048383` |
| `tests.test_bp_node_native.NativeBpNodeTests.test_deletion_report_intent_recovers_and_observation_does_not_release`, with test-only `7c1215d6` | PASS, real kind-5/kind-10 durable records, canonical report decode, crash/replay, uncertain cut, retained pin | `5e5fc43f30ae162179d9302035a7d37ba40a7d0ffb8b1b1960105e7e3ff2fde5` |

The frozen `e160442f` BP test first failed at its initial sender pin check
(`bp-deletion-report.log` SHA-256
`28bc0530f7cc786acbb0d2265e98c0f259d41d0f20f6fed6725d897db85fcf2e`).
A diagnostic wrapper recorded `sender_status` exit 1 and stderr `store: store
is already locked` because the test queried the sender Store while its own
long-running node held the lock (`bp-d1b-diagnostic.log` SHA-256
`d06e70b3777082378df991041a5a4d108da6e3c803933f18522b356237b1fea0`).
Test-only commit `7c1215d6` closes that sender before checking the pin and
asserts status exit 0. The successful rerun loaded the repaired test at its
explicit path, SHA-256
`d94ed0a5762ee11067ad8ea007155c9428487e35a1870360e0483ac47553e622`,
against the unchanged `e160442f` image. Its exact-path runner is
`build/freeze/bp-d1b-overlay-run.py`, SHA-256
`e86e72f6ccb447341c8ec008161a946e34a723f8fa2093233e228a1be8203eac`.
The first overlay invocation accidentally loaded the old gate test via Python
package resolution and failed identically; it is not counted as a patched
test run. The passing run is `bp-d1b-test-order-overlay-2.log` above.

This selected native run does not establish full farm coverage for the
test-only `7c1215d6` commit, general BP fragment behavior, Mini B3 reply
posting, or live-node deployment. The test-only branch passed `make check` and
the BP test was rerun on the source-matched frozen runtime image; no new image
was built for the test edit.
