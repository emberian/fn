# Frozen native topic and BP handoff image — 2026-09-23

The subject is committed source `86323c8976de711593c7d9eca977ed99a211d04c`,
archived with `git archive` into the isolated hbox gate
`/tank/fn/gates/integrate-topic-handoff-86323c89`. No live node or Store was
changed. Root's full Makefile-root ACL2 run `run-20260923T211742Z-172779`
passed on preceding source `f38c90a6` (521 reused certificates, two newly
certified); only the generated ledger changed between that source and 86323.
`make check` passed on 86323. The exact 86323 snapshot then acquired one
compatible default-profile artifact set from `/tank/fn/certcache` with
`/tank/fn/toolchains/w28/acl2-literal-4g`: set
`d2b1d0614ba6aedc68aa6c2a912e1bab3558150a931308c9d294523a5240d865`,
208 books, source closure
`f2684243467fd4f534399f7bf6bac4dcbfe3f85be4704fe40f672c68d47f0df3`.
The [acquire log](native-topic-handoff-863-logs/acquire-default.log) has SHA-256
`1e4b122103dfd0355da344ee27a421c0577eb9db6dda5dca7a149def8da88201`.
`proof_artifacts.py validate --profile default` loaded all 84 declared image
roots; its [log](native-topic-handoff-863-logs/validate-default.log) has SHA-256
`19ea4eca39f619cb95de155cf273534f11f9b17cd9fc1b9a968a8257a33b7d05`.

With `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, `FN_ACL2` set to
the w28 executable, and `swarm-build sh tools/build_native_host.sh`, the full
`host/native/build.lisp` produced both profiles. Production
`build/fn-host` launcher/core SHA-256 are
`044053de164bae03cf551f48b07f60e11d84b667f0e6e896c71595ef56fd6023` /
`4483d58589668e2467fa8cd45fceb745140a845b9d6f5f8531b60a958158f898`;
developer `build/fn-host-developer` launcher/core are
`c4cc70869a7e01f34b33442e4ca98bbd5ea24d4b5aca4c83d57b8e773c8f3879` /
`36d52bbfe1bf76074aca93892be6411c36c59568a1ae6ae8e5ab6e34426a2c3e`.
The [production](native-topic-handoff-863-logs/native-build-production.log) and
[developer](native-topic-handoff-863-logs/native-build-developer.log) build logs
have SHA-256 `217a634586b7ffc55e460f4a49d1c7ad388b31f0c37b6fff483455c58f01bcbb`
and `55a09d33e82fe08148bc0a5093269d578e99036d8c0261a3512b6a1645261c4e`.

All commands ran in that snapshot with
`LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib` and `PYTHONPATH` set
to the snapshot. `FN_NATIVE_HOST` selected the profile under test. The BP
suite additionally used `FN_NATIVE_DEVELOPER_HOST` pointing to the developer
image, `FN_NATIVE_SOURCE_ROOT` pointing to the snapshot, and the pinned w28
`FN_ACL2`; Topic used `FN_TEST_OPENSSL` pointing to the pinned OpenSSL CLI.

| Exact frozen test driver | Image | Result | Log SHA-256 |
| --- | --- | --- | --- |
| `tests/test_bp_node_native.py` SHA `d554705c266cea7ce44e9bd35ee44fccd7929c4c0f07b61ed6012093d3b0faa1`; `python3 -m unittest tests.test_bp_node_native -v` | developer | 9/9 PASS, 140.991 s; request retry/receipt release, wrong-peer collision, death after decision/kind 7/outbox, ambiguous kind 5/FNRJ/outbox | [`42a3f128e460147cfbec0d855ee6d4760527ac2023320a17010525974dd4fb5c`](native-topic-handoff-863-logs/test-bp-node-native.log) |
| `tests/test_native_topic_metadata.py` SHA `ec936698c6ac20257861a816177534dfba69dde4a0c93e4dbf2cb48ecd8cc0fe`; `FN_RUN_TOPIC_METADATA_E2E=1 python3 -m unittest tests.test_native_topic_metadata -v` | developer / production | 2/2 PASS on each; exact folded maximum-roster root and relayed carrier, altered-source refusal, signed-topic positive and duplicate/malformed negatives. Max field SHA `8b9aeeb3311f313d5b0826f105faaa05e93f398017451442ed7c128d04584851` | [developer](native-topic-handoff-863-logs/test-native-topic-metadata.log) `c7d1c0491e6ddf3bb03728142605dd803f642442314d59f7279696718e3f6882`; [production](native-topic-handoff-863-logs/test-native-topic-metadata-production.log) `6bc60b59d0fdd7bfc7a0b1d14a3022293e02fa82e1b266b030e28f0345bfb9a5` |
| `tests/test_native_reader_index.py` SHA `aa666bf04f6c9323ac5d655fad6860df9b7b2d50099d85f1333f6f2245bb9140`; `FN_RUN_NATIVE_READER_INDEX=1 python3 -m unittest tests.test_native_reader_index -v` | developer / production | 1/1 PASS on each; historical pins, restart, 96 concurrent indexed STAT requests (0.026 / 0.021 s in these runs) | [developer](native-topic-handoff-863-logs/test-native-reader-index.log) `83e2cca4b26151dc94b895027d9449764b2b403beff14b2f45a992308d04e915`; [production](native-topic-handoff-863-logs/test-native-reader-index-production.log) `807cca1f3183118fd19be5b0c1a2d533c4a1af0f81fe6f4ff4b7fbb6f024ef5f` |
| `tests/test_native_live_reconfiguration.py` SHA `3d9e89f8cab9df7739262ed7c24560dfd62f5ec286f11ee4689e2b7cf3fc8e6e`; `python3 -m unittest tests.test_native_live_reconfiguration -v` | developer / production | 11/11 PASS on each: four saved-image scenarios including old/new reader pins, group/peer durability and owner lock; seven source assertions | [developer](native-topic-handoff-863-logs/test-native-live-config-developer.log) `8ad40d667f4e92176e3436eb1360ff46cf6838c0c50b3462f81acc0b618e8534`; [production](native-topic-handoff-863-logs/test-native-live-config-production.log) `28f0ab9a82c13ac4933bec1357182555d5819a9510a8f691fd975f35856eb13a` |

The BP test subject is the current trusted-local A3 application path. It does
not qualify peer channel admission, expiry, or subsequent fragment-safety
changes. The Topic inspector reports an authenticated candidate and
`admission=unestablished`, not Store admission. These targeted runtime tests do
not replace the earlier frozen 884e4816 INN, matrix, and hybrid peering runs
or establish a general throughput bound.
