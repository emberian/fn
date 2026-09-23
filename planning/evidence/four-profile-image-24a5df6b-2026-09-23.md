# Four-profile frozen image at 24a5df6b — 2026-09-23

Source revision `24a5df6b41e8885f992610cbcfc267c0dbfdb17c` was checked out as a
detached local worktree and snapshotted by `tools/farm.py` to
`/tank/fn/gates/takeover-image-upgrade-24a5df6b` on hbox. The native image
build ran there with `/tank/fn/toolchains/w28/acl2-literal-4g` (SHA-256
`9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`),
OpenSSL `/tank/fn/toolchains/openssl-3.5.8`, cache `/tank/fn/certcache` and
`swarm-build` for each of four saves. No node or live Store path was used.

The incremental farm run `run-20260923T142047Z-4e1a` selected the 65 default
image roots, which contained all 49 DTN roots. Its closure held 174 books:
174 installed from the one source/closure/toolchain-matched cache origin
`/tank/fn/gates/freeze-dev-2e53fae2`, zero certified, zero missing. The
[manifest](manifests/certify-20260923T142058Z-3842630.json) reports `passed`,
ACL2 toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`
and `certify_wall_seconds: 0.001` because it did no fresh certification.
`tools/proof_artifacts.py acquire` then installed and ACL2-loaded the default
174-book and DTN 162-book profile sets from that same origin. Separate
`validate` invocations passed both loads. This is current-digest certificate
reuse and ACL2 load evidence, not a new proof run or a change to a theorem.

The four saved cores and launchers are under
`/tank/fn/gates/takeover-image-upgrade-24a5df6b/build/images/24a5df6b41e8885f992610cbcfc267c0dbfdb17c`.
`sha256sum -c image.sha256` passed over the four launchers/cores, copied SBCL
runtime and home, OpenSSL pair and libsodium. Core SHA-256 values:

| Profile | Core SHA-256 |
| --- | --- |
| Production | `b3a31ae7148fe04991953c603fbea0a9e6919879447a8d876d50a35d3db1846f` |
| Developer | `9e88fac4d2807b642d4f70264b6ef27bb4e36669d95d76a07a1e87697f36485f` |
| DTN production | `e8b5ca6ec0bd105f7c437c00a708ecdfb66f06795967a978adbec1ca36c55b1f` |
| DTN developer | `8eb9c16d26ed62a976d259898e8601a8576416118901abe6934b3903783c300b` |

For the relocation check, all four original `build/*.core` files were
renamed temporarily in the gate. Each frozen launcher ran under `strace -f -e
openat` and opened its corresponding core inside the image directory. A shell
trap restored all four source cores, and their presence was checked. An
isolated production install under `build/upgrade-fixture/releases/test`
returned the expected disabled-reader result (exit 5); its copied core hash
matched the production value above. These checks demonstrate actual core
selection, not every runtime dependency or protocol behavior.

The shared image regression suite is being run against these artifacts by the
entry-profile lane. Its first profile and production-control portions passed;
the DTN developer app-journal portion exposed a missing
`fn-workflow-undertake-record` executable counterpart. That symbol has no
ACL2 definition in this revision, and the workflow record recognizer has no
`:undertake` kind. Until the caller and contract are repaired and the image
rebuilt, this image does not qualify that operation. No live upgrade, Store
schema migration, full protocol matrix, or power-loss qualification was run.

## Shared source-matched runtime suite

The entry-profile lane ran the frozen launchers from this image with source
revision `24a5df6b` and reported these results; its later test-only commit
`72e0ce9e` was **not** in this image or these counts.

| Suite | Result at this image |
| --- | --- |
| `tests.test_native_image_profiles` | 12 passed |
| `tests.test_native_control` | 13 passed |
| `tests.test_native_storage_codec` | 11 passed |
| `tests.test_native_app_journal` | 8 passed, 2 failed: `FN-WORKFLOW-UNDERTAKE-RECORD` missing |
| `tests.test_native_checkpoint` | 8 passed, 9 failed: `FN-BS-PACK-RECLAIM-PLAN` missing |
| `tests.test_native_bp_obligation` | 2 passed, 1 failed: `FN-OWNER-WORKFLOW-FORWARD-PINNEDP` non-action |
| `tests.test_native_bp_app` | 2 passed, 1 failed: same non-action |
| `tests.test_native_admin` | Incomplete: four early failures from a stale lowercase `verification=verified` test expectation against `VERIFIED`; a long owner test was terminated after more than five minutes. |

The passing control suite includes its normal production posting and recovery
fixtures. The red DTN/BP cases are open caller/semantic gaps. The incomplete
admin suite cannot be counted as a pass. This record is scoped to the frozen
source and image; later test edits require their own run and source identity.
