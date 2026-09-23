# Second four-profile frozen image — 2026-09-23

The image source is exactly `f0b8b166a3d5d56124ba45114bda0bd34affa5b8`,
snapshotted in the isolated hbox gate
`/tank/fn/gates/takeover-image-upgrade-f0b8b166`. Nothing under
`/tank/fn/node` was changed. The build used
`/tank/fn/toolchains/w28/acl2-literal-4g` (SHA-256
`9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`),
`/tank/fn/certcache`, `swarm-build` for every saved core, SBCL 2.6.8 and the
matched OpenSSL 3.5.8 pair at `/tank/fn/toolchains/openssl-3.5.8`.

`tools/proof_artifacts.py` derived 66 default roots and 49 DTN roots; the DTN
set is a subset of default. Incremental farm run
`run-20260923T143814Z-b301` selected the 176-book union closure at two jobs.
It installed 174 current-digest certificates from the existing hbox cache
origin and newly certified `books/byte-store-compaction-correspondence` and
`books/byte-store-programs` in 5.045 certification wall seconds. The exact
[manifest](manifests/certify-20260923T143824Z-3863201.json) records passed
status and ACL2 toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
Default acquisition composed the two new certificates with the 174 cached
ones and ACL2-loaded the 66 roots. DTN acquisition and ACL2 load covered its
49 roots/162-book closure from one prior origin. This is source/closure/toolchain
certificate evidence, not a fresh certification of all 176 books.

The four generated saved images were frozen under
`/tank/fn/gates/takeover-image-upgrade-f0b8b166/build/images/f0b8b166a3d5d56124ba45114bda0bd34affa5b8`.
`sha256sum -c image.sha256` passed over all four launchers/cores, copied SBCL
runtime/home, OpenSSL pair and libsodium. The core SHA-256 values are:

| Profile | Core SHA-256 |
| --- | --- |
| Production | `004b694980fb1f2882eea9876da32028e8b183948277f72df5edbf6d66e19ff2` |
| Developer | `66115e4374e71d107dc94f9f214cc0aeb68ac933334b83ee46d777944c958747` |
| DTN production | `e09e56560176502ab7271445d4c623ac0b272134a50baa2d9cf997a46856e035` |
| DTN developer | `52c1460723945f4763af1cca1b51d3c5fc55691b8153d6855b79bd0279133dce` |

All four original `build/*.core` files were hidden temporarily under a shell
restore trap. Each frozen launcher ran under `strace -f -e openat` and opened
its own image-local core. The original build cores were restored and checked.
This establishes core path isolation for these launches; it does not test
power loss or every dynamic-library/host ABI path.

## Runtime witnesses and open paths

The entry-profile lane exercised the default production/developer pair at the
image source above. `tests.test_native_checkpoint` passed 17/17 and
`tests.test_bp_obligation_native` passed 4/4. This closes the earlier image's
missing pack-reclaim executable and forwarding-pin call binding in these
fixtures. `tests.test_bp_app_native` passed 2/3; its receipt fixture now reaches
`FN-WORKFLOW-RECEIPT-RECORD`, which is absent from this core. The A3 receipt
record/replay join remains open, and no known-missing workflow-constructor
test was rerun merely to obtain another failure.

The targeted
`NativeAdminTests.test_create_capacity_retire_reopen_preserves_history`
passed 1/1 in 0.526 seconds. It used the saved `f0b8b166` production image
with test-only harness fixes from `e5c2ff5f` (bounded startup announcement
read) and `1ae58422` (trim final domain-report newline), loaded outside the
frozen checkout. Thus that witness has **image source** `f0b8b166` and a
**later test harness**; those revisions must not be conflated. It exercised
operator posting, retirement, inspection, reopen and retained domain history.

The protected feed and served crash lanes were given these exact image paths
and hashes for independent source-matched fixtures. Their results belong in
their own records. No live node upgrade, schema migration or power-failure
qualification was run here.

The entry-profile lane subsequently ran the full `tests.test_native_admin` suite:
**9/9 passed in 2.744 seconds** on this `f0b8b166` production/developer pair.
Its test-only harness revisions were `e5c2ff5f`, `1ae58422` and `277f7e4f`,
copied to hbox `/tmp/fn-entry-admin-latest.py` outside the frozen checkout
(SHA-256 `a8e98aa1d188349326fa8ff259017af84675796b43dc5f08813788e9adaed58e`).
That harness came from lane tip `277f7e4f78bfacd1cdf2a76a8bf99cd57e4114a3`
and set synthetic `__file__` to
`/tank/fn/gates/takeover-image-upgrade-f0b8b166/tests/test_native_admin.py`
so its root resolved to the image source checkout. Ordinary admin/post operations
used the production image; only the explicit
`FN_IMMUTABLE_PUBLISH_TEST_FAIL` fault witnesses used the developer image.
This is a runtime result for the saved `f0b8b166` cores with a later, separately
identified test harness.
