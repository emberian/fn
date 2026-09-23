# Native matrix witness refinement on the da5fd8cb image — 2026-09-23

This record is a source-pinned negative protected-feed observation and a
positive native configuration observation. It does not turn V0-FEED-ONCE or
protected transit green. The matrix changes that accompany it require an ACL2
FNFD replay of the durable owner queue before they can report FEED-ONCE.

## Subject and invocations

The production image is hbox
`/tank/fn/gates/freeze-dev-2e53fae2/build/images/da5fd8cb5929601679bdb71c3be6986d430f05ed/fn-host`, built from `2e53fae2`
(the image's `da5fd8cb` label differs only under planning). Its launcher
SHA-256 is `9597f3b90fb06087e1e36ef9ae097b90f89a0a95c6c9046f0979d9e5d0835718`,
core SHA-256 `a6e5437e23fc74a743f07c21e46e7876b42f132de2a558f9db4142a781ab5cca`,
and observed `/proc` SBCL runtime SHA-256
`b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`.
The test tree is `/tank/fn/gates/takeover-matrix-witnesses`, copied from the
frozen tree with only the four matrix/test files overlaid from the
`implement/matrix-witnesses` lane based on `df5097b6`. Their SHA-256 digests,
in order for `tools/v0_matrix.py`, `tests/test_native_v0_matrix.py`,
`tests/test_native_protected_peering.py`, and `tests/test_feed_journal_live.py`,
are `6d503ea60091acb3d365621b22f8945b8dcdf600a8a3c1ba9a4a81905c9ce903`,
`aee80d8056efff4a818c2c5a27cb5a04fab81c491701aedcf44e861539c176b1`,
`7cdb253248b6a07db9c59a6468c08ae21dc37ef27d2a4ec0c871f5be35d91688`,
and `b232762bfb5ee4742254e33f56bab005b110c6c5cb40a9545c44ce9c5be1e92b`.
The source/tool overlay is separate from the saved-image source claim.

With `FN_NATIVE_HOST` set to that launcher, the three matching image hashes
set as `FN_NATIVE_LAUNCHER_SHA256`, `FN_NATIVE_CORE_SHA256`, and
`FN_NATIVE_RUNTIME_SHA256`, `FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g`,
and `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, the following ran
from the test tree:

```text
python3 -m unittest tests.test_native_protected_peering.NativeProtectedPeeringTests.test_acknowledged_protected_feed_does_not_reoffer_after_source_death -v
python3 -m unittest tests.test_native_protected_peering.NativeProtectedPeeringTests.test_reciprocal_starttls_authinfo_transfer_and_reconnect -v
FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g python3 -m unittest tests.test_feed_journal_live -q
```

The first two failed because the protected recipient never received the post
within 60 seconds. The ACL2 scanner tests passed. The complete invocation
outputs remain at `matrix-feed-once-fixed.log` (SHA-256
`e86bba457afc6388ee8404220802165a42c931141d308e7ce29b2c6614cd3804`),
`matrix-protected-control.log` (SHA-256
`e495d597f7bbf6b2549fec8310bd0f5840bd7566945f51b8d8b379819f2b3a2d`),
and `matrix-feed-inspector-tests.log` (SHA-256
`088adcd764c1001e873e04d55b60bb47d62504bd8de3af2a383179ababf4d0c0`)
in that isolated hbox tree. Earlier runs with an unconsumed owner stderr pipe
also stalled; the fixture now writes owner stderr to a regular file, and the
recipient still did not receive the article. The captured failure diagnostic
is `diagnostic/feed-once-initial.json` there (SHA-256
`5c9fcf24b1773b4d2e3f86469389d92734c6c8f1e4d6363148892e75fa1ea4d0`).

## Durable queue and configuration observations

The sender's copied, at-rest [FNFD snapshot](matrix-protected-da5fd8cb-queued.fnfd)
has SHA-256 `11b5c5eaf929d8e9fe9839a6293433cac9313e3a3692213c61146dceb567bb0d`.
The read-only inspector supplied its prefix/frame bytes to
`fn-feed-journal-scan` and folded its decoded entries through
`fn-feed-replay` in actual ACL2. The file contains one each of `:feed-restart`,
`:feed-intent`, and `:feed-commit` for the target peer and article. ACL2
reported `:queued` before and after `fn-feed-restart`, queue length 1,
attempts 0, next attempt 1, and no in-flight entry. There was no durable
`:feed-offer` or `:feed-sent`. The live A-to-B TCP connection had been observed
established, so this locates the failure before a feed offer; it does not by
itself distinguish a TLS, AUTHINFO, or mode-phase cause. The separate
`feed_replay` lane's TLS zero-poll diagnosis is a source-level explanation to
verify on a new exact-source image.

An isolated native `fn.toml` containing `[store] path`, `[listener]`, and
`[control]`, with no `[acl2] path`, was consumed by `packaging/fn-native
operator CONFIG init fn.letters`: exit 0, `initialized
/tank/fn/gates/takeover-matrix-witnesses/diagnostic/config-yoW1aW/store`.
`operator CONFIG status` then exited 0 and reported `transactions=0
articles=0`. Replacing the listener host with `0.0.0.0` in the same isolated
configuration made `operator CONFIG run` report `CONFIGURATION INVALID` with
exit 5. The latter is a genuine admission failure, but exit 5 is a usage
code, so the matrix keeps its outcome row `not-exercised` rather than
misreporting a D13 refusal.

The old image cannot take a controlled process-death cut after durable
`:feed-sent`, and its protected feed did not reach an acknowledged transfer.
The new FEED-ONCE mapper therefore has no accepted image witness here. A
source-matched image carrying the TLS zero-poll repair and the developer-only
stop-after-sent hook is needed for the pending protected and mid-transfer
observations.
