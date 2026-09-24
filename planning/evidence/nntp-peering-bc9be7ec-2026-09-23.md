# Native NNTP and peering qualification on bc9be7ec

The subject was the shared hbox production image built from
`bc9be7ec9672e9a20300b6cc294214d764785c6b` at
`/tank/fn/gates/reader-clone-poll-native-bc9-20260923/build/fn-host`.
The executable image SHA-256 was
`703ebc440fc696317e9f2169f0da1222ddd3a4fbe184c3c58d8b64353d606264`;
the saved core was
`d3920c214d8ce102b6a0216149cfc63114021383262a90a9ce5585ca92c7032f`.
The observed SBCL executable was `/tank/fn/sbcl/bin/sbcl`, SHA-256
`b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`.
The `packaging/fn-native` launcher SHA-256 was
`ae1e2f486c93ac89bb04d189f6c5f9215903f963cb8d07f693e5a41489435142`.
The image was built and certificate-qualified by the shared image lane; these
runtime tests consumed it without rebuilding. The image's declared source is
separate from the measured executable/core bytes.

The real INN 2.7.4 lab ran on hbox using isolated fn store
`/tank/fn/labs/bc9-inn-interop` and ports 23619–23623. The command was
`python3 tools/inn_lab.py bc9be7ec --host hbox --tree bc9-nntp
--native-image /tank/fn/gates/reader-clone-poll-native-bc9-20260923/build/fn-host
--native-openssl-prefix /tank/fn/toolchains/openssl-3.5.8
--lab-root /tank/fn/labs/bc9-inn-interop --inn-port 23619 --nnrpd-port 23620
--fn-port 23621 --tap-out-port 23622 --tap-in-port 23623`.
The [lab record](inn-lab-bc9be7ec-2026-09-23.md) and
[machine findings](inn-lab-bc9be7ec-2026-09-23.findings.json) report 33 held,
zero violated or inconclusive findings in 57.3 seconds. Observations include
fn POST and operator POST reaching INN by IHAVE 335/235, INN's innfeed reaching
fn by CHECK 238/TAKETHIS 239, duplicate 435 and loop 437 refusals, served
Path/Xref projection and unchanged body, and read-back after fn termination
and innd kill/restart. The findings SHA-256 is
`33253ed799e51bb416827b58fe75f1fb39859b70b7f630dddceaad834692457f`.

The first selected v0 transit/feed matrix attempt used the old
`tools/native_peering_matrix_slice.py` from `bc9be7ec`. It emitted 220
`not-exercised` rows without a useful blocker because the slice did not pass
`FN_OPENSSL_PREFIX` into the saved-image startup probe. A direct same-image
probe without that prefix exited 1 with
`FNN-HSIG-UNSUPPORTED: OpenSSL 3.5 or newer is required for ML-DSA`; the
INN lab supplied the prefix and passed. The [initial matrix](v0-native-peering-bc9be7ec-initial.json)
SHA-256 is `dcf94ed628cf591aa0e8752d354658f5c12325578338c5fc05f446aa740b982e`.
Commit `d45cc826` adds the explicit prefix to the slice and makes a startup
failure name and block the selected rows, returning exit 2. A focused mock
regression passed, as did `tests.test_native_v0_matrix`.

The repaired driver, staged from Git archive `d45cc826` under
`/tank/fn/labs/bc9-peering-driver-d45`, invoked
`tools/native_peering_matrix_slice.py` with the same image, pinned OpenSSL
prefix, `/tank/fn/sbcl/bin/sbcl`, and the declared bc9 source. Its driver
SHA-256 was `50a77fb0f20c2c30122c25b9510187880e3ea6c7ddb9eae91c91429e4113e8ad`;
the staged `tests/test_native_peering.py` SHA-256 was
`f3684ea3de7d1246023d7a7913e831bc9062386fbc7685d8526b4124107d1b60`.
The [matrix document](v0-native-peering-bc9be7ec-2026-09-23.json), SHA-256
`12ae929cc6d5b93777d334de6778387d8dea2c8eb5c8d835faefcb07ef810e8f`,
records 9 accepted and 2 expected duplicate refusals, zero disagreements,
and 209 rows outside this selected slice as `not-exercised`; the selected
transit/feed witness took 5.4 seconds. It checked each live owner through
`/proc` and matched the runtime/core digests above. The selected rows cover
two directions of IHAVE 335/235, byte-identical read-back, duplicate 435,
durable FNFD queue, and source process-death/restart requeue. They do not
establish feed-once after a successful acknowledgement.

This is one loopback INN installation and two local saved-image peers, not a
Usenet conformance audit or a v0 release gate. Neither this run nor the
selected matrix exercises protected cross-host peering or the current BP path.
The shared raw image launcher names an absolute hbox core/runtime path, so
this image was not moved to persvati for a second host run. The installed
service and live `/tank/fn/node` were untouched.
