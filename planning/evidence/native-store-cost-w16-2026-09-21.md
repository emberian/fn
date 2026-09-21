# Evidence: native store cost probe (W16)

Date: 2026-09-21. This is a bounded performance investigation, not a
certification, capacity qualification, or deployment claim.

## Scope and source identities

The requested target was the actual saved-image bridge (`fnn-call` through the
`fn-store-sn-*` program wrappers), rather than a direct ACL2 invocation. The
current lane began at `d1b0ed0`; its `host/native/io.lisp` SHA-256 was
`7ea68e715d7de45d0d30fa192d8d7cd10a735313ef9421d9ab3b6645e482ecbc`.

The current source did not produce a saved image on the available farm cache:

```
cd /home/ember/fn-lanes/w16-native-store-cost
python3 tools/certs.py --cache "$HOME/fn-certcache" install
FN_ACL2="$HOME/fn-tools/acl2-8.7/saved_acl2" sh tools/build_native_host.sh
```

The last command stopped at an uncached `books/byte-store-txn-name` include
(`ACL2 Warning [Uncertified]` in `build/native-host-build.log`). This is a
farm-artifact limitation, not a source or proof conclusion.

To measure a real saved image without treating an uncertified load as valid,
the probe used the existing certified W13 baseline on hbox:

| item | value |
| --- | --- |
| tree | `/tank/fn/lanes/w13-native-storage-codec` |
| revision | `452828c4bd9fa2c2e60122d0ab9f51a26101baba` |
| baseline `host/native/io.lisp` | `0d188dfc47bfc73d8ec20bf9b7850bf153b81513fbd5a921918636f19dbabc46` |
| ACL2 executable | `/tank/fn/acl2-8.7/saved_acl2` (ACL2 8.7 / SBCL 2.6.8) |
| platform | hbox, Linux 6.11 x86_64 |
| baseline image launcher/core | `f6f9581fa1fd92c93de8eec9b5e50d3e44d48496aa289c5735b3242e45db29c9` / `d4013cbdc76752793f494dd1b1bd11df03a9e06194109fc8007f90e2d093e8b0` |

The W13 baseline source was restored unchanged after the measurement.

## Test-only image and inputs

Development configuration admits 128 records. Its existing `probe 400` helper
can write 400 records without its public-post limit, but its final reopen
correctly rejects that out-of-profile store. It therefore cannot supply the
requested within-profile 400-record state.

For this probe only, a raw image was built from the certified W13 source after
two changes restricted to `fnn-command-probe`: initialization selected the
ACL2 `:scale` profile (4096 transaction limit), and each generated article
body was fixed at 1024 octets. No book, deployed image, public command syntax,
or ACL2 policy/default was changed. The test image's modified raw source hash
was `e7d038cf2c67017e2aa0b7e30e84884d5229ccf1baff1fc11ea188560d658aff`;
its launcher/core hashes were
`d4697e35c7e2c69b9e3bcf233baffbeeb6eaf56ebeb36ed2ca489fdc7a20f565` /
`a689c3675f09453a827f56833e99eca5aa7c3158ed90f023275fb381cc2175fc`.
It was built with:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_NATIVE_BUILD=host/native/build-cost-probe.lisp \
FN_NATIVE_IMAGE=build/fn-host-cost-probe \
FN_NATIVE_LOG=build/native-host-cost-probe.log \
sh tools/build_native_host.sh
```

The command was `build/fn-host-cost-probe --fn store ROOT probe N`, once each
at `N=50` and `N=400`, with a fresh local root. The JSON field
`payload_bytes` reports the configured 32768-octet ceiling; the generated
payload was the source-pinned 1024 octets above.

## Actual saved-image timings

| committed records | in-process commit seconds | reopen seconds | full process wall/user/sys seconds |
| ---: | ---: | ---: | --- |
| 50 | 0.0950 | 0.0350 | 0.16 / 0.12 / 0.03 |
| 400 | 9.3681 | 0.3260 | 9.77 / 9.33 / 0.43 |

The 8x state increase made the commit total about 98.6x larger (mean commit
time 1.90 ms to 23.42 ms per record). Reopen grew about 9.3x. These are two
points on one hbox and do not establish an asymptotic bound, but they do rule
out attributing the observed publish cost to fixed startup alone.

## Sampled body attribution

`perf` was unavailable to the unprivileged hbox account
(`kernel.perf_event_paranoid=4`). A second clearly test-only saved image added
`sb-sprof` around `fnn-command-probe` alone and wrote its flat report to
stderr. Its modified raw source hash was
`5ee6a1d5b2196315b5c8d8c49dbf4b71deba683110709affef06b58161972e5c`;
its launcher/core hashes were
`934fbeae11916ae208aae8bc77b02bf72e511e7ddf7ffaed8f6491d0d85b8b83` /
`94149034f4475ef3843b440ecc781019e1437a3299c227696c95364dbb16b1d2`.
The 400-record run produced 990 CPU samples at 10 ms (9.9 sampled seconds).

- `FNN-CALL` accounted for 978 total samples (98.8%); this directly observes
  the saved image calling the wrapper counterpart. It does **not** establish a
  blanket property of every native core call; frame-trailer and BP paths have
  separately identified direct book calls.
- `FNN-BRIDGE-PREPARE` → `FN-STORE-SN-PREPARE` → `FN-SN-PREPARE` →
  `FN-SF-PREPARE-RECORD` accounted for 92.9–93.2% cumulatively.
- The explicit `FN-SF-HISTORY-RECOVERABLEP` call in
  `books/store-files.lisp` was 93.2% cumulative. It replays the candidate
  history and calls `FN-NODE-STATEP` (53.6% cumulative), whose cross-field
  walkers include `FN-ALL-ARTICLE-MEMBERSHIPS`, binding Message-ID/identity
  walks, and list membership/equality.
- Raw host work was small in this run: `FNN-PUBLISH` was 1.8% cumulative and
  `FNN-DURABLE-RECORDS` 1.6%. The profile therefore does not support blaming
  the physical file loop for the publish growth.

This distinguishes a carried-invariant guard from the current bottleneck:
`fn-sf-prepare-record` deliberately performs a semantic replay admission
check in its executable body. Turning guards off, or adding a lint that bans
book calls, would not remove that work.

## Implemented bounded host improvement

Commit `2da8400` changes only `fnn-transaction-files` in raw native I/O. It
carries an explicit enumeration count while preserving the exact configured
limit, replacing the prior `(length files)` recomputation for every directory
entry. `tests/native_io_progress.lisp` exercises acceptance at the bound and
refusal of the first excess entry; `sh tests/test_native_io_progress.sh`
passes. This avoids a host-only O(n²) recount during recovery enumeration; it
does not change replay, allocation, publication, or semantic admission.

## Next proof/implementation packet

The next meaningful performance change is an ACL2-owned indexed or carried
admission representation for the candidate-history check. It needs a defined
representation, a correspondence theorem to the existing record history, and
preservation through prepare, durable completion, refusal/abort, and recovery.
The existing `fn-sn-indexedp` is precedent but is intentionally not yet the
subject used by `fn-sf-history-recoverablep`. No such correspondence or cost
claim is made by this packet.
