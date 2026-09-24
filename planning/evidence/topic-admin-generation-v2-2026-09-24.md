# TOP-002 versioned administrator-generation anchor (source checkpoint)

Fresh local root anchors now use canonical `fnto` version 2 and carry the
generation of the immutable earlier administrator-install event as field 8.
`fn-th-local-propose` calls `fn-th-prepare-anchor-local`, which takes that
installed event from the carried completed topic prefix; the connected owner
uses the existing same-euid OS observation only to authorize the local caller.
`fn-sn-prepare-topic`, the Store path reached by owner publication, refuses a
fresh version-1 anchor. Historical version-1 eight-field anchors still decode
and replay with their original ID-only meaning. Version-2 replay checks both
the installed administrator ID and its event generation; it never checks
today's UID. Other topic event kinds retain version 1, and unknown future
versions or cross-version shapes refuse.

The ACL2 source and test roots passed in scoped persvati ACL2 8.7 / SBCL
2.6.8 runs with the w25 toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
shared cache, at most two jobs, 120-second per-book limit, no `--closure`:

- Exact v2 local-admin and event-codec book/tests: manifests
  `certify-20260924T050342Z-401750.json` and
  `certify-20260924T050433Z-409954.json` on the initial 67d base.
- Versioned topic-prefix book/test:
  `certify-20260924T050631Z-430575.json` on that base.
- After merging dev `b074f94e`, called local-proposal book/test:
  `run-20260924T053516Z-f16b`, PASS manifest
  `certify-20260924T053527Z-710097.json`. An earlier attempt
  `certify-20260924T053221Z-680399.json` failed because the new theorem hint
  called `fn-stxk-find` with one argument; the source was corrected.
- Store-node and Store-topic test roots were already cached at exact merged
  bytes and checked together by `run-20260924T054038Z-c1ac`, PASS manifest
  `certify-20260924T054048Z-760063.json`.
- ACL2-produced second-root field vector, with a distinct signed source for
  mixed v1/v2 history, passed `run-20260924T053935Z-438f`, manifest
  `certify-20260924T053944Z-748903.json`.
- The owner book and actual local-control test passed together on the merged
  v2 source in `run-20260924T054443Z-4fca`, manifest
  `certify-20260924T054456Z-800480.json` (SHA-256
  `3ee21ef165abd5496e3aae6f0dde2cac9a7264c62266fe7573ee3e49449f6dca`).
  All 22 selected books certified with 113 matching dependencies installed.

The disposable dual-image test in `tests/test_native_topic_local.py` is
prepared, not run. It uses the qualified pre-v2 b074 developer image retained
at `/tank/fn/gates/wide-combined-b074f94e-exact-20260924/build/fn-host-developer`
(launcher SHA-256 `c901bdf5d366fa1982a8035a0db4178d543d8df17aadfb3f1798611a9aa0fbba`,
core SHA-256 `b6dcd8c31860962032290671e62189999c6076f1ea6358c0f970ef8678499f0b`)
to create a v1 install/root/report history, then proposes a distinct v2 root
after reopening with a future v2 image. It compares exact transaction names
and SHA-256 contents before/after historical retry and another reopen. A
second disposable Store checks that the old image refuses a new v2 anchor,
while the v2 image reopens it. The second root source's exact SHA-256 is
`b89c2e45cb7dccdf3295109d010c1f8739aad9402f140c7e4ad8d069eb3b530c`;
its field bytes are checked against `fn-th-field-encode` in ACL2.

This packet has no v2 saved-image result, full affected reverse closure or
physical durability refinement. Independently, the maintained topic-prefix
relation across every Store prepare/finish/crash/recover cut remains open; BP
and byte reopen theorems currently name observed-topic validity as an interim
premise. The v2 migration does not turn that premise into a proved property.
