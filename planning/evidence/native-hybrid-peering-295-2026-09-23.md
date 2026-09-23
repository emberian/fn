# Authored-carrier peering: missing injection projection

On 2026-09-23 hbox ran the new native peering test from `ea15bafa`
against the frozen `295bbe35` developer image described in
[native T8/T10a evidence](native-t8-t10a-295bbe35-2026-09-23.md).
The exact driver SHA-256 was `0e778e44d411e85b2269eacb26c2149c3b11948529683603376f9605a462cd5d`; it was copied to
`/tmp/fn-hybrid-peering-ea15bafa.py`. The image, native runtime and OpenSSL
prefix were unchanged from that record.

The invocation selected only
`NativeHybridAuthorTest.test_authored_carrier_survives_native_peering_and_receiver_restart`,
with `FN_RUN_HYBRID_E2E=1`, the frozen absolute `FN_NATIVE_HOST`,
`FN_TEST_OPENSSL=/tank/fn/toolchains/openssl-3.5.8/bin/openssl`,
`FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, its `lib` on
`LD_LIBRARY_PATH`, and the frozen source on `PYTHONPATH`. Both owners and
their temporary stores used loopback; the live node was not used.

**Result: failed**, with [the original log](native-hybrid-peering-295-failure.log).
Native enrollment, signing, authored submission and actual feed arrival
completed. The returned receiver article retained the exact authored suffix.
The test then failed while locating `Path` in the author's served article.
Independent verification of the relayed carrier and receiver restart were
therefore **not reached**; arrival is not evidence that those assertions passed.

Source inspection identifies a real composition gap: the authorized carried
submission requires the received payload to equal the raw rendered carrier,
and the native caller does not add the normal NNTP injection projection.
The relay transformation edits existing Path fields; it cannot repair this
omission. The repair must construct trace fields in ACL2, preserve exact
signed source and historical verdict binding, and retain old stored schema
compatibility. No host string-building substitute is authorized.

`08918810` changes the test's accidental StopIteration into an explicit
missing-Path assertion and corrects the expected matching-peer diagnostic
to the specified double exclamation separator. That driver has not yet
passed against a repaired image. The independent
[INN lab on295](inn-lab-295bbe35-2026-09-23.md) passed its ordinary posting
and transit scope; it did not exercise this authored submission route.
