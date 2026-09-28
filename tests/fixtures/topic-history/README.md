# Native topic admission vectors

`ml-dsa-65-test-{private,public}.pem` is a disposable test-only OpenSSL
ML-DSA-65 pair. The Ed25519 test pair and principal are constants in
`tests/test_native_topic_local.py`; no production key is present.

The two `FN-Topic` field files are exact results of ACL2
`fn-th-field-encode`, not a Python CBOR/base64 implementation.
`tests/acl2/topic-history-native-vector-tests.lisp` certifies both expected
field values against the executable encoder. The root value
is `(:root [1]×32 [85]×32 KEYSET "fn.test" (([85]×32 KEYSET)))`, where
`KEYSET` is the 48-octet `fn-th-verified-author-ref` keyset ID
`666e2f7375626a6563742f7631000102bbbc6e65db95b8315029519aa0eec38bf50e2c912481534a2d7fa102a1975749`.
The report value is `(:report ROOT-ID ROOT-ID nil)`, with `ROOT-ID` obtained
from the authenticated exact `matched-root.source` by the native
`hybrid-verify-source` ACL2 path:
`666e2f7375626a6563742f76310001020be9100e274debb5a9f99e0ada546a8041cd0a120079234dc5abe695e4bd6e27`.

The source files contain those exact field bytes. Editing the root source
changes its ID and invalidates the report fixture, by design.  The IDs are
BLAKE3 identities (algorithm 2, store format 10); lane blake3-digest
rewrote the SHA-256 (algorithm 1) fixtures by re-deriving both IDs
(tools/blake3_ref.py) and re-encoding the fields, octet for octet otherwise. Before native
admission, an existing signed-carrier image independently verified both
fixed sources and reported `controller-matched` for the root. A source-matched
image must still run the admission/reopen test; the fixtures alone do not
prove publication.

`matched-second-root.source` is the same ACL2-encoded root profile with a
different 32-octet nonce (`02` repeated) and a distinct Message-ID. Its field
is checked by `topic-history-native-vector-tests.lisp`; the exact source is
pinned by SHA-256 in the dual-image migration test. That test creates a v1
history with the older image, then admits this separate root through the v2
image under the same immutable local administrator installation.
