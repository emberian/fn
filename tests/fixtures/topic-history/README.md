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
`666e2f7375626a6563742f7631000101c9a3b20836655e1acfc6f495998f5a34fa8122d10254c74ac89306b04460c478`.
The report value is `(:report ROOT-ID ROOT-ID nil)`, with `ROOT-ID` obtained
from the authenticated exact `matched-root.source` by the native
`hybrid-verify-source` ACL2 path:
`666e2f7375626a6563742f76310001018922d895eb0b7e0c4ede370a7dc4813609c43991e546033950f6014ea4c67d0a`.

The source files contain those exact field bytes. Editing the root source
changes its ID and invalidates the report fixture, by design. Before native
admission, an existing signed-carrier image independently verified both
fixed sources and reported `controller-matched` for the root. A source-matched
image must still run the admission/reopen test; the fixtures alone do not
prove publication.
