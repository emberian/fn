# Transaction-directory fence projection packet, 2026-09-23

This is a partial K8 packet, not the post-fence universal crash-scan theorem.
At the source bytes in
[`certify-20260923T184817Z-4098647.json`](manifests/certify-20260923T184817Z-4098647.json),
ACL2 8.7 certified `books/byte-store-record-fence.lisp` and its test book on
hbox with the same `w28/acl2-literal-4g` toolchain and `--jobs 2` as the K5
packet. The selected command was `python3 tools/farm.py submit hbox --jobs 2
--acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache
--remote-root /tank/fn/gates/takeover-byte-store-k8
books/byte-store-record-fence tests/acl2/byte-store-record-fence-tests`.

The proved byte-state transition says that `fn-bs-fence-dir` on
`:transactions` materializes its view namespace and each entry into durable
directory state, while preserving root authority, the durable frontier, and
all view content and transaction reads. It drains only that directory's
pending operations. The witness reaches the second P-RECORD
`record-attempted` cut after the first record is durable; before the fence,
a crash may scan only the first record, while after it the durable namespace
and scanner have both records. The `must-fail` case removes the fence and
fails the exact two-record conclusion.

The remaining K8 proof obligation is to connect the fenced state's *durable*
transaction read to the source view's already established exact read under
`fn-bs-store-relation`, then prove the fenced byte state is related to
`fn-sf-record-dir-result ks :ok`. Only after that bridge may K1's scan
result be applied to every crash image of the fenced state. General K0, K6
raw frame provenance and physical A-DURABILITY qualification remain open.
