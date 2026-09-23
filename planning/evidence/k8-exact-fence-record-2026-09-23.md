# Exact record after the transaction directory fence, 2026-09-23

At source in `certify-20260923T190519Z-4130438.json`, ACL2 8.7 on hbox
certified `books/byte-store-record-fence.lisp` and
`tests/acl2/byte-store-record-fence-tests.lisp` with the
`w28/acl2-literal-4g` executable, `--jobs 2`, and the cached dependency
closure. The command was `python3 tools/farm.py submit hbox --jobs 2 --acl2
/tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache
--remote-root /tank/fn/gates/takeover-byte-store-k8
books/byte-store-record-fence tests/acl2/byte-store-record-fence-tests`.
The selected run finished with exit code zero. The manifest is
[`certify-20260923T190519Z-4130438.json`](manifests/certify-20260923T190519Z-4130438.json).

`fn-bs-k8-pending-link-fence-durable-records` proves that a related
`:record-attempted` byte/kernel pair **with a pending transaction link**
has, after `fn-bs-fence-dir :transactions`, exactly its old decoded durable
record list followed by the kernel candidate. The proof passes through the
same decoder read of the pre-fence view, the fenced inode's octets, the
pending link name, and the one-more-record list rule. The test reaches the
second actual P-RECORD publication after the first record is durable.

The pending-link premise is necessary under the current relation. At an
actual pre-link cut of that second program, advancing only the logical
kernel with `fn-sf-record-link-result :ok` produces a related
`:record-attempted` pair with no physical link. Fencing then retains only
the first record. This is a counterexample to the older phase-and-relation
only K8 statement; the corrected specification names the issued-link
premise. The host/model call-trace obligation that the real `:ok` result
follows an issued link is part of K0, not proved by this packet.

The universal post-fence crash/reopen scan statement still requires
preservation of `fn-bs-store-relation` across this fence, especially
authority-known/fenced bookkeeping when the pending target moves into the
durable transaction directory. K6 raw frame provenance, general K0, and
physical barrier qualification remain open. This certification says nothing
about live storage or physical power-loss behavior.
