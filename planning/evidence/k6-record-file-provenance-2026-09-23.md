# K6 P-RECORD file-fence provenance, first certified cut

`fn-bs-k6-actual-record-file-cut-has-exact-frame` in
`books/byte-store-record-provenance.lisp` names the actual `fn-bs-run` of
`fn-bs-record-program`: at pair index 5, after successful create, write-all,
file fsync and record-file observation, the fresh inode's durable octets equal
the exact supplied frame. The proof reduces that interpreted cut to the
create/write/fence transition and proves the raw octet equality; it does not
derive its result by comparing decoded Store record members.

The theorem requires `fn-bs-statep`, a fresh staging key, and a
true-list frame. `tests/acl2/byte-store-record-provenance-tests.lisp` executes
a second P-RECORD with one prior durable article and has separate failing
examples for an occupied staging key, malformed frame and a stale pending
write to the unallocated next inode. The prior article remains durable at
the observed cut.

Hbox selected certification: `python3 tools/farm.py submit hbox --jobs 2
--acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache
--remote-root /tank/fn/gates/takeover-byte-store-k568
books/byte-store-record-provenance
tests/acl2/byte-store-record-provenance-tests`, then
`python3 tools/farm.py wait hbox run-20260923T194601Z-8871 --wait-seconds 30`.
Both requested roots passed. Exact ACL2 executable/core identity, source and
closure digests, invocation and per-root results are in
`planning/evidence/manifests/certify-20260923T194604Z-4187906.json`.
`make check` passed after ledger regeneration.

K6 remains open at the immutable-link cut and the crash-image scanner: this
packet proves the raw frame at the file-fence inode, not yet that every
surviving transaction name in a crash image points to it. General K0
relation preservation and physical successful-directory-fence qualification
remain separate obligations.
