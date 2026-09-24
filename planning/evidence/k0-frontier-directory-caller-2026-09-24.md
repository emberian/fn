# Successful allocator directory cut and Store-node callback

Source: `2683ffff` on `implement/storage-k0-completion`, based on `8c61c098`.
The new K0 packet is `bb9b4f59`, `4509f4b5` and `bfc18af8`, with the
qualified Store v6 native bridge and K6 proof-cost repairs cherry-picked
into this source. The affected proof and teeth roots are
`books/byte-store-record-provenance.lisp` and
`tests/acl2/byte-store-record-provenance-tests.lisp`.

Under an already related ready byte/kernel input, a typed next-frontier
frame, and a fresh staging name, the actual `fn-bs-run` P-FRONTIER pair 12
after the root directory fence satisfies the full byte/kernel relation.
Pair 14 after the directory-success callback retains the same byte state,
has phase `:reserved`, and satisfies that relation. The new
`fn-bs-k0-frontier-native-call-sequence-matches-run` joins those interpreted
cuts to four successive `fn-sn-io` observations: start, file fence,
replacement, and root directory success. The native allocator issues those
observations in `host/native/io.lisp:1515-1536`; the standalone callback
calls `fn-sn-io` through `host/store-node-host.lisp:432`. The test book runs
a reachable first allocation and has one `must-fail` case for each theorem
premise: Store state, initial relation, typed frontier input, and fresh
staging name.

The shared native owner binds the observation callback to `fn-owner-io`
(`host/native/owner.lisp:101`, `host/owner-host.lisp:299`), whose owner event
projection is not proved by this packet. The theorem does not claim that
real syscalls have the modeled outcomes or that a physical crash honors the
model's barrier choices. The relation at other cuts, failure outcomes and
served call-entry establishment remain K0 work.

`python3 tools/farm.py submit hbox books/byte-store-record-provenance
tests/acl2/byte-store-record-provenance-tests --jobs 2
--timeout-seconds 300
--remote-root /tank/fn/gates/storage-k0-2683ffff-20260924` submitted
`run-20260924T040145Z-822a`. The archived
[manifest](manifests/certify-20260924T040155Z-843770.json) reports both
roots passed, ACL2 8.7, qualified hbox toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
and `certify_wall_seconds: 10.488` (provenance book 7.936 seconds, test book
2.527 seconds). Its `source_digests_sha256` bind the exact source and include
closure. The farm mirror has no Git metadata, so `git_revision` is null.
This is selected book/test certification, not a whole-image claim.
