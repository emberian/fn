# Repaired topic/index/BP combined gate: second verdict

Frozen source `f0d67034fca33c9a7701718a61f4c8c31ffd4a6e` passed root's
static `make check` but did **not** pass its one ordinary four-job hbox ACL2
qualification. The run was `run-20260924T041225Z-7481` at
`/tank/fn/gates/topic-index-repaired-f0d67034-20260924`, over 357 unique
default, DTN and ACL2-test roots, without `--closure`. It used the shared
`/tank/fn/certcache` and `/tank/fn/toolchains/w28/acl2-literal-4g` (toolchain
identity `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`).
The original manifest is
`planning/evidence/manifests/certify-20260924T041301Z-855900.json`, SHA-256
`85d444a947316b6bf1f8012113d0b4736286c4e22badafca2b8663cd27e8e527`.

The cache matched 521 of 618 books; 97 were attempted. Certification wall
time was 144.093 seconds. ACL2 slot wait totaled 0.019 seconds (maximum
0.008 seconds). Of 15 failed books/tests, two have direct proof failures:

| Book | First failed event | Exact log |
| --- | --- | --- |
| `books/consumer-store-invariants` | `FN-CSI-FINISH-ADVANCES-PROJECTION-BY-DEFINITION` (book wall 48.701 s) | `build/acl2/certify-20260924T041301Z-855900/books--consumer-store-invariants.certify.log` |
| `books/config-owner-live` | `FN-OCL-DURABLE-KEEPS-FILE-PHASE` | `build/acl2/certify-20260924T041301Z-855900/books--config-owner-live.certify.log` |

The other 13 failed because one of these certificates or its dependent
certificate was absent; they are not independent proof refutations. The
slowest successful books were `bp-fnbs-codec-invariants` (25.933 s),
`bp-fnbs-byte-invariants` (23.374 s), `owner-config` (15.056 s),
`bp-channel-ingress` (14.194 s), and `bp-node-fragment-guards` (12.299 s).
These are per-book wall times at this exact source/cache condition, not a
like-for-like speed regression claim. No event exceeded the 300-second
diagnostic bound.

The two direct proofs need scoped repair followed by another single combined
ordinary qualification. No `f0d67034` image was built; therefore this run
provides no native topic, indexed consumer/status, or BP-fragment runtime
claim. The protected `/tank/fn/node` service was untouched.
