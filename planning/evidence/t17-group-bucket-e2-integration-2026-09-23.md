# T17 group bucket integration on E2 owner, 2026-09-23

This finite source cut starts at integrated `8e4b9e77`, after the Store E2
consumer/owner constructor work, and applies the T17 component, called-path
implementation, proof, tests and registry. The owner connection and view keep
one appended group-bucket field; the existing E2 Store state/constructor
fields remain intact. `fn-own-run-preserves-relation` and
`fn-own-read-is-served-step-on-pinned-prefix` certified at this combined
source, so the E2 owner constructor obligations and the actual grouped read
are checked together. The later historical reader theorem packet remains a
separate follow-up with store_invariants and acceptance_stamp.

Hbox ACL2 8.7 / SBCL 2.6.8 jobs-2 incremental run
`run-20260923T221209Z-7f18`, manifest
[`certify-20260923T221217Z-297353.json`](manifests/certify-20260923T221217Z-297353.json),
passed 20 newly certified roots, including `books/served`, `books/owner`,
`books/owner-invariants`, `books/nntp-invariants`, `books/nntp-auth`, and both
new and actual owner-call test books. The two primitive source digests reused
matching earlier hbox certificates recorded in
[`certify-20260923T203905Z-62098.json`](manifests/certify-20260923T203905Z-62098.json)
and [`certify-20260923T211349Z-166035.json`](manifests/certify-20260923T211349Z-166035.json).
The owner configuration/TLS incremental run `run-20260923T221543Z-c531`,
manifest
[`certify-20260923T221548Z-309869.json`](manifests/certify-20260923T221548Z-309869.json),
passed its three newly certified roots. Exact source digests and toolchain
identity are in each manifest.

`python3 tools/green_check.py --changed-since 8e4b9e77 --summary` reports
18 changed books/test roots green at current bytes and 49 of 56 inclusive
roots not green at merged bytes. This is a selected-root integration packet,
not an all-dependent or native-image qualification. `make check` passes.
Root will reconcile its concurrent a51 test/ledger packet and run the next
frozen combined closure. No native image or live node operation ran here.
