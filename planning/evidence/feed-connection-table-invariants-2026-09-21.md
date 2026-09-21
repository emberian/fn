# Feed connection table invariant certification (2026-09-21)

Revision `9ccbc16f12cde3f5cae8b5b002da5fd2bbfc754f` was certified on
`nextop.local` (macOS arm64) with ACL2 8.7 at `/opt/homebrew/bin/acl2`:

```text
FN_ACL2=/opt/homebrew/bin/acl2 FN_ACL2_TIMEOUT_SECONDS=1800 \
  python3 tools/certify_books.py --jobs 2 --closure \
  books/feed-connection-invariants \
  tests/acl2/feed-connection-invariants-tests
```

Run `certify-20260921T105651Z-18213` passed all 39 roots in the requested
dependency closure in 191.637 seconds of certification wall time. The exact
environment, executable digest, source digests, per-book results, and timings
are in
[`manifests/certify-20260921T105651Z-18213.json`](manifests/certify-20260921T105651Z-18213.json).

This run establishes the ACL2 table initializer, lookup facts, put/remove
preservation, and selected-connection step preservation, together with the
reachable witnesses and premise teeth in the test book. It does not establish
that a host caller maintains the invariant: that requires the caller to
initialize with `fn-fc-table-initial-state`, update only through the proved
put/remove operations, and check the selected lookup before stepping it.
