# E2 consumer Store model join, 2026-09-23

The versioned `fnce` event shares the Store journal sequence and allocator
transaction ID. `fn-cpe-projection-step` admits bootstrap, register, ack,
rebase, unregister and incarnation rollover only at the exact next sequence.
`fn-sn-prepare-consumer` stages a valid proposal; `fn-sn-finish` carries its
projection only through a durable Store completion; `fn-sn-recover` and
`fn-cpo-open-observed` rebuild it from the exact Store event history. The
consumer slot follows the physical configuration-history slot, so the T8b
`fn-cpo-install` retains both. A structurally recoverable article and identity
history can still contain an unbootstrapped consumer registration; observed
reopen theorems now require `fn-sn-observed-consumer-okp` rather than claiming
that such an image succeeds.

`tests/acl2/consumer-store-node-tests.lisp` exercises bootstrap, register,
ack, duplicate-bootstrap refusal, staged and absent-link ack nonmutation,
crash/reopen equality, an invalid unbootstrapped image, and physical replay
with a configuration write tied to the registration's Store transaction ID.
The selected exact-prefix pack reconstructs the original event list under
`fn-cc-expand`; the separate node-checkpoint summary does not yet contain
consumer progress. The E2 pack/restore adversarial trace remains
`specified-not-executed`.

The scoped local certification invocation was
`python3 tools/certify_books.py --jobs 2 --timeout-seconds 180
books/consumer-store-projection tests/acl2/consumer-store-projection-tests
books/store-events books/replay books/store-node books/store-node-invariants
books/store-node-traces books/store-node-resolution books/store-observed
books/config-observed tests/acl2/consumer-store-node-tests`. All named roots
passed in `build/acl2/certify-20260923T191152Z-9425/manifest.json` with ACL2
Version 8.7 at binary SHA-256
`36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324`.
The manifest records each source digest and the WIP base revision
`702b9e13e70a137e06fb54708ff8ca151deaf58c`; this result covers those
exact files, not a merged image. `make check` passed after ledger generation.

No authenticated native consumer command, bounded poll/query selector,
consumer-owned database, source-processing proof, checkpoint projection
migration, or two-Store execution follows from these ACL2 model certificates.
The retained record-count Store profile must pay for every consumer ack event
before reservation; the 256-entry table bound does not bound ack history.
