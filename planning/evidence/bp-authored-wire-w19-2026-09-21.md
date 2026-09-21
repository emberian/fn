# W19 immutable authored-wire publication evidence

Functional source is commit
`a9c07b487b118308832545565444e8ff31a697bf` on
`w19/bp-authored-wire`.

The native `bp send` caller at `host/native/bp.lisp:188` calls
`fn-bpn-host-authored-wire-authorize`, a direct wrapper around
`fn-bpn-authored-wire-authorize`.  ACL2 derives the reserved decimal name and
exact wire, then returns the `fn-jpub` initial publication state consumed by
`fnn-immutable-publish-effect` at `host/native/bp.lisp:216`.  The host holds
`.spool.lock`, observes exact-name absence before authorization, checks ACL2's
returned echo, and does not author or replace the final wire itself.

`fn-bpn-authored-wire-authorize-carries-reservation` is a correspondence
projection for that call.  It returns the exact reservation sequence, the
name derived from it and `fn-bpn-send`'s exact wire under valid configuration,
endpoint, ADU, clock observation and reservation, plus the trusted lock-held
and exact-name-absent observations.  The theorem is not a registry keystone;
cross-operation nonreuse remains owned by the existing sequence-fidelity
proof.  The test book has a concrete sequence/name/wire witness and separate
`must-fail` checks for the lock, absence and reservation-token hypotheses.

The recovered persvati manifest
`certify-20260921T112508Z-3251134.json` records a passed 129-of-129 source
closure in 1003.158 seconds with 16 slots and ACL2 8.7.  Its exact per-file
digests match `a9c07b48`, including `books/bp-authored-wire.lisp`.  Because
`git_revision` is null, those digests are the source identity.  The executable
was `/home/ember/fn-tools/acl2-8.7/saved_acl2`, SHA-256
`c8a7a804d9cc80e2025a8ab0e1d9325f2a0c4a027a5dcdcb2c1093e9cd5c8163`.
The recovered closure does not include
`tests/acl2/bp-authored-wire-tests.lisp` as a root.

No source-matched native build or runtime result was recovered.  In
particular, this record does not establish that collision, restart or injected
publication-failure scenarios passed in an image, successful TCPCL exchange,
filesystem durability, or hardware persistence.  The DTN runtime scenario in
the source remains a test specification for those branches.
