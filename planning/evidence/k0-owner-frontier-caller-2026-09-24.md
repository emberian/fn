# Shared-owner allocator callback projection

Source: `88304618` on `implement/storage-k0-completion`, carrying the
successful pair-12/pair-14 K0 packet and the repaired Store v6 and owner
proof hints. The changed book and test are
`books/byte-store-record-provenance.lisp` and
`tests/acl2/byte-store-record-provenance-tests.lisp`.

The native allocator reports start, file-fence, replacement and root-directory
success at `host/native/io.lisp:1515-1536`. In the shared service,
`host/native/owner.lisp:718` binds that callback to `fnn-owner-observe`, which
calls `fn-owner-io` at `host/native/owner.lisp:101`. The program-mode host
wrapper at `host/owner-host.lisp:299-302` submits
`(:store (:io operation result))` through `fn-owner-step`, whose sole event
decision is ACL2's `fn-ocfg-step`. The keystone
`fn-bs-k0-owner-io-store-is-node-io` proves that this exact event's resulting
Store-node projection equals the result of `fn-sn-io`, for every
configured-owner value, operation and result. The four-event theorem
`fn-bs-k0-owner-frontier-calls-match-byte-run` applies that projection to
the earlier K0 byte interpreter trace: under a valid Store-node state,
already related byte/kernel input, typed successor frontier frame and fresh
staging name, configured-owner callbacks reach the pair-12 file state and
pair-14 related `:reserved` state. Its proof cites the projection keystone
and the previously certified frontier trace; it is a composition corollary.

The test book runs the four real owner event forms from a valid
`fn-ocfg-statep` configured owner over the initialized byte store, with a
nondegenerate frontier advance. Four `must-fail` cases remove, in turn, the
Store-node state, initial byte/kernel relation, successor frame contract,
and fresh staging name. The projection keystone has no hypotheses and the
positive witness executes it directly.

Persvati prefix-loaded proof REPL `k0owner` installed 133 cached dependencies,
loaded 235 earlier forms, admitted the projection theorem in 0.01 seconds and
the four-event join in 0.00 seconds, then stopped and released its ACL2 slot.
Those admissions were exploratory. The source-matched selected certificate
run was `python3 tools/farm.py submit persvati
books/byte-store-record-provenance
tests/acl2/byte-store-record-provenance-tests --jobs 1
--timeout-seconds 300
--remote-root /home/ember/fn-gates/storage-owner-k0-88304618-20260924`.
Run `run-20260924T042647Z-fe82` produced the archived
[manifest](manifests/certify-20260924T042715Z-67928.json): both roots passed,
ACL2 8.7, persvati toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
`certify_wall_seconds: 14.193` (book 10.420 seconds, test 3.748 seconds).
The manifest binds the exact source and include closure by digest; the farm
mirror has no Git metadata, so its `git_revision` is null.
`green_check --changed-since c4be0d3d --summary` reported both changed
roots green with zero not green. `make check` passed.

This closes the logical owner-to-Store-node callback projection for the
successful frontier trace. It does not establish the byte/kernel relation at
every served call entry, quantify error or torn-fsync outcomes, or prove the
operating system and storage device implement the modeled barrier semantics.
