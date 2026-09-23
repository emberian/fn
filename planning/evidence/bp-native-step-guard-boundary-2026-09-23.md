# Native BP step guard boundary, 2026-09-23

Commit `4f709de4` closes the saved-image load gap for the already certified
`fn-bpn-step` guard. Both `host/native/build.lisp` and
`host/native/build-dtn.lisp` now include `books/bp-node-machine-guards` before
loading `host/bp-node-machine-host.lisp`. The default and DTN
`proof_artifacts.py roots` declarations both name that guard book, and
`tests.test_proof_artifacts` passed. Merely listing the guard book as a
Makefile certification root had not loaded its `verify-guards` events into
either saved image.

`host/native/bp-service.lisp:fnn-bps-open` checks
`fn-bpn-machine-invariantp` once on its freshly constructed state.
`fnn-bps-step` checks the ACL2 `fn-bpn-machine-eventp` on every event before
calling the exact `fn-bpn-step` assurance subject. The service writes its
state only at construction and from a step answer, and
`fn-bpn-step-preserves-machine-invariant` proves preservation under exactly
those invariant and event premises. The event check is bounded (including
restart's 4096-record list); it does not scan held machine state. The
`fn-bpn-existing-sequence` executable arm and `fn-bpn-host-ready-peers`
projection also omit the previous per-call whole-state recognizers, relying
on that maintained state. The guarded `mbe` arm of
`fn-bpn-existing-sequence` retains its old total logical response.

This is a source-to-theorem call-boundary argument, not native-image
execution evidence. No new saved image or live node was built in this lane,
and A2's FNBS publisher/recovery must be integrated before the foundation
can be called natively. The source assumes service state is not modified by
code outside its construction and step-answer assignments; this was checked
against all `fnn-bps-state` writes in `host/native/bp-service.lisp`.

ACL2 8.7 / SBCL 2.6.8 on hbox with toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`
passed the guard-book closure in `run-20260923T173920Z-6d07`, manifest
`planning/evidence/manifests/certify-20260923T173922Z-4017092.json`, and
the seven affected dependent book/test roots in `run-20260923T174018Z-3378`,
manifest `planning/evidence/manifests/certify-20260923T174021Z-4018354.json`.
Both were explicit-root incremental runs with jobs 2 and no `--closure`.
`green_check.py --changed-since b4e1855c --strict` reported zero ungreen
changed/dependent roots at these bytes.
