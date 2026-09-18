# Actual BPv7 transport experiment — 2026-09-18

A pinned dtn7-rs 0.21.0 build passed the
[two-node harness](../bp-dtn7/run_two_node.sh). The
[machine-readable record](2026-09-18-bpv7-transport.json) records revision
`4daf02d7ea927e9293753b2a5c4497457f6e5a40`, locked Cargo build, tool versions,
binary/script digests and observed bundle IDs. Both control and convergence
listeners were restricted to IPv6 loopback; discovery was disabled.

The actual daemons queued a binary payload while the receiver was absent,
retained it across sender restart, and forwarded it after contact returned.
Receiver restart lost its in-memory endpoint queue, but inventory rediscovered
the stored bundle. Non-destructive download preserved the BPA copy while the
harness staged exact bytes with file and directory barriers, then explicitly
deleted the bundle. The test also checked duplicate suppression, the destructive
endpoint-pop behavior, and absence of an expired attempt after renewed contact.

The pinned implementation's submit API responds before its asynchronous store
push; a successful reply is therefore not evidence of durable BPA custody.
Endpoint pop can delete the retained singleton bundle. fn must persist attempt
intent before submission and use inventory/download/durable staging before
explicit deletion. The [active BP path](../../specs/bp-path.md) records this seam.

This is actual BP transport evidence for opaque application payloads, **not yet
an end-to-end fn exchange**. It does not prove application acceptance, receipt
authorization, retention handoff, quota behavior, liveness, power-loss durability
or a mission profile. Clean restart and a bounded absence observation have their
ordinary experimental meaning. The implementation is an integration candidate,
not a production dependency selection.

Reproduce with `tests/bp-dtn7/bootstrap.sh EMPTY_WORK_DIRECTORY`. It downloads
and builds the pinned source and starts temporary loopback daemons. This optional
experiment is separate from `make test`. It requires Cargo, Git, zsh, Python,
curl, ripgrep, lsof, and the standard shell tools used by the harness.
