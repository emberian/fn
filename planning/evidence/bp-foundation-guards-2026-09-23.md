# BP foundation typed ingress and guard batch, 2026-09-23

Commit `67c5fe18` makes the finite A1 `:receive-bundle` kernel accept only
typed `:cl` ingress provenance before it issues a kind-5 FNBS proposal. The
session is an unsigned-64 pair, transfer and generation are unsigned-64,
the announced peer is a BP EID, and the admitted principal is nil or bounded
canonical text octets. This is a replayable shape requirement, not proof that
the host's admission decision was honest or current. The test book checks a
well-shaped proposal and a malformed-session refusal with no publication.

The foundation's 39 helper functions now have explicit `verify-guards`
events. Accessors use the already guarded total `fn-bpn-nth` on arbitrary
inputs, and the receive decision requires a valid bundle. A primary-shape
lemma in the inherited outbound machine verifies its lifecycle record,
pending, and machine-state recognizer guards. These are actual ACL2 guard
events. `fn-bpnf-step` and the host-called `fn-bpn-step` remain unverified:
the latter's record applicability, proposal, and job expiry functions are
the first open guard dependencies, with branches depending on them. The
native host still calls `fn-bpn-step` at `host/native/bp-service.lisp:112`;
there is no new native caller or final receive-ACK gate in this batch.

The ACL2 8.7 / SBCL 2.6.8 incremental hbox run
`run-20260923T165155Z-3d4f` passed the machine, foundation, and foundation
test roots; its manifest is
`planning/evidence/manifests/certify-20260923T165201Z-3943323.json`.
After the inherited machine source changed, run
`run-20260923T165317Z-34dd` certified the seven affected dependent roots
and their missing prerequisites; its manifest is
`planning/evidence/manifests/certify-20260923T165320Z-3945487.json`.
Both use toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
jobs 2, and the bounded explicit-root incremental mode, without `--closure`.
`green_check.py --changed-since b4e1855c --strict` found zero ungreen changed
or dependent roots at these bytes. `make check` passed after local ledger
regeneration; generated ledger updates are left to root's integrated batch.

A2 refines the unchanged effect `(epoch op-id held)` and reconstructs the
initial held row from typed provenance and exact bundle wire. A physical
kind-5 encoder refusal must become a matched `:persist-result` `:refused`
before any receive answer; FNBS replay, recovery epoch/frontier restoration,
top-level guard closure, and the native service switch remain open.
