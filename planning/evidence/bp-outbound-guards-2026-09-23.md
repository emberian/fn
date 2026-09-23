# Inherited BP outbound guard packet, 2026-09-23

Commit `58fa245d` adds verified guards to the exact inherited
`fn-bpn-step` dependencies through enqueue, contact, forwarding callback,
persistence callback and clock. The machine book now verifies its
applicability, apply-record, proposal, expiry and field/accessor helpers as
well. These are ACL2 `verify-guards` events on the executable functions, not
standalone theorems about sibling APIs. The executable bodies are unchanged.

The guards of transition helpers carry `fn-bpn-machine-statep` as an
assumption. Local field facts and `:use` hints keep that recognizer closed
during their proofs. The contact branch uses the existing state constructor
and contact-list correspondence, moved from
`bp-node-machine-invariants.lisp` into `bp-node-machine.lisp` because a
guard proof in the machine cannot include its dependent invariants book.
The copied theorem names and statements are unchanged; no whole-state
recognizer was added to any served helper body. The forwarding callback
proof derives a true-list key from a found job rather than trusting a
callback key.

ACL2 8.7 / SBCL 2.6.8 on hbox passed `run-20260923T170820Z-970c`,
manifest `planning/evidence/manifests/certify-20260923T170828Z-3968925.json`
(machine, invariants, foundation and their tests), then
`run-20260923T170921Z-7aa1`, manifest
`planning/evidence/manifests/certify-20260923T170923Z-3970710.json`
(the four additional affected roots). Both runs used jobs 2, the exact
toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
an incremental cache and no `--closure`. Strict green check from
`b4e1855c` reports zero ungreen affected roots. `make check` completed
after local ledger regeneration; generated ledger edits were reverted for
root's integrated batch.

`fn-bpn-replay-records`, `fn-bpn-restart-step`, `fn-bpn-step` and
`fn-bpnf-step` still lack verified guards. Replay's recursive guard needs
the already proved downstream invariant that applying an applicable record
preserves machine state and a frontier bound that stays below 4096 for each
remaining record. A guard book including the invariant book is a possible
proof placement, but has not been admitted. `fn-bpn-step` still executes
its whole-state recognizer at entry, which must be removed or replaced by
a carried invariant before the native hot path switches. The native host
still calls the old step at `host/native/bp-service.lisp:112`; no physical
FNBS publisher or receive-ACK gate is claimed here.
