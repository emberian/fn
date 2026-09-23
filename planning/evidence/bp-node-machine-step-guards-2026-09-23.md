# BP step guard closure, 2026-09-23

The native outbound service still calls `fn-bpn-step` at
`host/native/bp-service.lisp:112`. This packet verifies that exact ACL2
function's guard, its bounded replay/restart helpers, and the named A1
refinement `fn-bpnf-step` in `books/bp-node-machine-guards.lisp`. The step
guard requires a maintained `fn-bpn-machine-statep` and a
`fn-bpn-machine-eventp`; a delegated `:base` event has the same event
requirement in the foundation guard. The event predicate bounds restart's
record list to 4096. No recognizer of the entire state is inserted into an
ordinary step's executable body to satisfy the guard. The inherited step's
logical arm retains its malformed-state response, while its `mbe` executable
arm calls the same named dispatcher directly; successful guard verification
establishes agreement under the stated guard. The dependent invariant and
authorization theorems continue to concern the host-called `fn-bpn-step`.

The guard proofs use carried state-preservation facts from
`bp-node-machine-invariants.lisp`, with recognizers closed at the replay and
restart call sites. They do not prove that the current native adapter enters
with those guard premises, nor do they establish an FNBS publisher or a native
receive-ACK gate. The foundation remains a named, unhosted refinement until
the A2 byte publisher/replay and the guarded native caller are connected.
Its currently verified guard covers the base-state component and delegated
event; it is not a recognizer for every new held/outcome/handoff slot.

ACL2 8.7 / SBCL 2.6.8 on hbox, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
certified explicit roots with jobs 2 and incremental matching cache, without
`--closure`. Run `run-20260923T172515Z-e78a` passed the invariant and new
guard books at the source digests in manifest
`planning/evidence/manifests/certify-20260923T172517Z-3998952.json`.
The affected book/test closure then passed across the source-matched results
in manifests `certify-20260923T172824Z-4003765.json`,
`certify-20260923T173001Z-4006083.json`,
`certify-20260923T173048Z-4007094.json`, and
`certify-20260923T173221Z-4009647.json`. The intermediate runs failed where
the authorization proof hints had not yet opened the factored dispatcher and
where an oversized-restart negative assertion attempted to evaluate a
guarded function outside its guard. The authorization proof hints now open
the dispatcher; its oversized-restart hypothesis tooth remains a certified
`must-fail` theorem case. The intermediate failures are preserved in their
manifests rather than called successful runs. `green_check.py --changed-since
b4e1855c --strict` reported zero ungreen changed/dependent roots at the final
bytes, and `make check` passed after local ledger regeneration. Root owns the
integrated generated ledger; this lane did not commit a lane-local ledger.
