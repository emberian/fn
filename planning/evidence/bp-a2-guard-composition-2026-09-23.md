# BP A2 replay and A1 guard composition, 2026-09-23

This lane combines the received FNBS kind-5 codec, byte publication cuts,
canonical byte replay, recovery-only `fn-bpnf-step` event, and mixed FNBS
namespace classifier with the guarded A1 foundation. The recovery event is
`(:recover-fnbs new-epoch base-records sequence-ready replay-result)`;
`fn-bpnf-recover-event` constructs it from the exact ACL2 byte replay of
observed `(name octets)` rows. A successful event installs the recovered
base and held rows together, clears volatile issued/wait state, and starts a
fresh epoch. A fault leaves the uncertain state fenced. The ordinary event
fence theorem explicitly excludes this recovery event.

The merged step preserves the total `fn-cbor-ag-car` event dispatch and
requires a valid base state; delegated outbound events satisfy
`fn-bpn-machine-eventp`, and recovery records are bounded to 4096 before
calling the guarded base restart. `bp-node-machine-guards.lisp` now verifies
both `fn-bpnf-recover-fnbs-step` and `fn-bpnf-step`. Cold recovery validates
each held row and its slot/byte budgets. Its scalar bounds are checked inside
`fn-bpnf-recovery-heldp`, so the guard proof does not pull a whole-state
invariant book into the foundation or revalidate the held list on an
ordinary served event.

The ACL2 mixed namespace plan classifies bounded hidden stages, legacy
20-digit final names, and epoch-operation kind-5 candidates in the one FNBS
directory. The legacy contiguous plan still validates its subset; kind-5
replay validates exact names against canonical decoded frames. The test book
has coexistence and unknown-name refusal witnesses. This does not yet make
the current native `bp receive` caller use the foundation. Its adapter still
uses the older receive/evidence path, and the outbound service's existing
namespace plan would reject a kind-5 name until a native mixed-recovery
join is installed. No native-image or two-process receive claim follows.

ACL2 8.7 / SBCL 2.6.8 on hbox with qualified toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`
passed the foundation and guard roots in run `run-20260923T180510Z-6cac`,
manifest `planning/evidence/manifests/certify-20260923T180512Z-4052030.json`.
Run `run-20260923T180630Z-04d0` certified all 13 stale or absent A2
dependent book/test roots, including the mixed namespace tests, manifest
`planning/evidence/manifests/certify-20260923T180633Z-4053762.json`.
Both used explicit roots, jobs 2, matching incremental cache and no
`--closure`; the second had a 300-second per-book limit. The strict
`green_check.py --changed-since b4e1855c` report found zero ungreen among
19 changed and four dependent roots at these exact bytes.
