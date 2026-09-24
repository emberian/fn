# Consumer Store integration convergence, 2026-09-23

The full Makefile-root farm run `run-20260923T213308Z-9bef` at `38d4905c`
used the hbox w28 ACL2 binary and existing content/toolchain-matched cache,
with four jobs and a 300-second per-book bound. Original manifest
[213325Z-210156](manifests/certify-20260923T213325Z-210156.json) records
312 cached books, 194 newly passed and 24 failed books/dependents in
195.125 seconds. Five source joins caused the red set: Store fast preparation,
owner constructor projections, stamp event classification, BP replay event
disjointness, and physical consumer crash recovery. Failures are preserved;
this is not a qualified release image.

## The actual optimized prepare

`fn-spc-prepare`, called through the native owner prepare path, now evaluates
the same bounded consumer-prefix step as `fn-sn-prepare`. This keeps the
existing `fn-spc-prepare-equals-specification-under-relation` statement intact;
it does not strengthen its hypothesis to hide a discrepancy. The optimized
path still omits whole-history replay. Keyring replacement preserves both the
consumer projection and identity sequence; the local field lemma now says so.

The test book retains the original missing-relation counterexample. Its stale
node now preserves the current sequence/projection, so the new gate does not
mask the counterexample. A separate structurally valid stale consumer prefix
passes the article and file candidate checks but is refused by both prepare
functions; a `must-fail` witness rules out staging that candidate.

The first repair certification reached a missing keyring-field lemma; the
original [213846Z-220430](manifests/certify-20260923T213846Z-220430.json)
manifest is retained. A live ACL2 session then admitted the corrected fields
and every remaining form in the book. Final incremental farm run
`run-20260923T214118Z-d30f` certified the actual book and test book with 67
matching cached dependencies, two jobs and a 90-second bound. The original
[214127Z-228040](manifests/certify-20260923T214127Z-228040.json) records the
source digests and exact toolchain. This repairs one source join, not the
other four or the full native E2 workflow.

`sh tests/test_native_owner_consumer_raw.sh` passed locally. Its recording
stubs exercise the native publisher's call order and refusal cut; they do not
establish disk durability or an authenticated end-to-end consumer session.

## Combined repair check

At `22418c27`, the next full Makefile-root run reused 515 matching books and
certified fourteen more in 43.390 seconds. Only the owner-prepare negative
fixture failed; all implementation and invariant books passed. Its stale-node
constructor also reset the identity sequence, so the new prefix gate masked
the intended missing-relation counterexample. The fixture now changes only
the node/index while retaining the actual sequence and consumer projection.
The scoped repaired test passed run `run-20260923T220303Z-19e5`; this is a
repair of the witness, with no new implementation or theorem weakening.
The original full-run manifest is
[215944Z-269366](manifests/certify-20260923T215944Z-269366.json).

The other repairs now derive physical and BP restart consumer validity from
`fn-csi-full-relationp`, a relation preserved by the Store trace, rather than
assuming the desired replay result. Native endpoint qualification remains a
subsequent task. `make check` passed at `22418c27`.
