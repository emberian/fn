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
