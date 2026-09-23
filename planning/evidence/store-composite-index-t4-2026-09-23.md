# T4: the accepted composite Store article and its carried index

`host/store-node-host.lisp:551` calls `fn-sn-finish` inside
`fn-store-sn-finish`. The certified
`fn-sn-finish-preserves-indexedp` now has only `fn-sn-indexedp` as its
hypothesis: it covers retention, neutral identity, accepted composite
identity, and ordinary article completion. Its composite arm relies on
`fn-sn-composite-replay-installs-one-article` and
`fn-sn-composite-replay-installs-decoded-payload`: from a valid idle node and
a non-nil composite replay, the new Store head is the decoded article, its
payload is the decoded record payload, and the old Store is the tail.
`fn-sn-composite-replay-preserves-index-invariant` proves that
`fn-sn-composite-delta` indexes that exact payload. The enabled completion
condition establishes replay success and the idle premise; neither is an
extra hypothesis on the finish theorem. No whole-Store projection runs in
the transition.

The real transition witness in
`tests/acl2/store-node-composite-index-tests.lisp` enrolls the hybrid
snapshot, installs a statement-verifying keyring, and finishes a bound
composite article with a signed `FN-Statement` header. It asserts the served
statement lookup changes from NIL to the signed statement, the installed
article payload equals the composite's encoded legacy record payload, and a
well-shaped stale index defeats the conclusion without `fn-sn-indexedp`.
The test uses the existing toy signature realiser and observed hybrid
verification statuses, not a proof of signature primitives.

Qualified persvati source-book certification passed in
[`certify-20260923T172429Z-2166338.json`](manifests/certify-20260923T172429Z-2166338.json)
for `books/store-node-invariants.lisp` SHA-256
`7e0e73c08d772ab2037e84e3da42bafdffa0f10753b29d9dd6c53eba49e82b67`.
It used ACL2 Version 8.7, qualified executable
`/home/ember/fn-gates/toolchains/w25/acl2-literal`, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
and two existing slots. This certifies the unrestricted theorem and its
local replay/index lemmas.

The focused test has **not yet certified**. Incremental runs
[`certify-20260923T172706Z-2191257.json`](manifests/certify-20260923T172706Z-2191257.json),
[`certify-20260923T172907Z-2212193.json`](manifests/certify-20260923T172907Z-2212193.json),
and the reduced-closure
[`certify-20260923T173250Z-2249474.json`](manifests/certify-20260923T173250Z-2249474.json)
failed before entering its forms: ACL2 rejected cached include certificates
with the same familiar book names but incompatible full-name/annotation
chains from different cache origins. The first error in the reduced run is
while including `store-node` from `store-node-index-tests`; the source book
had already certified at these bytes. No test assertion or test theorem was
executed by those runs. A coherent cached origin or bounded recertification
of the conflicting include frontier is the next certification step.

## Integrated test qualification

Root's coherent selected-closure run on persvati,
`run-20260923T173810Z-2a02`, certified the composite index test and all its
dependencies at source `586b275a` in
`/home/ember/fn-gates/takeover-cohesive-store-config-586b275a`.
The [manifest](manifests/certify-20260923T173817Z-2301915.json) records
71.753 seconds for the shared run. The run as a whole failed because the
independent experimental configuration replay book called an unverified
helper; the Store index book and its positive statement-lookup/payload and
negative stale-index tests passed. This was one deliberate coherent closure
qualification after mixed certificate origins prevented earlier tests from
reaching their forms, not an ordinary incremental rerun. The later FNWF
frame extension still requires qualification of the combined current source.
