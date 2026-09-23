# Topic authorship, fragment handoff and observed-channel admission

This source packet combines topic-authorship `54516681`, BP fragment handoff
`6286301c`, observed-channel admission `c9ba8b3d` and complete-peer hardening
`de3e5dc1` atop root `944916e6`. The generated ledger was rebuilt after the
merge. Both `PRF-064` (consumer Store projection) and `PRF-065` (topic
authorship), `CNS-001` and `TOP-001`, and `SCN-032` and `SCN-033` remain in
their registries. `make check` and `tools/ledger.py --check` passed at source
`d3af1b3e`.

The shared `fn-bpah-local-pendingp` selector now excludes fragments before it
produces the view consumed by the owner. The subsequent request and receipt
authorization gates use the current durable BP peer configuration and observed
channel context. The combined handoff test retains a parseable fragment-carried
request, a valid current-peer configuration, and a tooth showing that the
fragment still produces no authorized request view. Separate tests retain
matching/mismatching current-generation request and receipt authorization.

On persvati, `run-20260923T213726Z-ec1e` selected 13 changed/nearby BP
book and test roots, used two ACL2 jobs and the qualified w25
`/home/ember/fn-gates/toolchains/w25/acl2-literal` executable with shared
`/home/ember/fn-certcache`. Its [manifest](manifests/certify-20260923T213735Z-466682.json)
records 156 books in closure, 75 installed matching certificates, 81 certified,
no book failures and final status `passed`. This is a focused source packet;
root's later integrated closure must separately assess the broad Store and
owner dependents moved by the E2 base. The native source has not been built or
run from this combined packet, and neither topic admission nor full BP transit
policy follows from these component certificates.
