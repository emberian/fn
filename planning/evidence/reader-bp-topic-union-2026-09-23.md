# Reader, authorship, BP and topic union qualification

Frozen source: `536ca577`. Hbox gate:
`/tank/fn/gates/integrate-reader-bp-topic-20260923`.
Run: `run-20260923T201700Z-0e13`, original
[manifest](manifests/certify-20260923T201719Z-27437.json).
ACL2 executable `/tank/fn/toolchains/w28/acl2-literal-4g`, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.

The selection was the deduplicated union of `proof_artifacts.py roots
--profile default`, `--profile dtn`, and every `tests/acl2/*.lisp` root.
`farm.py submit hbox` used four jobs, 300 seconds per invocation, the existing
`/tank/fn/certcache`, and the gate above. It did not use `--closure`.
The first preflight refused duplicate roots before ACL2 started; the corrected
selection deduplicated the list. No running job was restarted.

The incremental run reused 300 of 509 closure books from eleven compatible
cache origins and attempted the remaining 209. It finished failed in 213.854
seconds: 203 newly certified books and six failures. There were three actual
failed proof roots, with each test book failing on its missing dependency:

- `owner-agent`: `fn-oag-dispatch-submission-names-the-configured-agent`.
- `owner-prepare-correspondence`: `fn-opc-reader-context-conn-okp`; an old
  connection constructor does not carry the new pinned Message-ID index.
- `nntp-auth-invariants`:
  `fn-served-dispatch-of-a-refused-post-leaves-the-wire-in-place`.

The auth/agent proofs still reason through the old authentication-step surface
while the served path now dispatches through its pinned variant. The precise
repair must preserve the actual called-path guarantees; an assumed good index
cannot silently replace a required maintained relation. The auth invariant
book consumed 163.762 seconds (14.6 million prover steps in its log); this
is a proof-engineering regression, not a reason to raise its timeout.
Other notable book wall times were owner-invariants 18.270 seconds,
store-node-invariants 11.485 seconds and bp-fnbs-codec-invariants 10.766 seconds.
The manifest carries per-book slot waits and timings.

`make check` passed after archiving a missing original cache-reproduction
manifest. That static check does not make the failed proof roots green.
The next reader/authored-peering/topic native image remains held for the finite
repairs. Independent A3 BP image qualification continues on its own source.
No live node was changed and no release claim follows from this run.
