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

## Finite repairs and full-root retry

Source `884e4816` repairs the reader-context constructor and the actual pinned
POST/agent theorem chain without changing their public conclusions. It also
adds the bounded portable authored-source export needed by the Mini adapter.
`make check` passed. Hbox run `run-20260923T203022Z-26d8` in
`/tank/fn/gates/integrate-reader-repair-20260923` selected the complete default
Makefile root set, covering the ideal and replay invariant books omitted by
the earlier profile/test union. It used the same executable, cache, four jobs
and per-book timeout, with no `--closure`.

The [original retry manifest](manifests/certify-20260923T203040Z-47285.json)
passes: 508 of 512 closure books reused from thirteen compatible origins and
four newly certified books in 7.918 seconds of certification wall time.
The repaired auth book's earlier scoped run took about six seconds rather
than the failing union's 163.762 seconds; that comparison is proof-event
repair evidence, not a full-tree benchmark. The source-matched developer
image and native reader, authored peering/restart, topic inspection and Mini
portable-verification runs are the next evidence; no runtime success is
inferred from this proof run.

## Indexed-open follow-up

Source `ceed4b9e` also routes owner opens through the indexed served-open
entry, reusing the existing pinned trie/verdicts instead of building and then
discarding a fresh trie for each connection. The full Makefile-root hbox run
`run-20260923T203850Z-16b5`, gate
`/tank/fn/gates/integrate-indexed-open-20260923`, passed with 483 compatible
cached books and 29 newly certified books in 51.753 seconds at four jobs.
[Original manifest](manifests/certify-20260923T203907Z-62267.json).
The `884e4816` saved image does not contain this later open-cost change;
its runtime results must not be attributed to the newer source.

The proof REPL now uses the same actual certificate-alist compatibility
selection as certification and image acquisition. The nine REPL tests passed
on the integrated source; one negative test deliberately refuses an
incompatible parent/child set before a session is started. The previously
unarchived primary hybrid-store certification was recovered from its original
hbox run, rather than recertifying for a ledger label.

## Crash, topic and authentication union

Source `2234c1f3` adds actual typed P-RECORD link/crash provenance,
topic constructor bounds/inverse and host-called authored-field binding,
and handled authentication-command correspondence. Hbox run
`run-20260923T204942Z-deec`, gate
`/tank/fn/gates/integrate-crash-topic-auth-20260923`, passed the full
Makefile-root incremental selection with 496 cached closure books from
fifteen origins and 17 certified in 15.164 seconds at four jobs.
[Original manifest](manifests/certify-20260923T204958Z-90622.json).
`make check` passed. This does not attribute runtime evidence from884 to
this later source or close general K0, topic governance or delegated-reader
correspondence.

## A3 and ordered crash-scanner union

Source `b9bf596d` integrates the A3 native/ACL2 application handoff through
lane `7ad230b5` and the K6 ordered scanner theorem conditional on the actual
pair-10 byte/kernel relation. Hbox run `run-20260923T205921Z-411b`, gate
`/tank/fn/gates/integrate-a3-scanner-20260923`, passed the full Makefile-root
selection at four jobs with 493 cached closure books from sixteen origins
and 28 newly certified books in 27.353 seconds.
[Original manifest](manifests/certify-20260923T205938Z-120445.json).
The slowest book, `bp-fnbs-codec-invariants`, took 10.832 seconds; the actual
record-provenance root took 7.229 seconds. `make check` passed; the native
matrix driver's 47 unit tests passed. Native host loading in the local static
gate is explicitly skipped without FN_ACL2; image evidence is separate.

The A3 native campaign remains pinned to its named images. Source review
found two actual caller gaps not covered by the successful loopback exchange:
missing observed-channel principal admission (spec §2.3), and potential
outbox publication uncertainty reported as refusal. Cooperating lanes are
repairing these; this proof run does not close either host boundary. K0 still
must derive the pair-10 relation along every supported served trace.
