# Operator-local author-key lifecycle: scoped source evidence

The host-called `hybrid-enroll` and `hybrid-revoke` constructors are
`fn-hl-enroll-event` and `fn-hl-revoke-event`. They require the next global
kind-3 generation, and a revocation requires an actively enrolled named
principal. `hybrid-author` calls `fn-hl-current-enrollment` in the serialized
owner: it selects a requested enrollment only when no later recognized
snapshot for that *principal* exists. This means enrolling B leaves A usable;
rotating or revoking A refuses A's older generation for a new local request,
without changing B's capability. The new `fn-hybrid-revoked-v1` kind-3 payload
is exactly one 32-octet principal. Existing `fn-hybrid-v1` bytes, kind-4
accepted verdicts and portable `hybrid-verify-source` keep their historical
meaning.

The ACL2 tests construct and replay A1, B2, A3 rotation and A4 revocation
through the actual kind-3 event constructor and replay interpreter. They check
A still active after B, A1 retired after A3, A3 refused after A4, B active
throughout, canonical tombstone encoding, wrong-profile/short-principal
refusal, an old v1 encode/decode, and retention of A1 and a kind-4 verdict
after replay. The native control book's test covers kind-6 revoke frame
roundtrip, wrong-size refusal and disjoint enrollment decoding.

On persvati, ACL2 8.7 with qualified toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`
passed the two changed books and two test books in
[`certify-20260924T054706Z-820554.json`](manifests/certify-20260924T054706Z-820554.json).
That run installed 98 matching closure books from the certificate cache and
certified four roots in 9.825 seconds. After adding the malformed tombstone
and exact historical-v1 test assertions, the changed lifecycle test book
passed again in
[`certify-20260924T055039Z-854201.json`](manifests/certify-20260924T055039Z-854201.json),
with 48 matching cached closure books. These manifests record the exact
source and certificate digests; the worktree source was uncommitted during
the runs, so their `git_revision` field is null. The host-side correction to
the offline history command did not change ACL2 book bytes.

The follow-up Store-node book proves two additional statements about the
actual kind-3 branch. Given `fn-sn-completion-enabledp` and a kind-3
completion record, `fn-hls-finish-snapshot-from-maintained-state`
equates the host's per-principal selector after `fn-sn-finish` to the exact
snapshot history returned by `fn-replay-identity-step`.
`fn-hls-finish-snapshot-keeps-historical-verdicts` has the weaker premise of
a kind-3 completion record and says the entire carried verdict list is
unchanged, whether finish completes or returns unchanged. The event-kind
separation lemma proves a
kind-3 snapshot cannot also be a retention, consumer or topic event. The
reachability test starts from the existing Store trace with A1 and a
committed kind-4 article/verdict, completes B2, A3 rotation and A4 tombstone
through `fn-sn-prepare-identity`, publication I/O and `fn-sn-finish`, checks
`fn-snt-relation` and the carried identity sequence at each state, then
reopens the five-record history through `fn-sn-open-observed`. B stays active
and the old A verdict and enrollment survive reopen. Two concrete `must-fail`
events show that a staged, uncompleted snapshot cannot be read as installed
and that a completed kind-4 event can change the verdict list. Persvati
certified the final fast source in
[`certify-20260924T061218Z-1058761.json`](manifests/certify-20260924T061218Z-1058761.json),
with 79 matching cached dependencies; the proof book took 2.479 seconds,
the test book 2.569 seconds, and the run 5.06 seconds. An earlier source in
`certify-20260924T060628Z-1004175.json` passed but spent 100.676 seconds in
one projection lemma because its hint opened the per-principal selector and
identity codec. The final hint keeps them closed. This is a maintained
completed-snapshot footprint plus a reachable Store trace. It is not an
inductive relation equating the per-principal view to every possible durable
history at every crash phase.

The subsequent recovery extension proves the actual `fn-sn-recover` success
branch: if a well-formed Store enters in `:replaying` and recovery reaches
`:recovering`, `fn-hls-successful-recover-current-enrollment` selects from
the kind-3 snapshots obtained by `fn-replay-identity` over the recovered
durable records, while
`fn-hls-successful-recover-historical-verdicts` equates the carried verdict
list to the kind-4 verdict pairs from that same replay. The test cuts B2
before publication (`:old/:absent`, B remains unenrolled) and after the
record-directory success but before live finish (`:old/:present`, B is
recovered), retaining A1's prior verdict in both. It also keeps the full
A/B/rotation/tombstone observed-reopen trace above. Persvati passed the two
changed roots in
[`certify-20260924T062045Z-1140805.json`](manifests/certify-20260924T062045Z-1140805.json):
2.48 seconds for the proof book, 2.627 seconds for the test book, 5.123
seconds overall with 79 matching cached dependencies. This is a theorem
about successful recovery and selected crash cuts; it does not assert every
physical crash boundary or a global trace induction for the local selector.

`python3 tools/harness_check.py --quiet` reported zero ACL2 arity/signature
findings, `python3 -m py_compile tests/test_native_hybrid_author.py` passed,
and an SBCL reader pass read the edited host files.

The frozen `863c2141` Linux production image passed the targeted native
author-key subset on hbox. The image's ACL2 build manifest is
`/tank/fn/gates/capability-863c2141-20260924/build/acl2/certify-20260924T061350Z-995404/manifest.json`
(SHA-256 `d25fb5027cfab2c6ca3c48fae3577ca0f48b22712a0feb41af67303d0904c156`);
the `build/fn-host` launcher is SHA-256
`d3214eb2abb382c170f35d102938854a03aa74650aeb20c2b42750dad4bfeb4f`
and its core is
`fb20885046e2cf5d86612f7198999ef98d2cb225c65d6a1f63867914d2803107`.
With `FN_NATIVE_HOST` set to that launcher, `FN_TEST_OPENSSL` set to
`/tank/fn/toolchains/openssl-3.5.8/bin/openssl`,
`LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib`, and
`FN_RUN_HYBRID_E2E=1`, these exact commands passed:

```sh
python3 -m unittest -v tests.test_native_hybrid_author.NativeHybridAuthorTest.test_enroll_author_refuse_tamper_and_restart_query tests.test_native_hybrid_author.NativeHybridAuthorTest.test_local_revocation_targets_one_principal
python3 -m unittest -v tests.test_native_hybrid_author.NativeHybridAuthorTest.test_portable_carrier_verifies_exact_source_and_keyset
```

The first ran two tests in 3.594 seconds and covers fresh signing,
tamper refusal, restart query, per-principal rotation/revocation and
unrelated-principal survival. The second ran one test in 2.360 seconds and
covers exact-source and ordered-keyset carrier verification. OpenSSL reported
3.5.8 for both executable and library. The archived
[`lifecycle.log`](native-author-lifecycle-863c2141/lifecycle.log) has SHA-256
`713d7a30c89a3a11e160841ddcb96ce560e2a72883d0fdcd9d719d67cfd5dfc0`;
[`portable.log`](native-author-lifecycle-863c2141/portable.log) has
`37b47558bf83f6b86de6715af450eddccf4fec866b4236c5e9880dcc0131370b`.
This is source-matched execution of the selected native CLI subset on scratch
Stores, not a deployed service or a general cryptographic proof.

PRF-069 remains in progress: the completed-snapshot
theorems and reachable tests are not a full crash-phase Store-node relation
for every possible lifecycle trace, nor a proof of
cryptographic security, remote succession, recovery from lost keys or
revocation delivery under partition. Destination-side admission of an
incoming signed carrier still needs its separate exact-authority caller and
source-matched evidence; local permission does not itself establish that
remote policy. The linear per-principal history scan also needs an indexed
correspondence if the snapshot history becomes large.
