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

`python3 tools/harness_check.py --quiet` reported zero ACL2 arity/signature
findings, `python3 -m py_compile tests/test_native_hybrid_author.py` passed,
and an SBCL reader pass read the edited host files. The opt-in native fixture
now covers fresh signed sources across rotation, revocation, a second active
principal, offline history and restart inspection, but **it has not run on a
source-matched saved image**. No native service or deployment result follows
from this packet. PRF-069 remains in progress: the ACL2 tests are reachable
examples and the two selector lemmas are definitional; they are not a
maintained Store-node proof for every lifecycle transition, nor a proof of
cryptographic security, remote succession, recovery from lost keys or
revocation delivery under partition. The linear per-principal history scan
also needs an indexed correspondence if the snapshot history becomes large.
