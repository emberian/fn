# External freshness anchor

## The property

A node that holds an external freshness anchor refuses a restore or clone of a
store image whose durable records stand under an anchor that the presented
anchor does not outdate, and advances an incarnation only under an anchor
strictly newer than the one it already holds; two images of one incarnation
that stand under different anchors are both refused and both preserved as fork
evidence; and it accepts only a response whose Merkle tree it can state,
reporting any other as uncertain. Covered scope: the anchor statement, its
ordering, the acceptance, restore, advance and pair decisions in
`books/anchor.lisp`, and the host entries `python3 tools/run_store.py anchor`
and `recover` call. Not covered: that a signature cannot be forged, that a
Roughtime server is honest, that a Merkle path binds a nonce to a root, or
that any physical medium retained what it acknowledged.

## Why an anchor at all

FLR-003 (`specs/failures.md`): "checksummed checkpoints do not establish
freshness against replacement of the whole store by an old valid snapshot."
Every integrity mechanism fn has is internal: a hash over an image an attacker
or an operator copied last year still matches. OBJ-006 forbids the obvious
patch — "freshness is not inferred from the current time" — and D10 records the
resolution: a restore creates a fresh sequence namespace *or* validates a
monotone anchor obtained from outside the node. This is the second of those.

Roughtime (draft-ietf-ntp-roughtime) is the external evidence. The client picks
32 octets no one can predict, the server answers with an Ed25519 signature over
a midpoint and a radius together with a Merkle proof that those 32 octets were
in the batch the response covers. A snapshot taken before the nonce existed
cannot contain a response naming it, so possession of one is evidence of
existing at or after that time — and unlike a wall clock reading, it is
evidence a second party can check.

## The statement

Ten fields reach the logic (`fn-anchor`, `books/anchor.lisp`):

| field | width | what it is |
| --- | --- | --- |
| `key-id` | 32 octets | the server's pinned long-term Ed25519 key |
| `delegate` | 32 octets | the short-lived key that key authorized |
| `mint`, `maxt` | uint64 µs | the window the delegation is valid for |
| `delegation-signature` | 64 octets | `key-id` over the DELE message |
| `midpoint` | uint64 µs | MIDP, microseconds since the Unix epoch |
| `radius` | uint64 µs | RADI, half-width of the asserted interval |
| `nonce` | 32 octets | the octets this node chose |
| `signature` | 64 octets | `delegate` over the SREP message |
| `root` | 64 octets | ROOT as the SREP carried it |

ACL2 owns what each signature covers. `fn-anchor-dele-octets` rebuilds the
72-octet DELE message and `fn-anchor-srep-from-root` the 100-octet SREP
message, each from its fields in the profile's little-endian tagged layout, and
each is prefixed with its context string before verification. The host never
tells the logic what was signed: it asks for those octets, runs Ed25519 over
exactly them, and passes back a verdict.
`tests/acl2/anchor-tests.lisp` asserts both reconstructions equal the octets a
real server sent, and `tests/test_anchor.py` re-checks that equality through
the live bridge.

`books/anchor-wire.lisp` now owns the bounded deployed RoughTime v1 response
grammar as well.  It parses the top response and nested CERT, DELE and SREP
messages, enforces the 4096-octet response bound, strict tag order, cumulative
offset bounds, required fields and widths, request-nonce equality, and the
PATH/INDX shape.  Before returning a record it compares the received nested
DELE and SREP byte strings with the canonical byte strings rebuilt from that
record.  `host/anchor-wire-host.lisp` returns those ACL2-produced signature
subjects to a native crypto caller; it does not reconstruct them in raw Lisp.
The same book produces the deployed 1024-octet NONC/PAD request from an exact
32-octet nonce.  `host/native/anchor.lisp` obtains that nonce from the OS
CSPRNG, sends ACL2's request as one connected UDP datagram, calls the ACL2
parser, and applies libsodium only to the two subjects in its `:parsed` result.
`books/anchor-servers.lisp` is the deployed pinned manifest: the bounded
`[anchor].server` name selects the endpoint and long-term key there, and the
same ACL2 profile carries nonce/request/response sizes and admits the
operator's per-I/O timeout.  Native code has no default endpoint or key.

DNS resolution has no whole-path deadline in this packet.  Send readiness and
receive readiness each get the selected timeout; a nonblocking race after
readiness is network uncertainty.  Receive allocates one byte beyond ACL2's
response limit and refuses a datagram that reaches it, so a valid bounded
prefix of an oversized datagram cannot be parsed as complete.

The native `anchor acquire STORE SERVER TIMEOUT` command holds the exclusive
store writer lock across reading the prior FNAN, acquisition, the actual
`fn-anchor-host-accept` call and publication.  Only `:accepted` reaches a
staged FNAN write; the file is barred, atomically replaces `anchor.fnan`, and
the store directory is barred before exit 0 is printed.  Failure after the
replacement attempt is `:uncertain`; a later invocation decodes the final
FNAN under the same lock.  `books/anchor-replace.lisp` owns these phases and
the native host calls `fn-anchor-rp-step` before rename (`:replace-issued`) and
after every I/O observation.  Recovery barriers the visible final file, when
present, and then its directory before decode; visibility alone never becomes
held state.  FNAN sealing and decode digests use `fn-frame-trailer` through
the shared `fnn-seal` and `fnn-digest-of` helpers.  This mutable replacement
contract is separate from the immutable artifact publisher's no-replace
contract.

`root` is a **field, not a derivation**, and that is what makes the
reconstruction the message that was verified. Until 2026-09-20 `fn-anchor-root`
was defined as `(fn-anchor-leaf-digest (fn-anchor-nonce a))`, so every theorem
about the signed octets described a one-nonce tree while the host verified
whatever root arrived on the wire; for a batched response the two came apart
and nothing noticed — **including on one of the three captured vectors**,
`tests/vectors/roughtime-int08h-2026-09-19-later2.json`, whose `PATH` is one
node deep and whose `INDX` is 1. int08h batches. The earlier claim that every
captured vector was single-nonce, in this file and in two handoffs, was wrong,
and the divergence was live in fn's own test suite on every run.

The root now travels on the record, and `fn-anchor-one-nonce-p` — `(equal
(fn-anchor-root a) (fn-anchor-leaf-digest (fn-anchor-nonce a)))` — is a branch
of every transition: a response whose tree this model cannot fold is
**`:uncertain`, with the reason `:unmodelled-tree`**. Uncertain and not
refused, because every signature in such a response is good and fn simply
cannot tell whether it covers this node's nonce; a refusal would claim
knowledge the node does not have, which is the same rule that makes an
unreachable server uncertain.

The nonce stays load-bearing rather than decorative: for a one-nonce response
the signed root is the digest of the nonce, so a different nonce is a
different signed message. That sentence now carries its hypothesis —
`fn-anchor-one-nonce-signed-octets-determine-the-leaf-digest`, a corollary of
the keystone `fn-anchor-signed-octets-determine-the-root`, which itself holds
for a response of any batch size.

## Strictly newer

An anchor asserts only that true time lay in `[midpoint - radius, midpoint +
radius]`. `fn-anchor-newerp a b` holds exactly when *a*'s whole interval lies
after *b*'s. Two readings whose intervals overlap are unordered in both
directions, and an unordered pair never advances anything. This is the same
conservatism `books/clock.lisp` applies to a host wall reading, and it is why
the captured witnesses in the test book are thirty seconds apart: ten is not
enough against a five-second radius.

## Hypotheses

Every keystone in `books/anchor-invariants.lisp` is conditional on:

- **The host supplies one value per A-CRYPTO seam, and nothing else.**
  `verdict` is `fn-anchor-signatures-okp`, the two constrained
  `fn-anchor-sig-verify` calls (32-octet key, 64-octet signature, boolean out;
  nothing more). `one-nonce` is `fn-anchor-one-nonce-p`, which runs through
  the constrained `fn-anchor-leaf-digest`. They are separate arguments because
  they have different answers: a failed signature is `:refused :unverified`,
  an unfoldable tree is `:uncertain :unmodelled-tree`.
  `fn-anchor-verifiedp-observed-is-verifiedp` discharges the Ed25519 half once
  and `fn-anchor-restore-observed-is-restore`,
  `fn-anchor-node-accept-observed-is-node-accept` and
  `fn-anchor-node-advance-observed-is-node-advance` are the equalities at the
  three entries the host calls, each under both hypotheses.
  **The delegation window is not part of it.** `mint <= midpoint <= maxt` is
  arithmetic on fields the record carries, so ACL2 owns it:
  `fn-anchor-verifiedp-observed` applies `fn-anchor-window-okp` inside the
  entry. Before 2026-09-20 that conjunct was half the discharge of this
  hypothesis and lived in `tools/roughtime.py:258`, with `anchor_verdict`
  supplying the other half from a different file; `roughtime.py:258` is now a
  preflight that nothing in the logic depends on.
- **The key is pinned.** `fn-anchor-pinnedp` checks membership in the node's
  list; `tools/roughtime_servers.json` is that list on disk.
- **The image really refers to the anchor it names.** The restore keystone is
  about `fn-anchor-image-referenced`; what a host puts there is a host
  obligation, discharged here by writing the accepted anchor into the same
  durable record the image carries (`anchor.fnan`, the FNAN family).

## The trust

- **Roughtime servers.** An anchor is only as good as the servers whose keys
  are pinned. A single server that signs an old midpoint can make a stale image
  look fresh; a server that refuses to answer can only produce `:uncertain`.
  fn pins keys per server and records when each was last seen answering. This
  is a named external trust, not a proved property, and it is the reason D10
  keeps the fresh-namespace alternative alongside it.
- **Ed25519 and SHA-512.** The current Python command computes them through
  `tools/crypto_host.py` and `tools/roughtime.py`; the no-Python native target
  provides the same bounded primitive observations in `host/native/crypto.lisp`
  through libsodium. `books/anchor.lisp` constrains the verifier to refuse
  a wrong-width key or signature and constrains the leaf digest to 64 octets;
  it claims no unforgeability and no collision resistance, and
  `tests/acl2/anchor-teeth-tests.lisp` ends with the concrete witness that
  shows unforgeability is *not* available: under a realiser satisfying every
  constraint of the encapsulate, two anchors with different signed messages
  verify under the same signature octets. (That book is explicit that it is a
  witness and not a `must-fail`, which proves only that the prover found no
  proof; this line used to say `must-fail` and was wrong.)
- **The pinned keys themselves.** Taken from the published Roughtime ecosystem
  list. Replacing that file replaces the trust.
- **The leaf digest, which remains a host observation.** `tools/roughtime.py:124`
  (`_leaf`) and native `fnn-crypto-anchor-leaf` compute SHA-512 of the single
  octet 0 followed by the nonce.  That observation
  is the only input that decides whether a response covers
  *this client's nonce*. `fn-anchor-leaf-digest` is a constrained function
  whose only constraints are "64 octets", and no book attaches a realiser to
  it (the sole `defattach` is a test-only one in
  `tests/acl2/anchor-teeth-tests.lisp`). ACL2 has **no executable SHA-512**:
  `books/sha256.lisp` is the only executable hash in logic, and Roughtime's
  fold is SHA-512. So "the host's leaf observation is
  `fn-anchor-leaf-digest`" is a named
  trusted correspondence and not a proved one, exactly as "the host's Ed25519
  is `fn-anchor-sig-verify`" is; it is the reading under which
  `Anchor.one_nonce` discharges `fn-anchor-one-nonce-p`.

  **What that trust no longer covers.** The wire parser, path depth bound and
  `INDX`-fits-`PATH` check are now ACL2-owned in `books/anchor-wire.lisp`.
  The node digest, path fold, sibling order and index bit order remain unowned
  host decisions in `tools/roughtime.py:128,132` (`_node`, `merkle_root`), and
  a fold that walked the tree the wrong way is still checked by nothing in the logic —
  but **fn no longer accepts an anchor that needs them**. A response with a
  non-empty `PATH` fails `fn-anchor-one-nonce-p`, so every transition answers
  `:uncertain :unmodelled-tree`; `merkle_root` is then load-bearing only on
  the path where it returns `_leaf(nonce)` and folds nothing. The trusted
  surface is one hash of 33 octets, not a tree walk of arbitrary depth.

  **The cost, stated plainly and measured.** fn cannot use a batched
  Roughtime response, and int08h batches: one of the three captures in
  `tests/vectors/` has a one-node `PATH`. Against a batching answer `fn
  anchor` reports `anchor uncertain: unmodelled-tree` and exits 3, the node
  keeps the anchor it had, and the operator retries. That is availability
  traded for honesty, and the honest reading of D13 puts it under
  `:uncertain` rather than `:refused`. Using batched responses is
  `books/sha512.lisp`, the fold above it and its attachment, designed in
  [HANDOFF-w11-one-owner](../planning/lanes/HANDOFF-w11-one-owner.md) §3
  steps 1 to 3 and not done — and it is now a **feature** item, not only an
  assurance one.
- **The model and the host now describe the same message.** This bullet used
  to record the opposite, and it is what lane `w11/anchor-root` closed. The
  root is a record field, so `fn-anchor-signed-octets` is the octets the host
  ran Ed25519 over, for a response of any batch size; and
  `fn-anchor-one-nonce-p` is a branch of every transition, so the responses
  this model cannot describe are reported uncertain instead of admitted.
  `Anchor.fields` (`tools/roughtime.py`) carries ten fields including the
  root, `fn-anchor-host-fields` takes ten, and the FNAN durable record has a
  tenth `:blob`. **An `anchor.fnan` written before 2026-09-20 has nine fields
  and no longer decodes**: `tools/run_store.py` raises rather than continuing,
  because a store that once held a freshness anchor and can no longer read it
  is not a store with no anchor. Re-run `fn anchor`.

## Three outcomes

`:accepted`, `:refused` and `:uncertain` stay distinct to the exit code.
`anchor` and `recover` exit `0`, `1` and `3` respectively. Not reaching a
server, `cryptography` being absent, and **a Merkle tree this model cannot
fold** (`:unmodelled-tree`) are all `:uncertain`: the node does not know
whether the image is stale, and a refusal would claim knowledge it does not
have. A store that never recorded an anchor reports `anchor=none` and
recovers as before — it has nothing to be stale against.

## What remains A-IDENTITY

A-IDENTITY (`books/assumptions.lisp`) says origin/incarnation allocation and
restore procedures avoid unrecognized reuse *subject to their explicit
freshness assumptions*. This book supplies one of those assumptions with real
evidence and proves what follows from it. It does not discharge A-IDENTITY:

- the counter-allocation side of OBJ-006 (that a given incarnation issues each
  counter once) is `PRF-017` and still open;
- a node that has never obtained an anchor is outside the rule entirely;
- fork evidence is *preserved*, not resolved — `fn-anchor-pair-admit` refuses
  both images and hands both back, and nothing here says which history a
  human should keep;
- the Roughtime trust above is an assumption, and the physical qualification
  item in FLR-003 and `HST-003` is untouched.

## Host files

`books/anchor-wire.lisp` (bounded response parser and canonical signed-message
binding), `host/anchor-wire-host.lisp` (program-mode parser bridge),
`host/native/crypto.lisp` (native Ed25519/SHA-512 primitive observations),
`host/native/anchor.lisp` (bounded OS-CSPRNG/UDP acquisition and composition),
`tools/roughtime.py` (current prototype client and Merkle path),
`tools/roughtime_servers.json` (pinned keys), `tools/crypto_host.py` (the only
importer of `cryptography` in the tree; absent, it raises rather than
accepting), `host/anchor-host.lisp` (program-mode marshaling),
`tests/vectors/roughtime-int08h-*.json` (real captured responses, so the tests
need no network).
