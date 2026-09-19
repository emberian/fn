# External freshness anchor

## The property

A node that holds an external freshness anchor refuses a restore or clone of a
store image whose durable records stand under an anchor that the presented
anchor does not outdate, and advances an incarnation only under an anchor
strictly newer than the one it already holds; two images of one incarnation
that stand under different anchors are both refused and both preserved as fork
evidence. Covered scope: the anchor statement, its ordering, the acceptance,
restore, advance and pair decisions in `books/anchor.lisp`, and the host
entries `python3 tools/run_store.py anchor` and `recover` call. Not covered:
that a signature cannot be forged, that a Roughtime server is honest, or that
any physical medium retained what it acknowledged.

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

Nine fields reach the logic (`fn-anchor`, `books/anchor.lisp`):

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

ACL2 owns what each signature covers. `fn-anchor-dele-octets` rebuilds the
72-octet DELE message and `fn-anchor-srep-from-root` the 100-octet SREP
message, each from its fields in the profile's little-endian tagged layout, and
each is prefixed with its context string before verification. The host never
tells the logic what was signed: it asks for those octets, runs Ed25519 over
exactly them, and passes back a verdict.
`tests/acl2/anchor-tests.lisp` asserts both reconstructions equal the octets a
real server sent, and `tests/test_anchor.py` re-checks that equality through
the live bridge.

The nonce is load-bearing rather than decorative: the SREP carries the Merkle
root, the root is the digest of the nonce, so a different nonce is a different
signed message.

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

- **The host's verdict is the seam's value for this anchor.**
  `fn-anchor-sig-verify` is a constrained function (32-octet key, 64-octet
  signature, boolean out; nothing more). `fn-anchor-restore-observed-is-restore`
  and `fn-anchor-node-accept-observed-is-node-accept` are the named theorems
  that make the entries the host calls the same functions the keystones are
  about, under exactly that hypothesis.
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
- **Ed25519 and SHA-512.** Used as computed by the host through
  `tools/crypto_host.py`. `books/anchor.lisp` constrains the verifier to refuse
  a wrong-width key or signature and constrains the leaf digest to 64 octets;
  it claims no unforgeability and no collision resistance, and
  `tests/acl2/anchor-teeth-tests.lisp` contains the `must-fail` case that shows
  unforgeability is *not* available.
- **The pinned keys themselves.** Taken from the published Roughtime ecosystem
  list. Replacing that file replaces the trust.

## Three outcomes

`:accepted`, `:refused` and `:uncertain` stay distinct to the exit code.
`anchor` and `recover` exit `0`, `1` and `3` respectively. Not reaching a
server, and `cryptography` being absent, are both `:uncertain`: the node does
not know whether the image is stale, and a refusal would claim knowledge it
does not have. A store that never recorded an anchor reports `anchor=none` and
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

`tools/roughtime.py` (client, parser, Merkle path, both signature checks),
`tools/roughtime_servers.json` (pinned keys), `tools/crypto_host.py` (the only
importer of `cryptography` in the tree; absent, it raises rather than
accepting), `host/anchor-host.lisp` (program-mode marshaling),
`tests/vectors/roughtime-int08h-*.json` (real captured responses, so the tests
need no network).
