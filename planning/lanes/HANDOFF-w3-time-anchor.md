# Handoff: w3/time-anchor

HEAD: `w3/time-anchor`, merged with `dev` twice (`6d29e76`, `b3d7a36`). Base: `dev` at `ca66782`.

## What this lane is

An external freshness anchor for D10/FLR-003, as a working thing: a Roughtime
client with pinned server keys, a single Ed25519 seam for the host
(`tools/crypto_host.py`, the tree's only importer of `cryptography`), an ACL2
book that owns the anchor statement and the monotone rule, a new FNAN durable
record family, and `run_store.py anchor` / `recover` on distinct exit codes.

## The server queried and the captured vectors

`roughtime.int08h.com:2002`, pinned long-term key
`AW5uAoTSTDfG5NfY1bTh08GUnOqlRb+HVhbJ3ODJvsE=`, profile RoughTime v1 (the
deployed pre-framing profile: no ROUGHTIM header, PAD\xff padding to 1024
octets, SHA-512 Merkle nodes of 64 octets, NUL-terminated context strings).
Three genuine responses were captured on 2026-09-19 and committed under
`tests/vectors/`, so every test runs offline:

| vector | MIDP (us since the Unix epoch) | RADI (us) |
| --- | --- | --- |
| `roughtime-int08h-2026-09-19.json` | 1789829805236961 | 5000000 |
| `roughtime-int08h-2026-09-19-later1.json` | 1789829939175579 | 5000000 |
| `roughtime-int08h-2026-09-19-later2.json` | 1789829955379640 | 5000000 |

The primary vector's `SREP` and `DELE` octets are transcribed into
`tests/acl2/anchor-tests.lisp`, where ACL2's own reconstruction of both signed
messages is asserted equal to them. Cloudflare's servers did not answer UDP
from this machine on 2026-09-19 (ports 2002 and 2003, classic and IETF-framed
requests all timed out); its key is pinned with `verified_answering: null`.

## The 2026-09-19 realignment of these books

The lane was written against the pre-realignment tree and never certified. It
has been merged onto the realigned `dev` (union resolution on `Makefile` and
`docs/prefixes.md`; `planning/ledger.{json,md}` taken from `dev` and
regenerated) and rewritten to `docs/proof-style.md`. **No keystone statement
changed.** What changed:

- **Four opaque records** (`docs/proof-style.md` sec. 1): the anchor statement,
  the outcome, the node's durable state and a store image each get a
  `-shapep`, a constructor, total `:guard t` accessors under `mbe` over two
  `fn-anchor-ag-` selectors, one accessor-of-constructor lemma per field, and
  the three forward-chaining shape facts (`-forward-shape`,
  `-accessors-forward-consp`, `<recognizer>-forward-shape`). The `:definition`
  runes are then withdrawn, so ground evaluation and type prescriptions still
  decide. The recognizers (`fn-anchor-p`, `fn-anchor-nodep`,
  `fn-anchor-imagep`, `fn-anchor-outcomep`) are now written in accessor
  vocabulary, never over `nth`/`len`.
- **Export theories** (sec. 2): `books/anchor.lisp` ends with
  `fn-anchor-vocabulary` (every record part, recognizer, reconstruction,
  transition, host entry and FNAN codec, as `(:d name)` only) and
  `fn-anchor-octet-vocabulary` (the `len`/octet rules). `books/anchor-
  invariants.lisp` ends with `fn-anchor-invariants-vocabulary`
  (`fn-anchor-earliest-not-after-latest`, the linear rule that is proof
  vocabulary for the order properties). Includers enable them by name.
- **Guard equalities are `:rule-classes nil`** (sec. 3):
  `fn-anchor-srep-octets-guard` (used by `:use` for both reconstructions'
  guards), `fn-anchor-dele-octets-length`, `fn-anchor-srep-octets-length`,
  `fn-anchor-record-anchor-is-an-anchor` (which is one conjunct of
  `fn-anchor-record-okp` restated, and carries that note).
- **Teeth are concrete witnesses** (sec. 5): `tests/acl2/anchor-teeth-tests`
  no longer includes `std/testing/must-fail`; every tooth is an
  `assert-event` on a specific violating value. To make the keystones' own
  subjects evaluable it attaches test-only realisers to the two A-CRYPTO
  seams (`fn-t-anchor-leaf-digest`, `fn-t-anchor-sig-verify`, registered in
  `docs/prefixes.md`) — they are the encapsulates' own local witnesses, so
  nothing is strengthened. The teeth are therefore about
  `fn-anchor-node-accept`, `fn-anchor-node-advance`, `fn-anchor-restore` and
  `fn-anchor-pair-admit` themselves, not about a sibling.
- **The seam split.** `books/anchor.lisp` holds the statement, the records,
  the order, the transitions and the host entries, and includes
  `cbor-invariants` and `clock` — **not** `frame`. The new
  `books/anchor-record.lisp` holds the FNAN family and is the only book of the
  cluster that includes `frame`/`frame-invariants`; it opens frame's small
  predicates and nothing else (not the field grammar, not the result records,
  not the splitter, not `fn-frame-encode`/`fn-frame-decode`), and discharges
  the two frame entry points from the named `:rule-classes nil` lemmas
  `fn-anchor-encode-frame-guard` and `fn-anchor-decode-frame-guard` over
  `fn-anchor-record-okp`. `books/anchor-invariants.lisp` includes
  `anchor-record`. No clock vocabulary is enabled anywhere: the anchor takes
  only `*fn-clock-max*` from that book.
- **New**: `fn-anchor-node-advance-observed` and its equality keystone
  `fn-anchor-node-advance-observed-is-node-advance`, with
  `fn-anchor-host-advance` in `host/anchor-host.lisp` as its caller. Without
  it the advance keystone had no host subject and no evaluable tooth.

## Theorems, verbatim

The seven keystones and the two host-entry equalities are unchanged from the
previous handoff; a third host-entry equality was added:

```lisp
(defthm fn-anchor-node-advance-observed-is-node-advance
  (implies (equal (and verdict t) (fn-anchor-verifiedp a))
           (equal (fn-anchor-node-advance-observed node a verdict)
                  (fn-anchor-node-advance node a))))
```

## Evidence

**ACL2 (8.7, SBCL, this laptop; one root at a time, `FN_ACL2_TIMEOUT_SECONDS=1800`).**

Certified: `books/anchor`, `books/anchor-record`, `books/anchor-invariants`, `tests/acl2/anchor-tests`, `tests/acl2/anchor-teeth-tests`.

`books/clock.cert` was stale after the merge (the bp deputy's clock realignment landed on `dev`) and was rebuilt in place; `make certs-install` installed nothing because the shared cache is being rebuilt.

Python, with the laptop's `python3` (3.14.7) which carries `cryptography` 50.0.1, so no virtual environment was needed. `CryptoSeam` and `RoughtimeClient`: 10 tests, OK, zero skips. Full suite (`python3 -m unittest tests.test_anchor -v`, all four classes):

```

```

## Open, and deliberately so

- **`fn-anchor-sig-verify` is still a local `encapsulate`.**
  `books/crypto-seam.lisp` is on `dev` now, but its seam is a digest and a
  tagged-preimage signature over fn's own statements, not an Ed25519 check of
  a foreign server's message, so it cannot absorb this one by functional
  instantiation as it stands. Cross-cluster item: either crypto-seam grows a
  raw `(key, message, signature) -> boolean` constrained verifier that this
  book instantiates, or this encapsulate stays and is named in the trust
  boundary. Owner: substrate.
- **Three hypotheses have no violating value** and are recorded open in
  `tests/acl2/anchor-teeth-tests.lisp` rather than deleted (the statements
  were held fixed for this rebase): `(fn-anchor-nodep node)` in
  `fn-anchor-accepted-anchor-is-strictly-newer`, `(fn-anchor-imagep image)` in
  `fn-anchor-restore-refuses-image-it-cannot-outdate`, and both hypotheses of
  `fn-anchor-accepted-restore-opens-a-new-incarnation` (on the accepted branch
  the payload's incarnation is `(+ 1 x)`, which is never `x`; on every other
  branch the payload is the image, whose fourth slot is `NIL`). Each is the
  guard the host carries, so deleting them would leave the host entry without
  a stated precondition; the next lane to touch these books should decide.
- **The unforgeability tooth is a witness now, not a `must-fail`.** Under a
  realiser satisfying every constraint of the encapsulate, two anchors with
  different signed messages both verify under the same signature octets. That
  assertion is the honest statement of what the seam does not constrain.
- The anchor covers the restore/clone side of OBJ-006. The counter-allocation
  side (`PRF-017`) is untouched, and A-IDENTITY is not discharged;
  `specs/anchor.md` says exactly what remains.
- Fork evidence is preserved, not resolved. `fn-anchor-pair-admit` refuses
  both images and hands both back; no rule here picks a winner.

## Trap paid for by this lane

Opening frame's field grammar (`fn-frame-values-okp`) over a nine-field spec
is an unbounded case split: `(verify-guards fn-anchor-encode)` ran for over
five minutes at 2 GB and reached "No induction schemes are suggested". The
grammar never needs to open — the guard of `fn-frame-fields-octets` *is*
`fn-frame-values-okp`, which is already a conjunct of
`fn-anchor-record-okp`. Any new frame family should copy the `e/d` at the top
of the FNAN section of `books/anchor.lisp`, the same one
`fn-frame-workflow-decode-of-encode` uses (`books/frame-invariants.lisp:800`).
