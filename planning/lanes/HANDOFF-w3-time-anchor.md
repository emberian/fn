# Handoff: w3/time-anchor

HEAD `642dea83fe52a966d52d8dc84b6c22f75c175a71 Give the store an external freshness anchor`

## What landed

An external freshness anchor for D10/FLR-003, as a working thing: a Roughtime
client with pinned server keys, a single Ed25519 seam for the host, an ACL2
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

## Theorems, verbatim

```lisp
(defthm fn-anchor-accepted-anchor-is-strictly-newer
  (implies (and (fn-anchor-nodep node)
                (fn-anchor-node-latest node)
                (equal (fn-anchor-status (fn-anchor-node-accept node a))
                       :accepted))
           (fn-anchor-newerp a (fn-anchor-node-latest node))))
```

```lisp
(defthm fn-anchor-accept-list-latest-never-goes-back
  (implies (and (fn-anchor-nodep node)
                (fn-anchor-node-latest node))
           (or (equal (fn-anchor-node-latest
                       (fn-anchor-node-accept-list node anchors))
                      (fn-anchor-node-latest node))
               (fn-anchor-newerp (fn-anchor-node-latest
                                  (fn-anchor-node-accept-list node anchors))
                                 (fn-anchor-node-latest node))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-anchor-node-accept-list node anchors))))
```

```lisp
(defthm fn-anchor-incarnation-advances-only-under-a-newer-anchor
  (implies (and (fn-anchor-nodep node)
                (fn-anchor-node-latest node)
                (not (equal (fn-anchor-node-incarnation
                             (fn-anchor-payload (fn-anchor-node-advance node a)))
                            (fn-anchor-node-incarnation node))))
           (fn-anchor-newerp a (fn-anchor-node-latest node))))
```

```lisp
(defthm fn-anchor-restore-refuses-image-it-cannot-outdate
  (implies (and (fn-anchor-imagep image)
                (fn-anchor-image-referenced image)
                (not (fn-anchor-newerp presented
                                       (fn-anchor-image-referenced image))))
           (and (not (equal (fn-anchor-status
                             (fn-anchor-restore node image presented))
                            :accepted))
                (implies (fn-anchor-acceptablep
                          presented (fn-anchor-node-pinned node))
                         (and (equal (fn-anchor-status
                                      (fn-anchor-restore node image presented))
                                     :refused)
                              (equal (fn-anchor-reason
                                      (fn-anchor-restore node image presented))
                                     :possibly-stale))))))
```

```lisp
(defthm fn-anchor-accepted-restore-opens-a-new-incarnation
  (implies (and (fn-anchor-imagep image)
                (equal (fn-anchor-status (fn-anchor-restore node image presented))
                       :accepted))
           (not (equal (fn-anchor-node-incarnation
                        (fn-anchor-payload
                         (fn-anchor-restore node image presented)))
                       (fn-anchor-image-incarnation image)))))
```

```lisp
(defthm fn-anchor-fork-admits-neither-image
  (implies (and (equal (fn-anchor-image-incarnation left)
                       (fn-anchor-image-incarnation right))
                (not (equal (fn-anchor-image-referenced left)
                            (fn-anchor-image-referenced right))))
           (and (equal (fn-anchor-status (fn-anchor-pair-admit left right))
                       :refused)
                (equal (fn-anchor-reason (fn-anchor-pair-admit left right))
                       :fork)
                (not (fn-anchor-pair-admittedp
                      (fn-anchor-pair-admit left right)))
                (equal (fn-anchor-payload (fn-anchor-pair-admit left right))
                       (list left right)))))
```

```lisp
(defthm fn-anchor-restore-without-an-anchor-is-uncertain
  (implies (not (fn-anchor-p presented))
           (and (equal (fn-anchor-status (fn-anchor-restore node image presented))
                       :uncertain)
                (not (equal (fn-anchor-status
                             (fn-anchor-restore node image presented))
                            :refused))
                (not (equal (fn-anchor-status
                             (fn-anchor-restore node image presented))
                            :accepted)))))
```

```lisp
(defthm fn-anchor-node-accept-observed-is-node-accept
  (implies (equal (and verdict t) (fn-anchor-verifiedp a))
           (equal (fn-anchor-node-accept-observed node a verdict)
                  (fn-anchor-node-accept node a))))
```

```lisp
(defthm fn-anchor-restore-observed-is-restore
  (implies (equal (and verdict t) (fn-anchor-verifiedp presented))
           (equal (fn-anchor-restore-observed node image presented verdict)
                  (fn-anchor-restore node image presented))))
```

## Python results

Run with a `python3.12` virtual environment holding `cryptography` 50.0.1
(an optional dependency; the laptop's system interpreter had it too, but the
absent case is exercised below):

- `python3 -m unittest tests.test_anchor.CryptoSeam tests.test_anchor.RoughtimeClient -v` -- 10 tests, OK.
  These cover the captured response verifying under the pinned key, a
  different pinned key failing, one flipped octet failing, a foreign nonce
  not being in the tree, the Merkle path folding to the signed root, request
  padding, and the tree-wide check that `tools/crypto_host.py` is the only
  importer of `cryptography`.
- The same command with a stub that makes `import cryptography` raise:
  `OK (skipped=6)` -- every Ed25519-dependent test skips with its reason and
  no path returns a verdict.
- `python3 tools/roughtime.py --server int08h --capture <path>` against the
  live server: `midpoint_us=1789829955379640 radius_us=5000000 server=int08h`.
- `python3 tools/ledger.py --write` regenerated `planning/ledger.{json,md}`
  and the `proofs.json` event arrays; `make check` is green.

## Not yet run

**ACL2 certification of the four new roots has not happened.** The lane's
baseline `make certify` was moved to a remote box by the root coordinator
partway through (the laptop was at load 98 with nineteen ACL2 processes), and
local certification is blocked until `books/*.cert` and `tests/acl2/*.cert`
are installed in this worktree. The roots to certify, in order, are:

```
books/anchor books/anchor-invariants \
  tests/acl2/anchor-tests tests/acl2/anchor-teeth-tests
```

They are already appended to `ACL2_BOOKS` in the Makefile after
`tests/acl2/clock-tests`. Until they certify, treat every theorem quoted
above as *proposed*, not proved: the books are written and self-consistent by
eye, and nothing more. The two Python test classes that need a live ACL2
session -- `Acl2OwnsTheSignedOctets` and `StoreAnchorCommands` -- are also
unrun for the same reason; they are the ones that check ACL2's reconstruction
against the wire through the bridge and drive the `anchor`/`recover` CLI over
the captured vectors.

## Open, and deliberately so

- `fn-anchor-sig-verify` is a local `encapsulate` in `books/anchor.lisp` with
  the shape the crypto-seam lane is building (public key, message octets,
  signature octets -> boolean). When that book lands, retire this one by
  functional instantiation rather than keeping a second copy.
- The anchor covers the restore/clone side of OBJ-006. The counter-allocation
  side (`PRF-017`) is untouched, and A-IDENTITY is not discharged;
  `specs/anchor.md` says exactly what remains.
- Fork evidence is preserved, not resolved. `fn-anchor-pair-admit` refuses
  both images and hands both back; no rule here picks a winner.
