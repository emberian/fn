# HANDOFF w9/digest — the digest is executable

Branch `w9/digest` off `dev` at `63cd9a2`. Box: hbox only, mirror
`/tank/fn/lanes/w9-digest`.

## What landed

**`books/sha256.lisp`** — FIPS 180-4 SHA-256 over octet lists, total,
`:guard t` on the entry point, guard verified, no bitvector library. Every
word passes through `fn-sha256-w32` (`mod` 2^32 of an `ifix`) and every step
is `logand` / `logior` / `logxor` / `lognot` / `ash` under that wrapper, so
the only facts the book uses about the bit operations are their built-in type
prescriptions; its two local includes are `arithmetic/top` and
`ihs/quotient-remainder-lemmas`, both already certified on hbox.
(`ihs/logops-lemmas` is NOT certified there, which is why the book is written
to need neither it nor `kestrel/crypto/sha-2` — see "what was not used".)
Exported: `fn-sha256-shape` (32 octets, always) and the two facts that the
argument coercion is invisible on octet lists.

**`tests/acl2/sha256-tests.lisp`** — the published vectors by evaluation: the
empty message, `"abc"`, the 56- and 112-octet FIPS messages, the million-`a`
vector, and the padding boundaries at 55, 56, 63, 64, 65, 119 and 120 octets,
which is where a padding defect the short vectors miss shows up. Plus teeth
that the realiser is not degenerate (two messages, two digests; not the zero
digest — the seam's own local witness is the zero digest).

**`books/crypto-attach.lisp`** — `defattach fn-digest fn-sha256` and
`defattach fn-frame-digest fn-sha256`, with the three constraints of the two
`encapsulate`s re-proved as named events first. No constraint of either seam
is stronger than "32 octets", so no finding about a constraint SHA-256 cannot
meet; if a later one appears it is a finding, never a weakened constraint.
Checked empirically on hbox: a later `defattach` overrides an earlier one, so
`tests/acl2/{crypto-seam,policy,lace,principal}-tests.lisp` keep their toy
realisers and their collision witnesses stay reachable.

**`books/auth-secret.lisp` + `tests/acl2/auth-secret-tests.lisp`** — the
AUTHINFO stored-credential scheme (16-octet salt, `salt || secret` under the
seam's `"fn-authinfo-v1"` tag, stored as `(:fn-authsec-v1 salt digest)`).
Keystones: the enrolled secret always checks; a verifier is never an octet
list (the slot cannot hold a cleartext secret); the stored digest is 32 octets
whatever the secret (no length leak); the preimage recovers `(salt, secret)`.
The secret hypothesis on the round trip proved unnecessary and was deleted.

**Served path** — `host/store-host.lisp` includes `crypto-attach` and gains
`fn-store-subject-id-of-payload` / `fn-store-obligation-id-of`, which derive
the identity end to end in logic. `tools/frame_bridge.py` `subject_id` and
`obligation_id` are now bridge calls with no `hashlib`, and
`host/native/io.lisp` `fnn-subject-id` / `fnn-obligation-id` no longer call
`fnn-sha256`. `tests/identity_differential.py` derives each identity both ways
through one live session and compares.

**Docs** — `planning/deputies/BOARD.md` carries two CHANGEs and one NOTE.
`docs/architecture.md` trust boundary: the digest is computed in
logic by a proved-executable definition; what remains assumed is collision and
preimage resistance, A-CRYPTO, stated as before. `specs/nntp.md` carries the
credential scheme as a table.

## Measurement (the number and its covered scope)

`(fn-sha256 (fn-sha256-t-repeat 32768 65))`, hbox, SBCL, ACL2 8.7, under
`swarm-build`, three consecutive `time$` runs in one `ld`:
**0.01, 0.02, 0.02 s realtime; 2.9 MB allocated per call.** 1 MiB takes
0.40 s (104 MB allocated). Covered scope: one call, warm image, box under a
load average of 6 to 8 with other lanes building; it measures the ACL2
function only, not the bridge marshalling that now carries the payload.

That is **an order of magnitude under the 200 ms threshold**, so no
by-reference plan is needed for the digest itself. The cost that did move is
**marshalling**: `tools/frame_bridge.py` used to send only a 19-octet preimage
head and hash locally, and now sends the whole payload as decimal octets
(about 4x expansion, so roughly 130 KB of pipe traffic for a 32 KiB article).
The native host (`host/native/io.lisp`) calls in process and pays none of it.
Since the recorded direction is to retire the Python host, the marshalling
cost is recorded, not optimised; if the Python bridge outlives that decision,
the by-reference plan is a payload handle the store already holds, not a
smaller digest.

## Findings

1. **`tools/crypto_host.py` does not hash.** The packet brief expected the
   Python-side hashing to be there; it is Ed25519 only, and no other module
   imports `cryptography`. The identity hashing was in `tools/frame_bridge.py`
   and in a hand-written SHA-256 in `host/native/io.lisp` (`fnn-sha256`, ~50
   lines of typed Common Lisp). That second one is the one the one-owner rule
   really bit on.
2. **`fnn-sha256` still has three callers** and is therefore still a twin for
   one of them: the **frame integrity trailer**
   (`host/native/io.lisp:757,762`, `tools/frame_bridge.py:153,160`) — ACL2
   owns the protected prefix, the host digests it. With `fn-frame-digest`
   attached this can now move too; it needs a `fn-store-frame-trailer`
   wrapper and is the obvious next packet. The other two callers (a JSON body
   digest for a log line, a CLI file hash) are host-only and are not twins.
3. **`kestrel/crypto/sha-2` exists on hbox but is not certified**, and neither
   is its dependency closure (`kestrel/bv`, `kestrel/bv-lists`,
   `kestrel/arithmetic-light`: zero `.cert` files). Certifying it was well
   outside the fifteen-minute budget the brief set, so the book was written
   instead. If the community closure is ever certified there, the honest
   follow-up is to prove `fn-sha256` equal to `SHA2::sha-256-bytes` rather
   than to replace it.
4. **AUTHINFO's last inch is blocked, and not by the digest.**
   `books/nntp-auth.lisp` still compares the cleartext secret with `equal`.
   Switching it is: `fn-auth-cred-secret` holds a `fn-authsec-verifierp`,
   `fn-auth-credp` recognizes it, `fn-auth-checkp` calls `fn-authsec-checkp`,
   and `books/nntp-auth.lisp` includes `auth-secret`. That is three
   recognizer edits, not one call, and **`books/peer-config.lisp` fails to
   certify on `dev`** (board note from `w9/server-polish`), so `nntp-auth` and
   everything above it cannot reach a verdict — the change could not even be
   `ld`-probed. It was therefore not made blind. Whoever lands `peer-config`
   should take this with it.
5. **`fn-anchor-leaf-digest` (`books/anchor.lisp`) is still constrained.**
   Attaching it is one `defattach` plus one shape discharge, in the anchor
   cluster's hands; this lane deliberately did not reach into it. Signature
   verification stays constrained everywhere: **Ed25519 is not this packet**,
   and nothing here is evidence about a signature.

## Evidence

All on hbox, ACL2 8.7 (`/tank/fn/acl2-8.7/saved_acl2`), SBCL, under
`swarm-build`, with `ACL2_CUSTOMIZATION=NONE` and `ACL2_BOOK_HASH_ALISTP=NIL`
(set by every tool), `FN_ACL2_TIMEOUT_SECONDS=1800`.

| root | verdict |
| --- | --- |
| `books/sha256` | certified |
| `tests/acl2/sha256-tests` | certified |
| `books/crypto-attach` | certified |
| `books/auth-secret` | certified |
| `tests/acl2/auth-secret-tests` | certified |
| `books/identity` | certified (unchanged) |
| `books/identity-invariants` | certified (unchanged) |
| `tests/acl2/identity-tests` | certified (unchanged) |

Farm run `run-20260920T185055Z-0836` (installed 216 cached certificates, 36
uncached, 19 certified in the run), evidence
`/tank/fn/lanes/w9-digest/build/acl2/certify-20260920T185152Z-1079466`;
the final pass, after the export-hygiene edits, certified all eight roots
together: `certify-20260920T190013Z-1089503`. **No existing root's closure changed**: `books/crypto-seam.lisp` and
`books/frame-octets.lisp` were not edited, so nothing downstream of them needed
recertification, and every existing keystone statement is untouched.

`tests/identity_differential.py`, hbox, one live session: **100 cases,
235,314 payload octets, every ACL2-derived subject and obligation identity
equal to the host's old SHA-256 derivation**, 0.104 s for the 200 ACL2
identity derivations including bridge marshalling. Cases include the empty
payload, the 56/64/65/119/120-octet padding boundaries and a 32 KiB payload.

`make check`: scaffold OK, ledger OK, `python3 tools/ledger.py --write` run.
`tools/host_check.py` is SKIPPED locally (no ACL2 on the laptop) and is not
evidence until it runs with a real ACL2.

### Two ACL2 facts this lane paid for

- **`zp` has guard `(natp x)`**, so a `:guard t` function that tests `(zp n)`
  on an arbitrary argument does not guard-verify. Bind `(nfix n)` first.
  Likewise `cddr`/`cadr` on an arbitrary object: `cdr`'s guard is
  cons-or-nil, so `(car (cdr x))` needs `(consp (cdr x))`, not `(consp x)`.
- **An attachment must not be called while computing a `defconst`** (`:DOC
  ignored-attachment`). A test book cannot bind a digest to a constant; the
  enrolment has to happen inside each `assert-event`. That restriction is
  worth keeping in mind for any book tempted to precompute a digest.
