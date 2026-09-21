# Handoff: w14/native-primitives — native crypto, TLS and anchor boundary

Branch `w14/native-primitives`, based on `f181a1a`.

## Result of the runtime inventory

D07 excludes Python from the deployed node, CLI and helpers.  It does not move
semantic ownership out of ACL2 and it does not decide D09.  The current runtime
gaps separate as follows.

| Operation | Current implementation | Native boundary | Dependency before deployment |
| --- | --- | --- | --- |
| Content and frame SHA-256 | `books/sha256.lisp`, attached by `books/crypto-attach.lisp` | Keep in ACL2; `fnn-sha256` is only a native differential helper | None for the primitive; callers must keep using the ACL2 result |
| Roughtime Ed25519 verification | `tools/crypto_host.py` via Python `cryptography` | `fnn-crypto-ed25519-observe`, implemented here over libsodium | Native anchor caller must get each exact subject from ACL2 and preserve unavailable/fault separately from a negative signature |
| Roughtime SHA-512 leaf | `tools/roughtime.py:_leaf` | `fnn-crypto-anchor-leaf`, implemented here over libsodium | The correspondence to constrained `fn-anchor-leaf-digest` remains a named trust assumption, not a theorem |
| DELE and SREP signed preimages | `books/anchor.lisp`; host wrappers in `host/anchor-host.lisp` | Remain ACL2-owned | Call `fn-anchor-host-delegation-octets` and `fn-anchor-host-signed-octets`; never rebuild either in raw Lisp |
| Delegation window | `fn-anchor-window-okp`, reached through `fn-anchor-verifiedp-observed` | Remain ACL2-owned | Remove the Python parser's historical preflight from the production composition; pass fields to the ACL2 entry |
| Merkle/nonce binding | Python parses/folds up to 32 nodes; accepted ACL2 scope is only `fn-anchor-one-nonce-p` | For the selected accepted scope, the host observes empty `PATH`, zero `INDX`, and equality of `ROOT` with `fnn-crypto-anchor-leaf(NONCE)` | A non-empty path stays `:uncertain :unmodelled-tree`.  A general native fold cannot establish acceptance until ACL2 models it (D22) |
| Roughtime tagged-message request/response grammar | `tools/roughtime.py` | `fn-anchor-wire-request` and `fn-anchor-wire-parse-response`, implemented in the follow-on packet | Native acquisition calls both through `host/anchor-wire-host.lisp`; no raw-Lisp grammar |
| Server list, pinned key and nonce generation | JSON plus Python `os.urandom` | OS CSPRNG implemented in `fnn-anchor-csprng-nonce`; pinned manifest still missing | One pinned native manifest must inject endpoint/key; no defaults or caller-selected unpinned key |
| FNAN framing and anchor decisions | `books/anchor-record.lisp`, `books/anchor.lisp`, `host/anchor-host.lisp` | Already ACL2-owned | Native storage must call those wrappers and preserve accepted/refused/uncertain |
| NNTP TLS | Python `ssl` in `tools/run_owner.py`; ACL2 owns the surrounding STARTTLS state | Native owner lane, using the existing OpenSSL 3 `libssl` dependency | Flush 382 before the handshake; on success call `fn-owner-tls-established`; handshake/certificate/cipher properties remain TCB claims |
| Native author signing and principal signature verification | Python CLI can make Ed25519 signatures, while `fn-sig-*` remains an abstract ACL2 seam | Not selected here | D09 must choose the suite/container, key custody and migration policy first |

The machine has libsodium 1.0.22.  `hbox` and `persvati` have the
`libsodium.so.23` ABI from 1.0.18.  All three have OpenSSL 3, with versions
3.6.4, 3.3.1 and 3.5.3 respectively.  This packet selects libsodium only for
the already-selected Roughtime Ed25519/SHA-512 profile.  It does not select
Ed25519 for native article authors or freeze any D09 key profile.

## Implemented primitive seam

[`host/native/crypto.lisp`](../../host/native/crypto.lisp) is self-contained
raw Lisp under the existing `fnn-` native prefix.  It exposes:

- `fnn-crypto-ed25519-verify`: `T` or `NIL` for a bounded detached signature;
  unavailable libraries and unexpected primitive returns signal conditions.
- `fnn-crypto-ed25519-observe`: `:verified`, `:refused`, `:unavailable` or
  `:fault`.  The last two are not signature verdicts.
- `fnn-crypto-sha512`: a bounded input to exactly 64 octets.
- `fnn-crypto-anchor-leaf`: exactly SHA-512 of `0x00 || nonce` for a 32-octet
  nonce.
- `fnn-crypto-initialize` and `fnn-crypto-version`: load/inspect the library and
  check the public-key, signature and digest widths exported by its ABI.
- `fnn-crypto-startup`: clears facility state serialized in a saved image, then
  reloads/reinitializes the library and repeats every ABI check.

The message cap is 4096 octets, the existing maximum Roughtime response size.
The actual ACL2-produced DELE and SREP signed subjects are 111 and 133 octets.
A shorter wrong Ed25519 key/signature width is a negative verification result,
matching the ACL2 seam constraints.  A value beyond the fixed key/signature
buffer bound faults before allocation or primitive entry.  Non-octet inputs and
library faults are also host faults.  None can become a verified observation.

The trust boundary contains libsodium's dynamic object and CPU implementation,
SBCL's alien interface and pinning, the integrity of the supplied key/message/
signature buffers, and the stated correspondence between this implementation
and the two constrained anchor functions.  The width checks and known-answer
tests constrain integration mistakes; they prove no cryptographic property.

## Required anchor call sequence

For one bounded datagram, the native caller must:

1. Call `fn-anchor-wire-host-parse(packet, nonce, pinned-key)`.  A malformed
   response is `(:refused reason)`; success is tagged `:parsed`, never accepted.
2. Take the ten fields, path/index, and both signature subjects from that
   result.  They are all projections of the same ACL2 parse.  Do not parse the
   packet or rebuild DELE/SREP in raw Lisp.
3. Verify those exact two results with `fnn-crypto-ed25519-observe`.
4. Treat either `:refused` as a false signature verdict.  Treat `:unavailable`
   and `:fault` as no verdict; the operation cannot report accepted.
5. Supply a true `one-nonce` observation only when `PATH` is empty, `INDX` is
   zero and `fnn-crypto-anchor-leaf(nonce)` equals the signed root.
6. Pass the combined verdict and one-nonce observation to the actual caller:
   `fn-anchor-host-accept`, `fn-anchor-host-restore`, or
   `fn-anchor-host-advance`.  These wrappers call the observed ACL2 subjects
   whose equality keystones are in `books/anchor-invariants.lisp`.

The native code must not perform the delegation-window decision, accept a
general Merkle path, substitute current configuration for the pinned key, or
write FNAN bytes of its own.

## Implemented wire grammar

`books/anchor-wire.lisp` owns the deployed RoughTime v1 tagged-message grammar
for the top response and nested CERT, DELE and SREP messages.  It bounds the
datagram at 4096 octets, tag count at 32, and PATH at 32 SHA-512 nodes before
walking them.  It requires strictly increasing numeric tags, monotone in-range
cumulative offsets, all required fields and exact field widths; binds NONC to
the caller's request nonce; constrains INDX to the PATH depth; and compares the
received DELE and SREP octets to `books/anchor.lisp`'s canonical reconstruction.

`host/anchor-wire-host.lisp` is the program-mode bridge.  Its `:parsed` result
contains the ten anchor fields, PATH, INDX, ACL2's delegation subject, ACL2's
response subject, and a one-nonce shape bit.  It makes no crypto, delegation-
window, pinned-membership, freshness or storage decision.
`host/native/anchor.lisp` now supplies nonce generation, UDP acquisition and
primitive composition.  The pinned server manifest remains separate; the
configuration/CLI lane owns only its bounded selected server name and correctly
refuses availability until that manifest and this consumer are integrated.

The public safety theorem is `fn-anchor-wire-parse-success-has-anchor`, whose
subject is exactly `fn-anchor-wire-parse-response`; the deployed bridge calls
that function at `host/anchor-wire-host.lisp:29`.  The empty-PATH captured
packet is the reachable non-degenerate witness in the test book.  The theorem
is unconditional, so it has no removable hypothesis to test with `must-fail`.

`tests/acl2/anchor-wire-tests.lisp` evaluates the parser on exact committed
int08h captures.  It includes both an empty-PATH response and the real one-node
batched response, plus nonce mismatch, duplicate/out-of-order tag, decreasing
offset, truncation and packet-bound negatives.  The book and test certified
under ACL2 8.7.  Exact source digests, invocations, results, manifests, the
independent host-load transcript and limitations are archived in
[`tests/evidence/2026-09-21-native-anchor-wire.md`](../../tests/evidence/2026-09-21-native-anchor-wire.md).

All 34 parser/request `defun` events are guard-verified in that archived run.
This corrects the first parser checkpoint, which certified with guard eagerness
disabled and therefore was not yet suitable for a native executable call.

## Native acquisition seam

`host/native/anchor.lisp` exposes `fnn-anchor-acquire(profile)`.  The profile
is the exact result of ACL2 `fn-anchor-server-host-select`: endpoint, selected
key, whole pin set, nonce/request/response sizes, and admitted timeout.  It
reads the requested nonce width from `/dev/urandom`, asks
`fn-anchor-wire-host-request` for the request, performs one connected IPv4 UDP
exchange with a one-byte overbound probe, asks
`fn-anchor-wire-host-parse` to parse and bind the response, and runs libsodium
only over the two subjects ACL2 returned.  For the currently accepted
one-nonce scope it also compares ACL2's signed ROOT with
`fnn-crypto-anchor-leaf(nonce)`.

The result is `:observed`, `:refused`, `:uncertain`, or `:fault`; this seam
never says `:accepted`.  Its observed payload is the ten ACL2 fields plus the
boolean signature and one-nonce observations for the existing ACL2
accept/restore/advance entries.  Timeout, DNS/socket failure and an unavailable
crypto facility stay uncertain.  Malformed/overbound responses are refused;
invalid local inputs and primitive/core faults remain faults.

The component test passed on `nextop`, `hbox` and `persvati`, and an ACL2 8.7
raw-mode smoke reached the real executable counterpart of
`fn-anchor-wire-host-request`.  Exact commands, versions, source/log hashes and
limits are archived in
[`tests/evidence/2026-09-21-native-anchor-acquisition.md`](../../tests/evidence/2026-09-21-native-anchor-acquisition.md).

The follow-on adds `books/anchor-servers.lisp` as the ACL2-owned pinned
endpoint/key/bounds manifest and registers native `anchor acquire`.  The
command calls the actual `fn-anchor-host-accept`, persists its accepted FNAN
by mutable staged replacement under the store writer lock, and prints accepted
only after the store-directory barrier.  This replacement is separate from
the shared immutable publisher.  The common native image loads the certified
wire/manifest books, anchor host wrappers, crypto and anchor raw components;
the command invokes `fnn-crypto-startup` after image restart.

DNS resolution remains outside a whole-path deadline; send and receive
readiness each receive the selected timeout.  Readiness can race nonblocking
I/O and remains network uncertainty.

Exact-revision certification, three-host component runs and the common-image
live acceptance/restart observation are archived in
[`tests/evidence/2026-09-21-native-anchor-runtime.md`](../../tests/evidence/2026-09-21-native-anchor-runtime.md).
The image-build tool retained an explicit failure because this lane did not
recertify the unrelated served closure; root's frozen integrated batch remains
the clean common-image gate.

## TLS composition contract for the owner lane

The host performs only the TLS record/handshake facility.  The ACL2 owner has
already emitted `(:starttls)` and the 382 reply, and `fn-owner-starttlsp` names
that obligation.  The native owner must completely flush the reply before
giving the socket to OpenSSL, must not feed pipelined bytes to NNTP, and on a
successful handshake must re-enter through `fn-owner-tls-established`.  A
handshake failure closes/faults that connection and never produces the
established event.  Certificate loading, private-key protection, TLS versions,
cipher implementation and OpenSSL itself remain explicit TCB/deployment gates.
This lane supplies no TLS socket code and does not overlap the owner lane.

## Loading and evidence

The common image should load `host/native/crypto.lisp` inside the existing raw
host block, before native owner/anchor callers.  A build may call
`fnn-crypto-initialize` as an early dependency gate, but **every restored image
must call `fnn-crypto-startup` from its process entry before dispatch**.  A
serialized `*fnn-crypto-state*` of `:ready` is not evidence that this process
loaded the same object, ran `sodium_init`, or checked its ABI.  The file has no
dependency on `host/native/io.lisp`.  Refusing an unavailable library is the
deployment gate; there is no Python or alternate semantic fallback.

[`tests/native_crypto_primitives.lisp`](../../tests/native_crypto_primitives.lisp)
runs directly under SBCL.  It covers the RFC 8032 empty-message Ed25519 vector,
tampered and wrong-width negatives, the FIPS 180-4 SHA-512 `abc` vector, and
both real signatures plus the one-nonce root from the committed 2026-09-19
int08h capture.

```sh
sbcl --noinform --disable-debugger --script tests/native_crypto_primitives.lisp
```

It passed at implementation revision `88b0cd3` on the laptop with libsodium
1.0.22 and on `hbox` and `persvati` with libsodium 1.0.18.  Exact source
digests, tool versions, invocations, outputs and limitations are archived in
[`tests/evidence/2026-09-21-native-crypto-primitives.md`](../../tests/evidence/2026-09-21-native-crypto-primitives.md).
This is component evidence for the primitive seam.  FNAN persistence/recovery,
owner STARTTLS and the no-Python deployment gate remain separate integration
evidence.

`tests/test_native_crypto_saved_image.sh` writes a temporary SBCL core whose
serialized state falsely says the facility is ready, restarts it, requires the
startup hook to replace the stale path/version, and calls SHA-512 through the
fresh process binding.
