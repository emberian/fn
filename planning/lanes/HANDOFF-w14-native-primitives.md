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
| Roughtime tagged-message parsing and request encoding | `tools/roughtime.py` | Still missing | Add an executable ACL2 grammar or a named bounded refinement before a native anchor command; do not translate the Python decisions into raw Lisp |
| Server list, pinned key and nonce generation | JSON plus Python `os.urandom` | Still missing | One bounded native/ACL2 configuration owner, explicit OS CSPRNG trust, and no caller-selected unpinned key |
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

For a parsed ten-field anchor record, the native caller must:

1. Ask `fn-anchor-host-delegation-octets(fields)` for the long-term-key subject.
2. Ask `fn-anchor-host-signed-octets(radius, midpoint, root)` for the delegated-
   key subject.
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

It passed on the laptop with libsodium 1.0.22 and on `hbox` and `persvati` with
libsodium 1.0.18.  This is component evidence for the primitive seam.  Native
anchor acquisition, FNAN persistence/recovery, owner STARTTLS and the no-Python
deployment gate remain separate integration evidence.

`tests/test_native_crypto_saved_image.sh` writes a temporary SBCL core whose
serialized state falsely says the facility is ready, restarts it, requires the
startup hook to replace the stale path/version, and calls SHA-512 through the
fresh process binding.
