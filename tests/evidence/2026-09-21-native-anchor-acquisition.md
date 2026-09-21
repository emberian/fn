# Native anchor acquisition component evidence — 2026-09-21

## Subject and exact inputs

This component run covers `host/native/anchor.lisp`: the OS CSPRNG nonce,
ACL2-produced request, connected bounded UDP exchange, ACL2 response parser
call, and libsodium observations over ACL2's exact delegation and response
subjects.  The input Git revision was `1e8955c` plus this follow-on packet.

| file | SHA-256 |
| --- | --- |
| `host/native/crypto.lisp` | `4ee2a19a83d825ecbed8b0f70518411ae4c7597547318e3b8c8d653a3bf83192` |
| `host/native/anchor.lisp` | `91f5012da4525b97303e12a4e98f802f41756229bee8b1da871c13d003ff7fff` |
| `tests/native_anchor_acquisition.lisp` | `89cb5e09656d9ece6e0fe6c0c62293e0ac318ae139e59f01dc7b98ce64f3398a` |

The raw component test uses narrow stubs for the already-certified ACL2 host
calls.  It checks the `/dev/urandom` result width/type, requires a pinned key of
exactly 32 octets before network I/O, verifies both real captured signatures
and the captured one-nonce root, observes a tampered signature as false, runs a
real local connected UDP request/response, and drives the full acquisition
function through its ACL2 request/parser call sites.

## Three-host run

The exact commands, OS and SBCL versions, input digests, libsodium version and
output are archived in:

| host | SBCL | libsodium | result | log SHA-256 |
| --- | --- | --- | --- | --- |
| `nextop.local` | 2.6.8 | 1.0.22 | passed | `892ef8ed829d1b2dba9cc1ec07f292d660a2647b93ddd51e09c7a6f8109ed513` |
| `hbox` | 2.2.9 | 1.0.18 | passed | `0d75506d52d5f9b8c3fb022de6b8eba28b24ddab4dab869096274f606035acdb` |
| `persvati` | 2.6.8 | 1.0.18 | passed | `85eaee3a02b988a558e206c9a39ed28726ba578df25867ae9091acc40d51675b` |

The files are `tests/evidence/native-anchor-acquisition/{nextop,hbox,persvati}.log`.

## Actual ACL2/raw composition smoke

On `nextop.local`, ACL2 8.7 loaded the certified `books/anchor-wire`, loaded
`host/anchor-wire-host.lisp`, entered a component trust tag, loaded the real
native I/O, crypto and anchor files, reinitialized libsodium, read a CSPRNG
nonce, and called `fnn-anchor-request`.  The actual raw `fnn-core` call reached
the executable counterpart of `fn-anchor-wire-host-request` and returned a
1024-octet request for the 32-octet nonce.

The exact driver digest, source digests, invocation and transcript are in
`tests/evidence/native-anchor-acquisition/nextop-acl2-integration.log`
(SHA-256 `0ff5a81f08cdc0c44e088122ddb3178e512ebefe7b9d4a37997bff25d56f8514`).

## Outcome and trust limits

The acquisition seam returns `:observed`, `:refused`, `:uncertain`, or
`:fault`.  A timeout, network failure, or unavailable crypto facility cannot
become an accepted observation.  A malformed response is the ACL2 parser's
refusal.  The seam itself never returns `:accepted`; the native FNAN/store
caller must pass the boolean signature and one-nonce observations to the
existing ACL2 accept/restore/advance entry and persist only its accepted
result.

These tests constrain integration and portability.  They prove no property of
libsodium, `/dev/urandom`, DNS, UDP, the remote server, or the physical store.
The pinned server manifest, native FNAN persistence/recovery, common-image load
order/startup, and CLI wiring remain integration gates.
