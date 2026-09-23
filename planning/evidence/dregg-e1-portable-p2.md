# Portable fn E1 authorship and Mini origin binding, 2026-09-23

This public synthetic test connects a real fn dual-signature native verifier
to Mini's source-owned E1 payload decoder and existing Lean native-prefix
re-admission. It establishes **portable exact-source authorship** under an
independently pinned full hybrid keyset, and **historical Mini origin
acceptance** under a separate genesis/profile pin. It does not establish
that the signed carrier was accepted or retained by an fn Store. The fn E2
fetch/cursor/ack interface and kind-4 event/snapshot-to-Store-position join
remain unserved, so no fn sequence, txid, incarnation, local membership or
historical verdict is promoted from caller metadata in this test.

The fn source branch `implement/mini-p2-portable` adds the read-only native
`hybrid-verify-source` verb at `e8f77755` and full raw ML key output at
`81c2a22b`, with generated ledger commits `c8e49d21` and `a078b956` and
contract text at `8fede54d`. `make check` passed on `8fede54d`. The command
uses the existing ACL2 received-carrier projection and source-ID derivation,
libsodium Ed25519 and OpenSSL ML-DSA-65 observations, and ACL2's both-required
authorization. It emits one `fn-portable-v1` line only on success: version,
principal, 48-octet source ID, Ed public key, 1952-octet ML public key and
exact authored source, all lowercase hex after the version token. The full
line here is 48,934 characters (SHA-256
`a74edea7f4dd875095ffcc6a59558017cd9dbf7af330f6392cf504449799a5f5`).

The shared developer image was built by the root image lane from frozen fn
`884e4816` after its default-profile load gate. Launcher:
`/tank/fn/gates/integrate-reader-repair-20260923/build/fn-host-developer`,
SHA-256 `ec8442a896d4b1b1ab242bfe649e5e595567c4bfb278fc7ce4091da581f0680a`;
core SHA-256
`4a49fe97136f8c592464eac64921b02b9f1482d38d90c46b5d219ccebecb17c1`.
Its OpenSSL prefix was `/tank/fn/toolchains/openssl-3.5.8`. The carrier was
the P0 public `signed.eml` (29,918 bytes, SHA-256
`dc5c8b864227ad808f8feef7b574bce6d8be2f1798ca1a3db8c14a7e63872e1e`).
The verifier returned the exact `source.eml` (22,393 bytes, SHA-256
`fca9c81e8cd02281b3703df4e931ae82c55a0bda63b3cf3447c8e32e13199000`),
source ID
`666e2f7375626a6563742f7631000101db8d0b5a12a710cbf1640087047eab7b685013c77082b9ecf6aa7e0340784a5c`,
principal `55` repeated 32 octets, the exact public Ed key, and the exact
1952-octet ML key pinned from the public PEM. No private key was present.

Mini isolated branch `implement/fn-evidence` at `0d50383` compiled a new
`Kernel.FnPortableSource` and modified `Host.Main` against the existing P1
native closure, reusing 3,088 source/package objects and recompiling only
those two Lean modules; the final response contains 3,090 objects. Lean
4.30.0; native binary
`/Users/ember/dev/minidregg-wt/fn-evidence/.lake/build/bin/minidregg-fn-portable-bounded`
SHA-256 `35c9bede8152132c367ccaa38f1b2e6a9524184f9106045aa530be0a1ef3b18d`.
The first incremental link took 25 seconds and the strict-claim Host-only
relink 10 seconds; the bounded-stdout Host-only relink took 17 seconds. The
native command reads the carrier within 32,768 bytes,
spawns its pinned verifier argument vector without constructing a shell command,
caps stdout during reading and parses its exact six-token
line below 70,000 characters, compares principal and both full public keys
with independent pins, checks the claimed source ID, Message-ID and group
text, then derives the base64 Mini package from the authenticated source in
Lean. Here, group text means the signed `Newsgroups` header, not the fn
Store's local membership set. The caller cannot substitute package bytes.
`FnEvidence.verify` then
re-admits the derived package against the independently selected Mini origin
pin. The derived package is byte-identical to public `package.bin` (16,136
bytes, SHA-256
`1bea29c16a63e8722f1567705b7b58e6ccdd7a8d5872d6b6f8c4b10d396f612b`).
The read-only result says `portableAuthorship: verified` and
`storeAdmission: unestablished` alongside the original Mini receipt.

The Mac Mini host invoked the Linux fn image through the 578-byte
`tests/fixtures/dregg-e1/portable-p2/hbox-transport-only.sh` (SHA-256
`631c338680978cd034b6fd1dfed7c64a4ce8d46ba756c2f06254afd5252282c2`).
That shim only copies the exact local carrier and public PEM into fresh
temporary hbox files and forwards stdout/stderr/exit; it performs no
semantic check. The operator-pinned image and this transport are trusted
execution boundaries for this test, as are the native crypto libraries.

The exact driver is
`tests/fixtures/dregg-e1/portable-p2/probe.py` (SHA-256
`63a2cbac0fba3da8fbd2d30ebf3f12bc2fae5472e00a30c3e7e32b8e44237ea3`).
It was invoked with the binary above, origin pin
`/tmp/mini-fn-evidence-final-20260923/independent-pin.json`, the transport
shim, and a fresh scratch output directory. Its 12-case result is
`native-results.json` (SHA-256
`68c2dc10aac0f74037d0211665569e994610b0a46f90cc3199e05a01e1f61e20`):
one exact positive; wrong source ID, Message-ID, group, principal, Ed key,
full ML key, and substituted ML PEM; a changed signed body; a wrong Mini
origin pin; an untrusted extra `storeAdmission` claim; and a verifier that
emits 70,002 stdout bytes. Every negative
exited 1 and created no source/package/result file. A separate Lean source
probe decoded the exact public package and refused four MIME/base64/layout
mutations; the strict portable-output probe refused trailing junk, wrong
version/field count, missing newline, uppercase hex and wrong key width.
These are native integration and parser observations, not proofs of physical
durability or cryptographic unforgeability.

The existing P1 Mini operation transaction is still a **synthetic** adapter
with a caller-supplied fn verdict reference. This P2 portable verifier is
read-only and does not turn that reference into a Store verdict, create an
operation intent, write an inbox/outbox, or ack fn. Production ingestion
requires a source-owned exact retained kind-4 event, enrolled snapshot and
Store position/history/incarnation evidence, joined to E2's future fetched
article and cursor before committing a Mini application decision. Distinct
transport attempt acknowledgements, fn application replies, and Mini current
execution authority remain separate.
