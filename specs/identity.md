# Identity: the crypto seam, principals and key succession

Status: local engineering substrate with a selected native signature suite.
D09 now requires Ed25519 **and** ML-DSA-65 from the first release (user decision,
2026-09-21). The native profile and runtime primitive boundary are implemented;
key custody, durable article composition and deployment qualification remain
open, and no public ABI is frozen (D08).
Cryptographic unforgeability remains an A-CRYPTO assumption in
[failures](failures.md), not an ACL2 theorem.

The executable profile in `books/hybrid-signature.lisp` binds version 1,
required suite 1, the principal, the ordered algorithm-tagged enrolled Ed25519
and ML-DSA-65 keys, and a length-delimited exact authored-source subject under
`fn-authored-source-hybrid-v1`. Both pure signatures cover those full bytes;
authorship is not reduced to an externally supplied content-id digest.
Both signatures must verify; unsupported, absent or invalid components cannot
authorize via a classical-only fallback. `fn-hsig-authorize` is the final ACL2
decision called through `host/hybrid-signature-host.lisp`. The native boundary
uses libsodium for Ed25519 and OpenSSL 3.5 or newer for ML-DSA-65, sharing the
TLS process library and explicitly fetching the provider algorithm. Callers
supply independent key material. Legacy unsigned NNTP submissions
retain their explicit gateway provenance. The standard primitive is
[ML-DSA in FIPS 204](https://csrc.nist.gov/pubs/fips/204/final);
[OpenSSL 3.5's ML-DSA interface](https://docs.openssl.org/3.5/man7/EVP_SIGNATURE-ML-DSA/)
is the native implementation boundary, not a proved primitive.

The production image exposes `fn hybrid-sign PRINCIPAL ED-PUBLIC ED-SECRET
ML-PUBLIC-PEM ML-PRIVATE-PEM SOURCE`. The first three binary files have exact
widths 32, 32 and 64 octets; the source is read byte-exact up to the article
limit. The command prints separate algorithm-tagged hexadecimal components
only after verifying the newly produced pair through the ACL2 profile. It
stores no keys and defines no custody or recovery authority.

The live owner also accepts bounded `hybrid-enroll` and `hybrid-author`
operations on its operator-authorized local-control socket. `hybrid-author`
verifies both native signatures against the selected enrolled keyring, then
asks ACL2 to render the portable received article and construct one atomic
article/verdict event. The embedded Store article contains the received
`FN-Authorship` carrier followed by exact authored source; the parent retains
that source separately with its ACL2-derived identity. The Store content
identity and charge apply to the received article. Its owner-observed
acceptance stamp remains in the embedded record. Missing, unknown, or
substituted enrollment generations are refusals. This local operator path
is not yet the portable authenticated author transport.

`fn-hsig-subject-body-injective` proves that equality of two valid authored
subject bodies implies equality of their principal, ordered Ed25519 and
ML-DSA-65 key set, and exact source octets. The proof projects the fixed-width
fields and the source from the bytes; there are no optional profile fields or
normalization variants. `fn-hsig-signed-preimage-injective` instantiates the
tagged-preimage theorem with the exact hybrid domain tag and those bodies.
Both results concern byte framing below the signature primitives. They make no
claim about signature unforgeability, hash collisions, library correctness, or
key custody.
The book and its concrete hypothesis counterexamples have
[source-matched hbox certification](../planning/evidence/hybrid-injectivity-certification-2026-09-21.md).
The initial failed attempt used older CBOR source and is retained separately.

Books: `books/crypto-seam.lisp`, `books/hybrid-signature.lisp`,
`books/hybrid-signature-invariants.lisp`, `books/principal.lisp`,
`books/principal-invariants.lisp`; tests `tests/acl2/crypto-seam-tests.lisp`,
`tests/acl2/principal-tests.lisp`. The [decision packet](../planning/decision-packet-d09-d11.md)
carries the proposals this profile assumes.

## Portable FN-Authorship v1 carrier (bounded precursor)

`books/hybrid-carrier.lisp` defines a distinct `FN-Authorship` field for the
exact-source hybrid signature. Its canonical binary value is nine ordered CBOR
items: version 1, suite 1, 32-octet principal, Ed25519 algorithm 1 and
32-octet public key, ML-DSA-65 algorithm 2 and 1952-octet public key, then
64-octet Ed25519 and 3309-octet ML-DSA-65 signatures. The encoded binary is
bounded to 5405 octets before emission and before parsing; the base64 field is
bounded to 8192 octets before emission and before decoding. A fixed nine-item
budget and the bounded article parser constrain work before any carrier value
can become a verification subject. A future version or suite is a separate
profile: these v1 bytes keep their meaning, and unknown bounded evidence may
be retained without gaining authority.
`fn-stxe-profile-supportedp` recognizes exactly `fn-hybrid-v1`. The evidence
record's `fn-stxe-authority-verdict` returns `:requires-binding` for that tag:
a tag and stored token alone cannot upgrade arbitrary detail bytes to a
verified author. The T10 Store join must bind the accepted event, keyring
snapshot and both primitive observations before presenting a verdict.

The authored source contains the signed Date, Message-ID, Newsgroups, From and
Subject fields. `fn-hc-native-plan` refuses the mutable namespace in native
source. `fn-hc-received-plan` requires one valid FN-Authorship field, projects
Path, Xref, Injection-Date and Injection-Info outside the signed source, and
retains original received octets on refusal. It also refuses other reserved
fn fields rather than guessing an authored source. This carrier does not give
FN-Statement's content-id signature the semantics of exact-source authorship.
`host/native/signatures.lisp` has a ready verification entry that calls the
ACL2 projection and preimage, asks libsodium and OpenSSL for independent
observations, and calls ACL2's both-required `fn-hsig-authorize`. The actual
The kind-4 accepted-event codec preserves version-0's eleven items and bytes.
Version 1 has thirteen items: the original eleven followed by exact authored
source and its versioned content identity. Replay accepts version 1 only when
the received article projects to that exact source, its canonical carrier
contains the enrolled principal and ordered key set plus both signature
components, and its recorded `:verified` verdict names that principal.
Replay retains the historical verdict without recomputing today's keyring
capability or trusting a profile tag alone. Native acceptance and reader
exposure require a combined image/runtime qualification; the reader projection
is still pending.

The native `hybrid-sign-carrier PRINCIPAL ED-PUBLIC ED-SECRET ML-PUBLIC-PEM
ML-PRIVATE-PEM SOURCE OUTPUT` command writes an ACL2-rendered article with
`FN-Authorship` to a new file after both signatures verify. The companion
`hybrid-verify-carrier ARTICLE ML-PUBLIC-PEM` command reads a bounded article,
uses ACL2's received-source projection, checks the Ed25519 and ML-DSA-65
signatures with native libraries, and asks ACL2 for the final conjunction.
ACL2's `fn-hc-render-at-most` refuses output when carrier expansion pushes the
complete received article over the same article cap the verifier reads.
It reports `verified PRINCIPAL-HEX` (exit 0) or `unverified REASON` (exit 1).
The caller-supplied ML public key must match the carrier's key set. This is an
independent portable artifact check, not Store acceptance or a historical
verdict. The commands use caller-supplied keys and do not enroll, succeed, or
revoke a principal; manual enrollment remains the existing node policy, and
the authority for key succession is still an unchosen D09 decision. A
generated field can travel with an article while the exact signed
source and mutable relay fields remain separate projections.

The remaining Store join needs a versioned accepted-article binding with two
distinct subjects: the received article octets used for storage and content
identity, and the exact authored source recovered by the ACL2 carrier
projection. Its admission constructor must show that the carrier's ordered
key set and both signatures equal the historical verdict detail, the selected
enrollment snapshot matches that key set, and both primitive observations
authorized that authored source. The versioned record should carry an ACL2-
derived authored-source identity separately from the received article's
content identity. Replay must check the structural bindings
without promoting an unsupported profile or reinterpreting old kind-4 bytes;
the recorded verdict remains historical, while current capability uses the
current keyring. Only after the composite finish/index theorem covers this
record can a served `:fn-verified` value be attributed to that accepted event.

## The seam

`fn-digest` (any object to 32 octets) and the triple `fn-sig-public-key`,
`fn-sig-sign`, `fn-sig-verify` are ACL2 constrained functions introduced by
`encapsulate` with local witnesses. ACL2 knows exactly four things about them:

| Constraint | Statement | What it does not say |
| --- | --- | --- |
| `fn-digest-shape` | the digest is 32 octets | nothing relates two preimages with equal digests; the local witness is a constant |
| `fn-sig-public-key-shape`, `fn-sig-signature-shape` | a public key is 1 to 4096 octets, a signature 0 to 4096 octets | which suite; hybrid ed25519 + ML-DSA-65 fits (32 + 1952, 64 + 3309) |
| `fn-sig-verify-is-boolean` | verification is a boolean | |
| `fn-sig-verify-of-sign` | for a 32-octet seed `sk` and octet message `m`, `(fn-sig-verify (fn-sig-public-key sk) m (fn-sig-sign sk m))` | that any other signature is rejected: the local witness accepts a signature equal to the public key |

Collision resistance and existential unforgeability are A-CRYPTO. The test
book attaches two realisers with `defattach` and ACL2 proves both satisfy the
seam: a 256-bit polynomial fold, and the input length zero-padded, under which
every equal-length pair collides. That the second one is admitted is the
evidence that the seam carries no collision claim; it rebuilds
`lengthScheme_not_binding` of `~/dev/minidregg/Theory/LaceMerge.lean`.
`must-fail` records that digest injectivity and signature unforgeability are
not theorems.

Shapes mirror `~/dev/breadstuffs/metatheory/Dregg2/Authority/BiscuitGraph.lean`
line 55 (`SigChecker`, an opaque `PubKey -> Block -> Bool` the law only reads)
and `Dregg2/Crypto/CapabilityChain.lean` line 65 (`SigScheme.verify` inside
`VerifyFrom`); the seed-derived hybrid key with a domain-separation context is
`~/dev/breadstuffs/blocklace/src/pq.rs` (`BLOCK_PQ_CTX`, `from_seed`) and
`signer.rs` (`HybridBlockSigner`).

## Domain separation

Every digested or signed preimage is `fn-digest-tagged-preimage tag m`: the
CBOR byte string of an ASCII tag `fn-<purpose>-v1` followed by the message.
Theorem `fn-digest-tagged-preimage-separates`: for a 1 to 64 octet tag and an
octet message within the one-item decoder cap, decoding the preimage yields
the tag item and leaves exactly the message. Theorem
`fn-digest-tagged-preimage-injective`: two tagged preimages are equal only if
their tags and messages are equal. Both are about preimages, below the digest.
Tags in use: `fn-principal-v1`, `fn-statement-v1`, `fn-statement-sig-v1`,
`fn-payload-v1`, `fn-policy-evidence-v1`.

## Principals

A principal id is `fn-digest-tagged "fn-principal-v1" (bstr pk || bstr token)`,
the ACL2 translation of `CellId = blake3::derive_key("dregg-cell-id-v1",
pubkey || token)` in `~/dev/breadstuffs/README-LLMs.md` section 2. The token
lets one key own several principals; a node checks a claimed genesis binding
with `fn-prin-genesis-bindsp` by recomputation.

| Theorem | Property | Hypotheses | Scope |
| --- | --- | --- | --- |
| `fn-prin-preimage-injective` | the encoded (key, token) pair determines both | key is 1 to 4096 octets, token at most 64 octets | the preimage; a principal id determines its key preimage only under A-CRYPTO collision resistance, which `principal-tests` shows failing under the length realiser |
| `fn-prin-id-unfolds` | the id is the tagged digest of that preimage | none | definitional; named so |

## Key succession

A principal's key chain is the state `(id key incarnation next-sequence)`. A
succession is a statement of kind `:succession` (see [statements](statement.md))
by the principal whose payload is one byte string, the new public key.
`fn-prin-succession-acceptablep st s` requires: well-formed statement, kind
`:succession`, creator equal to the principal id, incarnation and sequence
equal to the state's, sequence not exhausted, a decodable key, and
`fn-stmt-verifiedp s (current key)`. `fn-prin-resolve` folds a statement list
through `fn-prin-apply-succession`, skipping what is not acceptable.

| Theorem | Property | Hypotheses | Scope |
| --- | --- | --- | --- |
| `fn-prin-sign-succession-advances-key` | the holder of the current key moves the key to a new one | state well formed, seed's public key equals the state's key, new key well shaped, sequence below 2^32 - 1 | the satisfiable pole, using the seam's `fn-sig-verify-of-sign` |
| `fn-prin-first-key-move-is-verified-under-prior-key` | if resolution over any list moves the key, the first accepted statement is in the list, is a `:succession` by this principal, and verifies under the key held before it | state well formed | conditional on what `fn-sig-verify` accepts; unforgeability is A-CRYPTO |
| `fn-prin-trail-is-valid-chain` | the accepted trail is a chain in which every step verifies under the key its predecessor installed | none | the `VerifyFrom` shape of `CapabilityChain.lean` line 65 and `WellFormed` of `BiscuitGraph.lean` line 55, depth one at each step |
| `fn-prin-resolve-is-resolve-of-trail` | resolving the trail alone gives the same state | none | the skipped statements do not contribute |

Teeth (`principal-tests`): a succession signed by a non-holder is not
acceptable and leaves the state unchanged; a replayed succession, one signed
with the retired key, a wrong incarnation, a wrong principal id, a wrong kind,
an undecodable payload and an exhausted sequence are each rejected; a mixed
list resolves to the expected key with the expected trail.

## Keyrings

A keyring is a list of `(id . public key)` entries, the node's resolved view
of principals; `fn-prin-verifiedp s keyring` holds when the creator is a known
principal and the statement verifies under that key. An unknown creator never
verifies. How a keyring is persisted, and revocation under partition, are in
the decision packet; the policy theorems are conditional on the keyring.

## Assumed

A-CRYPTO for collision resistance and unforgeability; the keyring's genesis
bindings were checked by recomputation; the seed of a principal is held by
the principal (custody is a D09 proposal); the deployed realiser of the seam
is not chosen here.
