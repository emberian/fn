# Identity: the crypto seam, principals and key succession

Status: local engineering substrate with a selected native signature suite.
D09 now requires Ed25519 **and** ML-DSA-65 from the first release (user decision,
2026-09-21). The native profile, binding, key custody and runtime integration
still need implementation/qualification; no public ABI is frozen (D08).
Cryptographic unforgeability remains an A-CRYPTO assumption in
[failures](failures.md), not an ACL2 theorem.

The selected native-article profile must bind its version, required algorithms,
enrolled key set and length-delimited exact authored-source octets in a
domain-separated signed preimage. Both primitives sign that framed message;
an externally supplied content digest alone is not the authored message.
Both signatures must verify; unsupported, absent or invalid components cannot
authorize via a classical-only fallback. Legacy unsigned NNTP submissions
retain their explicit gateway provenance. The standard primitive is
[ML-DSA in FIPS 204](https://csrc.nist.gov/pubs/fips/204/final);
[OpenSSL 3.5's ML-DSA interface](https://docs.openssl.org/3.5/man7/EVP_SIGNATURE-ML-DSA/)
is a candidate native implementation boundary, not a proved primitive.

Books: `books/crypto-seam.lisp`, `books/principal.lisp`,
`books/principal-invariants.lisp`; tests `tests/acl2/crypto-seam-tests.lisp`,
`tests/acl2/principal-tests.lisp`. The [decision packet](../planning/decision-packet-d09-d11.md)
carries the proposals this profile assumes.

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
