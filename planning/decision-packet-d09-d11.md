# Decision packet: D08 profile, D09 keys and suites, D10 forks, D11 authority

Status: PROPOSAL from the substrate lane (C1-11), 2026-09-19. Every item
below is a proposal for ember to select or reject; nothing here is recorded
in `decisions.md` by this packet. The certified books
(`books/crypto-seam.lisp`, `principal.lisp`, `statement.lisp`, `lace.lisp`,
`policy.lisp` and their invariants) implement the shapes under constrained
cryptographic functions, so a different selection changes the realiser and
the profile constants, not the theorems, except where noted.

## P1 (D09). Suite: ed25519 now, hybrid ML-DSA-65 as a profile slot

Proposal: the deployed realiser of `fn-sig-*` is ed25519 (RFC 8032, 32-octet
seed, 32-octet public key, 64-octet signature) with `verify_strict`. A second
profile, `hybrid-v1`, carries ed25519 plus ML-DSA-65 (FIPS 204) over the same
signing preimage, exactly as `~/dev/breadstuffs/blocklace/src/lib.rs`
(`Block::sign_by`, `verify_signature`) and `pq.rs` do: the ML-DSA key is
derived from the ed25519 seed (`MlDsaSigningKey::from_seed`), signed under a
domain-separation context (`BLOCK_PQ_CTX`, here `fn-statement-sig-pq-v1`),
and the verifier pins the enrolled ML-DSA public key rather than a key
carried in the statement. Under `hybrid-v1` a public key is 32 + 1952 octets
and a signature 64 + 3309 octets, inside the seam's 4096 bounds.

Consequence for the books: none; the seam's shape bounds already admit both.
Consequence for a different choice (say ML-DSA only, or a non-seed-derived PQ
key): the principal id preimage stays (public key, token); the keyring entry
becomes two keys; `fn-stmt-verifiedp` becomes a conjunction. The theorems are
unchanged because they only read `fn-sig-verify`.

Evidence still required before selection: an independent implementation's
test vectors run through the ACL2 encoder (C2-01), and the library choice for
the host (ed25519-dalek and fips204 in dregg; the Lean-verified ML-DSA cores
`dregg-pq` are the verified-TCB option and are the default to prefer).

## P2 (D09). Digest: BLAKE3 keyed derivation, 32 octets

Proposal: `fn-digest` is BLAKE3 in `derive_key` mode where the context string
is the fn tag, mirroring `blake3::derive_key("dregg-cell-id-v1", ...)` and
`Hasher::new_derive_key("dregg-blocklace-block-v1")`. The ACL2 books already
prefix every preimage with a length-delimited tag, so a plain SHA-256 realiser
over the tagged preimage is an equally valid choice with the same theorems;
BLAKE3 is proposed for speed and because dregg's vectors then transfer.

Quote the pessimistic number: a 32-octet digest gives a 2^128 collision bound,
not the 2^256 second-preimage figure; the equivocation and receipt theorems
depend on collision resistance (A-CRYPTO) and `lace-tests` shows what a
collision does.

## P3 (D08). Encoding profile used, not frozen

Used: item sequences of the existing bounded CBOR primitives (uint32 and
definite byte strings, `books/cbor.lisp`), one item per field, no arrays or
maps, explicit counts before repeated fields, tags as length-prefixed ASCII.
This is Candidate A of `docs/article-byte-examples.md` in spirit (explicit
lengths, versioned grammar) realised over CBOR heads rather than raw `u16be`
lengths, so the codec proofs of `cbor-invariants` carry.

Proposal: keep this as the local profile until C2-01, which is the point to
decide between staying with item sequences (smallest proof surface, no map
canonicalisation) and adopting deterministic CBOR maps (Candidate B, easier
evolution, larger canonicality boundary). Nothing in `specs/encoding.md` is
frozen by this lane; the byte layouts in `specs/statement.md` are local.

## P4 (D09). Custody on agent hosts and the human workflow

Proposal: an agent host holds its principal's seed in a host keystore outside
the replicated store (SEC-002), never in a statement, journal or lace. The
host's ACL2 core never sees the seed: signing is a host boundary call that
returns a signature over the preimage ACL2 computed (`fn-stmt-signing-preimage`),
and ACL2 checks `fn-sig-verify` on the result before the statement enters a
lace. A human author signs on their own device with a CLI (D17) that emits a
complete statement; the host is a relay for it and attests submission with its
own principal (gateway provenance, D02). Delegated hosts that post on a
human's behalf hold a separate principal whose authority comes from a policy
statement listing it, not from the human's seed.

## P5 (D09). Rotation by succession statements

Proposal: as implemented in `books/principal.lisp`: a `:succession` statement
by the principal, signed under the current key, naming the next public key,
at the principal's next (incarnation, sequence). The id is stable; the keyring
entry moves. Recovery from a lost seed is NOT rotation: without the current
key nothing can sign a succession. Proposal for recovery: a policy statement
of the group authority may name a replacement principal id for a member; the
old principal's statements remain attributable to the old id. A "recovery key"
pre-registered in the genesis binding is an alternative (token carries a
second key hash); it costs a larger preimage and is deferred.

## P6 (D10, D09). Offline revocation semantics under partition

What a partitioned node can conclude:

- A statement that verifies under the key its keyring holds for the creator
  was signed by a holder of that key at some time; the node cannot know
  whether a succession or revocation it has not received exists.
- A succession the node holds retires the prior key for statements at LATER
  slots of that principal; statements at earlier slots verified under the
  prior key remain verified (the chain is anchored at genesis, `VerifyFrom`).
- Two verified statements by one principal at one (incarnation, sequence)
  prove equivocation regardless of partition; the node keeps both and admits
  neither as a policy (`fn-pol-current` returns none).

What it cannot conclude: that a key is still authorised now; that a
counterparty has seen the same policy; that an absent statement does not
exist. Proposal: revocation is a succession to a distinguished "null" next
key (all zeros, never a real key) which makes every later slot unverifiable;
a policy statement removing a member takes effect for statements whose
predecessors include that policy (causal, not wall-clock). A receipt binds
the policy term so that a later reader sees which policy was in force for
the admitting node, not whether it was globally current.

## P7 (D10). Forks and restore

Proposal: no external freshness anchor for detection. A restored node
continues its incarnation only if it can prove it holds its own latest
statement (the frontier); otherwise it opens a fresh incarnation, declared by
its first statement at (incarnation + 1, 1) whose predecessors include the
last statement it knows of the previous incarnation. Reuse of a slot
is detected structurally (`fn-lace-reissue-is-equivocation`); which fork is
live is a policy decision of the group authority, not a fact the substrate
decides. C2-12 implements the restore/clone protocol against these books.

## P8 (D11). Group authority

Proposal: a group is identified by its authority principal id plus its name
octets; two authorities may use the same name and are different groups
(`policy-tests` shows this). Local aliases map an NNTP group name to one
(authority, name) pair in configuration. Owner/admin succession is a policy
statement by the authority listing a new authority as a member with a
`:policy` capability, deferred: the books implement depth-one authority only
(`fn-pol-authorizedp ... :policy` is the authority alone). Multi-party
governance is out of scope.

## P9. What changes if ember selects otherwise

| Selection | Books affected | Theorems affected |
| --- | --- | --- |
| Different digest or size | `*fn-digest-octets*`, realiser | none |
| Non-hybrid PQ-only suite | keyring entry shape, realiser | none |
| CBOR maps for the envelope (D08) | `statement.lisp` codec and its invariants | the round-trip and canonicality proofs are redone against the map codec; identity and policy theorems only read `fn-stmt-id` and field accessors |
| Key-is-identity instead of derived principal id | `principal.lisp` preimage | `fn-prin-preimage-injective` becomes trivial; succession must then change the id, breaking receipt attribution across rotation |
| Wall-clock ordering of policies | `fn-pol-slot-lessp` | `fn-pol-current-is-not-superseded` and confinement under equivocation no longer hold structurally |

## Not proposed here

No public ABI, no test vectors from a real library (C2-01), no MLS or private
group decision (D04), no per-principal resource accounting (C1-08).
