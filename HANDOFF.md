# HANDOFF: lane `substrate` (C1-11)

Branch `lane/substrate`, worktree `/Users/ember/dev/fn/build/lanes/substrate`,
branched from `0bd0b5c`. HEAD: see the `git rev-parse HEAD` block at the end.

## What this lane delivers

The identity, statement, lace and policy substrate as ACL2 books under a
constrained cryptographic seam, with invariant books, test books carrying
teeth, four specs, a decision packet and the Makefile roots. Nothing here is a
cryptographic claim: every use of a digest or signature reads a constrained
function; collision resistance and unforgeability are A-CRYPTO and are stated
as such in each spec.

## Files

New books (all in `books/`): `crypto-seam.lisp`, `statement.lisp`,
`statement-invariants.lisp`, `principal.lisp`, `principal-invariants.lisp`,
`lace.lisp`, `lace-invariants.lisp`, `policy.lisp`, `policy-invariants.lisp`.

New test books (`tests/acl2/`): `crypto-seam-tests.lisp`,
`statement-tests.lisp`, `principal-tests.lisp`, `lace-tests.lisp`,
`policy-tests.lisp`.

New specs: `specs/identity.md`, `specs/statement.md`, `specs/lace.md`,
`specs/policy.md`. New planning: `planning/decision-packet-d09-d11.md`.

Edited: `Makefile` (fifteen roots appended after `tests/acl2/nntp-tests`),
`docs/prefixes.md` (six rows). `tools/certify_books.py` `DEFAULT_BOOKS` was
not edited (not owned); the Makefile passes the full list.

## Ground truth each shape mirrors

| fn definition | dregg / minidregg artifact |
| --- | --- |
| `fn-stmt-make-header` (creator incarnation sequence preds kind ref), `fn-stmt-make` (header payload signature) | `~/dev/breadstuffs/blocklace/src/lib.rs` `pub struct Block { creator, sequence, predecessors, payload, signature, pq_signature }`; `~/dev/breadstuffs/metatheory/Dregg2/Authority/Blocklace.lean:58` `structure Block` |
| `fn-stmt-content-id` = tagged digest of header bytes; `fn-stmt-sign` signs the id | lib.rs `Block::id` (`new_derive_key("dregg-blocklace-block-v1")` over creator, sequence, predecessors, payload) and `Block::sign_by` (signature over `id()`) |
| `fn-prin-id pk token` = tagged digest of (bstr pk, bstr token) | `~/dev/breadstuffs/README-LLMs.md` section 2: `CellId = blake3::derive_key("dregg-cell-id-v1", pubkey||token)` |
| `fn-sig-verify` as an opaque boolean oracle; `fn-prin-chain-validp` | `Dregg2/Authority/BiscuitGraph.lean:55` `SigChecker`, `WellFormed`; `Dregg2/Crypto/CapabilityChain.lean:65` `VerifyFrom` / `VerifyChain` |
| seam shapes (32-octet seed, key up to 4096, signature up to 4096), domain-separated preimages | `blocklace/src/pq.rs` (`BLOCK_PQ_CTX`, `MlDsaSigningKey::from_seed`, PK_LEN 1952, SIG_LEN 3309), `signer.rs` `HybridBlockSigner` |
| `fn-lace-p`, `fn-lace-lookup` | Blocklace.lean:66 `Lace := List Block`, :70 `Lace.lookup` |
| `fn-lace-canonicalp` | Blocklace.lean:80 `Lace.Canonical` |
| `fn-lace-lookup-of-member` | Blocklace.lean:86 `lookup_of_mem` |
| `fn-lace-new`, `fn-lace-merge` | `Dregg2/Distributed/LaceMerge.lean` `newBlocks`, `mergeLace` (finality.rs:690); `~/dev/minidregg/Theory/LaceMerge.lean` `newEvents`, `merge` |
| `fn-lace-merge-ids-are-union`, `-idempotent`, `-commutative-ids`, `-associative-ids`, `-monotone`, `-lub` | LaceMerge.lean `laceIds_mergeLace`; minidregg `ids_merge`, `merge_idem`, `merge_comm`, `merge_assoc`, `merge_monotone`, `merge_lub` |
| `fn-lace-cross-canonicalp`, `fn-lace-cross-canonical-self`, `fn-lace-canonical-append-iff`, `fn-lace-same-view-of-cross-canonical` | LaceMerge.lean:247 `CrossCanonical`, `crossCanonical_self`, `canonical_append_iff`, `sameView_of_canonical_eq_ids`; minidregg section 3 |
| `lace-tests` gap section under `fn-toy-length-digest` | minidregg `lengthScheme`, `lengthScheme_not_binding`, `crossCanonical_is_the_gap`, `merge_drops_at_collision`, `merge_computes` |
| `fn-lace-equivocatorp`, `fn-lace-distinct-same-slot-is-equivocation` | lib.rs `EquivocationProof { creator, sequence, existing, conflicting }`; Blocklace.lean:152 `Equivocator` |
| `fn-lace-causally-closedp`, `fn-lace-merge-preserves-closure` | lib.rs "Key Invariants" 2 (`Blocklace::insert` causal closure) |
| design rules applied (satisfiable pole plus teeth per keystone, policy term not decision bit, pessimistic number) | `~/dev/minidregg/ATLAS.md` section 6 laws 1, 2, 12, 14 |

The packet asked for `fn-equivocatorp`; the prefix registry requires a layer
tag, so it is `fn-lace-equivocatorp` (same signature: lace, principal,
incarnation).

## Proposals for files this lane does not own

### `specs/objects.md`

- Line 14 (table row "Statement"): replace `| Statement | Kind, issuer, scope, subject references, terms/dependencies, authenticated encoding |` with `| Statement | Block-shaped header (creator principal, incarnation, sequence, predecessor content ids, kind, payload ref), payload, signature over the content id; see [statement](statement.md) |`.
- Line 15 (row "Origin event"): replace with `| Origin event | Subsumed by the statement header: (creator, incarnation, sequence) is the slot, predecessors are the causal references; see [lace](lace.md) |`.
- OBJ-004 paragraph: append the sentence `Two distinct statements at one (creator, incarnation, sequence) are retained and make the creator an equivocator in every lace holding both (fn-lace-distinct-same-slot-is-equivocation); which fork is served is a policy decision.`
- OBJ-006 paragraph: append `The structural half is fn-lace-reissue-is-equivocation; detection needs no freshness anchor, only both statements.`
- OBJ-007 paragraph: append `Authorization is a policy statement by the group authority resolved in the local lace (fn-pol-current); admission and receipts commit to the policy term, never to a boolean; see [policy](policy.md).`

### `specs/encoding.md`

- Status paragraph, after "The byte grammar is not frozen": add `The substrate books use item sequences of the existing primitives (uint32 and byte strings, one item per field, explicit counts) as a local profile; see [statement](statement.md). This is Candidate A of the article-byte examples over CBOR heads and is not a D08 selection.`
- ENC-003: append `Every digest and signing preimage in the substrate starts with the length-prefixed ASCII tag fn-<purpose>-v1 (fn-digest-tagged-preimage), proved to separate tag from message.`

### `planning/decisions.md`

- D09 row, Recommendation cell: append `Proposal P1/P2/P4/P5 of [the packet](decision-packet-d09-d11.md): ed25519 now, hybrid ML-DSA-65 profile slot, BLAKE3 derive-key digest, seeds in a host keystore, rotation by :succession statements.`
- D10 row: append `Proposal P6/P7 of the packet: structural fork detection via equivocation; a fresh incarnation is declared by its first statement; no external anchor for detection.`
- D11 row: append `Proposal P8 of the packet: a group is (authority principal, name); owner-only policy change; depth-one authority.`
- D08 row: append `Proposal P3 of the packet: item sequences as the local profile until C2-01.`
- Resolution log: nothing to add until ember selects.

### FNWF / FNRJ record fields (books/bp-workflow-records.lisp, books/bp-receipt-records.lisp, tools/workflow_journal.py, tools/receipt_journal.py)

| Record | Current field | Proposed |
| --- | --- | --- |
| FNWF `:enqueue` (11 fields) | index 7 `policy-id` text | keep, and add index 11 `policy-stmt-id` (32-octet blob, `fn-stmt-id` of the policy in force) and index 12 `policy-evidence` (32-octet blob, `fn-pol-evidence-digest`); `fn-bp-enqueue-prepare-event` takes the pair |
| FNWF `:receipt-intent` (12 fields) | receipt fields 3 to 11 | add `policy-stmt-id`, `policy-evidence` copied from the decoded receipt's term (`fn-stmt-receipt-term`) |
| FNRJ `:request-context` (5 fields) | index 4 `policy-authorized` constant `t` | replace by `policy-stmt-id` and `policy-evidence`; `fn-bprr-recordp` requires both to be `fn-digest-octetsp`; `fn-bpr-accept-request` receives the term and the record is applied only if `fn-pol-receipt-groundedp` holds against the local lace |
| FNRJ `:receipt-intent` (5 fields) | index 4 `policy-authorized` constant `t` | replace likewise; `fn-bpr-prepare-receipt` takes the term; the emitted receipt ADU carries it |
| Python `workflow_journal.py` SCHEMA, `receipt_journal.py` SCHEMA | `("policy-authorized","true")` | `("policy-stmt-id","blob32"), ("policy-evidence","blob32")` with a 32-octet length check; the constant `t` path is removed |

This is the record-level closure of review defect D9; it is a proposal for the
FNWF/FNRJ refinement wave (C1-02/C1-03), not done here.
