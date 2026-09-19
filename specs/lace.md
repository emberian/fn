# Laces: statement sets, merge, canonicity, equivocation, closure

Status: local engineering profile from the substrate lane; certified books.

Books: `books/lace.lisp`, `books/lace-invariants.lisp`; tests
`tests/acl2/lace-tests.lisp`.

## Shape

A lace is a list of statements ([statement](statement.md)); its observable is
the set of content ids `fn-lace-ids`. `fn-lace-lookup lace id` is the first
statement with that id. This is the replica's `HashMap<BlockId, Block>` of
`~/dev/breadstuffs/blocklace/src/lib.rs` and `Lace := List Block` with
`Lace.lookup` at `~/dev/breadstuffs/metatheory/Dregg2/Authority/Blocklace.lean`
lines 66 to 70.

`fn-lace-merge lace delta` appends to `lace` every statement of `delta` whose
id is not already present: `mergeLace` and `newBlocks` of
`Dregg2/Distributed/LaceMerge.lean` (the `contains_key` continue at
`finality.rs:690`) and `merge` and `newEvents` of
`~/dev/minidregg/Theory/LaceMerge.lean` section 2.

`fn-lace-canonicalp` is `Lace.Canonical` (Blocklace.lean line 80) and
`fn-lace-cross-canonicalp` is `CrossCanonical` (LaceMerge.lean line 247;
minidregg section 3); canonicity is defined as the diagonal of
cross-canonicity, so `crossCanonical_self` holds by definition.

## Theorems

Each row mirrors the named Lean theorem.

| Theorem | Mirrors | Property | Hypotheses |
| --- | --- | --- | --- |
| `fn-lace-merge-ids-are-union` | `laceIds_mergeLace`, `ids_merge` | an id is in the merged lace iff it is in either input | none |
| `fn-lace-merge-idempotent` | `merge_idem` | `(fn-lace-merge lace lace)` equals `lace` | lace is a true list (stronger than the id-set form) |
| `fn-lace-merge-commutative-ids`, `fn-lace-merge-associative-ids` | `merge_comm`, `merge_assoc` | the two merge orders and the two groupings have the same id set | none |
| `fn-lace-merge-monotone`, `fn-lace-merge-absorbs-delta`, `fn-lace-merge-lub` | `merge_monotone`, `merge_lub` | inflationary in both arguments and the least id-set upper bound | none |
| `fn-lace-lookup-of-member` | `lookup_of_mem` | in a canonical lace a member resolves to itself | canonical, member |
| `fn-lace-cross-canonical-self`, `fn-lace-canonical-append-iff` | `crossCanonical_self`, `canonical_append_iff` | canonicity of an append is canonicity of both parts and cross-canonicity | none |
| `fn-lace-same-view-of-cross-canonical` | `sameView_of_canonical_eq_ids` | equal id sets and cross-canonicity give equal lookup at every id | same ids, cross-canonical; the two per-lace canonicity premises of the Lean statement are not needed because ACL2's lookup returns the first match |
| `fn-lace-merge-preserves-canonical` | (LaceMerge scope note) | merge of canonical laces is canonical | both canonical; no cross premise, because the skip guard removes the delta's colliding statements |
| `fn-lace-merge-drops-at-collision` | `merge_drops_at_collision` | a delta statement whose id is held by a different statement is discarded | member of the lace with that id, delta statement not in the lace |
| `fn-lace-distinct-same-slot-is-equivocation` | `EquivocationProof` (lib.rs) | two distinct members at one (creator, incarnation, sequence) make the creator an equivocator | both members, distinct, same slot |
| `fn-lace-reissue-is-equivocation` | `Equivocator` (Blocklace.lean line 152), restore/fork of D10 | a key that reissues an (incarnation, sequence) with a different payload is an equivocator in any lace holding both statements, whatever the signatures, predecessors or kinds | payloads differ, both members |
| `fn-lace-reissue-detected-after-merge` | | the merge of the two forks shows the equivocation | payloads differ and the two content ids differ (A-CRYPTO edge) |
| `fn-lace-merge-preserves-equivocation` | | equivocation evidence survives merge | none |
| `fn-lace-merge-preserves-closure` | `insert` causal closure (lib.rs "Key Invariants" 2) | merge of causally closed laces is causally closed | both closed |

The cross-canonical gap is exhibited, not proved away: `lace-tests` attaches
the length digest and rebuilds `crossCanonical_is_the_gap` (two canonical
laces, equal id sets, no cross-canonicity, different lookups), the failure of
`canonical_append_iff`'s cross term, `merge_drops_at_collision`, and shows the
restore/fork becoming invisible after a merge under collision; `must-fail`
records that same-view without cross-canonicity is not a theorem. Under the
mixing digest the same tests show `merge_computes` and the fork detected.

Teeth for equivocation: a single statement, an identical reissue, another
incarnation, another principal and another sequence are each not an
equivocation.

## Assumed

A-CRYPTO: distinct statements have distinct content ids, so a lace can hold
both forks and a merge does not drop one; the lace's members are well-formed
statements (`fn-lace-p`); nothing here verifies signatures (that is
[policy](policy.md) through the keyring).
