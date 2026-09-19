# Statements: the block-shaped signed unit

Status: local engineering profile from the substrate lane. Certified codec
and signing books; the encoding profile (D08) is a proposal and not frozen.

Books: `books/statement.lisp`, `books/statement-invariants.lisp`; tests
`tests/acl2/statement-tests.lisp`.

## Shape

A statement header is `(creator incarnation sequence preds kind ref)` and a
statement is `(header payload signature)`. This is the `Block` of
`~/dev/breadstuffs/blocklace/src/lib.rs` (`pub struct Block { creator,
sequence, predecessors, payload, signature, pq_signature }`) and
`~/dev/breadstuffs/metatheory/Dregg2/Authority/Blocklace.lean` line 58
(`structure Block`), with two fn changes: an explicit origin `incarnation`
(D10) and a `kind` in `:article`, `:policy`, `:receipt`, `:succession`. The
creator is a 32-octet principal id ([identity](identity.md)); predecessors are
at most 16 distinct content ids; `ref` is `fn-digest-tagged "fn-payload-v1"
payload` and binds the payload to the signed header, as `Block::id` covers the
payload in lib.rs.

## Bytes

Every structure is a sequence of items of the bounded CBOR profile of
`books/cbor.lisp` (uint32 and definite byte strings), concatenated. One
generic item-sequence codec, `fn-stmt-encode-items` and
`fn-stmt-decode-items fuel octets`, turns bytes into items under an explicit
item budget; each structure is a projection to and from an item list. Bounds
are checked before any item is parsed: the input cap (`fn-cbor-at-mostp`), then
the item budget, then each item by the primitive decoder. Layout:

```text
uint 1  bstr creator  uint incarnation  uint sequence
uint n  bstr pred[0] ... bstr pred[n-1]  uint kind  bstr ref
bstr payload  bstr signature                    ; whole statement only
```

Kind codes: article 1, policy 2, receipt 3, succession 4. Header at most 1024
octets and 24 items; whole statement at most 16384 octets and 26 items;
payload at most 8192 octets. These are local bounds, not a format decision.

## Identity and signing

```text
content id       = fn-digest-tagged "fn-statement-v1"     (header bytes)
signing preimage = "fn-statement-sig-v1" tag || content id
signature        = fn-sig-sign seed (signing preimage)
```

This is `Block::sign_by` in lib.rs: the signature covers the id, the id covers
creator, sequence, predecessors and payload. `fn-stmt-verifiedp s pk` holds
when `s` is well formed and `fn-sig-verify pk (signing preimage) signature`.

## Theorems

| Theorem | Property | Hypotheses | Scope |
| --- | --- | --- | --- |
| `fn-stmt-decode-items-of-encode-items` | the item codec round-trips | items well formed, fuel at least their count, bytes within the CBOR cap | generic sequence codec |
| `fn-stmt-encode-items-of-decode-items` | every accepted byte string re-encodes to itself | none beyond acceptance | canonicality of the sequence codec for all inputs |
| `fn-stmt-header-round-trip`, `fn-stmt-header-accepted-input-is-canonical` | header codec, both directions | header well formed; accepted input | headers |
| `fn-stmt-round-trip`, `fn-stmt-accepted-input-is-canonical` | whole statement codec, both directions | statement well formed; accepted input | statements |
| `fn-stmt-header-encode-injective` | equal header bytes, equal headers | both well formed | the step below the digest; content-id collisions are A-CRYPTO |
| `fn-stmt-sign-is-verified` | a statement signed with seed `sk` verifies under `(fn-sig-public-key sk)` | seed is 32 octets, fields well shaped | the only use of the seam's correctness constraint |
| `fn-stmt-receipt-round-trip`, `fn-stmt-receipt-accepted-input-is-canonical`, `fn-stmt-receipt-bytes-determine-term` | receipt payload codec, and equal receipt bytes carry equal policy terms | receipt well formed | receipts; see [policy](policy.md) |
| `fn-stmt-content-id-unfolds` | the content id is the tagged digest of the canonical header bytes | none | definitional; named so |

Teeth (`statement-tests`): a golden header byte vector independent of any
digest; decoder rejections for a non-minimal head, an unknown version, a
trailing octet, 17 predecessors, a duplicate predecessor, an unknown kind, a
short creator, an oversize input and truncation; a tampered payload is not a
statement (ref mismatch), a tampered signature and another key do not verify;
a decoded statement still verifies; a receipt with a bad field is rejected.

## Receipts

Kind `:receipt` carries the payload `(subject obligation policy-id evidence)`:
the admitted statement's content id, the obligation identity, and the policy
term `(policy-id . evidence)` of [policy](policy.md). There is no decision
field. This is the shape the FNWF and FNRJ journals are proposed to adopt
(HANDOFF proposal for `bp-workflow-records` and `bp-receipt-records`).

## Assumed

A-CRYPTO for content-id uniqueness and signature unforgeability; the CBOR
primitive profile's own proofs (`books/cbor-invariants.lisp`); no relation to
the article source bytes yet (an `:article` payload is opaque octets here; the
D01 exact-source binding is C2-01).
