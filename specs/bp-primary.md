# The BPv7 primary bundle block

Status: executable model and codec, certified by ACL2: `books/bp-primary-cbor`,
`books/bp-primary` and `books/bp-primary-invariants` certify, and every theorem
named here is a proved one unless "What remains open" below says otherwise.
This is not a bundle
protocol agent, a forwarder, a BPSec implementation, or a claim of
interoperability with any deployed BPv7 node.

[The independent review](../planning/review-2026-09-18-independent.md) records
as structural naivety 4 that "BP is three verbs on one BPA ... no primary block,
no creation-timestamp-plus-sequence identity, no fragmentation, no lifetime
semantics, no BPSec, and the BID is a dtn7-rs table key. A relay cannot be built
on that identity." This specification is the primary block half of closing that.

## What is modeled

`books/bp-primary-cbor.lisp` extends fn's deterministic CBOR profile
(`books/cbor.lisp`, unchanged) with exactly the vocabulary RFC 9171 §4.3.1
needs: definite-length arrays of bounded arity (major type 4), definite-length
text strings (major type 3), and unsigned integers to 2^64-1 — the original
profile stops at 2^32-1 and answers `:unsupported` for CBOR additional
information 27, which RFC 9171 §4.2.6 warns that DTN times "will nearly always"
require. Byte strings come from the existing book. Negative integers, maps,
tags, floats, simple values, the break stop code and every indefinite-length
form stay outside, and are refused before any argument is read.

`books/bp-primary.lisp` models the block itself.

| Field | RFC 9171 | Model |
| --- | --- | --- |
| Version | §4.3.1 | fixed at 7; not a record field, because a stored version could only ever disagree with the codec |
| Bundle processing control flags | §4.2.3 | a bounded bit set: the whole 64-bit unsigned value, with named accessors for the eight assigned flags. Unrecognised bits are kept, because §4.2.3 says they MUST be ignored, not rejected |
| CRC type | §4.2.1 | 0, 1 or 2 and no others; §4.2.1 says "and no others" |
| CRC | §4.2.2, §4.3.1 | X-25 CRC-16 and CRC32C implemented in ACL2, over the block's own encoding with the CRC field present and zero-filled, emitted as a two- or four-octet byte string in network byte order |
| Destination EID, source node ID, report-to EID | §4.2.5.1 | `dtn` (§4.2.5.1.1) including `dtn:none`, and `ipn` (§4.2.5.1.2) node and service numbers, as bounded structured values |
| Creation timestamp | §4.2.7 | DTN time in milliseconds since 2000-01-01T00:00:00Z (§4.2.6) plus the source BPA's sequence number, both unsigned to 2^64-1 |
| Lifetime | §4.3.1 | milliseconds past the creation time. The expiry decision itself is [specs/time.md](time.md) |
| Fragment offset, total ADU length | §4.3.1, §5.8 | present exactly when the fragment flag is set; absent otherwise, and the codec checks the block's arity against the flag and CRC type |
| Previous Node, Bundle Age, Hop Count | §4.4.1, §4.4.2, §4.4.3 | the block-type-specific data of each, as bounded values with both codec directions. The canonical block frame of §4.3.2 is not modeled |

The packet that commissioned this work cited "§4.2.8" for lifetime and "§4.2.9"
for the fragment fields. RFC 9171 has no such sections: §4.2.8 is
Block-Type-Specific Data, and both lifetime and the fragment fields are
specified in §4.3.1 as fields of the primary block. The sections above are the
RFC's own.

### Both directions, and canonicality

Underneath the two `fn-bpp-` theorems, the CBOR round trip for encoder output
(`fn-bpc-decode-of-encode`, `fn-bpc-value-round-trip`), the fact that a
successful decode yields a value in the domain (`fn-bpc-dec-yields-shape`), and
canonicality over *arbitrary* accepted input (`fn-bpc-accepted-input-is-canonical`,
through `fn-bpc-argument-of-decode-head`) are all certified. The base-256
inverse the last of these needed, `fn-bpc-u64-bytes-reassemble`, is proved once
over the two 32-bit halves of the 27-form argument and is the only place
`floor` and `mod` enter the decoder theory.

`fn-bpp-decode-of-encode` proves every valid block decodes back from its own
encoding, CRC included. `fn-bpp-accepted-input-is-canonical-by-construction`
proves every accepted octet sequence re-encodes to exactly itself, so there is
no second spelling of any accepted block. Underneath,
`fn-bpc-accepted-input-is-canonical` proves the same for arbitrary accepted CBOR
input — not only for encoder output — which is what makes a non-minimal
argument or an indefinite-length head unable to pass.

Four refusals stay distinct: a CBOR-level reason (`:noncanonical`, `:limit`,
`:truncated`, `:trailing`, `:unsupported`), a structurally wrong block
(`:malformed`), a block whose attached CRC is not the one §4.2.2 prescribes
(`:crc-mismatch`), and a block whose CBOR spelling is not deterministic
(`:noncanonical`).

Bounds precede allocation at every level: the whole input is length-preflighted
before an octet is examined, an array's arity is checked before an element is
decoded, and a string's claimed length is checked before `take` copies
anything. The item budget is simultaneously the decoder's termination measure
and its work bound.

### Conformance versus decodability

`fn-bpp-blockp` accepts exactly what the wire format allows.
`fn-bpp-flags-conformantp` is a separate predicate carrying the two MUSTs of
§4.2.3 — an administrative record must request no status reports, and a bundle
with an anonymous source must set "must not be fragmented" and request no
status reports. Keeping them apart means a peer that violates a MUST produces a
decodable block and a policy decision, rather than a parse failure that cannot
be distinguished from corruption.

## Bundle identity, and how fn's BID maps onto it

RFC 9171 §4.3.1 (under Creation Timestamp) says the creation timestamp,
"together with the source node ID and (if the bundle is a fragment) the fragment
offset and payload length, serve to identify the bundle". §5.9 groups fragments
for reassembly by source node ID and creation timestamp alone.

The model keeps those two notions apart, because they are not the same thing:

- `fn-bpp-adu-key` is `(source node ID, creation time, sequence number)`. It is
  the §5.9 reassembly key and it is entirely determined by the primary block.
- `fn-bpp-bundle-id` adds the fragment offset and **this bundle's payload
  length**. The payload length lives in the payload block, not the primary
  block, so `fn-bpp-bundle-id` takes it as an argument. **The primary block
  alone does not determine a fragment's bundle identity.** Two fragments of one
  ADU at the same offset with different payload lengths have identical primary
  block fields other than the CRC and are different bundles.

`fn-bpp-encode-is-injective` gives the "determined by the canonical encoding"
result for everything the primary block does carry: two valid blocks with the
same encoding are the same block, hence have the same ADU key and the same
bundle identity for any payload length.
`fn-bpp-adu-key-ignores-destination-lifetime-and-crc-type` and
`fn-bpp-adu-key-separates-source-and-timestamp` pin down that the key is exactly
the §4.2.7 projection and nothing more.

A source node ID of `dtn:none` makes a bundle not uniquely identifiable at all
(§4.2.3); `fn-bpp-identifiablep` says so, and
`fn-bpf-anonymous-conformant-bundle-is-not-fragmentable` shows the consequence.

### fn's current BID

fn's BP adapter (`tools/bpa_dtn7.py`) carries a **BID**: a bounded visible-ASCII
string of at most 512 octets, obtained from the pinned dtn7-rs agent's
`/status/bundles` inventory and used as the raw query argument of `/download?`
and `/delete?`. Nothing in fn parses it. It is a key into one agent's table.

| Bundle identity needs | fn's BID supplies |
| --- | --- |
| source node ID as a structured EID in a known scheme | nothing; the BID is opaque text |
| creation time and sequence number as separate unsigned integers | nothing |
| fragment offset and payload length when the bundle is a fragment | nothing |
| stability across agents | none: the BID is meaningful only to the agent instance that issued it |
| stability across that agent's restart | not established by any fn test; inventory is re-read after restart and the BID is re-used as found |

The consequences, in order of severity:

1. **A relay cannot be built on it.** Forwarding a bundle received from agent A
   through agent B requires constructing a primary block for B, which requires
   the source node ID and creation timestamp as values. They are not available.
2. **Duplicate suppression is not bundle-level.** fn recognises duplicates by
   the application work-id inside the ADU (`specs/bp-adu.md`), which is why
   defect D10 of the review is a work-id squatting denial of service. Bundle
   identity would give a second, protocol-level key that a peer cannot choose
   freely, because §4.2.7's sequence counter belongs to the source BPA.
3. **Reassembly is impossible.** Without the ADU key, fragments cannot be
   grouped; `books/bp-fragment.lisp` has no input.
4. **Expiry is impossible.** Without the creation timestamp and lifetime,
   `fn-clock-expiry-decision` has no arguments; see [specs/time.md](time.md).

What a relay needs that fn does not yet carry, concretely: the decoded primary
block of every staged inbound bundle, persisted alongside the ADU; the payload
block's length; and, for anything beyond a two-node laboratory, the Previous
Node and Hop Count extension blocks so that a forwarding loop terminates.

## Where implementations differ

Only what could be determined offline is recorded. No network access beyond
fetching RFC 9171, RFC 9172 and RFC 9173 was taken for this lane.

**dtn7-rs 0.21.0** (pinned at revision `4daf02d7ea927e9293753b2a5c4497457f6e5a40`
in `tests/bp-dtn7/pin.json`) uses crate `bp7` 0.10.7 for its BP codec.

- *dtn scheme-specific part.* `bp7` 0.10.7's `eid.rs` stores and encodes the
  complete SSP including its leading `//` — its own decoding test reads
  `82 01 6c "//node1/test"` back as `dtn://node1/test`, and its parser
  normalises the bare name `node1` to the SSP `//node1/`. That agrees with RFC
  9171 §4.2.5.1.1. The same crate's shipped `doc/encoding_samples.md` publishes
  primary blocks whose dtn SSPs omit the `//` (`82 01 68 "n2/inbox"`). The
  documentation is stale relative to the code it ships with. fn implements the
  RFC form, and `tests/acl2/bp-primary-tests.lisp` records that the documented
  sample block is refused for that reason while its CRC is still checked
  exactly.
- *CRC type codes.* `bp7`'s `CrcValue` has an `Unknown(u8)` variant and carries
  unrecognised CRC type codes through. RFC 9171 §4.2.1 lists 0, 1 and 2 "and no
  others" as valid. fn refuses anything else.
- *Bundle framing.* `bp7` serialises the bundle as an indefinite-length CBOR
  array, which is what RFC 9171 §4.1 specifies for the bundle; it is not a
  primary block property and this lane does not model the bundle frame.

**ION** could not be examined. No ION source or documentation is present on
this machine and no fetch was permitted, so this lane makes no statement about
ION's behaviour beyond what RFC 9171 itself records: Appendix A lists the
significant changes from RFC 5050, and §4.2.5.1.1 warns explicitly that the
dtn-scheme syntactic rules "impose constraints on dtn-scheme endpoint IDs that
were not imposed by the original specification" and that developers of
RFC 5050-era applications "are advised of the potential for compromised
interoperation". Claiming an ION difference without a vector from ION would be
exactly the interoperability claim the assurance rules forbid.

## What remains open

- **Four theorems are stated in their books but commented out as open**, each
  with the reason at its site: `fn-bpp-previous-node-round-trip` and
  `fn-bpp-hop-count-round-trip` in `books/bp-primary-invariants.lisp` (the
  Previous Node and Hop Count data therefore have both codec directions
  executable but only the Bundle Age round trip proved), and
  `fn-bpf-cut-covers` and `fn-bpf-reassemble-ok-agrees-with-every-fragment` in
  `books/bp-fragment-invariants.lisp` (a cut's fragments are proved to agree
  with the payload and to share its total, not yet to cover it; a successful
  reassembly is proved to reconstruct a complete agreeing cover, not yet to
  agree with each fragment it consumed). Nothing else in this document cites
  them.
- **Two theorem hypotheses are kept for their guards, not for their truth.**
  `fn-bpp-adu-key-ignores-destination-lifetime-and-crc-type-by-definition` and
  `fn-bpf-fragment-block-preserves-adu-key` both hold without `fn-bpp-blockp`;
  neither has a tooth, and each test book proves the unconditional fact
  instead. The section below records this.
- **No host calls any of this.** The theorem subject rule applies: these are
  theorems about functions with no caller. `tools/bpa_dtn7.py` still treats
  bundles as opaque and `tools/bpa_payload_extract.rs` still uses the pinned
  upstream decoder. Wiring is the next packet, and until it lands no BPv7
  conformance or interoperability claim may cite a host line.
- **BPSec (RFC 9172) and its default security contexts (RFC 9173)** are not
  modeled. This matters for one specific allowance: RFC 9171 §4.3.1 permits the
  primary block's CRC type to be zero only when the bundle carries a Block
  Integrity Block targeting the primary block. fn's model represents CRC type
  zero but has no way to check that precondition, so a zero-CRC primary block
  must be treated as unprotected by policy above this layer.
- **The canonical block format (§4.3.2) and the payload block** are not modeled,
  which is why bundle identity needs the payload length passed in.
- **Custody** is not in BPv7 at all and must not be imported by assumption from
  RFC 5050; RFC 9171 Appendix A is the reference. Nothing here provides it.
- **Status reports (§6.1)** are not generated or parsed. The status-report
  request flags are modeled as flags only. As [specs/bp-path.md](bp-path.md)
  and REP-006 both state, a status report is not an fn obligation receipt.
- **Block processing control flags (§4.2.4)** are documented in the model's
  comments but not implemented, because they belong to the canonical block
  format.
- **Lifetime overrides** (§4.3.1) are not modeled.
- **Guard verification** is complete for every function in these books, but no
  resource-cost bound is proved for CRC computation; the CRC is linear in the
  encoded block length, which is itself bounded by the codec's input preflight.

## Teeth bitten by instance, and hypotheses that are unnecessary

Twelve teeth in the two test books asked the prover to refute a general
statement and did not finish: some ran past a 1800 s budget, and some aborted
with a hard rewriter call-depth error, which is not a fast refutation either.
In each the negated goal opens the very recursion the hypothesis was there to
escape. Each is now bitten by a concrete
counterexample instead -- an `assert-event` that evaluates the theorem body on
one witness violating the dropped hypothesis and checks the body is false. No
theorem was weakened; the witness is a strictly sharper refutation than
`must-fail`, which only reports that ACL2 did not find a proof. Where the
witness is outside a callee's guard the body is evaluated under
`with-guard-checking :none`, which is the point of the witness.

In `tests/acl2/bp-primary-tests`:

- `fn-bpc-decode-of-encode`, item-budget hypothesis dropped: flg `:item`,
  x `(:uint . 1)`, rest `nil`, budget `0`. The decoder answers
  `(:error :budget)`.
- `fn-bpp-decode-of-encode`, `fn-bpp-blockp` dropped: b `0`, evaluated
  logically because `0` is outside `fn-bpp-encode`'s guard.
- `fn-bpp-value-block-of-block-value`, `fn-bpp-blockp` dropped: b `0`,
  crc-octets `nil`. `fn-bpp-crc-width` of a non-type is 0, so both surviving
  hypotheses hold, and the reader answers `nil` rather than `0`.
- `fn-bpp-accepted-input-is-canonical-by-construction`, success hypothesis
  dropped: octets `(1)`, which the decoder refuses as `:malformed`.
  Re-encoding the block that refusal does not carry gives the all-default
  block's octets, not `(1)`.
- `fn-bpp-previous-node-round-trip`, `fn-bpp-previous-nodep` dropped: the dtn
  endpoint `//n2/inbox`, whose demux is non-empty, so it is not a node ID.
  The round trip answers `nil`.
- `fn-bpp-hop-count-round-trip`, `fn-bpp-hop-countp` dropped: the hop count
  with limit `0`, which is out of the 1..255 range. The round trip answers
  `nil`.

In `tests/acl2/bp-fragment-tests`:

- `fn-bpf-complete-agreeing-cover-reassembles-to-payload`, `fn-bpf-covers-all`
  dropped: payload `*bpf-payload*`, fs `*bpf-gap*`, whose two fragments agree
  and are in bounds but leave indices 3 and 4 uncovered. The reassembly is
  `(:missing 3 5)`.
- `fn-bpf-complete-agreeing-cover-reassembles-to-payload`,
  `fn-cbor-octet-listp` on the payload dropped: payload `(10 20 30 . 7)`, an
  improper list of length 3 whose elements are octets, and one fragment
  carrying `(10 20 30)` at offset 0 of total 3. It is in bounds, agrees and
  covers, yet the reassembly is `(:ok (10 20 30))`, which drops the final
  cdr.
- `fn-bpf-reassemble-ok-agrees-with-every-fragment`, `member-equal` dropped:
  fs `*bpf-cut*`, total `8`, k `0`, and a fragment outside the list.
- `fn-bpf-reassemble-ok-agrees-with-every-fragment`, `:ok` dropped: fs
  `*bpf-gap*`, total `8`, f its first fragment, k `0`. The reassembly is
  `(:missing 3 5)`, whose bytes position is the index `3`, and the nth of an
  index is `nil`, not the fragment's byte `10`.
- `fn-bpf-disagreeing-fragments-yield-conflict`, disagreement dropped: fs
  `*bpf-overlap*`, total `8`, its two fragments, i `4`. Both carry a real byte
  at index 4, and the byte-identical overlap reassembles `:ok`.
- `fn-bpf-disagreeing-fragments-yield-conflict`, `member-equal` for g dropped:
  fs `*bpf-cut*`, total `8`, i `0`, and g a fragment carrying `99` at offset 0
  that is not in the list. `*bpf-cut*` still reassembles `:ok`.
- `fn-bpf-missing-low-index-is-uncovered`, `:missing` dropped: fs
  `*bpf-conflict*`, total `8`. The result is `(:conflict 4)`, whose second
  position is the conflicting index `4`, and index 4 is covered by both
  fragments.

### Two hypotheses that are unnecessary for the conclusion

Two teeth have no witness, and are recorded as hypothesis-unnecessary rather
than claimed:

- `fn-bpp-adu-key-ignores-destination-lifetime-and-crc-type-by-definition`
  without `fn-bpp-blockp`.
- `fn-bpf-fragment-block-preserves-adu-key` without `fn-bpp-blockp`.

`fn-bpp-adu-key` reads positions 4, 6 and 7 of the record -- source, creation
time and sequence -- and `fn-bpp-with-destination`, `fn-bpp-with-lifetime`,
`fn-bpp-with-crc-type` and `fn-bpf-fragment-block` each rebuild the record
through `fn-bpp-make-block`, which is a `list`, copying exactly those three
positions. The conclusion therefore holds for every object, block or not. Each
test book proves that fact locally, so the claim is checked and not merely
asserted, and both theorems keep `fn-bpp-blockp` for their guards rather than
for their truth.
