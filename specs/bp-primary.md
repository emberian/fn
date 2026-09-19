# The BPv7 primary bundle block

Status: executable model, codec and certified properties. This is not a bundle
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
