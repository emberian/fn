# Experimental BP application ADU codec

Status: integrated laboratory codec profile. This is not selection of the D01 native
article schema, the D09 signature grammar, a BP security-block profile, or a
replacement for the existing raw legacy-article ingress experiment.

`books/bp-adu.lisp` defines a bounded deterministic wrapper in the `fn-bpa-*`
namespace. It uses only the restricted canonical CBOR unsigned-integer and
definite byte-string primitives. The stream begins with byte-string magic
`FN-BP-ADU`, unsigned version `0`, unsigned kind, and unsigned field count `9`.
Kind `0` is a request and kind `1` is an application receipt.

Request fields are ordered as follows:

1. work identity
2. immutable content subject
3. source EID
4. destination EID
5. policy identity
6. origin incarnation
7. authorization context
8. terms identity
9. exact legacy article octets

The first eight are nonempty octet-domain strings of at most 256 octets. The
article is an opaque octet list of at most 32,768 octets. Encoding and decoding
preserve it exactly. The current receiver composition unwraps it with this codec
and pass only those exact octets to the existing article parser and Store
acceptance path. Envelope source, subject, policy and terms are context inputs;
they do not override article fields or authorize local acceptance.

A work identity is scoped by source EID, origin incarnation, policy and terms.
The request `origin incarnation` names the source/requesting node incarnation
that issued the work identity; it is not a Store generation or a receiver
incarnation. It is not globally authoritative alone. Message-ID remains inside
the exact article. This profile does not add a second Message-ID field whose
consistency would otherwise require a separate ingress proof.

Receipt fields exactly match the current nine-field workflow receipt order:
receipt identity, work identity, subject, issuer EID, peer EID, policy identity,
incarnation, authorization context and terms identity. The receipt incarnation
is the copied source/request incarnation binding for that work, not an issuer
clock or local transaction generation. The current outbound composition requires the
workflow checks that issuer equals the configured receipt authority and peer EID
equals the work/config peer. Authorization context is carried evidence for that
check; peer-supplied bytes never substitute for the receiver or sender host's
configured A-POLICY decision. Decoding a receipt establishes none of those
conditions.

The decoder preflights the complete input bound, accepts only octets and
canonical CBOR items, requires the fixed magic/version/kind/count and exact end
of input, validates every decoded field, and re-encodes the result to require an
exact canonical preimage. `fn-bpa-round-trip` proves decoding every typed
encoding returns the original value. `fn-bpa-success-is-canonical` proves every
successful decode re-encodes to the exact input.

Local Store transaction IDs and generations, local NNTP article numbers, BPA
bundle IDs, attempts and transport status are absent. The codec performs no
signature verification, authorization decision, article syntax validation,
durability operation, receipt-intent commit, freshness check or replay decision.
The exact byte profile is experimental and may be replaced when D01/D09 and the
portable receipt authority contract are selected.

The [guard closure](../tests/evidence/2026-09-18-bp-guards.md) verifies all 41
functions in this codec, including public guard-`T` decoding. Internal streaming
callees retain their explicit natural-number/octet-list guards. Existing logical
bodies are unchanged. This is separate from resource-cost, authority and host
refinement obligations; the full BP host graph still has unverified guards.
