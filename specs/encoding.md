# Encoding and format evolution

Status: requirements with a proposed restricted deterministic CBOR profile.
D01 selects exact authored source bytes with separate mutable trace/injection
projections. The byte grammar is not frozen: settle D08/D09 and the concrete
native profile before publishing persistent or interoperable formats.

`books/cbor.lisp` currently implements uint32 and definite byte strings as
experimental primitives. `books/cbor-invariants.lisp` proves full value round
trips and exact accepted-input re-encoding for both supported types.
`books/records.lisp` composes them into the provisional schema-0 transaction
grammar described in the [storage experiment](store-experiment.md); its invariant
book proves the full variable-record round trip, and
[record canonicality](../books/records-canonicality.lisp) proves every successful
exact decode re-encodes the same octets. All 21 CBOR and 45 record functions have
verified guards; public encode/decode boundaries retain guard T. The independent
[CBOR probe](../docs/cbor-interop.md) covers 38 cases with cbor2. Native/signature
schemas remain open. The
primitive limits are local experiment bounds, not a permanent format decision.

## Layers

Keep three grammars separate: NNTP wire bytes, portable fn objects/statements,
and local storage frames. Sharing a codec primitive does not equate their
semantics. Durable records must contain enough version information for an
independent future reader to determine how to interpret them.

ENC-001: for every accepted value in a specified schema, deterministic encoding
has a single defined output and decoding that output returns the value. Canonical
validation must reject alternative encodings when identity/signature rules require
it. Round-trip correctness is not, by itself, proof of canonical uniqueness.

ENC-002: parsing is bounded in input length, nesting, allocations, and work. The
proposed profile uses definite lengths, rejects duplicate map keys, avoids floats,
and limits integer domains per field. Parsers do not use the Common Lisp reader,
intern arbitrary remote symbols, or execute data. Bound checks precede allocation.

## Content identity, and the domain separation it lacks

[`books/identity.lisp`](../books/identity.lisp) owns the two derivations the
adapter used to own:

    subject    = "sha256:"  || lowercase-hex(SHA-256(payload))
    obligation = "archive:" || lowercase-hex(SHA-256(msgid || 0x00 || subject))

ACL2 decides the labels, the hexadecimal alphabet and case, the separator
octet, the order of the preimage and every length; the host supplies the digest
octets under A-CRYPTO. The hexadecimal projection is proved invertible in both
directions and injective, so an identity collision is a digest collision and
nothing else. The charge policy `fn-charge-for-payload` is proved positive and
monotone in payload length.

**This preimage is not domain separated, and ENC-003 asks that it be.** It
carries no domain label, no schema version and no algorithm identifier, so a
future preimage of another kind could collide with it by construction rather
than by digest collision. Existing lab stores and fixtures depend on the exact
bytes above, so the derivation stands. The v1 profile to adopt, for the
substrate lane building the portable statement header:

    subject-v1    = SHA-256("fn/subject/v1" || 0x00 || uint32-be(len(payload))
                            || payload)
    obligation-v1 = SHA-256("fn/obligation/v1" || 0x00 || uint32-be(len(msgid))
                            || msgid || uint32-be(len(subject)) || subject)

with the label carried in the encoded identity rather than prefixed to a hex
string, and with the algorithm identifier part of the container so that
algorithm agility (D09) does not change the meaning of an existing identity.
Length-prefixing every variable field removes the remaining ambiguity that the
single 0x00 separator only papers over.

ENC-003: identity and signature preimages specify a domain, schema version,
algorithm identifiers, field encoding, and exact bytes. Do not hash native Lisp
printing, platform-endian memory, ambiguous concatenations, or normalized display
text. Per D01, the native source signature binds the exact authored octets;
mutable Path/Xref and gateway injection records are separate projections. The
preimage must bind its version/domain/context without normalizing that source.
Byte-string payloads preserve the news octets unchanged. The initial hash
and signature suites remain D09; algorithm agility is part of the container.

ENC-004: evolution distinguishes known-and-interpreted objects from unknown
opaque objects. An unknown schema may be carried under bounded relay policy,
but it cannot authorize an operation or establish semantic acceptance. Migration
preserves old objects and explicit provenance; it does not silently change the
meaning of an existing content ID or signed statement.

## Proposed codec deliverables

Specify accepted and rejected forms, size limits, unknown-field handling,
deterministic ordering, integer bounds, signature inputs, and error categories.
Publish golden byte vectors with independent decoding checks. Include empty
values, boundaries, duplicate keys, non-minimal encodings, truncation, oversized
length declarations, and unfamiliar schema versions.

## The durable frame grammar

Chosen and proved, replacing four Python-only grammars (FNST, FNWF, FNRJ,
FNBI). One layout serves all four:

    FRAME := MAGIC(4) VERSION(1) KIND(1) LENGTH(4, big-endian)
             PAYLOAD(LENGTH) TRAILER(32)

It is a direct octet layout rather than a CBOR item, for two structural
reasons. The frame's job is to bound the payload before anything allocates, so
building it on the CBOR decoder would make that bound depend on the parser the
frame exists to protect, and the store payload is itself a CBOR record. A
fixed-width big-endian field also has exactly one encoding of each accepted
value, so ENC-001's canonical uniqueness here is structural: `books/frame.lisp`
defines `fn-frame-encode` and `fn-frame-decode` and
[`books/frame-invariants.lisp`](../books/frame-invariants.lisp) proves
`fn-frame-decode-of-encode` for every accepted value and
`fn-frame-encode-of-decode` for every accepted octet string. ENC-002's bound is
`fn-frame-decode-refuses-oversize-before-validation`: an input longer than the
caller's cap is refused with no hypothesis about its contents at all, so no
octet was examined and nothing was allocated. Journal payloads use a field
grammar in the same book (u16-prefixed UTF-8 text, u32-prefixed blob, 64-bit
big-endian natural, one-octet 1-based enumeration) with both round-trip
directions proved over field-specification lists. UTF-8 validity is the wildmat
book's RFC 3629 decoder; there is no second table.

FNWF and FNRJ frames are byte-identical to the Python frames they replace, and
`tests/acl2/frame-tests.lisp` asserts that against vectors generated from the
Python encoders. FNST gains the record kind octet it lacked, so a store written
under the old framing is refused by its configuration format
(`fn-store-experiment-3`) rather than misread. FNBI moves its BID length into a
payload text field; because an inbound bundle can reach four mebibytes and
cannot cross the decimal-octet bridge, ACL2 builds and validates the frame head
and the host concatenates bundle bytes it never interprets.

**A-CRYPTO.** The 32-octet trailer is SHA-256 in deployment and ACL2 does not
compute it. `fn-frame-digest` is an `encapsulate` whose only constraints are
output shape (an octet list of length 32), with a local witness proving the
constraints satisfiable. No theorem in this tree claims collision or preimage
resistance for it. `fn-frame-seal` and `fn-frame-open` are the specification
functions stated against the constrained digest; `fn-frame-encode` and
`fn-frame-decode` take the digest as an argument and are what the host calls,
and `fn-frame-encode-is-seal` and `fn-frame-decode-is-open` state exactly what
the host must have computed for the two to coincide, naming `fn-frame-digest`
in their hypotheses. See the measurement in `HANDOFF.md` for why the installed
`books/kestrel/crypto/sha-2/` formal specification is not used to compute the
trailer.

The commit/checkpoint grammar must still be designed alongside the
[storage failure model](failures.md).

See [RFC 8949 §4.2](https://www.rfc-editor.org/rfc/rfc8949.html#section-4.2) for
deterministic CBOR requirements. COSE is a candidate for signatures, not an
already selected profile.
