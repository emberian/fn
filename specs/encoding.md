# Encoding and format evolution

Status: requirements with a proposed restricted deterministic CBOR profile.
The byte grammar is not frozen. Resolve D01, D08, and D09 before publishing
persistent or interoperable formats.

`books/cbor.lisp` currently implements uint32 and definite byte strings as
experimental primitives. `books/cbor-invariants.lisp` proves the full uint32
round trip; byte-string round-trip proof and native schemas remain open. The
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

ENC-003: identity and signature preimages specify a domain, schema version,
algorithm identifiers, field encoding, and exact bytes. Do not hash native Lisp
printing, platform-endian memory, ambiguous concatenations, or normalized display
text. Byte-string payloads preserve the news octets unchanged. The initial hash
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

The initial frame fields to evaluate are magic, version, record kind, bounded
length, payload, and integrity trailer. This is a field inventory, not a chosen
binary layout. The commit/checkpoint grammar must be designed alongside the
[storage failure model](failures.md).

See [RFC 8949 §4.2](https://www.rfc-editor.org/rfc/rfc8949.html#section-4.2) for
deterministic CBOR requirements. COSE is a candidate for signatures, not an
already selected profile.
