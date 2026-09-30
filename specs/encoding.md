# Encoding and format evolution

Status: requirements with a proposed restricted deterministic CBOR profile.
D01 selects exact authored source bytes with separate mutable trace/injection
projections. The byte grammar is not frozen: settle D08/D09 and the concrete
native profile before publishing persistent or interoperable formats.

`books/cbor.lisp` currently implements uint32 and definite byte strings as
experimental primitives. `books/cbor-invariants.lisp` proves full value round
trips and exact accepted-input re-encoding for both supported types.
`books/records.lisp` composes them into the transaction-record grammar
(schema 3 when all integer fields fit u32, schema 4 when one requires u64)
described in the [storage experiment](store-experiment.md). The invariant and
[canonicality](../books/records-canonicality.lisp) books state the full
variable-record round-trip and accepted-input re-encoding obligations.
Changing the record grammar requires matching certification; source, proof,
image and deployment coordinates remain separate in
[the current view](../planning/current.md).

The record codec is behind a seam (plan 2026-09-22 §4.1, step T1).
`books/records.lisp` defines `fn-record-encode-impl` and
`fn-record-decode-exact-impl`; `books/records-seam.lisp` constrains the public
`fn-record-encode` and `fn-record-decode-exact` by domain, round-trip,
canonicality, input-bound, magic, schema and encoding-length properties.
The accepted sixth octet must equal `fn-record-schema-octet` of the decoded
record: 3 for narrow integer fields and 4 for a wide field. The local witnesses
are the implementation; `books/records-attach.lisp` attaches that implementation
with `defattach`, which discharges the constraints rather than adding an axiom.

Every record has twelve logical fields. The acceptance stamp remains an
unsigned integer giving whole seconds since the DTN epoch; the final field is
the immutable first-acceptance binding. It is separate from the stored payload's
content subject and release evidence. The binding's byte string is exactly
56 octets: NUL followed by ASCII `FN-AB1` (seven octets together), one profile
octet, and the 48-octet typed subject of the received bytes. Profile codes are
1 (`:post-d25`), 2 (`:relay-v1`) and 3 (`:native-source`). The subject begins
with ASCII `fn/subject/v1`, NUL, version 1 and algorithm 2, followed by the
32-octet digest. `fn-ab-decode` rejects another length, magic, profile or typed
subject header. A valid descriptor is not itself authorization.

The record appends that binding as a canonical CBOR byte string after the
stamp: the two-octet head `58 38` and 56 data octets add 58 octets to the record.
Missing or malformed binding bytes are refused `:invalid-binding`; an extra
item after the binding is refused `:trailing`. Schemas 0, 1 and 2 are retired
and refused `:unknown-version`; no binding is inferred for an old record.
Fresh deployment remains the selected format-transition policy.

The exact schema-3 and schema-4 golden encodings are literal vectors in
`books/records.lisp`, with corresponding encode and decode events including
`fn-record-schema3-golden-octets-are-the-encoding` and its schema-4 counterpart.
Round-trip and canonicality alone do not identify those bytes: both properties
also hold under a length-preserving permutation of the encodings. Books above
the codec and the host call the constrained names; image and ground-vector
test books include the attachment. The independent CBOR probe covers narrow
and wide records, all three binding profiles, retired schemas, inconsistent
width markers, and invalid binding fields. Its current-source run is a
separate obligation from historical probe results.
The record itself -- domains, accessors, `fn-record-p`, result shapes -- is
`books/records-shape.lisp` and is not a codec. The independent
[CBOR probe](../docs/cbor-interop.md) records its historical runs separately
from the current grammar checks. Native/signature schemas remain open. The
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

## Content identity: the v1 profile, adopted

[`books/identity.lisp`](../books/identity.lisp) owns the two derivations, and
they are the domain-separated v1 profile:

    subject-v1    = BLAKE3("fn/subject/v1" || 0x00 || uint32-be(len(payload))
                            || payload)
    obligation-v1 = BLAKE3("fn/obligation/v1" || 0x00 || uint32-be(len(msgid))
                            || msgid || uint32-be(len(subject)) || subject)

An identity is the triple (label octets, algorithm id, digest octets),
rendered canonically as

    identity = label || 0x00 || version-octet || algorithm-octet || digest

with version 1 and algorithm 2 (BLAKE3, 32-octet output; store format 10
and later). Algorithm 1 (SHA-256) was written by formats up to 9 and is not
read: a format-10 store holds none (D34, fresh deploys, no migrations). The kind is carried *inside* the
encoded identity rather than as a hex prefix, and the algorithm identifier
travels in the container, so algorithm agility (D09) changes the algorithm
octet and does not change the meaning of an identity already written. A
subject identity is 48 octets and an obligation identity 51.

The canonical identity is octets. `fn-id-text` renders it as lowercase
hexadecimal, whole and label included, and the host uses that rendering at
exactly the three boundaries where a string is unavoidable: the store record's
metadata fields, the workflow journal's JSON records and the NNTP header
value. Nothing else renders an identity. The projection is proved invertible
in both directions and injective, so a string comparison at one of those
boundaries is an octet comparison and an identity collision is a digest
collision and nothing else.

ACL2 decides the labels, the version and algorithm octets, the hexadecimal
alphabet and case, the separator octet, every length prefix and the order of
each preimage; the host supplies the digest octets under A-CRYPTO. For a
subject the host is given only the fixed preimage head
(`fn-id-subject-prefix`) and appends the payload itself, so a 32 KiB article
never crosses the bridge. The charge policy `fn-charge-for-payload` is proved
positive and monotone in payload length.

**ENC-003 is met rather than deferred.** Every variable field is
length-prefixed, so a field boundary is a decoded number and not a separator
octet that the field might itself contain, and the domain labels differ, so
the keystone

    fn-id-subject-and-obligation-preimages-differ

holds with no hypotheses at all: for *every* payload and *every*
(msgid, subject) pair the subject and obligation preimages are different octet
strings. Two kinds of identity cannot share a preimage by construction.

The pre-v1 derivation — `"sha256:" || hex(SHA-256(payload))` and
`"archive:" || hex(SHA-256(msgid || 0x00 || subject))` — is deleted, not kept
beside this one. A store holding those identities was written under an
experimental store format long retired; an image opens one format,
`fn-store-10` (`fn-bs-meta-formatp`,
[`books/byte-store-frame.lisp`](../books/byte-store-frame.lisp)), so such a
store is refused at open by its profile rather than misread.

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
meaning of an existing content ID or signed statement. No release reads
another release's store (fresh deploys at 6.6.0): the mandatory-binding
record schemas 3 and 4 replace schemas 0, 1 and 2, whose version octets are
refused rather than decoded with invented provenance.

## Experimental signed-source topic metadata

`books/topic-history-metadata.lisp` implements the bounded `FN-Topic: v1`
candidate grammar proposed in [P3](../planning/topic-history-p3-2026-09-23.md).
The article parser supplies the exact authored-source field view; the topic
codec accepts one nonduplicate field, canonical padded base64 without internal
whitespace, and a restricted CBOR item sequence. It caps the field at 2,048
octets, binary at 1,536 octets and items at 39. Root author and report-parent
lists are strictly ordered and reject duplicates. The native
`topic-inspect-carrier ARTICLE ML-PUBLIC-PEM` command verifies the existing
hybrid carrier and calls this source projection, reporting candidate metadata
separately from topic admission. It does not install a root, adopt a control,
or admit a report. The fixed-controller public roster remains an experimental
profile, and this grammar has not been declared a universal topic policy.

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
Python encoders. FNWF extends the deployed seven-kind table append-only with
codes 8 (`:undertake`) and 9 (`:release`); the old seven code values and
their captured octets are unchanged. FNST gains the record kind octet it lacked, so a store written
under the old framing is refused by its format word (the one format an image
opens is `fn-store-10`, `fn-bs-meta-formatp`) rather than misread. FNBI moves its BID length into a
payload text field; because an inbound bundle can reach four mebibytes and
cannot cross the decimal-octet bridge, ACL2 builds and validates the frame head
and the host concatenates bundle bytes it never interprets.

**A-CRYPTO.** The 32-octet trailer is BLAKE3 in deployment (SHA-256 up to store
format 9), computed by ACL2's attached `fn-blake3-stobj` (books/blake3.lisp;
the C BLAKE3 in the saved images, A-CRYPTO-NATIVE). `fn-frame-digest` is an `encapsulate` whose only constraints are
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

### Bounded Store-event profile

The generic CBOR entry points retain their original 65,538-octet input and
65,535-octet byte-string limits. Store event decoders that carry keyring
snapshots or accepted-statement composites call the explicit-budget decoder.
The caller supplies a whole-input budget and a per-item byte-string budget;
both checks occur before `take` allocates the declared value. A prefix decoder
checks the whole input once, then parses a fixed item count without rescanning
each suffix. Canonical keyring snapshots larger than the generic ceiling and
kind-4 composites round-trip through the actual Store-event dispatcher.

FNST's 196,608-octet ceiling counts its payload, excluding the fixed 42-octet
frame header and trailer. The store profile (FNSM kind 1, format
`fn-store-10`, the one format an image opens; every other word is refused
at the open by name, "not an fn store of this release: redeploy fresh":
STO-028, books/byte-store-frame.lisp, books/store-profile-open.lisp) is one
text (the format) and fifteen eight-octet frame naturals, the operator's fields
in the order of `*fn-bs-profile-field-names*`; `fn-bs-profile-validp` states
the relations between them and the codec ceilings (the per-record field R is
at most this FNST ceiling and at least every Store event kind's worst case).
Admission is ACL2's own count and sum:
fewer than T committed records, the prospective record within R, and the
committed record octets plus it within H (`fn-sbud-verdict-at`). The former
relation `T x R <= H` is dropped; the octet sum it stood in for is now
counted (`fn-sbud-bytes-used`), so no host aggregate is an authority.

See [RFC 8949 §4.2](https://www.rfc-editor.org/rfc/rfc8949.html#section-4.2) for
deterministic CBOR requirements. COSE is a candidate for signatures, not an
already selected profile.
