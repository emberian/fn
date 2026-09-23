# Topic history metadata: first experimental slice

Status: bounded candidate codec and native inspection; local topic admission is
not implemented. The [P3 design](../planning/topic-history-p3-2026-09-23.md)
proposes a fixed-controller public-roster profile, not a universal governance
policy. Independent topic histories remain the active design direction.

TOP-001: `books/topic-history-metadata.lisp` owns the `FN-Topic: v1` field grammar. It
accepts exactly one field in a successfully parsed **exact authored source**,
not an arbitrary received relay projection. The existing T10 hybrid carrier
extracts that source before any topic projection. The 32-octet principal and
48-octet subject identity are different types; root/controller, control and
report fields use the typed roles stated in P3. Ordered author references and
report parents reject duplicate or out-of-order members. The binary format is
restricted to canonical CBOR uint/byte items; the field is standard padded
base64 with no internal whitespace. The ACL2 decoder caps items at 39, binary
input at 1,536 octets and field value at 2,048 octets before conversion.
Unknown versions, duplicate fields, malformed folding and noncanonical
encodings produce an unsupported candidate, leaving ordinary article handling
separate.

`books/topic-history-metadata-invariants.lisp` proves that every valid
constructor encodes to at most 1,531 binary octets and 39 items, and that
decoding its encoding recovers the original value. The decoder checks the
1,536-octet whole-input limit before invoking the statement item decoder.
The source-binding theorem names the host-called `fn-th-host-inspect-source`:
success requires one FN-Topic field in the parsed authored source and returns
the decode of that field's unfolded value. Tests keep a different relay
FN-Topic, Path and Xref in received bytes separate from that source.

The native `topic-inspect-carrier ARTICLE ML-PUBLIC-PEM` command checks both
hybrid signature suites through the existing carrier verifier, then passes the
returned exact source to `fn-th-host-inspect-source`. Its output distinguishes
`carrier=authenticated` and `topic=candidate` from
`admission=unestablished`. This is an offline inspection path. A carrier
signature is not an anchor, adopted policy, current roster membership, Store
topic event or application authorization. No parser examines Mini application
bytes, and no external data is passed to a Lisp reader.

The source and host-called projection are covered by PRF-062 and SCN-030.
Store topic events, durable admission and current-policy status remain the
next P3 composition steps and need their own host-called theorems and physical
evidence. RFC 5536 header syntax comes from the article parser. The one-field,
canonical metadata and size choices are stronger local fn experimental rules,
not RFC requirements.
