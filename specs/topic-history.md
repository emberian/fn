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
base64. The ACL2 renderer emits 72 base64 octets on the first physical line
and each continuation line, with exactly one HTAB before continuation data.
The projector accepts this folded form only when its raw lines equal the
canonical renderer for the decoded value. It also accepts an unfolded
single-line value when the article parser's physical-line limit permits it;
arbitrary whitespace and noncanonical folding are refused. The ACL2 decoder
caps items at 39, binary input at 1,536 octets and normalized field value at
2,048 octets before conversion. A folded parsed value is prechecked at 2,144
octets before bounded whitespace stripping.
Unknown versions, duplicate fields, malformed folding and noncanonical
encodings produce an unsupported candidate, leaving ordinary article handling
separate.

`books/topic-history-metadata-invariants.lisp` proves that every valid
constructor encodes to at most 1,531 binary octets and 39 items, and that
decoding its encoding recovers the original value. The decoder checks the
1,536-octet whole-input limit before invoking the statement item decoder at
its standard profile budgets; declared-length checks remain constrained by
the prechecked input's remaining bytes.
The source-binding theorem names the host-called `fn-th-host-inspect-source`:
success requires one FN-Topic field in the parsed authored source and returns
the decode of that field's canonical raw-line representation. Tests keep a different relay
FN-Topic, Path and Xref in received bytes separate from that source.

The article parser's local header envelope is 16,384 octets and 256 physical
lines; its complete-source cap remains 32,768 octets and physical-line cap
remains 998. An ACL2-generated maximum root with 16 authors and 64 domain
octets has 2,047 normalized field-value octets, 29 rendered physical lines,
and 2,143 field-wire octets. In a native-style source with 143 octets of
ordinary headers, the full FN-Authorship carrier has a 9,811-octet header and
135 physical header lines. These bounds are local resource policy, not RFC
requirements or a topic authority decision.

The native `topic-inspect-carrier ARTICLE ML-PUBLIC-PEM` command checks both
hybrid signature suites through the existing carrier verifier, then passes the
returned exact source, verified principal and ordered keys to
`fn-th-select-verified-source`. The selector uses `fn-th-host-inspect-source`
for the metadata, then derives an author reference from that verified principal
and the ACL2 subject identity of its canonical keyring snapshot. A root's
declared controller and keyset identity are marked matched only if both equal
that verified reference. A control or report carries no self-authorizing
controller claim; its candidate author comes from the verified context,
regardless of `From`. The historical `fn-th-select-accepted-event` first calls
the schema-1 Store event/snapshot binding predicate, then selects from the
event's retained exact source and the enrolled historical principal and keys.
An unbound event is refused. The selector does not adopt a roster, resolve a
fork, or commit an admission. The native output distinguishes
`carrier=authenticated` and `topic=candidate` from
`binding=controller-matched|controller-mismatch|not-root` and
`admission=unestablished`. The existing candidate output remains available
even for a mismatching root; a mismatch never asserts root authority. This is
an offline inspection path. A carrier
signature is not an anchor, adopted policy, current roster membership, Store
topic event or application authorization. No parser examines Mini application
bytes, and no external data is passed to a Lisp reader.

The source and host-called projection are covered by PRF-062 and SCN-030;
the verified and historical authorship binding is PRF-065 and SCN-032.
Store topic events, durable admission and current-policy status remain the
next P3 composition steps and need their own host-called theorems and physical
evidence. RFC 5536 header syntax comes from the article parser. The one-field,
canonical metadata and size choices are stronger local fn experimental rules,
not RFC requirements.
