# Canonical Store size carries

This is a constructor dependency for the maintained checkpoint growth reserve
in P12/S7 (STO-020), not an implemented admission gate. PRF-1113 and PRF-1120
are source-admitted components. There is no certification manifest or matching
native image for them, and the live owner does not yet install their sidecars.

The target is the exact `fn-scc-encode` representation, not the wire article's
length. Every nonempty octet-list subtree collapses to a single instruction;
an empty list encodes as NIL. Consequently a parent's size cannot always be
computed by adding its children's encoded lengths plus a CONS octet.

`books/store-tree-size.lisp` carries three scalars alongside each referenced
immutable value: encoded octets, octet-list length or NIL, and whether the value
itself is a scalar octet. `fn-scs-atom` sizes a scalar without allocating its
encoded bytes. `fn-scs-octets` takes a byte span's already established length,
including zero. `fn-scs-cons` reads just the two child carries and reproduces
the codec's compact-list decision. `fn-scs-spine` composes the carries for a
new record spine. None traverses a child/context value. Integer sizing takes
one step per base-256 digit; codec/profile representability is a separate
obligation, and sizing does not claim to validate that representation.

`fn-scs-summary` and `fn-scs-correspondsp` are logical correspondence functions.
They must not be called to rescan shared contexts on POST, capture or admission.
The cons keystone requires the exact summaries of both children; its literal
teeth retain the other hypothesis while independently corrupting each one.
The span and spine keystones have corresponding positive/removal cases.

`books/held-record-size.lisp` pairs the actual `fn-held-make` result with a
carry composed from its field carries. Its payload-remap companion replaces
slot 4 and that field's carry; the old facts, context, memberships and other
fields are shared. Its theorem proves exact size after a replacement, including
scalar-width crossings such as 255 to 256. The positive test constructs a
nonempty held record. The shape and atom hypothesis removals are explicitly
logical cases outside the executable guard. The separately planned mandatory
binding field must add one field and carry to this companion when its actual
held constructor changes; slot 4 remains the payload handle.

`fn-hsz-remap-root` uses the actual root's encoded length and the old/new
payload scalar widths. Its keystone requires an exact root size, scalar old
and new payloads, and a non-octet suffix after slot 4. That suffix prevents
compact-octet collapse at any reconstructed ancestor. The function preserves
an arbitrary trailing binding field and needs no retained per-field carries.
Its witnesses include a genuine 255-to-256 width crossing, the octet-collapse
counterexample and independently corrupted old/new leaf shapes and root size.
This is not yet the actual pool admission delta: the caller must install and
maintain that exact old root size and apply its required row padding.

`books/identity-context-size.lisp` carries summaries for the six fields of the
actual `fn-stxk-context`. Its snapshot/verdict companions call the original
transition exactly once. A snapshot generation change selects the same snapshot
cons as the original decision. A successful verdict step selects its verdict
cons. Duplicate/fault branches preserve the shared trees, and only scalar
coordinate/diagnostic fields are rebuilt. The keystones preserve field
correspondence under context shape, old field correspondence and new-event
correspondence. Tests assert each literal antecedent and conclusion and
independently remove each hypothesis; the malformed context is labeled as a
corrupted-state case. No authorization, retention or persistence decision is
changed by these companions. The existing identity decision may search its
snapshot list; the sidecar adds no such walk and does not claim to establish
a scheduling bound for that existing decision. Fixed-width sidecar shape
checks stop after the record width even on malformed metadata.

## Installation still owed

The served node's `fn-sn-identity-context` intentionally reconstructs a context
with NIL verdicts, while the checkpoint identity value is the full
`fn-replay-identity-loop` accumulator. The live Store verdict-pair list cannot
be relabeled as this full accumulator. Installation must maintain the actual
checkpoint context and its sidecar together through all replay/composite and
owner writer paths, with bootstrap carries produced in the bounded decoder.
The decoder's public atom/pair/span descriptors stay unchanged. The source
prototype `fn-hds-begin`/`fn-hds-feed` returns the exact parser plus a parallel
temporary annotation stack, a streamed NIL-prefix bit and a usable bit. A
leaf annotation is `(root-carry)`; a pair is `(root-carry car-info . cdr-info)`.
`fn-hds-info-root` reads its root carry, and `fn-hds-select-fields(n, info)`
returns field carries plus usability while walking only the selected spine.
The six identity fields use `n=6`; octet-span children remain single leaves.
Pair construction and successful selection preserve their exact logical
correspondence. Length/list-shape premises were removed after proving the
stronger selection theorem. Literal leaf, NIL-matcher, constructor and field
selection witnesses are source-admitted in a fresh protected session.

The full byte-fed stream invariant and bootstrap of the actual checkpoint
identity accumulator are still open. This prototype is not host installed.
Accepted NIL symbol aliases and zero-length byte spans use their normalized
canonical sizes; arbitrary nonminimal integer spelling uses the decoded value.
Each annotation leaf allocates four cons cells, each annotation pair five,
including its three-scalar root carry; the additional size-stack cell, actual
decoder nodes and source pool coexist. These are representation counts, not a
proved or measured funded heap bound. Selection retains only six root carries
and their fixed list spine after child scratch is dropped; row completion
retains only the root size, never uncharged per-field row metadata.

Every constructor of consumer, topic, identity and held/context values must
establish or preserve its carried correspondence. A missing or stale carry
cannot be replaced by wire bytes, a guessed limit or a whole-context scan.
The owner must not publish a usable carry that another writer can bypass.
The held ordinal remap must update handle widths before the padded pool delta
is handed to the reserve algebra. Shared source/target lifetime, spool and
cleanup coexistence, all profile representability checks, actual pool
allocation and the complete funded rescue inequality R >= W remain owed.
