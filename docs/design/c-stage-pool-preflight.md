# Atomic C stage pool preflight

The actual `fn2-succ-stage` keeps its existing slot grammar and schema-room
check. Before scratch or spare acquisition, the read-only
`fn2-idc-stage-pool-preflight` computes missing arenas from the actual requested
schema count and existing spares, checks free overlay rows, and adds scratch
only when the engine does not already hold it. When arena and scratch use one
class, their combined demand is compared once with the same
`fn2-pool-reservable-count` consumed by actual generic reservation.

A preflight refusal leaves pool, engine, overlay and index resources unchanged.
Existing slot evaluation and transaction phase/counters are preserved; the
original stage form is fingerprinted and compared after removing only the
explicit new bindings and guard-hint name. No whole-pool audit or copied
allocator arithmetic is introduced. The nonyielding stage carries the existing
pool accounting invariant; unexpected allocator/ownership corruption still
follows existing error paths, rather than an invented rollback.

The eight prepared controls call public `fn2-successor-stage` after actual
put/argument/resolve and use real scratch/spare/NAME/query/credit constructors.
They cover same-class joint shortage, sufficient capacity, existing scratch,
existing spare, different-class shortage, a nonempty query-pinned buffer,
protected credit, and logical overlay-row shortage with a real frozen NAME row.
They assert actual schema room/request count and compare complete physical
resource projections on refusal. Slot/field evaluation is intentionally outside
that frame. Assertions are unrun; no compute was allocated.

This prevents partial capacity hoarding within one stage call. It does not fund
a new upload across yields, cancel earlier payload IO, establish C schema room
across other writers, or prove sealer progress. The existing OPEN-on-full stage
grammar is unchanged; the CLOSING staged retry interaction remains with the
mutation/lifetime owner. No source mutation fence, pool API/layout, or activation
policy changes here.
