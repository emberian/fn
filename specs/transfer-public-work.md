# Transfer public read work bound

Status: draft during the assurance integration certification hold. This book
extends the certified entry-local traversal accounting in `transfer-work` to
the public `fn-transfer-missing-ranges` read operation. There is no separate
public candidate-read operation in the frozen transfer kernel: candidate
construction remains the already-accounted entry-local operation, while
reserve and add-chunk candidates belong to mutation paths outside this wave.

`books/transfer-public-work.lisp` defines a costed call graph for the actual
public missing-range function. It independently repeats the recursive work of
`true-listp`, bounded-list preflights, octet validation, profile validation,
entry and chunk validation, pairwise overlap checks, distinct-label checks,
reserved-byte traversal, entry lookup, and the certified declared-position
missing traversal. Its intended public projection theorem is equality of the
costed value with `fn-transfer-missing-ranges`, including `:invalid-state` and
`:unknown-label` results.

The public bound must have two raw-input parameters in addition to profile
capacities. Let `R` be the structural size of the supplied ACL2 state value
and `Q` the structural size of the supplied query label. A profile alone does
not bound either value: `fn-transfer-missing-ranges` first applies
`true-listp` to arbitrary `st`, before a profile can be reached, and it passes
an arbitrary `label` to `equal` during lookup without a label preflight. Thus
there can be no honest public invalid-state or unknown-label bound expressed
only with capacity, reservation, chunk, and stored-label limits.

For a valid state with profile capacities `E` (maximum reservations), `K`
(maximum chunks per entry), `L` (maximum chunk octets), `B` (maximum stored
label octets), and `N` (the selected entry's declared length), validation has
the expected polynomial shape `O(E * (B + K^2 * L)) + O(E^2)` and the
missing-byte traversal adds `O(N * (1 + K) * (1 + L))`. The public draft will
publish a conservative explicit polynomial in `R`, `Q`, `E`, `K`, `L`, `B`,
and `N` after its ACL2 arithmetic proof is certified.

The logical accounting assigns one unit to ACL2 primitive numeric checks and
explicitly counts recursive cons traversal, including the structural equality
comparisons in distinct-label validation and entry lookup. It does not claim
bignum bit complexity, allocation, garbage collection, persistence, network
I/O, or a parser boundary. The kernel accepts logical internal state; it does
not parse remote Lisp. A future boundary layer that accepts untrusted encoded
state or labels must apply its own bounded parser/label guard before invoking
this public logical operation.
