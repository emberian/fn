# Transfer public read work bound

Status: certified costed-projection layer. This book
extends the certified entry-local traversal accounting in `transfer-work` to
the public `fn-transfer-missing-ranges` read operation. There is no separate
public candidate-read operation in the frozen transfer kernel: candidate
construction remains the already-accounted entry-local operation, while
reserve and add-chunk candidates belong to mutation paths outside this wave.

`books/transfer-public-work.lisp` defines a certified costed call graph for
the actual public missing-range function.  It is a root of the integrated
certification batch and carries a certificate; the header comment that said
certification was deferred was stale and has been removed. It independently repeats the
recursive work of
`true-listp`, bounded-list preflights, octet validation, profile validation,
entry and chunk validation, pairwise overlap checks, distinct-label checks,
reserved-byte traversal, entry lookup, and the certified declared-position
missing traversal. Its public projection theorem proves equality of the costed
value with `fn-transfer-missing-ranges`, including `:invalid-state` and
`:unknown-label` results.

The public bound must have two raw-input parameters in addition to profile
capacities. Let `M` be the structural size of the supplied ACL2 state value
and `Q` the structural size of the supplied query label. A profile alone does
not bound either value: `fn-transfer-missing-ranges` first applies
`true-listp` to arbitrary `st`, before a profile can be reached, and it passes
an arbitrary `label` to structural equality during lookup without a label
preflight. Thus there can be no honest public invalid-state or unknown-label
bound expressed
only with capacity, reservation, chunk, and stored-label limits.

`fn-transfer-equal-work` recursively compares cons structure and returns the
same Boolean result as ACL2 `equal`. Distinct-label validation and entry lookup
both call this worker, so stored-label and query comparisons contribute their
actual recursive visits to the cost.

The companion [public-bound specification](transfer-public-bound.md) records
the hypothesis-free theorem
`fn-transfer-missing-ranges-work-public-bound`. With `K` and `L` the
naturalized profile chunk limits and `N` the naturalized declared length of the
selected entry, its executable bound is:

```text
16 + 21M + 11M^2 + 9M^3 + 2M^4
   + M(1 + 2Q)
   + N(1 + K)(1 + L)
```

The powers of `M` cover the complete validation graph, including entry and
chunk checks, overlap scans, pairwise stored-label comparisons, and reserved
byte accounting. `M(1 + 2Q)` covers lookup against an arbitrary query, and the
last term is the declared-position missing traversal.

The logical accounting assigns one unit to ACL2 primitive numeric checks and
explicitly counts recursive cons traversal, including the structural equality
comparisons in distinct-label validation and entry lookup. It does not claim
bignum bit complexity, allocation, garbage collection, persistence, network
I/O, or a parser boundary. The kernel accepts logical internal state; it does
not parse remote Lisp. A future boundary layer that accepts untrusted encoded
state or labels must apply its own bounded parser/label guard before invoking
this public logical operation.
