# Wildmat matcher work accounting

Status: ACL2 work-accounting experiment for the frozen RFC 3977 Wildmat base
matcher. It applies after parsing and UTF-8 decoding, to a valid parsed pattern
list and a decoded target scalar list. It is not a host-runtime, parser, or
UTF-8 decoding bound.

[`books/wildmat-work.lisp`](../books/wildmat-work.lisp) implements costed
executions with the same branches and values as the frozen dynamic-programming
row functions, pattern matcher, rightmost-pattern search, and codepoint-level
decision. Theorems project each costed value to the corresponding executable
function. The worker calculates its own cost; no theorem merely attaches a
budget to an uninstrumented matcher call.

Let `T` be the decoded target codepoint count and `P` the item count in one
pattern. The row engine makes one fresh row per item and scans the target once
per row. ACL2 proves that its costed row execution has exact cost
`P * (T + 2)`. It also proves exact `T`/`T + 1` costs for the target-row
auxiliaries, row construction, and row-last scan. Consequently, the complete
one-pattern DP matcher has exact cost `2 * (T + 1) + P * (T + 2)`: initial
row construction, every item row, and the final-row scan are all included.

For a parsed pattern list with `K` entries and total item count `P_total`, ACL2
proves the rightmost-search worker is bounded by
`K + 2 * K * (T + 1) + P_total * (T + 2)`. This charges the actual rightmost
list walk and conservatively charges a full DP match for every entry; an early
rightmost match can only reduce the work. The codepoint-level decision adds one
unit to that bound. These composed results retain value equivalence to the
frozen rightmost matcher and codepoint-level decision.

The frozen RFC base grammar has only exact scalar items, `*`, and `?`.
Bracket classes, ranges, inverted classes, quoting, and class-membership scans
are rejected extension syntax, so they contribute no `R` class-item parameter
to this matcher hot path. The executable row functions likewise do not call
`reverse`, `append`, `nth`, `len`, or list membership; their costs are zero in
this accounting. Those operations do occur in parser/decoder code and must be
counted by a separate parser/UTF-8 proof.

The accounting is logical ACL2 list work. It does not establish constant-time
machine arithmetic, allocation/GC, cache behavior, guard safety, stack use,
raw UTF-8 decoding, parser/recognizer validation, malformed input refusal, or
host I/O behavior.
