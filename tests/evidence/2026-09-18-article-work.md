# Complete public article-parser work — 2026-09-18

All six new proof books and the boundary assertion book passed a frozen
seven-root ACL2 8.7 / SBCL 2.6.8 invocation. The
[record](2026-09-18-article-work.json) retains commands, source/dependency/tool
digests and results. Original parser sources are unchanged.

`fn-article-parse-work-value` proves exact correspondence with the actual
parser's *value* for every ACL2 input (`article-public-bound.lisp:112`); the
*cost* side (`:128`) is a separate instrumented shadow checked by reading, not a
measurement of the parser's own execution, and its closed-form ceiling of
17,450,479,652 traversal/control units is roughly 16,000x above the real
traversal cost for the profile it covers — quote the ceiling and this gap
together, not the ceiling alone. The input and fixed-profile work theorems are
also unconditional: malformed atoms, improper lists, non-octets and all
rejection paths are included. The [cost specification](../../specs/article-work.md)
charges validation, line/field/body scans, repeated length operations,
reversals, and folded-header prefix copying.

Executable boundary checks cover source lengths 32768/32769, line lengths
998/999, field counts 64/65, physical header lines 128/129, folding and binary
bodies. They supplement the general theorems.

Integer bit complexity, memory allocation bytes, GC, evaluator overhead and
host I/O are outside this structural cost model. The instrumentation is a
logical proof witness and is not separately guard verified. PRF-016 remains
open for the broader parsing, staging and allocation contract.
