# Complete public article-parser work — 2026-09-18

All six new proof books and the boundary assertion book passed a frozen
seven-root ACL2 8.7 / SBCL 2.6.8 invocation. The
[record](2026-09-18-article-work.json) retains commands, source/dependency/tool
digests and results. Original parser sources are unchanged.

`fn-article-parse-work-value` proves exact correspondence with the actual parser
for every ACL2 input. The input and fixed-profile work theorems are also
unconditional: malformed atoms, improper lists, non-octets and all rejection
paths are included. The [cost specification](../../specs/article-work.md)
charges validation, line/field/body scans, repeated length operations, reversals,
and folded-header prefix copying. The conservative profile ceiling is
17,450,479,652 traversal/control units; this is not a runtime estimate.

Executable boundary checks cover source lengths 32768/32769, line lengths
998/999, field counts 64/65, physical header lines 128/129, folding and binary
bodies. They supplement the general theorems.

Integer bit complexity, memory allocation bytes, GC, evaluator overhead and
host I/O are outside this structural cost model. The instrumentation is a
logical proof witness and is not separately guard verified. PRF-016 remains
open for the broader parsing, staging and allocation contract.
