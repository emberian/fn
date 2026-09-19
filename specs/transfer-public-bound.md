# Transfer public missing-range work bound

Status: ACL2-certified logical work bound for the total public
`fn-transfer-missing-ranges` read.

`books/transfer-public-work.lisp` instruments the actual public call graph:
state and profile validation, bounded entry and chunk validation, pairwise
stored-label comparison, query lookup, refusal, and the declared-position
missing traversal.  Its value projection is exactly
`fn-transfer-missing-ranges`, including `:invalid-state` and `:unknown-label`.
Structural comparisons use the value-equivalent `fn-transfer-equal-work`
worker; they are not treated as free primitive operations.

`books/transfer-public-bound.lisp` defines `fn-transfer-tree-size`, which
counts every cons cell in an arbitrary ACL2 value and assigns atoms size zero.
Let:

- `M` be the tree size of the supplied state;
- `Q` be the tree size of the supplied query label;
- `K` be the naturalized maximum-chunks field of the supplied profile;
- `L` be the naturalized maximum-chunk-octets field of that profile; and
- `N` be the naturalized declared length of the entry selected by lookup.

ACL2 proves, without hypotheses, that the instrumented public work is at most:

```text
16 + 21M + 11M^2 + 9M^3 + 2M^4
   + M(1 + 2Q)
   + N(1 + K)(1 + L)
```

The first line covers validation of arbitrary and malformed state values.  It
includes nested entry/chunk checks, pairwise overlap checks, distinct stored
labels, and reserved-byte accounting.  The second line covers public lookup
with an arbitrary query: each comparison costs at most `1 + 2Q`, and the raw
state structure bounds the number of entries examined.  The final line is the
certified missing-position hot path for a valid selected entry.  Invalid-state
and unknown-label executions stop before that traversal, while the same total
budget remains valid.

The theorem is `fn-transfer-missing-ranges-work-public-bound`; its executable
right-hand side is `fn-transfer-public-bound-for`.  The proof uses no assumed
work predicate, trust tag, skipped proof, or validity premise.  Raw structure
parameters are necessary because the total public function examines malformed
states and arbitrary query labels before profile bounds can constrain them.

## What this bound is about, and who may cite it

The bound is about `fn-transfer-missing-ranges` and nothing else.  That
function has no caller outside `books/transfer*.lisp` and
`tests/acl2/transfer-tests.lisp`: no host file, no adapter and no other book
calls it, so the bound currently governs no served path.  Under the assurance
rule that a theorem's subject must be the function the host calls, PRF-016
should not cite `fn-transfer-missing-ranges-work-public-bound` as evidence for
bounded staging, and PRF-011 should not cite the transfer assembly theorems as
merge evidence, until a caller exists and is named.  `planning/proofs.json` is
not owned by this lane; this paragraph is the proposal to its owner, not a
registry change.  The other two public transitions, `fn-transfer-reserve` and
`fn-transfer-add-chunk`, have no costed shadow at all, so no bound covers a
staging *mutation*; `fn-transfer-add-chunk` now performs an overlap byte
comparison and a per-position uncovered-run split, whose cost is bounded by the
arrival length times the retained fragment count but is not modeled here.

One work unit represents a recursive structural visit or a primitive numeric
check/comparison in the logical implementation.  Structural equality charges
the nodes it actually compares.  The theorem does not model integer bit
complexity, allocation, garbage collection, host recursion limits, persistence,
network I/O, or encoded-input parsing.  Those remain host and boundary costs,
not claims of this ACL2 work model.
