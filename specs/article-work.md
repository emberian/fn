# Received-article parser work correspondence

This specification closes the structural-work part of PRF-016 for the complete
public `fn-article-parse` operation in `books/article.lisp`. The grammar, limits,
error precedence and malformed-input behavior remain those of
[the parser specification](article-parser.md). No RFC interpretation changes.

## Instrumentation and cost units

`fn-aw-parse` returns `(value work)`. `fn-aw-v` and `fn-aw-c` select its value and
work. The worker follows the actual parser's short-circuit call graph. It charges
one unit for each recursive list-walk activation, including the terminating
activation, and one unit for each bounded scalar/control/constructor block in a
composite worker. A block contains a fixed number of scalar tests, selectors,
arithmetic operations, tag comparisons and fixed-arity constructors. A unit is
not a CPU instruction or a time measurement.

Every input-dependent traversal called by the parser has a costed counterpart:

- The bounded source-length preflight and subsequent octet validation are
  separate passes, including malformed-input and early-exit cases.
- Physical-line and colon scans include their accumulated-prefix reversals.
- Field-name validation, value-byte validation, visible-character scanning and
  name downcasing are separate passes, with the original short-circuit order.
- Both occurrences of a line-length calculation and the conditional field-count
  calculation are charged independently.
- Each fold copies the old raw-line-list prefix and the old unfolded-value
  prefix. Both copies are charged on every continuation.
- Header accumulation charges line reversal and both append prefixes. It does
  not scan the existing header suffix: the actual append does not scan it.
- Final header/field reversals and the complete body CRLF scan are charged.

The paired-result plumbing and arithmetic that maintain the cost counter are
instrumentation, not additional parser work. The parser's tag comparisons are
against fixed atoms; it performs no equality comparison between two unbounded
structures. `fn-article-fieldp`, `fn-article-lower-namep`, and
`fn-article-syntax-p` are not called by this parser body. Their use in verified
helper guards does not add repeated recognition passes to this algorithm. This
book does not bound separately requested field lookup or semantic validation.

The public execution reaches only proper-list reversals. The total reverse
worker also preserves ACL2's string case for its unconditional helper value
correspondence; that branch is outside the public parser path.

The model excludes integer bit complexity, memory allocator behavior/allocation
bytes, garbage collection, cache/stack effects, ACL2 evaluator/guard-checking
bookkeeping, compiler costs and host I/O. It is a structural algorithmic work
bound with fixed-size primitive blocks, not a wall-clock, heap-byte, or host
runtime theorem. The original public parser has guard `T`; its verified internal
guards justify its executable list operations without changing its logical
malformed-input behavior. The new paired work functions are logical proof
witnesses; this task does not claim separate guard verification or native-runtime
performance for the instrumentation itself.

## Certified correspondence and bounds

`fn-article-parse-work-value` proves, for **every ACL2 input**, that

```
(fn-aw-v (fn-aw-parse octets)) = (fn-article-parse octets).
```

Let `N = min(len(octets), 32768)` and define the envelope

```
B(0, n, s) = 1
B(k, n, s) = 32*(n+s+1) + B(k-1, n, s+2*n+4),  k > 0.
```

`fn-aw-budget-polynomial` proves the natural-argument closed form

```
B(k, n, s) = 1 + 32*k*(n+s+1) + 32*(n+2)*k*(k-1).
```

`fn-article-parse-work-input-bound` proves **without hypotheses**:

```
work(fn-aw-parse octets) <= 3 + 2*N + B(129, N, 0).
```

`fn-article-parse-work-profile-bound` proves the corresponding fixed-profile
bound, also without hypotheses: **17,450,479,652 work units**. This is a
conservative envelope, not a tight estimate. It follows the actual 129-step
header fuel, including the separator step, and the actual 32768-cell preflight.
No successful-parse premise, cost recognizer, prevalidated-input premise, or
post-hoc output filter is assumed.

## How far the envelope is from the cost it bounds

In one sentence: the envelope is degree one in `N` — substituting `k = 129` and
`s = 0` into the closed form gives `3 + 2N + B(129, N, 0) = 532514*N + 1060900`,
whose quadratic factor is the header fuel `k`, not the input length — and at the
520-octet maximally folded regression article it allows 277,968,180 units
against the 17,190 units the instrumented parser actually charges there, about
1.6 * 10^4 times the cost it bounds. The ratio is structural, not an artifact of
that input: the envelope charges each of the 129 header steps the whole
remaining input plus the accumulated state, while the parser scans each octet a
fixed number of times. `tests/acl2/article-work-tests.lisp` asserts those three
numbers as executable witnesses, so the distance is checked rather than
estimated. Closing the gap is a separate, unattempted piece of work; nothing in
this specification claims the bound is tight.

## The cost side is by construction, not by theorem

`fn-article-parse-work-value` proves the **value** side for every ACL2 input:
`fn-aw-parse` returns exactly what `fn-article-parse` returns. There is no
theorem relating `fn-aw-parse`'s counter to the work `fn-article-parse`
performs, and there cannot be one without a second, independent cost semantics
for the original parser to compare against; none exists in this tree. The
correspondence between the charges and the parser's recursion is therefore
established **by construction, not by theorem**: the worker mirrors the
parser's call graph branch for branch, it is checked by reading, and it is
checked at specific inputs by the exact-charge vectors in
`tests/acl2/article-work-tests.lisp`. A reader who accepts
`fn-article-parse-work-profile-bound` as a bound on the real parser is relying
on that reading, not on a proof. This is the honest reading of the "exact
correspondence with the actual parser for every ACL2 input" claim: it is true
of the value, and it is a construction claim about the cost.

The loop induction uses a size measure consisting of the reversed field count,
reversed header length, current field's raw-line count, and current field's
unfolded-value length. Scanner results do not exceed remaining input length;
each recursive state grows this measure by at most `2*n+4`. Local work is bounded
by `32*(n+s+1)`. Certified monotonicity composes these facts across both new-field
and continuation branches. Malformed input and all early returns are included.

## Books and regression evidence

The proof layers are `article-work-primitives`, `article-work-scanners`,
`article-work` (field workers), `article-work-budget`, `article-public-work`
(complete value correspondence) and `article-public-bound` (complete work bound).
`tests/acl2/article-work-tests.lisp` checks exact charges for malformed atoms,
improper spines, nested non-octets, empty articles and prefix-copy helpers; it
also exercises exact source, line, field-count and continuation-count limits,
including rejection before octet validation and opaque binary body bytes.
The general public theorems provide the all-input evidence; the examples do not
replace them. No trust tag, axiom, or skipped proof is used.
