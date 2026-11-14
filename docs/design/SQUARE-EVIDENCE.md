# Formula-bound square evidence

`books/square-evidence.lisp` generates ground witness proofs from an existing
`fn2-squares` statement. It does not prove that universal statement, change its
`:proof` status, or replace live execution tests. All metadata remains in the
same square row under `:evidence`; this is not a second obligation ledger.

The initial author form supports an equality between two admitted function
calls, optionally beneath `implies`. Decomposition uses only the live statement
function's canonical translated body: `IMPLIES(H,C)` or `IF(H,C,'T)` for implication and
`IF(H,REST,'NIL)` for conjunction. The row's raw `:formula` author metadata is
not trusted, even when a direct table update replaces it. Hypothesis selectors
must match the actual translated clauses; unsupported macro spellings fail.

```lisp
(defsquare-evidence name
 :positive ((x '3))
 :negative (:kind :hypothesis-removal
            :remove (natp x) :bindings ((x '-1))))
```

Alternatively, use `:kind :mutation`, `:at concrete-function`, and
`:replace mutant-function`. The concrete function must be the left endpoint
named in the square's `:sides`; the reference function must be its right
endpoint. The mutant must have the concrete function's argument count and
stobj input/output signature. Unsupported formula shapes are refused.

Every statement variable has one quoted binding, in declaration order. The
generator obtains both endpoints' actual guards from the ACL2 world and
instantiates them at the stated calls. A positive witness proves the guards,
the entire antecedent, and the entire conclusion. A mutation control also
proves the mutant's guard and falsifies the conclusion with that endpoint
replaced. A hypothesis-removal control proves all remaining clauses, falsifies
the exact selected clause, and falsifies the conclusion. Duplicate selected
clauses are refused. An opaque antecedent is one clause; the generator does
not invent a decomposition of a helper predicate.

Witnesses are ground `defthm` events, not `defun-nx` functions mislabeled as
executable tests. This lets ACL2 check the complete logical stobj values
without materializing production state on a served path. Existing executable
`:teeth` remain separate evidence. Runtime constructors and concrete execution
bindings are not implemented by this first form.

`fn2-assert-square-evidence` verifies the recorded formula, admitted ground
theorems, endpoint bodies, guards and ABI against the current world, then
regenerates and proves both assertions. It does not trust a stored success
flag or an arbitrary zero-argument function returning true. Certification of
the fixture still requires the usual current-closure record-toolchain entry;
this metadata alone makes no certification claim.

`tests/square-evidence-unit.lisp` pilots the actual mutable child compiler:
the full result preserves an unrelated sibling, while a mutant clobbering
that sibling is detected. Refusal controls cover vacuous positive premises,
wrong endpoints/ABI, ineffective mutation, incorrect removed hypotheses,
stale formula metadata, omitted function bindings and an unrelated proof.
The independent redirected-formula control keeps the original statement and
its translation while replacing author metadata with a different hypothesis
and shifted reference call. False redirected witnesses are refused; genuine
original witnesses remain bound to the original statement. The OWED renderer
uses the same live claim lookup, with its implementation in `owed-report.lisp`.
