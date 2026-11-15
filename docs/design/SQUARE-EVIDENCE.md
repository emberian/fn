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

For an opaque conclusion, add `:correspondence theorem-name`. The admitted
theorem must have the exact translated form `equal(C, equal(actual-call,
reference-call))`, optionally under `implies(D, ...)`. Its left side must
structurally equal the original live conclusion C, including any translated
`mv-let` lambdas. The endpoint calls come from that theorem, never a supplied
replacement formula. The original row's `:sides` must name their functions.
Equivalence alone is insufficient: the concrete endpoint must either occur
as an actual call in C or expose every output of that call as a list, exactly
once and in order. The wrapper's admitted body is beta-reduced without
unfolding or evaluating other functions. Its tuple width must equal the
actual subject's result ABI. Hidden producers, dropped/reordered outputs and
unrelated equivalent endpoints fail closed. The subject's actual arguments,
body, guard and ABI are bound and checked again on replay.

The generator proves `H => (D and the endpoint/subject guards)` for the entire
original antecedent H and also requires D at both ground witnesses. A correspondence restricted to a removed
hypothesis therefore cannot justify a negative witness outside its domain.

Every normalized witness still proves the original C (or its negation for
hypothesis removal), as well as the corresponding endpoint equality. This
does not replace the original statement or discharge its universal obligation.
For mutation, it additionally falsifies the original C with the actual
subject call replaced by the mutant result, so changing an unrelated view
cannot masquerade as sensitivity of the original computation.
The correspondence theorem's exact body, normalization domain and endpoint
equation are checked again during replay. Whole-formula logical equivalence
does not authorize changing H or choosing another C.

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
`tests/square-evidence-correspondence-unit.lisp` additionally exercises an
actual mutable operation with a full-result `mv-let` predicate and a sibling
clobber mutant. It refuses redirected correspondence theorems, a domain that
holds only at the chosen examples, and a removal witness outside the theorem's
domain. Coherent theorem-name/body metadata tampering cannot redirect C.
An admitted equivalence to unrelated constant endpoints is rejected even
when the original conclusion is universally true; partial-result wrappers
are rejected even when their remaining scalar output is correct.
The independent redirected-formula control keeps the original statement and
its translation while replacing author metadata with a different hypothesis
and shifted reference call. False redirected witnesses are refused; genuine
original witnesses remain bound to the original statement. The OWED renderer
uses the same live claim lookup, with its implementation in `owed-report.lisp`.
After fixture certification, `tools/acl2 --timeout 60 <
tests/square-evidence-export.lsp` writes and reads the actual report, checking
that redirected display metadata cannot replace its statement. File output
runs outside book events; no trust tag is needed.

## Direct predicate conclusions

`:conclusion-kind :predicate` accepts the exact live conclusion as an admitted
predicate call, including predicates of `mv-nth` results. It does not invent
an equality endpoint or claim producer equivalence. Its only negative kind is
`:hypothesis-removal`: the positive theorem asserts `H and C`; the negative
asserts every remaining conjunct, `not removed`, and `not C`. The selected
hypothesis must occur exactly once by default in the translated conjunction tree. A
composite stored guard can be removed as a whole; all outside carrier premises
remain. A constant-true predicate cannot pass the required false-C theorem.

Predicate bindings may be quoted values or closed ACL2 pseudo-terms, in exact
statement-variable order. Constructor calls therefore remain logical terms
whose complete ground assertions ACL2 must prove, not host-computed state or
raw execution of malformed stobjs. Indices and other constants in this
translated-term interface must be quoted. Optional `:positive-hints` and
`:negative-hints` permit reuse of admitted ground facts with the actual raw
producer disabled. Replay regenerates the original assertions and uses those
same proof hints; hints never replace H or C.

Programmatic consumers use
`fn2-square-predicate-evidence-events-with-hints(name, positive, negative,
positive-hints, negative-hints, recheck, world)`; the five-argument variant
supplies empty hints. Existing equality/correspondence APIs and their quoted
binding restriction are unchanged. Predicate evidence leaves the row's
universal proof status unchanged.

`tests/square-evidence-predicate-unit.lisp` contains positive, composite-guard,
wrong-formula, vacuity, open-binding, remaining-premise and unsupported-mutation
controls. The exact five-book predicate/correspondence fixture union is qualified
at source `eb137e8f0`: provider author 0.24 seconds, predicate fixture 0.23 seconds,
and existing correspondence fixture 0.21 seconds. The record reused three qualified
parents and certified both test leaves under toolchain `8aeb`; see
[the receipt](receipts/predicate-evidence-five-record.json). The six actual guarded
checkpoint-reader consumer instances remain pending their separate gate.

## Repeated hypotheses and actual member

Predicate removal defaults to exactly one structural occurrence. An explicit
`:occurrences 2` removes two identical copies of the selected predicate, while
proving every other conjunct, the predicate's negation, and the exact false C.
A changed count or a failed remaining premise refuses admission. This is needed
when a readonly recognizer occurs both explicitly and inside the stored guard;
it does not remove the whole guard or weaken the universal statement.

`tests/checkpoint-member-guarded-evidence-unit.lisp` binds the actual member
consumer. It checks exact ABI, same original conclusion, retained original
premises and actual stored guard before registering the distinct admitted
guarded theorem. It also emits the domain-containment theorem. The positive
uses the existing actual constructor with only its checkpoint value repaired;
the negative reuses the admitted readonly-type counterexample. Both bind all
12 actual arguments. Raw stobj executable counterparts are disabled by live
signature metadata during proof. The original remains refuted and unfinished.

The exact 41-book member/predicate/correspondence/report union is qualified at
source `3bbbca421`; see [the receipt](receipts/member-predicate-forty-one-record.json).
The member leaf admitted in 7.51 seconds under the original per-event 2M-step/20-second
budget. The actual export replay preserves the original refutation and prints
one proved guarded row. The generic refutation status still labels candidate
replacement links unverified: this leaf's checked domain relationship is not a
global replacement-status upgrade, proof of the original, or proof of served
caller reachability. No production member body, guard or theorem changed.
