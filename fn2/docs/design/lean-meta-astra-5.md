
codex
**1. `ArmCorrect` is substantially right for a fixed child-form arm, conditional on faithful metadata and translation.**

- The fuel quantifiers are right: `∃ N, ∀ fuel ≥ N` requires eventual agreement, not accidental agreement at one fuel. `N` may depend on inputs and `rest`; this is termination, **not a work bound**. The existential `v` is fixed by the dispatch equation. [Pathway:62](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Pathway.lean:62)
- Keep universal `rest`, including malformed logical values. Untaken children should be irrelevant. But this establishes **output independence**, not absence of reads: reading and discarding a child satisfies it. Section 9.3’s claim that any such read supplies a counterexample is too strong. [§9.3:248](/Users/ember/dev/fn/build/coordinator/fn2/LEAN-METATHEORY.md:248)
- Framing **unreturned**, rather than merely untaken, children is correct: read-only inputs also need preservation. `normalize` correctly handles a handler returning only its bare wake value. [Pathway:51](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Pathway.lean:51)
- Establish metadata well-formedness separately: child form; distinct tuple/takes/returns; signature names contained in the tuple; actual formal/output correspondence; `sig.results = nOuts observe`; faithful guard lookup and declaration membership. `Sig.results` is presently ignored. Missing guards make the implication vacuous, and `KindCorrect` itself does not restrict to child form. [Arms:75](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:75), [Pathway:74](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Pathway.lean:74)
- Add exact result shape. `project` silently supplies `nil` for missing children; `frameKept` checks only the first occurrence of each name. These are harmless once shape/uniqueness are proved, but should not be implicit. [Pathway:45](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Pathway.lean:45)

I would package the conclusion as:

```text
∀ pre given, InputShape pre given → Guard_FN (pre ++ given) →
  ∃ v, fns FN (pre ++ given) = some v ∧ NarrowResultShape v ∧
    ∀ rest, ∃ N, ∀ fuel ≥ N,
      runArm … (widen pre given rest) fuel =
        .ok (reconstructFullResult (entering given rest) (normalize v))
```

Here reconstruction preserves every unreturned child and replaces returned children by name. Under valid metadata and exact shapes, this is your projection-plus-frame statement.

The 963 checks establish guard inhabitation and finite observations, **not instances of the entire quantified proposition**. Moreover, the measured frame uses truncating `zip`, unlike `frameKept`: a shortened output can escape that check. [§9.3:250](/Users/ember/dev/fn/build/coordinator/fn2/LEAN-METATHEORY.md:250), [Measure:142](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Measure.lean:142)

**2. The reader is not exact over the whole advertised vocabulary.**

The logical values of `+`, `*`, unary/binary `-`, `1+`, `1-`, comparisons, equality, `and`, `or`, and well-formed `cond` agree on the representable subset. In particular, unary `+/*` really do insert `0/1`; `=` and `/=` logically use equality, without numeric coercion; singleton `cond` returns its test value. `member-eq → MEMBER-EQUAL` is also logically correct, although their execution guards differ. [Arms:248](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:248), [ACL2 definitions](https://raw.githubusercontent.com/acl2/acl2/master/axioms.lisp)

The divergences are:

| Form | Finding |
|---|---|
| `logand`, `logior` | **Reject valid zero/unary forms.** Empty results are respectively `-1` and `0`; unary forms return their argument logically, with an integer guard. Binary and longer expansions agree. [Arms:296](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:296), [axioms:17076](/Users/ember/dev/acl2-fix/axioms.lisp:17076) |
| `progn` | **Invented semantics.** ACL2’s `progn` is an event-sequencing macro expanding to `progn-fn`, not expression sequencing returning the last argument. Remove it from this expression vocabulary or explicitly define a different DSL construct. [Arms:302](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:302), [axioms:7128](/Users/ember/dev/acl2-fix/axioms.lisp:7128) |
| `prog2$` | Last-value semantics is logically correct, but it must have **exactly two arguments**; the reader accepts any positive count. It does not model first-argument execution/effects or guard checking. [Arms:302](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:302), [axioms:3504](/Users/ember/dev/acl2-fix/axioms.lisp:3504) |
| `mv` | List encoding is correct for legal uses; zero/unary forms are wrongly accepted. ACL2 requires at least two values and enforces multiple-value context compatibility; the reader has no such discipline. [Arms:299](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:299), [axioms:6763](/Users/ember/dev/acl2-fix/axioms.lisp:6763) |
| `case` | Valid terminating pure cases have equal values, including a bare `nil` key matching nothing. But the reader duplicates compound-key evaluation instead of binding it once, accepts missing keys and invalid/non-`eqlable` patterns, and reads bodies of empty-key clauses that ACL2 discards. Duplication matters for cost, even when values agree. [Arms:279](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:279), [axioms:6851](/Users/ember/dev/acl2-fix/axioms.lisp:6851) |
| Syntax generally | `toList` discards dotted tails: malformed applications, quotations and clauses can be accepted. Vocabulary functions receive no reader-time arity check, and variable binding legality is deferred. Thus `readKind` is not an ACL2 admission checker. [Arms:243](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:243), [Val:78](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/ACL2/Val.lean:78) |
| Constants | Only integer-valued constants are exported/read. Legal symbolic, string, character and cons-valued constants fail; non-ACL2-package constants are also excluded by the printer. Rational/complex constants cannot inhabit `Val`. [Arms:238](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:238), [print-world:309](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/emit/print-world.lisp:309) |
| Index constants | `ROW-SLOT → SLOT`, kind → `KIND`, ordinal → `ORDINAL` correctly implement the **child-form DSL convention**, not ordinary ACL2 constant evaluation. Quoted symbols correctly remain quoted. The current ordinal→kind change at generator line 123 is the running mutation, not a reader defect. [Arms:233](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:233), [machine-arms:54](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/books/machine-arms.lisp:54) |
| Pure operations | **Argument placement differs:** the reader interleaves children according to `stobjsIn`; the generator appends all children after value arguments. They agree only for trailing-stobj signatures. Either require that layout explicitly or fix the generator. Rejecting child outputs is right; multiple non-child outputs still need context validation. [Arms:309](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:309), [machine-arms:190](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/books/machine-arms.lisp:190) |

Also, accepting a vocabulary name does not guarantee executable semantics: `ZIP`, `POSP`, and `ASH` are accepted but absent from this emitted dispatch and the natives. Root the full supported vocabulary, or make closure completeness explicit. [Arms:211](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:211), [Val:259](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/ACL2/Val.lean:259)

**3. Decision 7 removes expression-rewrite sharing, not declaration-decoding or semantic-dependency sharing.**

Still shared/trusted:

- `fn2-arms-options`, function naming, child-form detection, **whole-tuple construction**, and narrowed signatures. Tuple construction matters especially: a child absent from `k.tuple` is outside the frame theorem entirely. [print-world:172](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/emit/print-world.lisp:172), [print-world:207](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/emit/print-world.lisp:207)
- Lisp `meta-step` plus Python `step` decode the declaration before Lean sees it. For example, literal `:when nil` is already erased into absence. PW3 proves the meaning of **that decoded object** unless this bridge is validated independently. The generated environment is still constructed, but `meta-expr/meta-next` now ignore it. [print-world:107](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/emit/print-world.lisp:107), [print-world:130](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/emit/print-world.lisp:130), [emit_embed:296](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/emit/emit_embed.py:296)
- Phase constants, column descriptions, operation resolution/signatures/answers, wait registry, translated operations/accessors/setters, natives and guard translation. Shared operation implementations are appropriate for proving arm composition, but their bugs are not independently detected by PW3. They remain PW1/PW2 or operation-contract obligations. [print-world:215](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/emit/print-world.lisp:215), [print-world:236](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/emit/print-world.lisp:236)

**4. Feasible, but replace “unfold and simp” with a small reusable proof interface first.**

First totalize **`readNext` too**, alongside `readExpr` and `Term.eval`. Prefer structural/size recursion with list helpers; these traverse finite syntax, so extra fuel is unnecessary. `partial` definitions cannot supply unfolding equations to kernel proofs. [Arms:326](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:326), [Val:319](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/ACL2/Val.lean:319), [Lean reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)

Then generate **per-name dispatch and guard equations**. A `match` is reasonable, but repeatedly unfolding a 758-entry dispatch is unnecessary; symbolic arm proofs should rewrite directly to the named callee.

Keep list-valued stobjs for PW3. Prove accessor/update/frame and checked-write lemmas once; do not unfold array recognizers or list traversal throughout every arm. Leave operations opaque when both sides call the same function. In particular, scribe’s fill/patch/verify are shared `.do_` callees, not interpreter `:repeat` loops: their internal induction belongs to PW1 adequacy, not each arm proof. [LayerAKinds:130](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Instances/LayerAKinds.lean:130)

Finally prove successful-run fuel stability and construct bounds compositionally. Change the repeat helper’s zero-fuel success to an error, or prove that branch cannot yield a successful composed arm; its surrounding continuation currently also consumes fuel, so **local success is not itself a demonstrated truncation counterexample**. [Arms:594](/Users/ember/dev/fn/build/lanes/fn2/lean/fn2/meta/Fn2/Arms.lean:594)
