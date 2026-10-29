I found **no definite elaboration or proof-script failure in the current files**. Consequently, I have no required replacement text for an elaboration blocker. This is a source review, not certification: execution cost and elaborator resource limits remain untested.

I did find substantive overclaims: **`restrict` is not the advertised cartesian lift; `Diamonds` does not establish enabledness preservation; and `registry_wf` checks only the modeled subset of the macro guard.** Several witness statements also need strengthening to meet the stated whole-antecedent-and-conclusion discipline.

I read all six requested files, the requested regions of `LayerA.lean`, and all of `emit_lean.py`. I did not run Lean or edit files.

**File-by-file elaboration review**

1. **[Decl.lean](/Users/ember/dev/fn/build/lanes/fn2/lean-meta/fn2/meta/Fn2/Decl.lean): no definite blocker.**

   - Lines 59–73, 84–93, 192–203 and 219–223: parameterized `deriving DecidableEq, Repr` is supported. The generated instances acquire the necessary parameter instances. In particular, `ColKind S` can use decidable equality for `List S`.
   - Lines 162–169 and 182–186: both well-formedness predicates are `abbrev`s. Instance search can expose their conjunctions and bounded quantifiers.
   - Line 185 does **not** require `DecidableEq (ColumnsDecl S)`. Lean’s bounded-list existential instance decides the predicate at each list element; it does not implement this by deciding equality between arbitrary rows.
   - `List.Nodup`, bounded universal quantification, and bounded existential quantification have computational instances in core. See [List.Basic.lean:872](/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/List/Basic.lean:872) and [List.Basic.lean:1403](/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/List/Basic.lean:1403).
   - Lines 209–210: `List.flatMap` is available through the default imports. Its logical definition is `flatten (map ...)`; the compiler implementation supplied by core is separate. Nothing here requires the incorrect assumption that an append with a variable left operand reduces to a constructor.
   - The constructor field named `case` is legal in this position.

   **Required elaboration replacement: none.** The specification discrepancy in `WF` is discussed below.

2. **[Square.lean](/Users/ember/dev/fn/build/lanes/fn2/lean-meta/fn2/meta/Fn2/Square.lean): no definite blocker.**

   - Lines 68–75 use the installed Mathlib API correctly: `CategoryTheory.RelCat`, `RelCat.Hom.ofRel`, and `.rel` exist. `RelCat` is definitionally `Type u`, so supplying `A` and `B` as objects is valid.
   - `Tight.toRelCat_comp` is genuinely `Iff.rfl`. Mathlib’s composition has the order
     ```lean
     ∃ b, R a b ∧ S b c
     ```
     matching this file. See [RelCat.lean:49](/Users/ember/dev/minidregg/.lake/packages/mathlib/Mathlib/CategoryTheory/Category/RelCat.lean:49) and [Data/Rel.lean:148](/Users/ember/dev/minidregg/.lake/packages/mathlib/Mathlib/Data/Rel.lean:148).
   - The current names avoid the suspected collisions: the relation type is `Tight`, and the identity functions are named `ident`. There is no problematic unqualified root `Rel` or `id` use here.
   - Lines 100, 113, 120 and 127: `intro`/`rintro` can expose the binders of `Sq`. Applications such as `h₁ a b a' hR hfa` likewise unfold its function type.
   - Lines 101–107: `cases hfa : f a` does not automatically rewrite the pre-existing `hf` hypothesis. The explicit `simp ... at hf` and `simpa ... using hf` are appropriate.
   - Lines 121–130: conversion through `Loose.ident` and `Tight.ident` makes the `Option.some.inj` and `have e := hab` uses valid.
   - Lines 135 and 145: `rfl` works by proof irrelevance. The interchange expressions have the same square boundary.
   - Lines 154–168: the append proof uses propositional associativity where necessary. In `run_pair`, `congr 1` leaves the function equality that the following `funext` proves; binding an unknown `Option` to `some` is not already definitionally the identity.
   - Lines 178–203: the induction hypotheses and applications of `Sq.seq` have the required boundaries.

   **Required elaboration replacement: none.** The framing claim is nevertheless incorrect.

3. **[Coherence.lean](/Users/ember/dev/fn/build/lanes/fn2/lean-meta/fn2/meta/Fn2/Coherence.lean): no definite blocker.**

   - Lines 50–53: `Frame.{u}` has type `Type (u + 1)`, with `State` and `Label` in `Type u`. Its uses are universe-consistent.
   - Lines 74–77: both list equalities are definitional. The four `run_append` rewrites account for the outer and inner concatenations on both sides.
   - Lines 95–111: the transported run equality, application of `Sq.run`, and extraction of final-state equality are correctly oriented.
   - Lines 136–139, 206, 219–222 and 325: the concrete frames are `abbrev`s. In particular, `twoRecv.Label` reduces to `Conn` at the transparency needed for instance search.
   - Lines 145–167: `intro` exposes `Diamonds`; application exposes `footIndep`. The frame/update rewrites establish the stated commutation equation.
   - Lines 178–199 and 230–246: the `have ... := ...` and `show` conversions through `Action.incr`, frame abbreviations, and preceding structure fields are valid.
   - Lines 240 and 245 use `simp [...] <;> omega`, so there is no following-`omega` failure if `simp` closes the goal.
   - Lines 287 and 302 use disjunction destruction followed by substitution. The current files contain no problematic `rcases ... with rfl` variant.
   - Lines 349–353: after reverting `e'`, the target is a closed implication between concrete observations. Its type does not depend on the proof of the assumed diamond; `decide` can evaluate it.
   - Lines 373–387: the catalogue proof and the uncovered-case contradiction have the expected reductions.

   **Required elaboration replacement: none.** `Diamonds`’s documentation overstates its meaning.

4. **[Conservative.lean](/Users/ember/dev/fn/build/lanes/fn2/lean-meta/fn2/meta/Fn2/Conservative.lean): no definite blocker.**

   - Lines 62–68: the explicit `rw [hs] at h'` steps are necessary and valid. `cases hs : ...` generalizes the target expression, rather than rewriting all existing hypotheses.
   - Lines 70–75: projection transport and the successful `Option.bind` reduction match the induction hypothesis.
   - Lines 85–96: both directions of `conservative` use the correct simulation/lifting direction.
   - Lines 130–150: the structure-field proofs reduce through `base`, `revised`, and `translate4`. The `lift` field’s `Option.some.inj h` has exactly the required orientation.
   - Lines 161–164: **`subst e` retains `n` and eliminates `s'`**. Lean 4.30’s `substEq` checks the right-hand variable first. Thus `show n = n + 0` is valid. See [Subst.lean:173](/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Lean/Meta/Tactic/Subst.lean:173).
   - Lines 167–171: the recursive run and `postsCount` reduce as claimed.
   - Lines 182–194: both negative witnesses reduce to contradictory natural-number equalities.

   **Required elaboration replacement: none.** The run-property theorem is soundly scoped; some surrounding prose should be narrower.

5. **[Param.lean](/Users/ember/dev/fn/build/lanes/fn2/lean-meta/fn2/meta/Fn2/Param.lean): no definite blocker.**

   - Lines 34–42 and 100–111: the recursive occurrences beneath `Obs → ...` and `Nat → ...` are strictly positive. Calling the recursion on `k observation` is supported structural recursion through a function-valued constructor field.
   - The corresponding induction hypothesis in the `observe` case is indexed by the observation. Consequently, line 62’s `ih _ _ _ hst` has the right number and order of arguments.
   - Lines 85–92: multiplication by the numeral `2` and division by the positive constant `2` fall within `omega`’s arithmetic support.
   - An explicit Mathlib import is not required to obtain `omega`; the default `Init` imports include its support.
   - Lines 117–120: the two runs reduce to `1` and `2`; `decide` is applicable.

   **Required elaboration replacement: none.**

6. **[LayerAFacts.lean](/Users/ember/dev/fn/build/lanes/fn2/lean-meta/fn2/meta/Fn2/Instances/LayerAFacts.lean): no definite blocker.**

   - Lines 22, 27, 32, 48 and 53: **`decide +kernel` exists in Lean 4.30**. It builds a proof checked using kernel reduction; it is not `native_decide`. See [Init/Tactics.lean:1315](/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Tactics.lean:1315) and [Decide.lean:101](/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Lean/Elab/Tactic/Decide.lean:101).
   - The 376-constructor enum does not inherently prevent reduction. This version’s enum-specific derived equality compares constructor indices and returns `isTrue`/`isFalse`; its proof fields do not obstruct deciding the enclosing proposition. See [DecEq.lean:264](/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Lean/Elab/Deriving/DecEq.lean:264).
   - The finite list checks do not require a `Fintype Sym` instance.
   - Lines 37–40: the four numeral inhabitants of `Fin 4` are valid.
   - Lines 59–63 are a correctly typed specialization of `Sq.run_cover`.

   I independently checked the input data: the modeled `WF` conjuncts hold, qualified identities are unique, bare names repeat, and there are 22 phase cases plus 9 event cases. This supports the truth of the closed propositions; it does not measure kernel evaluation cost.

   **Required elaboration replacement: none.**

7. **[LayerA.lean](/Users/ember/dev/fn/build/lanes/fn2/lean-meta/fn2/meta/Fn2/Instances/LayerA.lean:774) and [emit_lean.py](/Users/ember/dev/fn/build/lanes/fn2/lean-meta/fn2/meta/emit/emit_lean.py): no current-output blocker.**

   Expected types propagate correctly through the generated list and structure fields:

   ```lean
   ⟨.s_phase, (.enum .s_fn2_listener_state [...])⟩
   ```

   has expected type `Column Sym`, giving its components types `Sym` and `ColKind Sym`.

   ```lean
   budget := ⟨4096, 32, 4⟩
   ```

   supplies the three `Nat` fields of `Budget`.

   ```lean
   (.s_generation, ⟨"FN2-MACHINE-INITIAL-GENERATION"⟩)
   ```

   has expected type `Sym × Opaque`.

   I regenerated the output into an in-memory string, without writing a file. It matched the existing `LayerA.lean` byte-for-byte.

   **Required elaboration replacement: none.** I cannot determine resource-limit failures for enum derivation or registry evaluation without running the toolchain.

**Statement and witness findings**

**1. `Square.lean:85–93`: the weakest-precondition theorem is valid; the cartesian-lift claim is false for these partial transitions.**

`Sq.iff_le_restrict` establishes precisely a pointwise greatest input relation satisfying a simulation obligation. It does not establish the universal factorization required of a cartesian cell.

There is a concrete obstruction. Make all state types `Unit`, and write `⊥` for the nowhere-enabled transition. Take

```text
f = identity     g = ⊥
f' = ⊥          g' = identity
R'' = True
```

Then, at the unique state pair,

```text
restrict f g (restrict f' g' R'') = False
restrict (f ; f') (g ; g') R''   = True
```

The composite top transition never fires, making the second obligation vacuous. Factoring through the intermediate square would require the first bottom transition to fire, which it cannot.

Thus these proposed restrictions do not compose as cartesian lifts must. Thinness does not repair the missing existence of a factorization.

Replace the docstring at lines 85–86 with:

```lean
/-- The greatest input relation making a forward-simulation square with the given
top transition, bottom transition, and output relation. Equivalently, this is the
weakest precondition on the input pair for that simulation obligation. -/
```

Keep `Sq.iff_le_restrict` unchanged. Remove the claim that this construction establishes a **framed** double category from the module introduction. The square-pasting and interchange results remain useful and valid.

**2. `Coherence.lean:63–66`: equality of two-step partial runs does not imply enabledness preservation.**

Consider two distinct labels with the same transition on `Bool`:

```lean
fun s => if s then none else some true
```

Both labels are enabled at `false`. Either one disables the other. Nevertheless, both two-step runs are `none` from every state, so the current `Diamonds` predicate holds for every declared pair.

This refutes “so neither enables nor disables the other and, enabled together, they reach one state.” It does **not** refute `trace_run`: equality of partial composites is sufficient for that theorem.

The exact documentation replacement for the current predicate is:

```lean
/-- Every declared pair has equal two-step partial runs from every state.
This includes agreement on failure of the composite run. -/
```

If G2 is intended to include the advertised enabledness condition, introduce the stronger predicate:

```lean
def Enabled (F : Frame.{u}) (t : F.Label) (s : F.State) : Prop :=
  ∃ s', F.step t s = some s'

def IndependentDiamonds (F : Frame.{u})
    (I : F.Label → F.Label → Prop) : Prop :=
  Diamonds F I ∧
  ∀ t v, I t v →
    (∀ s s', F.step t s = some s' →
      (Enabled F v s ↔ Enabled F v s')) ∧
    (∀ s s', F.step v s = some s' →
      (Enabled F t s ↔ Enabled F t s'))
```

I would strengthen **`footprint_diamonds`** to establish `IndependentDiamonds`. Its existing `gα` and `gβ` arguments contain the essential enabledness-preservation reasoning. Keep `trace_run`’s weaker sufficient hypothesis unless consumers actually need the stronger one.

**3. `coherence` proves conditional successful-run simulation, with an interpreted reference word.**

The theorem does not assert that arbitrary schedules complete. It assumes a successful implementation run. Also, `w` and `w'` are both implementation-label words; the reference executes `expand C.interp w'`. There is no reference-side trace-equivalence relation in the statement.

Replace the docstring at lines 91–94 with:

```lean
/-- From a G0-related pair, G1 squares and implementation diamonds transport
every successful implementation run along `w` to a successful reference run
along `expand C.interp w'`, whenever `w` and `w'` are trace-equivalent.
The resulting observations are equal. -/
```

The theorem itself need not be weakened or repaired.

**4. `Decl.lean:158–169` and `LayerAFacts.lean:21–22`: `registry_wf` does not establish every `defmachine` guard.**

The modeled predicate omits checks that the actual macro performs, including symbol/keyword restrictions and initial-value syntax. It also does not require the first column’s **name** to be `phase`, or require the common columns to be present.

For example, retain a machine’s states and continuations, replace its columns by one enum column with those tags, give that column an arbitrary name, and set `initial := []`. Its `MachineDecl.WF` can still hold despite the absence of every common field.

The underlying model cannot recover initial-value validity from arbitrary `Opaque.text`. This needs additional representation and a bridge to the macro guard, not a different tactic.

Replace the `MachineDecl.WF` docstring with:

```lean
/-- Recorded-row consistency: nonempty distinct states with at most 256 tags;
continuation keys equal the states in order; distinct observation, column, and
initialization keys; initialization keys name columns; and the first column is
an enum whose tags equal the states. -/
```

Replace the `registry_wf` docstring with:

```lean
/-- The emitted rows satisfy the recorded-row and cross-row consistency
conditions represented by `Registry.WF`. -/
```

The corresponding “the guard ... restated” claim in `Decl.lean`’s introduction also needs correction. Retain the existing theorem as a control while extending the model toward the full guard claim.

**5. `LayerAFacts.lean:9–14`: the connection and mutation claims are too broad.**

`q1_licensed` specializes **`Sq.run_cover`**. It does not instantiate `coherence`, `conservative`, or `abstraction` for the ACL2 implementation. Its transition systems, relation, interpretation, and square proofs remain parameters.

The mutation-control claim also has an immediate counterexample: change a machine’s `capacity` text, an owed formula, or a continuation’s function name while keeping its phase key. The current controls need not fail. Those values are not constrained by the asserted properties.

Replace lines 9–14’s claim with:

```text
These are pinned structural regression controls over the emitted registry.
`q1_licensed` specializes `Sq.run_cover` to its catalogue; it remains conditional
on the correspondence's transitions, relation, interpretation, and per-case
square proofs.

A mutation is detected when it changes one of the properties asserted below.
```

The theorem is correctly conditional. It supplies no proof that the 39 ACL2 obligations are discharged.

**6. `Conservative.lean`: the theorem establishes semantic run conservativity, not a formal proof-system conservativity result.**

The quantified property equivalence is substantive and correctly proved. However:

- `Extension.step` is forward simulation of successful extension steps, not equality of partial transitions. A new label can be disabled even when its translated base word succeeds.
- No syntax, derivability relation, or soundness/completeness bridge for theories is represented.

I would retain `conservative`, qualify the introductory prose accordingly, and expose its concrete semantic content with this additional statement:

```lean
theorem runs_exactly {Base Ext : Frame.{u}}
    (X : Extension Base Ext) (s₀ : Base.State)
    (w : List Base.Label) (b : Base.State) :
    run Base.step w s₀ = some b ↔
      ∃ w' x',
        run Ext.step w' (X.convert s₀) = some x' ∧
        expand X.translate w' = w ∧
        X.proj x' = b
```

This is a proposed statement; its proof can use `lift_run`, `expand_map`, and `Sq.run` already present.

**7. None of the principal theorems appears logically vacuous, but the exported witness statements do not consistently meet the requested packaging discipline.**

The concrete `sumCorr`, `revision`, and `counter_doubled_related` constructions provide meaningful inhabited certificates. The issue is that some advertised witness theorems export only fragments of the promised package.

I would make these changes:

- **`twoRecv_routes_agree`:** add the declared independence/diamond premise, explicit trace equivalence, and a successful concrete run. Its present statement exports distinct words and equality of run functions, but neither trace equivalence nor successful execution.
- **Add `twoRecv_coherence_witness`:** use the zero counters, the two opposite receive orders, final counters equal to one, and reference total two. Assert G0, diamonds, trace equivalence, successful source and interpreted target runs, and observation equality together. `sumCorr` supplies the G1 and observation-edge certificate through its type.
- **`acceptClose_routes_disagree`:** the current result is a useful observable counterexample, but it does not package a correspondence satisfying all the retained hypotheses of `coherence`. I would restate the tooth as:

  ```lean
  theorem acceptClose_without_g2 :
      ∃ (C : Correspondence acFrame acFrame Nat)
        (a b a' : acFrame.State) (w w' : List ACLab),
        C.R a b ∧
        TraceEq differentMachine w w' ∧
        run acFrame.step w a = some a' ∧
        ¬ (∃ b',
          run acFrame.step (expand C.interp w') b = some b' ∧
          C.obsA a' = C.obsB b')
  ```

  Choose the identity correspondence, singleton label interpretation, and admitted-count observation. This directly asserts every remaining hypothesis and failure of the conclusion after removing G2.

- **`footprint_diamonds`:** the accept/close example supplies a tooth for dropping footprint independence while retaining `Respects`. Add a separate tooth for dropping `Respects`: declare empty read/write footprints for two always-enabled actions, one setting a position to zero and the other setting it to one. The declared footprints are independent, but the runs disagree. This tests the other essential obligation.
- **`badRevision_breaks_counts`:** package it with the retained conversion, translation, and lifting conditions, plus the positive base property. The existing two negative theorems identify the right failure, but do not themselves assert that complete removal-of-G1 package.
- **`peek_breaks_abstraction`:** this is a valid counterexample to extending the client interface with raw inspection. It is not a counterexample within `Client` after removing a primitive-relatedness obligation. For that additional tooth, use identity observations and equal initial states with one implementation incrementing by one and the other by two; the permitted client “command, then observe” separates them when command preservation is dropped.

`Sq.thin` and `Sq.interchange` are deliberately proof-irrelevance results, exactly as their docstrings say. They should be classified as structural laws, rather than presented as behavioral evidence about fn2 execution.