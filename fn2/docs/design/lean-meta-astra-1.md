# Draft sections for LEAN-METATHEORY.md

**ACL2 owns the executable instances and their proofs; Lean owns the mathematical statements about how such instances compose.** The DSL supplies the presentation to both. A Lean theorem explains which local obligations suffice for a specified global conclusion. It does not discharge those obligations merely because their names occur in the registry.

I agree with that division of labour. I would amend “ACL2 is wrong for the frame” to “ACL2 is the wrong engineering home for this frame.” First-order logic can describe declarations, syntax and interpretations as data. The issue is the machinery we would have to build and maintain to reason about them. Conversely, some reusable metatheory already belongs comfortably in ACL2: an abstract fold theorem with constrained functions, instantiated for concrete functions, is exactly the right tool.

All code citations below refer to **`137695dfc18a398f257a8297cf3395524256364c`**, the value of `origin/fn2/main` inspected for this draft. Paths abbreviated to `machines.lisp:234–240`, for example, mean `fn2/books/machines.lisp` at that revision. Design-document citations refer to the supplied coordinator notes. Proposed Lean names and structures below are interface specifications, not a report that the Lean author has implemented or proved them.

## A. The division of labour

A seat can classify a new obligation by its subject:

1. **A statement about named ACL2 functions, one generated representation, one concrete square, or one admitted book belongs in ACL2.** This includes the applicability conditions of a functional instantiation, the relation established by a converter, guard obligations, arithmetic bounds, and preservation of outputs and effects.
2. **A statement quantifying over declaration presentations, theories, interpretations, clients of an abstract interface, or constructions of diagrams belongs in Lean.** Its hypotheses must describe the properties the ACL2 instances supply.
3. **A statement about the correspondence between an exported row and its ACL2 subject belongs to the bridge between them.** It is neither an ordinary execution theorem nor a consequence of Lean’s categorical library.
4. **A claim about physical execution, environmental evidence or eventual progress does not become a coherence theorem by being registered.** Its adapter assumptions, persistence model or fairness premises remain explicit.

“Quantifies over every execution” does not by itself mean Lean. ACL2 should prove a named machine’s theorem for every admitted execution. The distinction is between quantifying over executions of an instance and quantifying over the presentations and interpretations from which instances are constructed.

Functional instantiation is the ACL2 realization of a theory morphism in this design: substitute concrete functions for constrained functions and discharge the constraints. SOFT can organize families of these substitutions without extending ACL2’s logic. APT can generate representation transformations and their theorem instances. ATC can generate correctness theorems relating supported ACL2 functions to its formal C semantics. These remain ACL2 proof routes, with their own applicability hypotheses; Lean does not replace them. See the official documentation for [functional instantiation](https://acl2.org/doc/index-seo.php?xkey=ACL2____FUNCTIONAL-INSTANTIATION), [SOFT](https://acl2.org/doc/index-seo.php?xkey=SOFT____SOFT), [APT](https://acl2.org/doc/index-seo.php?xkey=APT____APT), and [ATC’s generated theorems](https://acl2.org/doc/index-seo.php?xkey=C____ATC).

The five worked obligations are:

| Obligation | ACL2’s instance | Lean’s theorem | What the combination establishes |
|---|---|---|---|
| **The 39 Q1 dispatch cases** | Bind each case to a statement about the actual concrete transition, accounting operation, reference transition and loop relation. Establish the case selectors’ coverage and any exclusions. The machine declarations supply **22 continuation labels and 9 observed-event labels**: listener 2+2, echo 6+4, scribe 14+3 (`machines-a.lisp:17–60`). The remaining eight labels belong to the router and executor in DSL-METATHEORY §3.5. | A covered family of valid step simulations, together with entry and exit obligations, composes along legal finite executions. The theorem quantifies over the case family and its interpretation. | **The 39 labels are a catalogue for Q1, not 39 proofs or 39 independent semantic guarantees.** Missing selectors, omitted branches and unbound contracts remain missing premises. |
| **`fn2-turn-refinement`** | Prove the actual statement in `reference.lisp:242–255`: equal status, observation count, visit count and action count; both resulting cores well formed; the resulting representation relation; action and work bounds. | Explain the composition from local steps through the loop and its boundaries. A general composition theorem does not supply the instance’s accounting or stopping facts. | The existing turn statement is discharged only when its actual antecedent and every conclusion are established. EXECUTION-MODEL §4’s broader refinement contract remains broader than this particular owed statement. |
| **G2’s accept/close candidate** | Construct both legal execution orders at a suitable state and compare the selected observation contract. The shared resource is real: admission reads the free head and active/connection counts and updates allocation state (`machines-a-run.lisp:81–106`); release can return the echo row to the free list and decrements the active count (`machines-a-run.lisp:126–146`). | Valid adjacent swaps preserve observations along any explicitly generated sequence of swaps. Also prove a toy counterexample to the proposed inference “different machines implies independence.” | **No accept/close diamond is licensed merely by distinct machine identities.** The full client-visible contract distinguishes refusal followed by release from release followed by admission. A false candidate is classified dependent, not added as an assumed generator. |
| **Q9’s v3/v4 extension** | For an implemented converter and event interpretation, establish initialization, `π(step₄(s,e)) = Fold₃(π(s),h(e))`, and agreement of old observations. These are future obligations for the specified migration, not existing production proofs. | Prove separately that every model of the old presentation has an expansion retaining its old interpretations; and that the step equation lifts over admitted suffixes. | **Model conservativity, converter correctness and preservation of old behaviour are three obligations.** An `ext` label proves none of them. The new thread observations are outside the old-observation conclusion. |
| **DSL-METATHEORY decision 1: shared handlers** | State the precise refinement being checked and supply an independent semantic contract where required. Q1 deliberately shares observation and machine semantics while independently selecting transitions (`reference.lisp:92–142`). | Prove representation independence for clients in a specified interface language whose primitives respect the relation. Alternatively, prove correctness of a specified generator relative to its declaration semantics. | Shared declarations can support substantive representation and compiler refinement. **Q1 alone does not independently validate the shared handlers’ intended behaviour.** An additional semantic oracle or proof supplies that judgment. |

For Q1, the loop relation must match the implementation boundary. The concrete loop accounts work after each transition, including a u60 overflow branch (`executor.lisp:103–132`). The reference loop accumulates work in arguments and writes the counters on exit (`reference.lisp:145–157`). Therefore the proposed intermediate relation is:

```text
LoopRelated(ctx, concrete, reference, lists) :=
  RepresentationRelated(
    concrete,
    NormalizeReferenceWork(reference, ctx.refBytes, ctx.refSteps),
    lists)
```

A case obligation has the shape:

```text
LoopInv(ctx,c,r,lists)
∧ Continue(ctx,c,r,lists)
∧ CaseSelected(case,ctx,c,lists)
⇒
  transition result tuples agree
∧ the named output/effect contract holds
∧ LoopInv(ctx', AccountWork(c'), r', lists').
```

These helpers are the proposed contract from DSL-METATHEORY §3.3. The emitter substitutes the case identity; it does not invent a stronger precondition to make a difficult case pass.

The bridge to `fn2-turn-refinement` separately owes entry, selector coverage, preservation, termination, status agreement, counter finalization and the numerical bounds. If the current antecedent permits an overflow mismatch, the instance must expose and resolve it. A Lean theorem about a narrower invariant cannot silently discharge the existing broader statement.

For Q9, the two Lean conclusions should have visibly different types:

```text
ModelExpansion:
  ∀ M₃ : Model T₃, ∃ M₄ : Model T₄, reduct M₄ ≅ M₃

OldBehaviourPreserved:
  ∀ admitted s₄ es,
    π(Fold₄(s₄,es)) = Fold₃(π(s₄), concatMap h es).
```

The first retains the old logical sorts and operations. `State₄ = State₃ × ThreadAnnotations` is an additional representation, not a replacement of the old sort masquerading as an expansion. The second needs the per-event equation and admissibility hypotheses. This is the distinction already made in MODAL-KERNEL §4.4.

## B. The tenth artifact: the declaration’s Lean presentation

The tenth artifact is **a Lean term describing the declaration and its obligations**. It is not a second implementation of its ACL2 functions.

There are three layers:

```text
ACL2 world tables
    ↓ export and schema decoding
Lean presentation data
    ↓ an explicitly supplied interpretation
semantic declarations, morphisms and square propositions.
```

The first arrow must preserve names, payloads and ordering. The second assigns mathematical meaning. Combining these arrows invisibly would make an opaque handler name appear to carry a proof of its behaviour.

### The current rows

The initial exporter has concrete sources:

- `fn2-machine-kinds`, written by `fn2-machine-events`, contains `:states`, `:columns`, `:accounts`, `:budget`, `:continuations`, `:observes`, `:capacity`, `:initial`, `:layout`, `:packed`, `:calling-convention` and `:obligations` (`machines.lisp:203–240`).
- `fn2-columns` contains `:columns`, `:column-reasons`, `:rows-bound`, `:extra-fields`, `:extra-field-reasons` and `:init-name` (`columns.lisp:602–605`).
- `fn2-core-children` contains `:stobj`, `:init`, `:profilep`, `:reference`, `:order` and `:why` (`core-children.lisp:25–40`).
- `fn2-owed` contains `:vars`, `:formula`, `:teeth`, `:doc` and `:status`. Its declaration introduces a `$OWED` function and a table row, not a theorem (`owed.lisp:11–22`).

These are the implemented schemas at the inspected revision. The common declaration keys, callback registry, correspondence registry and `fn2-squares` schema below are proposed extensions.

The existing export pattern is suitable: `tools/owed-export.lsp` loads the relevant books, reads the world table, and writes it through ordinary top-level I/O (`tools/owed-export.lsp:5–16,35–57`). The Lean exporter should follow that separation. It should export structured data rather than parse the Markdown owed report.

### Names, terms and common metadata

The presentation needs these distinctions:

```text
Acl2Name       = package name + symbol name
DeclId        = declaration kind + Acl2Name
FunctionRef   = reference to an ACL2 function identity
TermRef       = reference to an uninterpreted ACL2 syntax payload
TheoremRef    = reference to an admitted-event claim and its statement payload
ContractId    = identity of a specified observation/relation contract
```

The encoding must be injective on ACL2 names. Lowercasing, dropping package names or replacing punctuation without reversible escaping is insufficient.

Qualified declaration identities are necessary because `defmachine` emits a `defcolumns` declaration under the same name (`machines.lisp:203–215`). Thus these are distinct:

```text
(:machine ACL2::FN2-ECHO)
(:columns ACL2::FN2-ECHO)
(:core-child ACL2::FN2-ECHO-TABLE).
```

The proposed common structure carries `decl-id`, `layer`, `book`, `requires`, `generated` and `cases`, using the names of the corresponding proposed ACL2 keys. A mechanically escaped Lean field such as `«decl-id»` preserves that correspondence.

Missing metadata remains missing. The exporter may derive a declaration kind from the source table, but it must not invent a function signature, dependency or proof status absent from the world and the declared export schema.

An export envelope additionally records the implementation revision, schema version, loaded-book closure and assembly section. These identify the snapshot; they are not properties of an individual declaration.

### Structures for all fourteen declaration kinds

Each row below specifies a distinct Lean structure. `TermRef` and `FunctionRef` are data, never implicit Lean implementations. For planned forms, this is the target schema from DSL-METATHEORY §1.1, §1.2 and §5.7.

| Kind / Lean structure | Payload fields |
|---|---|
| **`columns` / `ColumnsDecl`** | `columns : List ColumnSpec`; `column-reasons`; `rows-bound : Nat`; `extra-fields`; `extra-field-reasons`; `init-name : FunctionRef`. Extra-field syntax is preserved, including syntax the typed decoder does not yet interpret. Current keys: `columns.lisp:602–605`. |
| **`core-child` / `CoreChildDecl`** | `stobj : Acl2Name`; `init : TermRef`; `profilep : TermRef`; `reference : StateOrEnvironment`; `order : FoundationOrMachineOrExtension`; `why : String`. Current keys and accepted alternatives: `core-children.lisp:25–40`. |
| **`layout` / `LayoutDecl`** | `layout` field specifications; `value-width`; `phase`; `fields : Nat`; `max-size`; `encode`, `decode`, `decode-step`, `start`, `size : FunctionRef`; `roundtrip-hyps : TermRef`. This follows the B-side schema documented in DSL-METATHEORY §2.1; it is not claimed to have been extracted in this draft. In particular, `fields` is a count. |
| **`shape` / `ShapeDecl`** | `fields : List FieldSpec`; `semantic : Option FunctionRef`; `served : Bool`, required false for this kind. The semantic predicate is separate from the field types. |
| **`machine` / `MachineDecl`** | `states`; `columns`; `accounts`; `budget`; `continuations : List (Phase × FunctionRef)`; `observes : List (Event × FunctionRef)`; `capacity : TermRef`; `initial : List (Acl2Name × TermRef)`; `layout`; `packed`; `calling-convention`; `obligations`. These reproduce the current payload (`machines.lisp:234–240`). Later schema revisions remove or replace keys when their ACL2 owners do. |
| **`callback` / `CallbackDecl`** | `args`; `returns`; `row-bindings`; `writes`; `cost`; `refusal`; emitting section and owner, plus the arm contract’s `uses`, `holds`, successor and resource information when implemented. The owner may be a machine or an operation-owning artifact. This is proposed: the current callback emitter introduces a function and shape lemmas and writes no callback row (`machines.lisp:320–333`). |
| **`command` / `CommandDecl`** | `machine`; `protocol-states`; `occasion`; `syntax`; `decide`; `retry`; `pre`; `post`; `refusals`; `disclosure`; `reads`. Predicates and executable operations are named references. |
| **`projection` / `ProjectionDecl`** | `stream`; `state`; `init`; `step : List (Event × FunctionRef)`; `obs`; `coverage`; `read-fallback`. |
| **`summary` / `SummaryDecl`** | The projection fields, plus `replaces`; `relation : FunctionRef`; `converter : FunctionRef`. The relation and converter remain separate entries because their obligations differ. |
| **`port` / `PortDecl`** | `foreign`; `target`; `interpretation`; `observes`; `kernel`; `commands`. The interpretation denotes a theory mapping; its reduct runs in the opposite direction on models. |
| **`migration` / `MigrationDecl`** | `from`; `to`; `alpha`; `beta`; `base`; `loss`, plus the event-range information used by a transformation when supplied. A grade must be explicitly recorded if the schema uses grades; it cannot be inferred from `loss = nil`. |
| **`correspondence` / `CorrespondenceDecl`** | `template`; `contract`; `sides`; `cases-from`; `checker`; `teeth-from`; `composition`. It binds contributed case labels to obligations. |
| **`owed` / `OwedDecl`** | Current payload: `vars`; `formula : TermRef`; `teeth : List FunctionRef`; `doc`; `status` (`owed.lisp:18–20`). After the store migration, this becomes the author-facing declaration of an obligation row, not a second store. |
| **`square` / `SquareDecl`** | `schema`; `template`; `owner`; `origin`; `case`; `boundary`; `contract`; `sides`; `statement`; `vars`; `formula`; `translated`; `requires`; `checker`; `teeth`; `proof`; `checks`, following DSL-METATHEORY §3.1. Schema-specific payloads distinguish simulation, quotient, bound, invariant and ordinary assertion obligations. |

`Decl` is the tagged union of these structures. The fourteen constructors do not imply fourteen implemented macros or fourteen populated registry families.

The registry is an immutable Lean term, conceptually:

```lean
def layerA : Registry :=
  { declarations := ...
    caseSources  := ...
    obligations  := ...
    snapshot     := ... }
```

Its collections preserve the orders consumers actually use. Machine registration order is obtained by reversing `table-alist` (`machines.lisp:269–275`). Core children are first restored to registration order and then grouped by foundation, machine and extension strata (`core-children.lisp:8–19`). Sorting everything lexically would change the presentation of the assembly.

Two current rows illustrate why the payload cannot be simplified into a collection of natural numbers:

- Echo’s capacity is the ACL2 term `(fn2-profile-c profile)`, while scribe’s is the literal `1`; both occur under `:capacity` (`machines-a.lisp:35,52`).
- The scheduler child’s initializer calls `fn2-machine-index-count`, and its reference treatment is `:environment` with an explanatory `:why` (`core-children-a.lisp:17–20`). That row describes an embedding and reference policy, not just a storage type.

### Opaque syntax is an honest boundary

Emit `ACL2::FN2-CONNECTION-REPLY` as a `FunctionRef`. Do not emit an arbitrary Lean function with that name.

Emit `(fn2-profile-c profile)` and an owed row’s `:formula` as named, losslessly retained syntax payloads. A payload can have a typed syntax tree or a canonical serialization, but it is not interpreted as a Lean expression. A term identity should carry the owning row and key, with exact payload comparison available; a digest is useful for indexing and change detection, not a substitute for the payload.

This preserves three useful facts:

- which symbol or term the declaration names;
- whether two rows name the same symbol or contain the same term;
- whether the exported subject changed.

It does **not** establish what that symbol computes or whether the term is true.

There must be no fallback that translates an unsupported formula to `True`, invents a Lean axiom for it, or quietly drops the row. Unsupported syntax is retained opaquely and marked unavailable to semantic interpretation.

The present `defthm-owed` translates its formula by introducing a `defun-nx`, but stores the supplied formula rather than a separate translated-body field (`owed.lisp:11–20`). Consequently, the proposed `translated` field must be obtained from the admitted world or added by the owning machinery. Renaming the current `formula` field does not supply it.

### Case catalogues and morphisms

A catalogue entry identifies an obligation source:

```text
owner       = (:machine ACL2::FN2-ECHO)
case        = (:run ACL2::FN2-ECHO :reply)
handler     = ACL2::FN2-CONNECTION-REPLY
source-key  = :continuations.
```

That entry is grounded in `machines-a.lisp:40–42`. It is not yet a simulation square. The `fn2-q1` correspondence supplies the two endpoints, case selector, relation, observation contract and statement template.

The export should retain the distinction:

```text
CaseLabel
BoundSquarePresentation
RealizedSquareProof.
```

The first emission experiment may populate the first two without supplying the third. In particular, the machine registry supplies 31 machine labels; it does not by itself supply the router’s fallback label or the executor’s seven selectors. Those require their own registered case sources. Writing eight labels by hand in `LayerA.lean` would defeat the tenth-artifact rule.

For the semantic layer, fix the axes with a diagram rather than relying on inconsistent uses of “horizontal,” “vertical,” “tight” and “loose”:

```text
         f
   A ───────→ A'
   │          │
 R │          │ R'
   │          │
   B ───────→ B'
         g
```

Here the objects are representation **state spaces**, transitions run left to right, and representation relations run top to bottom. For total deterministic transitions:

```text
Square(R,R',f,g) :=
  ∀ a b, R(a,b) → R'(f(a),g(b)).
```

The fn2 version adds invariant states, enabledness, outputs and a label-to-word interpretation where matching stutters. A partial transition cannot be made total by erasing refusal or disabledness. A nondeterministic simulation has an existential matching execution and establishes containment unless additional hypotheses establish equality.

Time composition pastes transitions. Representation composition uses relational composition. Square proofs can be proposition-valued and thin; position maps, residual occurrence maps and loss descriptors remain data and need their own equations.

The brief and HIGHER-STRUCTURES entry 4 use opposite tight/loose conventions. This is a harmless transpose if the author fixes it once. It is not a reason to change the simulation condition.

## C. What the Lean theorem licenses

The precise theorem is:

> **For the stated frame and observation contract, if its local generators and compatibility obligations hold, every diagram constructed from those generators preserves that contract.**

“All routes agree” requires an additional premise: the routes being compared are connected by such a diagram. Showing that every intended interchangeable pair has such a connection is completeness, a separate theorem.

A suitable proposed interface is:

```text
generated_sound:
  ∀ presentation interpretation,
    ValidGenerators(presentation, interpretation)
    → ∀ diagram : GeneratedDiagram(presentation),
        PreservesDeclaredContract(interpretation, diagram)

routes_agree:
  ValidGenerators(P,J)
  → ConnectedByGeneratedDiagram(P,route₁,route₂)
  → Obs_J(route₁) = Obs_J(route₂).
```

These are schematic signatures. `ValidGenerators` must expose COHERENCE §3.2’s hypotheses, rather than hide the desired result in a field named `coherent`:

- **H0:** related initialization or conversion, admissibility and invariant preservation.
- **H1:** legal matching transitions, including outputs, refusals and effects.
- **H≈:** endpoint equivalence preserves the relevant future behaviour.
- **HI:** each declared swap has two legal routes and preserves occurrence identity and the contract.
- **HM:** representation changes respect rescheduling, including label interpretations.
- **HQ:** all compared routes preserve the same declared observations; losses are composed honestly.
- **H2:** carried route data agrees where later operations consume it.

For an explicit finite sequence of validated swaps, an induction composes the observations. Dynamic cube or residual-consistency laws are needed when claiming more—for example, that occurrence identity is independent of the chosen swap sequence, or that a reduction algorithm may omit unexamined schedules. They are not prerequisites for every elementary two-step comparison.

Similarly, the theorem does not turn two one-way refinements of a nondeterministic specification into equality of implementations. If the specification permits `0` and `1`, two refining implementations may choose differently.

### The names and statements that cross the boundary

For each bound obligation, the bridge carries:

| Cross-boundary item | Required agreement |
|---|---|
| Qualified declaration identity and case identity | The exported owner and case designate the ACL2 row supplying the obligation. |
| Template, boundary and contract identity | The Lean premise is the same kind of obligation at the same execution boundary, with the same observations. |
| Endpoint and helper function names | Package-qualified names resolve to the intended functions in the recorded world. |
| Formals and calling convention | Variable order, result positions, stobj inputs/outputs and the relevant guards agree. |
| Source formula and translated formula | The row records the exact statement, and the binding associates it with the semantic premise required by the Lean theorem. |
| Proof reference | The cited admitted theorem proves that translated formula, or a separately proved equivalence supplies the connection. |
| Check reference | Revision, profile, input domain, horizon and unit, reached/exercised cases, verdict and evidence location identify what was actually checked. |
| Dependencies | Every premise used by the composed conclusion is linked to its own obligation or explicit assumption. |

For the proposed Q1 reply case, the cross-boundary names include:

```text
case:
  (:run ACL2::FN2-ECHO :reply)

concrete operations:
  ACL2::FN2-TRANSITION
  ACL2::FN2-EXEC-ACCOUNT-WORK

reference operation:
  ACL2::FN2-REF-TRANSITION

contract helpers:
  FN2-Q1-LOOP-INVP
  FN2-Q1-CONTINUEP
  FN2-Q1-CASEP
  FN2-Q1-EFFECTS-AGREEP
  ...the remaining named helpers of the bound template...
```

The first three executable operations exist at the cited revision (`executor.lisp:89–110`; `reference.lisp:95–142`). The Q1 helper family is proposed by DSL-METATHEORY §3.3.

The statement must include equality of the transition result tuples, the specified effects, and preservation of the normalized loop invariant. A theorem proving only `fn2-core-wfp` is not a match. A theorem proving the claim under an additional unestablished hypothesis is not a match either.

The bridge should compare exact translated terms under a declared canonicalization. If an instance proves a wrapper such as `$OWED(vars)` rather than the stored body, it needs the explicit definitional connection. A matching theorem name, a successful include or a comment saying “proved” is insufficient.

There are three distinct results:

```text
Lean kernel checks the composition implication.

ACL2 checks an instance theorem establishing a premise.

The bridge binds that instance theorem’s statement to that premise.
```

The first experiment does not need to import ACL2 proof objects into Lean. It must not simulate that import by generating axioms from proof-status rows. The Lean theorem remains parameterized by realizations of its premises, and the report records which premises have ACL2 proofs, checks or no evidence.

When an ACL2 proof of the composed instance is desired, instantiate the applicable ACL2 composition lemma and admit the resulting theorem in ACL2. TRANSPORT §9 reports exactly this route for the toy `fc-rel-fold` instance. Its successful use is evidence that this local proof mechanism is useful; it is not certification of fn2’s current turn theorem.

### What a successful check establishes

A checked row stays owed.

For a checked G1 instance, the conclusion is about the recorded related states and transition. For a checked G2 instance, the conclusion is about the two legal orders exercised at that state. Composition is justified over recorded runs only when the intermediate states, label interpretations, contracts and evidence scopes actually join.

For example, checks of:

```text
fused → unfused
unfused → reference
```

can support a composed comparison on a shared recorded unfused trajectory. Merely intersecting two sets of seed numbers does not establish that join.

A general Lean theorem does not promote finite observations into a universal premise. Even exhaustive finite exploration needs an explicit finite domain, a coverage argument and a correct checker before it can support a bounded universal conclusion. Ordinary check records remain evidence, not admitted proofs.

The report should therefore distinguish:

```text
requirements
bound statements
ACL2-proved statements
checked instances and their scopes
unexercised or unresolved cases
composition premises still missing.
```

The current teeth machinery checks that named zero-argument evaluators exist and return exactly `t` (`owed.lisp:29–49`). That is useful evidence plumbing. It does not, by itself, establish that an evaluator inhabits a theorem’s whole antecedent or supplies the intended hypothesis-removal counterexample.

### The toy must make the theorem falsifiable

The positive toy needs a real diagram: an inhabited state, enabled transitions that change it, and a nonconstant observation. An empty alphabet or a one-state model alone would make the most important obligations trivial.

The negative toy should model the accept/close obstruction:

```text
initial:
  the only reusable slot belongs to an old connection
  a new acceptance and the old connection's release are both pending

accept; release:
  acceptance observes no free slot and refuses
  release makes the slot free

release; accept:
  release makes the slot free
  acceptance acquires it.
```

The observation records the admission outcome. Both routes are legal; their observations differ. The false declaration “these occurrences are independent because they belong to different machines” therefore fails HI.

This toy refutes the proposed independence inference in its own model. It is not a claim that the production fixture has been executed. The ACL2 fixture supplies that connection to the actual allocator and scheduler.

For parametricity, the initial Lean theorem should quantify over a **defined client language**:

```text
RelatedPrimitives(interfaceA, interfaceB, R)
→ WellFormedClient(interface, client)
→ RelatedInputs(R, xA, xB)
→ RelatedResults(evalA(client,xA), evalB(client,xB)).
```

A constructor that branches directly on representation data is the negative control. Permitted tests and outside calls must themselves respect the relation.

A direct-call whitelist is not enough if a permitted helper can inspect hidden representation through its callees. The production restriction needs a closed account of primitive contracts or transitive calls. Nor should the Lean author assume that an arbitrary polymorphic Lean term supplies the intended parametricity theorem without a proved restriction.

## D. The trust story

The new assumption is **faithfulness of the exported presentation and its interpretation to the specified ACL2 world**.

Let:

```text
W  = the recorded ACL2 world
E  = the export-and-decoding process
P  = E(W)
J  = the interpretation connecting P to ACL2 logical subjects.
```

The assumption is:

> For every declaration, artifact, case and obligation used by a claimed result, `P` identifies the corresponding subject in `W` without omission or conflation; and the semantic premise interpreted by `J` is the property stated by the recorded ACL2 formula about that subject, with the same domains, boundaries, outputs, effects and observation contract.

This is one interface assumption with several checkable clauses:

1. **Identity fidelity:** qualified names designate the same declarations, functions and events.
2. **Payload fidelity:** values and order are retained; unsupported payloads remain explicit.
3. **Artifact fidelity:** generated subjects are the functions and statements actually admitted, including artifacts emitted during later assembly sections.
4. **Obligation fidelity:** catalogue entries become the intended case statements, and coverage is not inferred merely from the catalogue’s existence.
5. **Semantic fidelity:** the Lean premise bound to an ACL2 formula means what that formula states.
6. **Evidence fidelity:** proof and check records belong to the recorded subject and revision.

The fifth clause is the part opaque names do not discharge. An opaque presentation can be perfectly faithful as syntax while its proposed interpretation is wrong.

This is the **new bridge assumption**, not the entire system’s only trust assumption. ACL2’s and Lean’s trusted implementations, the execution model’s environmental assumptions and the connection to native execution remain their existing subjects.

### Two macro mutations, with different purposes

The mutation experiment should include both a row-visible change and a change that today’s rows fail to expose.

**Control 1: mutate declaration-derived layout.**

In an isolated fixture copy, change the common `deadline` field from `:u60` to `:u32` at `machines.lisp:6–8`.

The machine emitter builds its columns from those common fields, emits `defcolumns`, and records the columns as both `:columns` and `:layout`, together with `:packed` metadata (`machines.lisp:203–240`). The packing function obtains each field’s width and advances the offset by it (`machines.lisp:10–17`). The columns emitter records the column specifications separately (`columns.lisp:602–605`).

The expected semantic-data diff is therefore:

```text
each affected MachineDecl:
  columns.deadline: u60 → u32
  layout.deadline:  u60 → u32
  packed.deadline width: 60 → 32
  subsequent packed offsets: reduced by 28 bits

each corresponding ColumnsDecl:
  columns.deadline: u60 → u32.
```

The reviewer checks that both declaration identities changed, all affected rows were emitted, and the original width and positions were not copied from a hand-maintained Lean fixture. Successful typechecking alone would not catch stale values of the same Lean type.

This is a mutation control, not a proposed change to fn2’s field width.

**Control 2: mutate generated behaviour without changing the row.**

Remove the generated `:retired` phase exclusion from `NAME-OBSERVES-P` at `machines.lisp:227–231`, while retaining the table construction at `machines.lisp:234–240`.

The function’s behaviour changes, but the current machine row need not change: the same states, observed-event entries, columns and names remain recorded.

This control exposes the limit of a table-only exporter. It must not be reported as passing because the Lean registry still typechecks.

To detect this class, the common `generated` manifest must bind exported artifact names to their actual admitted definitions or statement payloads. The export can retain these as opaque syntax plus fingerprints. The mutated run must then show either:

- a changed artifact payload in the emitted presentation and invalidated evidence bindings; or
- a named failure that the export does not cover that artifact.

A source revision change by itself is inadequate: it invalidates freshness but does not demonstrate that the relevant generated artifact was captured.

The reviewer checks the changed `FN2-ECHO-OBSERVES-P` body, the manifest connection and the evidence invalidation. This control establishes sensitivity to this class of mutation. It does not prove generator correctness.

### The shared-handler control checks a different assumption

Use a mutation in a handler shared by the concrete and reference executions. A concrete candidate is changing the send offset from `off` to `0` in the send call at `machines-a-run.lisp:172–176`.

A fixture with a partially sent, nonconstant payload can distinguish the correct remaining suffix from a repeated prefix. Q1 may continue to agree because both sides use the shared handler; an independent client-byte contract must reject the mutated behaviour.

This control supports two conclusions:

- Q1 can remain a meaningful scheduler-refinement check despite sharing handlers.
- Q1 cannot be advertised as independent validation of those handlers’ byte semantics.

The fixture must actually exercise the changed call. A mutation that is unreachable in the fixture supplies no evidence either way.

### What Lean cannot establish from this export

The proposed Lean layer cannot establish:

- soundness of ACL2;
- correctness of ACL2’s implementation or native execution;
- truth of an arbitrary ACL2 formula represented as opaque syntax;
- that a `defthm` named in a row has the advertised statement merely because the name exists;
- completeness of the current case catalogue merely because every emitted row typechecks;
- universal generator validity from bounded passing checks;
- native durability, fairness or environmental integrity from finite simulation squares;
- that all intended fn2 route equalities follow from the toy’s generator basis.

Carrying the translated formula makes mechanical statement comparison possible. It is necessary for that comparison, but still insufficient for Lean to understand the formula: semantic binding requires a justified interpretation of the supported schema.

The export also cannot recover metadata that the macros do not record. For example, callbacks currently reconstruct scalar arguments from the machine’s `:columns` and emit a function plus shape lemmas (`machines.lisp:320–333`); the recorded `:calling-convention` at `machines.lisp:238–239` is not itself evidence that this consumer used that field. The manifest and world extraction must describe the actual emitted function.

## E. Five decisions for ember

These are my pessimistic planning allowances, not measured delivery times. They price the specified packages, not a proof of the full fn2 frame.

| Decision | Recommendation | Pessimistic cost and covered scope |
|---|---|---|
| **1. Where does the frame metatheory live?** | Adopt Lean with pinned Mathlib for presentations, semantic squares, generated-diagram soundness, one revision-extension model and a restricted client parametricity theorem. Keep executable instance proofs and functional-instantiation kits in ACL2. | **8 engineer-days** for that bounded Lean foundation, including inhabited examples, the accept/close negative toy, theorem-boundary checks and build qualification. This does not price global frame completeness, dynamic partial-order reduction or production R7 enforcement. |
| **2. What does the first emitter deliver?** | Export the actual world tables into typed presentation data, with all fourteen kinds specified but only implemented families populated. Keep arbitrary terms opaque. Add case sources with their owning consumers. | **5 engineer-days** for the four inspected registry families, identity/order preservation, deterministic serialization, typed decoding and structural mutation fixtures. A 39-case emission claim additionally requires the router and executor sources; the machine table alone supplies 31 labels. |
| **3. How strong is the bridge to ACL2 claims?** | Require exact translated-statement binding and generated-artifact provenance before reporting an ACL2 theorem as realizing a Lean premise. Keep an unbound row visible. Do not generate Lean axioms from proof-status metadata. | **7 engineer-days** for statement extraction and matching, manifest coverage, revision binding and the behaviour-only mutation control. This is a checked linkage package under the stated faithfulness assumption, not a verified ACL2 semantics translation or proof importer. |
| **4. May the two sides share a declaration or handler?** | Yes for the stated representation or compiler refinement. Record sharing and require independent contracts for consequential behaviour. Adopt the shared-send-offset control against Q1 and the client oracle. | **6 engineer-days**, already within DSL-METATHEORY decision 1’s DM3/DM10 allowance, for provenance, adapters and controls; do not charge them twice. Production enforcement of a complete arm language remains the separately priced R7 work. |
| **5. Does Lean become a release gate?** | **Not before the first release.** Report the metatheory, exported-instance coverage and outstanding bridge premises as information. A failed Lean check prevents calling that artifact proved; it does not create a new general shipping prerequisite. | **2 engineer-days** for the advisory report and integration path, covering artifact freshness, checked theorem status, instance bindings and named failures. No later gate is authorized by this decision; that requires a concrete consumer and a measured cost. |

The additional allowances total **22 engineer-days for the bounded Lean-and-export package**, with the separate **6 engineer-days for sharing controls already accounted for in the DSL plan**. They exclude the existing DSL migration programme and production instance proofs.

My disagreements with the coordinator’s framing are narrow but material:

- **“ACL2 is wrong for metatheory” is too absolute.** The useful boundary is representation and maintenance cost. Generic relational folds and their functional instances already fit ACL2; the frame’s theories-as-objects and structural quantification justify Lean.
- **“If the generators commute, every route agrees” needs its route restriction.** Soundness concerns generated diagrams. Completeness concerns which intended route pairs those diagrams connect. The accept/close witness is a reason to preserve this distinction in the theorem statement.
- **“The same registry” does not by itself establish faithfulness to generated behaviour.** The retired-phase mutation demonstrates why actual artifact bindings are necessary.
- **“Information, like certify” should describe release policy, not logical status.** An admitted ACL2 theorem, a Lean theorem, a translated owed statement and a passing check supply different kinds of assurance even when none is a pre-release shipping gate.
- **An opaque Lean presentation is the correct first artifact, but it is not yet a semantic model of the executable ACL2 instance.** The report must expose that remaining interpretation obligation rather than hide it behind a populated registry.