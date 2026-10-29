# fn2 and transport along equivalences: the newest higher-categorical work, tested against the server (2026-10-28; Opus researcher; present state)

Brief: `build/coordinator/briefs/TRANSPORT-20261028.md`. Ember, verbatim: "are we able to find any extremely-recent higher-category works that we can experiment with seeing how the ideas fit for us? i feel like being able to transport along equivalences and other structures is somehow vital for modeling and composing with the server and finding useful systems software that is even worth composing with."

Read against: `UNIVERSAL-CONSTRUCTIONS.md` (UC; its §13 rejections bind this note), `STORAGE-DESIGN.md` §4 decision 1 (STORAGE), `PLANES-AND-GAMES.md` §4.2 and §4.5 (PLANES), `PLANES-ADDENDUM-INTERWEAVING.md` (ADDENDUM), `EXECUTION-MODEL.md` §4-5 (EXEC), `fn2/docs/design/briefs/FN2-SEAT-COMMON.md` (SEAT; the three DSLs, "no new checkers"), `EMBER-ARCHITECTURE-WORDS.md` (the rulings D34, D38's withdrawal, D46 and D68: one format, no previous-format readers, a kind lands with its producer, no migration or compatibility obligations), and the code as it stands on `fn2/main` (e198ab1af) and `fn2/b-durability` (b4d422f99): `defcolumns` (`fn2/books/columns.lisp`), `defmachine` with `:observes` (`fn2/books/machines.lisp`, `machines-a.lisp`), `deflayout` with a `schema-version :u8` in every record header (`fn2/books/layout.lisp`, `format.lisp`), and `defthm-owed` (`fn2/docs/OWED.md`). Papers are cited by filename in `~/paperbin/` (a `.pdf` with its `.txt` beside it unless the name ends `.txt`); 46 were fetched for this note and are listed in the "Transport and higher categories" section of `~/paperbin/README-fn2-20261028.md`.

The rule this note keeps is UC's: **a construction is named only if it predicts something concrete.** A prediction is a missing law, a field a DSL must record, an obligation with a definite shape, or a check that can fail. Items that only rename what the documents already say are marked *(placement)*; items that predict nothing are **cut**, and the cut is said in the same line. The draft was attacked by Astra (§7; six fatal and twelve material findings, all accepted), and this text is the corrected present state.

## Contents
0. The answer in one page
1. The newest works, and what each predicts for fn2
2. The versioned-world essay mapped onto fn2's algebra
3. Transport as fn2's migration discipline
4. Five experiments, specified
5. The cost, and the risks
6. Five decisions for ember
7. Astra's round, folded in
8. Bibliography
9. Experiments A and B: results

---

## 0. The answer in one page

fn2 already *is* a versioned executable world in the essay's sense. The journal is the execution history. Fold and projection interpretations, record formats, machine kinds and Decide functions are the program-revision axis. What fn2 lacks is a **language of evolution**: today a revision is a sentence in a decision document ("a changed interpretation is a new version with its own coverage, never an in-place change", PLANES §4.2; "a new or changed fold may use an existing summary only through a valid bootstrap or migration rule", STORAGE decision 1), with no declaration form, no obligation shape and no check.

One standing ruling shapes the answer. **D68 (ember, 2026-10-06, KEEP): "no migration or compatibility obligations for any layout, schema or wire format"**, with D34 ("fresh deploys, no migrations, one format") and the withdrawal of D38 (no previous-format readers). Ember, verbatim: "there are no such thing as future migrations :) when we cut 6.6.0 will be the first time that anyone else uses this, and we'll be redeploying all our nodes" (EMBER-ARCHITECTURE-WORDS §4). Before its first release, then, fn2 owes no transport *between versions*: every revision is a wipe and rebuild, and building version-to-version migration now would contradict a KEEP ruling. The draft of this note missed D68, and Astra's round found it (§7, item 18).

Transport still matters now, *within* one format, between two representations of one interpretation, and there it predicts the most. What survives the "predicts something concrete" test and Astra's round:
1. **Summary adequacy is transport, and it is owed now.** A fold and its summary are two representations of one interpretation (STORAGE decision 1). The certificate is a relation `R` between them that is closed under each event kind's step, up to UC's all-future observational congruence. That is Pumpkin Pi's `Iota` rule (`ringer2021-proof-repair-across-type-equivalences-pumpkin-pi.pdf`) in fold form, with the relational form that Astra's `(n mod 2, 0)` counterexample needs (`abstract-account-up-to-techniques-inductive-behavioural2024-2412.07351.pdf`). An executable converter and its correctness are a *separate* obligation (Astra 2). Experiment A builds the generic contract and one summary.
2. **Proof transport across development revisions.** Under D68 the data is wiped, but the theorems and the owed statements (`defthm-owed`, OWED.md) must survive every change of representation the DSLs make during development. That is the proof-repair problem, and ACL2 already has its tools: functional instantiation over a constrained fold contract, APT's `defiso` and `propagate-iso` (`coglio2020-acl2-apt-isomorphic-data-type-transformations.pdf`; ACL2 8.7 `kestrel/apt/propagate-iso.lisp`), and `defabsstobj` correspondence under a fixed logical view (`kaufmann-moore2013-abstract-stobjs-isa-modeling.pdf`). The structure identity principle supplies the rule that makes them work: a theorem transports only if it is stated through the declared interface (`init`, `step`, `obs`), never through the representation. Experiment B measures `propagate-iso` on a real column shape.
3. **Interpretation identity is a manifest Name.** An interpretation is identified by the content Name of a canonical manifest of its declaration *and* the transitive closure of the definitions it depends on (Unison, corrected by Astra 9: a hash of the declaration alone misses a changed helper). It is needed now, for the revision the simulator records (EXEC rule 10) and for the checkpoint claim's fold/schema identity (STORAGE decision 4). It is a real component and an encoding decision, not a macro line.
4. **Composition predicts one rule and one check.** Double categories of open systems (`myers2023-categorical-systems-theory-book-draft.pdf`, `double-operadic-theory-of-systems2025-2505.18329.pdf`) say a check that composes *wired* behaviours is unsound over undeclared shared state. fn2's listener-to-echo interaction is an allocation protocol over shared tables, not a capability on a wire, so a compositional check must model the allocator as its own component (Experiment E, after layer D).

**After the first release, if D68 is revisited** (decision 1), the evolution discipline is specified in §3.2 so that the DSLs keep enough information to support it. Its parts:
- revisions at definite durable boundaries (Tesseract's DDaM, `online-schema-evolution-almost-free-snapshot-databases2022-2210.03958.pdf`; Julia's world age, `belyakova2020-julia-world-age-in-julia.pdf`), with a rule for Decide work that crosses the boundary;
- migrations that declare what they preserve, transporting coverage *at the converted state's cut*;
- rollback only by a backward migration valid in the current state;
- declared 2-cells between migration routes checked on all future suffixes (homotopical patch theory, `angiuli-morehouse-licata-harper2014-homotopical-patch-theory.pdf`; Experiment D);
- a Decide compatibility relation checked over obligation *kinds*, bounded;
- conservative, enforced read dependencies (the read-after-write lesson of `exelmans2024-operation-based-versioning-live-executable-models-sosym.pdf`).

None of it is built before then, and by D46 ("a kind lands with its producer") no revision record kind is added ahead of its producer.

What is cut: cubical computation and univalence as an axiom; guarded recursion and clocked type theory; categorical cybernetics; Σ-migrations by the chase; a general lens library; shortcut memoization; early cutoff across revisions (false, Astra 10); and mandatory equivalence-only rollback. Each is cut in §1 in the line that names it.

The five decisions (§6): keep D68 through the first release and specify the post-release discipline without building it; adopt the relational per-event-kind certificate for summaries now; adopt the manifest Name for interpretation identity when the projection plane is built; state fold theorems through a constrained interface so they transport; run Experiments A and B now, E after layer D exists, and defer C and D until an editing consumer and real migration routes exist.

---

## 1. The newest works, and what each predicts for fn2

Each entry: what it is, its date, and **predicts** (or **cut**). Newest first within each group where the group allows it.

### 1.1 Transport and univalence as engineering

- **Trocq: proof transfer for free, with or without univalence** (Cohen, Crance, Mahboubi; ESOP 2024; `cohen-crance-mahboubi2024-trocq-proof-transfer-for-free.pdf`). A Coq-Elpi plugin that generalizes the univalent parametricity translation with a *graded* notion of relatedness: each direction of a relation between `A` and `B` has a class in `{0, 1, 2a, 2b, 3, 4}` (nothing; a map; a map whose graph is contained in the relation; a map determined by the relation; both; both with coherence, i.e. an equivalence), and the translation computes, for each goal, the weakest class that suffices (Definitions 5-6 and Figure 2). **Predicts:** a migration between two versions is not "an equivalence or nothing"; it carries a class, and each theorem that is to be transported needs a class determined by where the migrated type occurs in its statement. Concretely, a theorem quantifying over old states and concluding about observations needs only a map that commutes with the steps; a theorem quantifying over *new* states and concluding about the old needs the backward direction. The cases fn2 would use (§3.2) are this note's proposal, not a demonstrated restriction of Trocq's lattice (Astra 2). What Trocq contributes is the principle that the strength a migration needs is fixed by the statements to be carried, so a migration declares what it preserves and each carried theorem is checked against that.
- **Transport via partial Galois connections and equivalences** (Kappelmann; APLAS 2023, extended version 2025; `kappelmann2023-transport-via-partial-galois-connections-equivalences.pdf`). Transport in *simple* type theory (Isabelle/HOL), with partial Galois connections and partial equivalences closed under function relators, (co)datatypes and composition. **Predicts:** this is the version of transport that fits ACL2's first-order logic, and it is partial for the reason fn2's formats are: a v1 encoding maps into a *subset* of v2 encodings (a widened field accepts values v1 never wrote), and a narrowed field maps only a subset of v1 values. The closure under composition is what a layout compiler would need, a relation per field composed into a relation per record, with whole-record constraints (lengths, references, identity bindings) stated beside the field relations because they are not independent (Astra 5). Under D68 (§2.3) no previous-format reader exists before the first release, so this is post-release design. Its use now is Experiment B's partial-iso teeth, where it shows why a widened representation is an isomorphism only onto its image.
- **Proof repair across type equivalences** (Ringer, Porter, Yazdani, Leo, Grossman; PLDI 2021; `ringer2021-proof-repair-across-type-equivalences-pumpkin-pi.pdf`) and **across quotient type equivalences** (Viola, Fan, Ringer; OOPSLA 2025, arXiv 2310.06959 of 2023; `cosmo-ringer2023-proof-repair-across-quotient-type-equivalences.pdf`). Pumpkin Pi transforms proof terms along an equivalence given as a *configuration*: how to build new values from old constructors (`DepConstr`), how to eliminate (`DepElim`), and the `Eta` and `Iota` rules that make the two agree computationally (§4.1). The quotient work extends this to setoid-style equivalences, where every downstream function must respect the quotient. **Predicts:** (a) what a fold migration must record to be mechanical is the configuration's analogue: the state map, the per-event-kind step correspondence (the `Iota` rule: `σ(δ₁(s, e)) = δ₂(σ(s), e)`), the initial-state correspondence, and the observation correspondence. These are UC §2.2's homomorphism equations with two versions in place of a state and its summary. (b) A summary is a quotient (UC §2.2, the observational quotient), so any projection that reads a summarized fold must read it *only through its declared observations*; reading the representation breaks quotient transport. This is a checkable rule on `defprojection`'s sources.
- **Transporting functions across ornaments** (Dagand, McBride; ICFP 2012, technical report; `dagand-mcbride2012-transporting-functions-across-ornaments.pdf`). An ornament builds a new datatype from an old one by adding information, with a forgetful map back; functions lift along it with a *coherence* property (the lifted function, forgotten, is the old function). Williams and Rémy's ML ornaments (POPL 2018) were not fetched (gap). **Predicts:** "add a field" and "add an event kind" are the commonest revisions, and they are ornaments, not equivalences. Their obligation is coherence on *every admitted event*: `φ(δ₂(s, e)) = δ₁'(φ(s), e)`, where `δ₁'` is the old fold extended to the new event kinds by a *declared* old meaning (usually "no effect", which then obliges new events to leave the old component alone), together with initialization and `obs₁ ∘ φ = obs₂` restricted to the old observations. Coherence on old event kinds alone is not enough: a new event may change the old component while `δ₁` ignores it (Astra 1). The new fields need their own justification. A lift with `φ ∘ ℓ = id` preserves the old state but says nothing about whether a new field's value is historically right (a new counter lifted to zero has lost the prefix count), so the new observations are covered only when no event before the revision could have affected them (§3.2).
- **The marriage of univalence and parametricity** (Tabareau, Tanter, Sozeau; JACM 2021; `tabareau-tanter-sozeau2021-marriage-univalence-parametricity.pdf`). Univalent parametricity: transfer as a syntactic translation of each definition, given an equivalence per type, with univalence needed only at the type level. **Predicts:** nothing beyond Trocq, which generalizes it. Kept as Trocq's base; **no separate prediction**.
- **Homotopy Type Theory: Univalent Foundations** (the HoTT book; 2013; `hott2013-homotopy-type-theory-univalent-foundations-book.pdf`) and **Introduction to Homotopy Type Theory** (Rijke; 2022, CUP 2025; `rijke2022-introduction-to-homotopy-type-theory.pdf`); **The univalence principle** (Ahrens, North, Shulman, Tsementzis; 2021, Memoirs AMS; `ahrens-north-shulman-tsementzis2021-univalence-principle.pdf`). Transport along paths; univalence identifies equivalences of types with equalities; the structure identity principle makes every property *expressible in the structure's own language* invariant under structure-preserving equivalence. **Predicts** one rule, the engineering content of the structure identity principle: *a theorem transports along a migration only if it is stated through the declared interface (observations, steps, initial state), never through the representation.* So fn2's fold theorems are stated over `obs`, `step` and `init` as constrained functions (Experiment A's generic contract), and a theorem that names a representation accessor is, by construction, not transportable and must be re-proved. Univalence itself, as an axiom, is **cut**: ACL2 has none, and fn2's equivalences are discharged as obligations.
- **Cubical Agda** (Vezzosi, Mörtberg, Abel; ICFP 2019, JFP 2021; `vezzosi-mortberg-abel2021-cubical-agda-dependently-typed-univalence-hits.pdf`). Transport that *computes*, with higher inductive types. **Cut**: fn2's served code is ACL2 and C; computational univalence predicts nothing for either. Its higher inductive types are the vehicle of homotopical patch theory (§1.3), which is kept for its prediction, not its vehicle.
- **ACL2's own transport** (no new paper; the books are in ACL2 8.7): *functional instantiation* (a theorem about constrained functions in an `encapsulate` holds for any functions satisfying the constraints; `~/dev/acl2aiguide/examples/books/encapsulate-fi.lisp` is a worked example), **APT `isodata`** (re-expresses a function over an isomorphic representation; `coglio2020-acl2-apt-isomorphic-data-type-transformations.pdf`), **`defiso` and `propagate-iso`** (given a `defiso`, the base functions' isomorphic versions *and their correspondence theorems*, supplied by the author, `propagate-iso` walks a range of events and regenerates the *functions and theorems* that use them (Astra 12); `kestrel/apt/propagate-iso-doc.lisp`, "it applies the substitution to existing theorems to generate theorems on the new functions"), and **`defabsstobj`** (`kaufmann-moore2013-abstract-stobjs-isa-modeling.pdf`: an abstract stobj with correspondence, preservation and guard theorems against a concrete stobj). **Predicts:** the three transport mechanisms the brief asks for already exist in fn2's logic, at three grains: functional instantiation for a fold contract across representations (Experiment A), `propagate-iso` for carrying the theorems about a column's users across a representation change *during development* (Experiment B; under D68 this is proof maintenance, not data migration), and `defabsstobj` for a struct-of-arrays layout change under a fixed logical view. The last is the strongest transport fn2 has: EXEC rule 1 already keeps "logical views (maps, sequences, octet lists) never materialized on the served path", so a layout change that preserves the abstract view preserves every theorem stated over it *(placement: the mechanism is EXEC's; the prediction is that layout revisions should be stated as abstract-stobj correspondences and nothing more)*.
- **Transporting theorems about typeability in LF across schematically defined contexts** (2025, arXiv 2509.26362; not fetched). **Cut**: specific to logical-framework contexts.

### 1.2 Categorical systems theory: what is worth composing with the server

- **Towards a double operadic theory of systems** (Libkind, Myers; 2025; `double-operadic-theory-of-systems2025-2505.18329.pdf`), **Categorical Systems Theory** (Myers; book draft, last updated 2023-09-03; `myers2023-categorical-systems-theory-book-draft.pdf`), **Double categories of open dynamical systems** (Myers; 2020 extended abstract; `myers2020-double-categories-of-open-dynamical-systems.pdf`). A systems theory is a module of systems over a double category of interfaces and interactions; Moore machines over lenses are the directed case, Petri nets over undirected wiring diagrams the variable-sharing case. Myers's central theorem (book §5.3) is that *behaviours* of a fixed shape (trajectories, steady states, periodic orbits) are representable and compose: the behaviours of a wired composite are computed from the behaviours of its parts along the wiring, as a composite of spans. **Predicts** two concrete things. (a) **A compositional check**: for two machine kinds wired only through declared events and actions, the bounded traces of the composite equal the relational composite (a pullback over the wire) of each kind's bounded traces under an environment that offers any wire value. The simulator can check that equality on the tiny profile (Experiment E), and when it holds, each kind can be explored separately. (b) **The rule that makes (a) sound**: an interaction that does not pass through the declared vocabulary is variable sharing, not wiring. Variable sharing has compositional theories of its own (the cospan works below), so the rule is not "only wiring composes" (Astra 15). It is that a check composing *wired* behaviours is unsound over undeclared shared state. Myers's general construction is also lax: the composite of component behaviours maps into the composite's behaviours, and recovering all of them needs further conditions (book §5.3.3). fn2's real kinds share a lot. `fn2-listener-admit` reads the active and connection counts, reserves a pool slot and writes the echo row (`machines-a-run.lisp`), so the listener-to-echo interaction is an allocation protocol, not a capability on a wire. A compositional check therefore needs the allocator modelled as its own component with declared request and grant events, on the scheduler's common timeline (Experiment E).
- **An algebra of resource sharing machines** (Libkind; 2020; `libkind2020-algebra-of-resource-sharing-machines.pdf`), **Structured cospans** (Baez, Courser; TAC 2020; `baez-courser2020-structured-cospans.pdf`), **Structured and decorated cospans from the viewpoint of double category theory** (Patterson; 2023; `patterson2023-structured-decorated-cospans-double-category-viewpoint.pdf`), **Double categories of open systems: the cospan approach** (Baez; 2025, v3 2026; `double-categories-open-systems-cospan-approach2025-2509.22584.pdf`). The variable-sharing paradigm, composed by pushout of cospans. **Predicts** nothing beyond (b) above: the pushout identifies shared variables, and fn2's discipline is to name them. **No separate prediction.**
- **Nondeterministic behaviors in double categorical systems theory** (Wang; 2025, v2 2026; `nondeterministic-behaviours-double-categorical-systems-theory2025-2502.02517.pdf`). Trajectories of nondeterministic Moore machines composed through conditional products in Markov categories, with deterministic channels. **Predicts** one caveat for Experiment E: fn2's environment is nondeterministic (fault choices, completion order), so component behaviours are *sets* of traces and composition is relational, and a composite can have strictly fewer behaviours than the product (a wired pair can deadlock where neither part does). The check compares sets, never counts.
- **Polynomial functors: a mathematical theory of interaction** (Niu, Spivak; 2023, v2 2024; `niu-spivak2023-polynomial-functors-mathematical-theory-of-interaction.pdf`) and **Dynamic operads, dynamic categories** (Shapiro, Spivak; 2022; `shapiro-spivak2022-dynamic-categories-dynamic-operads.pdf`). An interface is a polynomial `Σ_{i ∈ p(1)} y^{p[i]}`: positions are what the system currently exposes, directions are the inputs it accepts *at that position*. Dynamic categories let the wiring itself change with state. **Predicts** (a) *(mostly placement)*: a machine's interface is mode-dependent, and the observations it can receive in a state are the completions of the operations it has outstanding in that state. fn2's `:observes` accepts every declared observation in every state and treats stale completions in code; the operation vocabulary already counts strays (`fn2-ops-stale-or-duplicate-post`, OWED.md). Declaring the outstanding-operation set per state would make UC §6.2's shared protocol table and the machine's interface one declaration. It is worth doing only when a DSL revision touches `:observes` anyway. (b) *(placement)*: subscription edges that change by log events (INBOX) are dynamic wiring.
- **Compositional program verification with polynomial functors in dependent type theory** (Aberlé; 2026-04; `compositional-program-verification-polynomial-functors-dtt2026-2604.01303.pdf`). Implementations *and* verifications compose along wiring diagrams; Mealy machines give the operational semantics; dependent polynomials encode pre/postcondition specifications; formalized in Agda. **Predicts** the *shape* of EXEC §4's refinement obligation when assurance comes: per-kind specifications (each command's preconditions and observable postconditions, UC §7.1) composed along the declared wiring, rather than one global relation `R` over the whole core. It changes nothing now. It is a reason to keep each kind's commands and observations declared separately, so that the per-kind specifications exist when the proof starts.
- **Towards foundations of categorical cybernetics** (Capucci, Gavranović, Hedges, Rischel; ACT 2021; `capucci-gavranovic-hedges-rischel2021-towards-foundations-categorical-cybernetics.pdf`). Parametrised optics for controllers, learners and games. **Cut**: fn2's core has no agent optimizing a utility. A game client's AI would, but it lives outside fn2 (PLANES §4.9).

**What a double category of open fn2 machines predicts for `defmachine` and for the fast plane's interface.** For `defmachine`: interfaces are the event and action vocabulary (`fn2/books/vocab.lisp`), wiring is the executor's routing of an action's completion to the observing kind, and the two predictions above (compositional check; shared variables declared) are all it yields. For the fast plane (PLANES §2.4): the tick executor is an open system whose interface to fn2 is *exactly* its published transient items, its consequential transactions carrying `(scope, incarnation)`, and its `external-checkpoint` records (PLANES §4.5). The theory says this interface is worth keeping *directed-only*: the executor shares no variable with fn2 except through the lease Obligation, which is itself an event-mediated fence. That is why a zombie executor is refused by name rather than corrupting shared state, and it is the property that makes an external executor "worth composing with": its whole interaction is a span over declared events, so fn2 can check it from the journal alone *(placement: PLANES already specifies the interface; the theory says why nothing may be added to it except as an event)*.

### 1.3 Higher categories of migrations and versions

- **Living databases** (Deshpande; 2026-05; `living-databases2026-continuous-schema-evolution-versioning-2605.00676.pdf`). One abstraction for versioning, schema evolution and transformations, with provenance, conditional propagation, and "declarative mechanisms to control the evolution" of dependent objects such as views; prototype on Prolly trees. **Predicts:** a derived object must say what happens to it when its source revises. For `defprojection` (PLANES §4.2) that would be one field, `on-source-revision`. Under D68 every revision before the first release is a wipe and rebuild, so the field is **deferred** to the first post-release revision (Astra 18). Even then a lossy source may remove exactly the observation a reader needs, so each reader discharges its own compatibility obligation (Astra 8).
- **Schema evolution in interactive programming systems** (Edwards, Petricek, van der Storm, Litt; Programming 2025, arXiv 2412.06269; `schema-evolution-interactive-programming-systems2024-2412.06269.pdf`). Schema changes as first-class edit operations, each with an intended inverse, and the observation that some inverses lose information: *Extract Entity* conflates indistinguishable rows, so its inverse cannot restore them (§2, Table 2). **Predicts:** a lossy migration declares its *kernel* as an identification relation (which old states it merges, and hence which old observations it can no longer distinguish), not merely a list of dropped fields (Astra 3). The loss is then a named fact, never a discovery. A history-compressing summary that preserves every retained observation is *not* lossy in this sense, even though its representation forgets history.
- **Relational to RDF data migration by query co-evaluation** (Wisnesky, Filonik; 2024, v2 2026; `wisnesky2024-relational-to-rdf-migration-query-coevaluation.pdf`) and **Automating transfer of robot task plans using functorial data migrations** (Aguinaldo, Patterson, Regli; IEEE 2025, arXiv 2406.15961; `aguinaldo2024-robot-task-plans-functorial-data-migrations.pdf`). Co-evaluation is the left adjoint of query evaluation, so a query written in one direction yields the other direction with a unit and counit. AlgebraicJulia's conjunctive-query migrations transfer real plans between real schemas. **Predicts:** for the supported mappings of UC §2.5, a `defcolumns` change written as one conjunctive query between two schemas can generate both the forward migration and a round-trip test, and the counit's failure to be an isomorphism *is* the kernel the lossy grade must declare. That is a mechanical source for the declared loss. Kept for after the first release, and only for the supported mappings; under D68 nothing migrates before then.
- **Fast left Kan extensions using the chase** (Meyers, Spivak, Wisnesky; JAR 2022; `meyers-spivak-wisnesky2022-fast-left-kan-extensions-chase.pdf`). Σ-migrations (unions and quotients) computed by the chase. **Cut for 5.1.1**: it is the algorithm *if* a Σ-shaped fold migration (merging keys) is ever required, and it is exactly the general construction UC §11 warns against building ahead of need.
- **Homotopical patch theory** (Angiuli, Morehouse, Licata, Harper; ICFP 2014; `angiuli-morehouse-licata-harper2014-homotopical-patch-theory.pdf`). A patch theory is a higher inductive type: repository states are points, patches are paths, and patch laws (two independent patches commute) are paths between paths. An *interpreter* is a function out of the type, so it preserves the laws by functoriality, and each patch is interpreted as a bijection. **Predicts** three things for fn2's versions. (a) **The version graph is a category, and invertibility is a property of an edge in a state, not of a grade.** Rollback needs a backward migration that is valid for the current state, the events still admitted and the outstanding contracts. A global equivalence is sufficient, not necessary: an extension rolls back by forgetting, a narrowing may be reversible on the reachable subset, and retained complementary data can make a lossy step reversible (Astra 4). (b) **2-cells are obligations, not free, and only declared ones bind.** Defining the HPT interpreter requires *supplying* the images of the declared path laws; functoriality then preserves them. Parallel routes that are not declared interchangeable need not agree. In ACL2 every declared equality of routes (`m₂₃ ∘ m₁₂ ≈ m₁₃`) is a check the migrations must pass on observations, for all future suffixes. (c) **The interpretation is the semantics, the graph is the syntax.** The declared graph and its laws are data, and the migration functions are the interpreter, which keeps the declarations reviewable apart from the code. Under D68 fn2 has no version graph before its first release, so Experiment D is specified and deferred (§4).
- **Operation-based versioning as a foundation for live executable models** (Exelmans, Teodorov, Vangheluwe; SoSyM, published 2024-10; `exelmans2024-operation-based-versioning-live-executable-models-sosym.pdf`). Record both design edits and interpreter *execution steps* as operations in one versioned history, so a live edit becomes a merge. The authors' own correction: recording only write-after-write dependencies missed conflicts between execution steps and edits, and they had to add **read-after-write** dependencies (§1.1). **Predicts:** fn2's Decide functions need *conservative, enforced* dependencies on what they read, derived through the actual access boundary rather than a hand-written list, which would miss helpers, configuration and authorization state (Astra 8). A change in a dependency's identity changes the composed interpretation identity and triggers a compatibility check. It does not by itself change command semantics, because an observationally equivalent representation change of a fold leaves its readers' behaviour alone.
- **Project Cambria** (Litt, van Hardenberg, Henry; Ink & Switch, 2020; `litt-vanhardenberg-henry2020-project-cambria-translate-data-with-lenses.txt`; HN 24699615). Bidirectional lenses between schema versions, composed along a graph so every version reads every other. **Predicts** two things, both post-release under D68. Translate-on-read is the mechanism a previous-format reader would use, though STORAGE reclaims physical placements, so what must be preserved is required meanings and evidence, not every old encoding forever (Astra 5). And Cambria composes lenses along *any* path in the graph without checking that routes declared interchangeable agree, which is the gap Experiment D's harness closes.
- **Lenses for partially-specified states** (Matsuda, Nguyen, Wang; 2026-01; `lenses-partially-specified-states2026-2601.04573.pdf`). Several views share a source; update intentions are partially specified and partially ordered, which gives merge semantics and a refined update preservation. **Predicts** the law Experiment C checks for two projections that edit one record: field-level partial edits from two views merge by field, and the merge is the fold over field-edit events. Beyond that restricted language, UC §7.1 stands: **no general lens framework**.
- **Edit lenses** (Hofmann, Pierce, Wagner; POPL 2012). Not fetched (both hosts returned HTML; gap). Diskin's delta lenses (`diskin-xiong-czarnecki2011-delta-based-bidirectional-transformations.pdf`, already here) cover the use made of them.
- **Online schema evolution is (almost) free for snapshot databases** (Hu, Wang, Zhou; VLDB 2023; `online-schema-evolution-almost-free-snapshot-databases2022-2210.03958.pdf`). Tesseract models a schema change as a data modification of the whole table (DDaM) under MVCC, so snapshot readers keep the old schema and the change is transactional and online. **Predicts** the post-release boundary rule (§3.2(i)): a revision is a committed event with a position. `exactly-at(p)` reads for `p` before the revision interpret under the old version, and the migration's own work is ordinary charged maintenance behind a frontier (UC §2.4), never a stop-the-world rewrite.
- **Unison: "the big idea"** (Unison docs, current; `unison2026-docs-the-big-idea-content-addressed-code.txt`; HN 27652677). Definitions are identified by the hash of their syntax tree, and names are separate metadata. **Predicts** decision 3, corrected by Astra (9): an interpretation's identity is the content Name of a canonical *manifest* binding the declaration and the transitive closure of the definitions, constants and macro expansions it depends on. A hash of the declaration alone is not enough: `machines-a.lisp`'s declarations call helpers such as `fn2-connection-reply`, so a helper could change under an unchanged declaration hash. Unison names definitions by hash *with* their dependencies' hashes. In ACL2 the manifest is computable from the world (each supporting function's normalized body), but it is a real component, not a macro line. The checkpoint's fold/schema field is currently `(:id schema)`, not a digest, so adopting a Name is also an encoding decision.
- **Build systems à la carte** (Mokhov, Mitchell, Peyton Jones; ICFP 2018; `mokhov-mitchell-peytonjones2018-build-systems-a-la-carte.pdf`). The essay's "Blaze" is Google's build system (Bazel outside); the paper classifies it as a builder with *constructive traces* keyed by content hashes, which permits early cutoff. **Cut** (Astra 10). The draft predicted early cutoff for a projection rebuilt after a revision when output digests matched. That is false across revisions: two counters can both read zero at a checkpoint while one steps by one and the other by two. Reuse needs the same computation and dependencies, or a certificate that the retained states have identical future behaviour, which is the migration certificate itself.
- **Dynamic software updates using CRDTs** (Wyns, Bauwens, Gonzalez Boix; 2026-06; `dsu-using-crdts2026-2606.10920.pdf`). Application code replicated as a CRDT under a semantic-version total order, with API-compatible message delivery so partially updated components keep working. **Predicts** *(placement)* what UC §6.2 already says: peers at different revisions interoperate only through a declared protocol version, and a reply branch that changes what the client must do is a new protocol version.

### 1.4 Simulation and observational equivalence as transport

- **Verifying equivalence of database-driven applications** (Wang, Dillig, Lahiri, Cook; POPL 2018; `wang-dillig-lahiri-cook2018-verifying-equivalence-database-driven-applications.pdf`) and **Synthesizing database programs for schema refactoring** (Wang, Dillig et al.; PLDI 2019; `wang2019-migrator-synthesizing-database-programs-schema-refactoring.pdf`). Equivalence of two programs over two schemas, proved by a bisimulation invariant of a restricted form, a conjunction of equalities between relational queries over the old and new schemas, inferred automatically. Migrator then synthesizes the new program from the old one and the target schema. **Predicts:** the simulation relation for a `defcolumns` revision has a *searchable* shape, per-table equalities `πcols(T₁) = q(T₂)`. For the supported mappings of UC §2.5 the migration declaration can *be* that relation, and the per-event-kind step obligation is checked against it. Experiment B states its relation in this form.
- **An abstract account of up-to techniques for inductive behavioural relations** (Sangiorgi; 2024-12; `abstract-account-up-to-techniques-inductive-behavioural2024-2412.07351.pdf`). Up-to techniques transported to trace-like (inductive) relations. With Pous's "coinduction all the way up" (LICS 2016; not fetched, the hosts returned HTML; gap). **Predicts** one refinement of UC §2.2's certificate. A migration or summary certificate may be a *relation* `R ⊆ S₁ × S₂` that is closed under the steps up to UC's *all-future* observational congruence (present-answer equality is not enough, Astra 2), not only a function. That is the form that passes Astra's `(n mod 2, 0)` counterexample (UC §13 item 2): relate `n` to `(n mod 2, k)` for every `k`. Experiment A's generic contract therefore takes a relation, with a function as the common special case.
- **Abstract stobjs** (Kaufmann, Moore; ACL2 2013; `kaufmann-moore2013-abstract-stobjs-isa-modeling.pdf`) and **codewalker** (`hardin2015-acl2-codewalker-llvm.pdf`, already here). The ACL2 side of simulation: `defabsstobj`'s correspondence theorems are a per-operation simulation between a concrete and an abstract machine. **Predicts** *(placement)*: EXEC §5's stobj/ATC correspondence and every layout revision share one proof shape, a per-operation simulation against the abstract view.
- **The clocks are ticking: no more delays!** (Bahr, Grathwohl, Møgelberg; LICS 2017; `bahr-grathwohl-mogelberg2017-clocks-are-ticking-clocked-type-theory.pdf`). Clocked type theory for guarded recursion. **Cut**: productivity of infinite observers is not an obligation fn2 states, and ACL2 has no guarded types. Hur et al.'s parameterized coinduction (paco, POPL 2013) is **cut** for the same reason (metadata only, not fetched).

### 1.5 The essay's sources

- **Incremental live programming via shortcut memoization** (Kirisame, Porter et al.; 2026-03; `chordata2026-incremental-live-programming-shortcut-memoization-2603.19560.pdf`). Learns multi-step "shortcuts" over CEK machine states with abstracted variables, reaching speed-ups up to 13.03× on Hazel edit traces at 19.97× memory overhead. **Cut**: it predicts that a projection rebuild after a small revision could reuse work, but fn2's folds take bounded per-event steps over a journal already summarized by design, and a 20× memory cost is the wrong trade for a node whose resident memory is profiled (EXEC rule 9). Performance would be published, never a gate, and nothing asks for it.
- **Live functional programming with typed holes** (Hazelnut Live; Omar, Voysey, Chugh, Hammer; POPL 2019; `omar2019-hazelnut-live-live-functional-programming-typed-holes.pdf`). Evaluation proceeds around holes, and *fill-and-resume* continues from the previous evaluation state, justified by a commutativity theorem: filling then evaluating equals evaluating then filling. **Predicts** a narrow resume rule: when a revision only adds observations that depend on event kinds that did not exist before it, the new fold resumes from the old state instead of refolding, and the obligation is the ornament coherence of §1.1 read in time. The analogy is limited (Astra 1). Hazel resumes because it *retains* the closures and environments of its holes, while a fold that ignored an event retains nothing, so a new observation over old event kinds cannot resume and needs a refold or a declared gap.
- **Bidirectional evaluation with direct manipulation** (Sketch-n-Sketch; Mayer, Kunčak, Chugh; OOPSLA 2018; `mayer2018-sketch-n-sketch-bidirectional-evaluation-direct-manipulation.pdf`). Output edits pushed back into the program. **Cut**: a put side over programs, which UC §7.1 already declined.
- **World age in Julia** (Belyakova, Chung, Gelinas, Nash, Tate, Vitek; OOPSLA 2020; `belyakova2020-julia-world-age-in-julia.pdf`). A running call sees the method table as of the *world age* when control last left top level. Definitions made by `eval` become visible only on re-entry, which is what lets optimized code stay valid. Only 4-9% of 4,000 packages use the bypass (`invokelatest`). **Predicts** the activation rule, with one correction (Astra 6): work in progress runs under the revision in force when it started, and a revision takes effect for new activations at a definite boundary. Julia's rule cannot be copied for Decide. A Decide that spans turns (budget exhaustion leaves a continuation, EXEC rule 3) and was started under r17 would commit *after* the r18 boundary, and a position-indexed revision map would misattribute it. So a Decide revision activates only when no command of the revised set holds a continuation in that domain, or the crossing command is revalidated under the new revision before it commits. Continuation migration (Julia's bypass) is a separate, explicit act, and Julia's measurement says it is rarely needed.
- **Kitsune** (Hayden, Smith, Denchev, Hicks, Foster; OOPSLA 2012; `hayden2012-kitsune-dynamic-software-updating-for-c.pdf`; HN 4885466 and 9811095). Whole-program dynamic update at programmer-declared update points, with state transformers generated by `xfgen` from short declarative specifications. The retrofit costs 57-159 changed lines per C program, plus 27-200 lines of xfgen (HN 4886332, quoting the paper's table). One of the authors: "We are talking 100-300 LOC even for applications that are 100 KLOC. And these changes are robust in the sense that once you retrofit to include them, you rarely need to make further changes of that sort" (HN 9813906). **Predicts:** the update point for a machine-kind revision is the turn boundary, where no transition is mid-flight (EXEC rule 2), and the state transformer per machine row is *generated from the two `defmachine` declarations* for the cases xfgen covers (a field added with a default, a field removed, a state renamed). Only the remaining cases are hand-written.
- **Theseus** (Boos, Liyanage, Ijaz, Zhong; OSDI 2020; `boos2020-theseus-operating-system-structure-state-management.pdf`). An OS structured to minimize *state spill* (one component holding state that belongs to another) so components can be replaced live. **Predicts** the precondition for a machine-kind revision, as corrected by Astra (16): no *untracked, representation-dependent alias* into the revised kind's state. Copying an immutable value is harmless, and a generation-checked handle prevents stale-slot reuse, not interpretation under the wrong layout. fn2's machine directory carries only `(kind, slot)`, with fields in each kind's own struct of arrays (`machines-a.lisp`, header comment), so the rule is mostly kept *(placement)*. What a restart adds is handle invalidation: every handle names an incarnation that a restart retires.
- **Operation-based versioning** (SoSyM 2024): see §1.3.
- **Practitioners on event versioning** (Scry over `hackernews.items`): "you need to keep support for old event versions forever, and either need code to" upcast them (HN 38930591); "Our event store is not immutable. Instead we will run migrations to rewrite the events ... You either have to either deal with the complexity of maintaining two versions of code or the complexity of migrating" (HN 13344350); a per-event version date with cascading version logic "lets us replay events as they happened, run an event using two different versions and perform only the diffs" (HN 17821626); and the failure case, replaying old transaction logs under new code: "Imagine if everytime your rebooted your Postgresql cluster and it replayed Postgres 7 transaction logs, even though your running on Postgres 13, and generated an objectively different state" (HN 28703963). These are the four options: keep old interpreters (world age), rewrite history (forbidden in fn2: the journal is append-only), version each event (the record header's `schema-version`), and the bug that a positioned revision prevents. Before its first release fn2 takes a fifth, by ember's ruling D68: wipe and rebuild (§2.3).

---

## 2. The versioned-world essay mapped onto fn2's algebra

### 2.1 The two coordinates
The essay's world has two coordinates, program revision and execution history. In fn2 the execution history is the **Log** (one per commit domain, positions as prefixes; UC §1.1). The program-revision axis has four kinds of thing that can change, each a revision of one of UC's irreducibles or of the executor:
- a **fold or projection interpretation**, a revision of a **Fold** (PLANES §4.2's `id` and `version`);
- a **record format**, a revision of what an event *is* on disk (a `deflayout` and the `schema-version :u8` in every record header, `format.lisp`);
- a **machine-kind revision**, a revision of a `defmachine` (fields, states, continuations), which is the executor's own code;
- a **Decide revision**, a revision of the command processor at a domain's head, which changes what an accepted command means from then on.

**Name** has no revision. A content name is a commitment and never changes meaning, which is why it is the right identity for the other four (decision 3).

The essay's identity triad maps cleanly:
- **entity identity** is a Name or an exact Message-ID (STORAGE decision 6);
- **revision identity** is the identity of the interpretation that produced a value;
- **presentation name** is the projection `id` string or a command word.

fn2 has the first and third. The second exists only as integers chosen by authors (`version`, `schema-version`), and nothing prevents two different interpretations carrying the same integer. Decision 3 addresses that.

### 2.2 The five operations: what fn2 has, what it lacks, what the lack costs

| essay operation | fn2 mechanism | status | what the lack costs |
|---|---|---|---|
| **execute** | Decide at the head, Folds over the Log, machines under the scheduler | has | nothing |
| **edit** (a new program revision) | a new projection version "with its own coverage" (PLANES §4.2); a new `deflayout`; a new `defmachine`; a new Decide | *by ruling, a wipe and rebuild* (D34, D68) before the first release; no declaration relates a revision to its predecessor | nothing before the first release, by design. Afterwards every revision is a restart, and `exactly-at(p)` is ill-defined across a revision because nothing says which interpretation was in force at `p` |
| **migrate** (change representation, keep meaning) | STORAGE decision 1's "valid bootstrap or migration rule" for summaries; EXEC's abstract views | *named, no form*: no certificate shape, no checked obligation | summaries are migrations of a fold to a smaller representation, and they are owed now. Without the certificate shape, each summary rule is argued by hand (Experiment A supplies it) |
| **materialize** | projections, `at-least(p)` and `exactly-at(p)` reads, `catch-up` (UC decision 2) | has, once UC decision 2 lands | nothing |
| **fork** (explore with recorded effects; promote separately) | the simulator: profile, seed, observation order, fault choices and revision recorded (EXEC rule 10); transient-to-durable promotion by a referencing commit (ADDENDUM item 3) | *half*: forks exist only in the simulator, and the only promotion is of transient items within one history | an exploratory branch cannot be promoted into the live world (question (c) below) |

The essay's three modes of change, and where each stands:
- **"Revise the computation"** (recompute from new code) is a projection rebuild from retained history. fn2 has this wherever history is retained, and D68's wipe and rebuild is its whole-node form.
- **"Evolve the activity"** (keep the past, change future behaviour) is a new Decide from a boundary onward. fn2 lacks it, and by D68 does not need it before the first release. After that it needs a positioned revision with a crossing rule (§3.2(iv)).
- **"Migrate the state"** (change representation, keep meaning) is, inside one release, exactly a summary (a fold migrated to a representation that forgets history the contract does not observe). fn2 names it and has no form for it.

### 2.3 The three concrete questions

**(a) Can fn2 today change a fold's interpretation without losing coverage?**
- *Before the first release:* the question does not arise. A changed interpretation is a new build, and D68 makes the node a wipe and rebuild.
- *Within one release, between a fold and its summary:* this is the case STORAGE decision 1 permits ("discarding semantic history requires an identified summary rule, proved as an observation-preserving simulation"), and coverage is preserved exactly when the summary's certificate holds. The certificate has no stated shape. Experiment A gives it one: a relation closed under each event kind's step, up to all-future observational congruence.
- *After the first release, if D68 is revisited:* a new interpretation of a fold whose history is retained refolds from history start, losing nothing and reusing nothing. For a fold whose history sits behind a summary there are two outcomes. Coverage can start at the summary position with the earlier range declared unavailable (PLANES §4.2's `coverage` field), a permanent gap in every `exactly-at` answer before it. Or a migration from the old summary state is needed, with a certificate. Coverage then transfers *at the converted state's cut*, not at the revision position (Astra 3), and no historical snapshot is created.

**(b) Can fn2 change a record format with its proofs intact?**
- *Codec level, yes, by regeneration:* `deflayout` regenerates the encoder, decoder and their correspondence obligations from the layout expression (`layout.lisp`: "Correspondence obligations refer to the generated exports"). A new layout gets its codec obligations without anyone writing them. They are owed, not proved (OWED.md), but they are owed *automatically*, which is transport by re-derivation and the best kind.
- *Semantic level, not needed:* D38's withdrawal and D68 say no reader of a previous format exists. So a v2 fold never reads a v1 record, and the semantic upcasting problem (the practitioner failure "replayed Postgres 7 transaction logs ... on Postgres 13", HN 28703963) cannot occur.
- *What the lack would cost after the first release:* each format change would be a manual audit of every fold that reads the record kind. Two parts of the format would also need a compatibility boundary first: maintenance records without semantic event numbers, and allocation and physical-reference records (`format.lisp`; Astra 5).

**(c) Can fn2 promote a simulator branch into the live world?** No. A simulator run is its own history with its own incarnation, and its recorded effects are simulated completions. No operation takes a branch's *commands* and offers them to the live head, where Decide would recompute each against the live state (rebase, UC §7.1 item 2) and refuse by name where the branch's assumptions no longer hold. **Cost:** the essay's what-if use (plan in a branch, promote what still holds) is unavailable. It is not needed for 5.1.1, and the mechanism it would need already exists: commands carry their binding as a precondition (STORAGE decision 1), and Decide refuses a moved head by name. So **promotion of a branch would be command replay with rebase, not state merge**. That rules out the SoSyM paper's state-merge model for fn2, because fn2's state is never the authority (UC §7). Building it is deferred. The prediction is that it needs no new primitive.

### 2.4 "This happened under r17"
The essay's sentence: "observations remain valid as 'this happened under revision r17' while becoming invalid as evidence about r18". fn2 already keeps the first half, since journal entries are never rewritten and STORAGE's retry contract returns the *original* outcome to a retrier. Under D68 the second half does not arise before the first release, because there is no r17 history beside r18.

Afterwards it needs two coordinates, the position and the interpretation identity, because neither determines the other (Astra 6):
- A position-indexed map of revisions misattributes a Decide that started under r17 and committed after r18's boundary. §3.2(iv) therefore forbids that crossing or revalidates it.
- `at-least(position of r18)` may return an answer produced under r19.

So a read that asks for "evidence about r18" names both a position and an interpretation, and a historical read may request a specific projection version. "The version in force at `p`" is one policy, not the only well-defined semantics.

---

## 3. Transport as fn2's migration discipline

The discipline has two parts. The first applies now, inside one release, under D68. The second is the evolution discipline for after the first release. It is specified, not built, so that the DSLs record enough to support it if ember revisits D68 then (decision 1).

### 3.1 Now: transport between representations of one interpretation

**(i) The certificate.** One shape serves every representation change fn2 makes inside a release: a summary replacing retained history (STORAGE decision 1), a layout change under a fixed logical view (EXEC rule 1), and the stobj and ATC realizations (EXEC §5). Between representations `S₁` and `S₂` of one interpretation, it states:
- the **admissible states** of each (the reachable or invariant-satisfying ones);
- an **initial relation** `R(init₁, init₂)`;
- **step preservation per event kind**: `R(s₁, s₂) ⇒ R(δ₁(s₁, e), δ₂(s₂, e))` for each event kind `e`, up to UC's *all-future* observational congruence (present-answer equality is not enough);
- **observation agreement**: `R(s₁, s₂) ⇒ obs₁(s₁) = obs₂(s₂)` for the observations the retained contract names (UC §2.2: by reference to existing contract observations).

A relation, not a function, is the general form: it is what passes Astra's `(n mod 2, 0)` counterexample (UC §13 item 2). It establishes *behavioural* equivalence and nothing more. An **executable converter** (a bounded, resumable function from an `S₁` state to an `S₂` state) is a separate artifact with its own correctness obligation, `R(s, convert(s))` (Astra 2). STORAGE's summaries need both.

**(ii) Three levels of evidence, never conflated** (Astra 17), as fn2 already distinguishes them:
- a *tested implementation* (unit tests and simulator scenarios: refuting evidence, never a proof);
- a *recorded obligation* (`defthm-owed`, which creates no theorem);
- a *proved theorem*.

STORAGE already requires discarding history to be "proved as an observation-preserving simulation", so no coverage claim rests on the first two. A negative experiment needs an *evaluated witness* that satisfies the domain assumptions and falsifies the equation. A `must-fail` on its own can succeed because automation failed on a true statement.

**(iii) Theorems are stated through the interface.** A fold's theorems are stated over constrained `init`, `step` and `obs`, in a contract that each representation instantiates (Experiment A). A theorem that names a representation accessor is, by construction, not transportable and is re-proved on every representation change. This is the structure identity principle as an engineering rule, and functional instantiation, `propagate-iso` and `defabsstobj` are its ACL2 implementations.

**(iv) Interpretation identity is a manifest Name** (decision 3). It is the content Name of a canonical manifest: the declaration plus the normalized bodies of the transitive closure of the functions, constants and macro expansions it depends on, computed from the ACL2 world. The simulator records it as the run's revision (EXEC rule 10), and the checkpoint claim's fold/schema field binds it. That field is `(:id schema)` today, so adopting the Name is an encoding decision. This is a component, not a macro line (Astra 9).

**(v) Dependencies are conservative and enforced.** A Decide's or projection's dependencies on folds are derived through the actual access boundary, not listed by hand. A change in a dependency's manifest Name changes the composed interpretation's Name and triggers a compatibility check. It does not, by itself, change command semantics (Astra 8).

**(vi) Composition.** A check that composes wired behaviours is unsound over undeclared shared state (§1.2). Any compositional check fn2 adopts models each shared table (allocator, pool, accounts) as a component with declared events on the scheduler's common timeline (Experiment E).

### 3.2 After the first release, if D68 is revisited: the evolution discipline

**(i) A revision takes effect at a definite durable boundary.** A fold or projection, a record kind's format, or a Decide for a command set is revised by a committed record in the owning domain (Tesseract's DDaM). It names the old and new interpretation Names and the migration, if any. Work in progress finishes under the interpretation it started with (world age), except Decide (iv). A read names both a position and an interpretation (§2.4).

**(ii) A migration declares what it preserves, and only that transports.**
- It states its admissible states, its event correspondence, the §3.1(i) certificate between the old and new interpretations, and its converter.
- Coverage transports **at the converted state's cut**: if the old materializer is at `c` when the conversion runs, the new interpretation is covered from `c`, and later processing advances it. No historical snapshot or previously unavailable `exactly-at` answer is created (Astra 3).
- The four labels the draft proposed (equivalence, extension, lossy, reinterpretation) survive only as *summaries of evidence*, never as authorizations (Astra 2, 18):
  - an **extension** needs coherence on every admitted event, with the old meaning of each new event kind declared, plus a separate justification for each new observation (it is covered only if no event before the cut could have affected it; otherwise it is refolded or a declared gap);
  - a **lossy** migration declares its kernel as an identification relation;
  - the default, with no certificate, is reinterpretation, PLANES §4.2's "new version with its own coverage".
- Rollback needs a backward migration valid for the current state, the events still admitted and the outstanding contracts. An equivalence is sufficient, not necessary (Astra 4).
- Routes declared interchangeable must agree on observations for all future suffixes (Experiment D's harness). Undeclared parallel routes need not.

**(iii) Formats.** A format revision restricted to semantic records is an alphabet map `u : E₁ → E₂`. For a context-free, one-to-one conversion its obligation is `σ(δ₁(s, e)) = δ₂(σ(s), u(e))` per reading fold, with initialization, observations and domain invariants (Astra 5). That obligation covers none of the following:
- framing, decoder bounds, the authentication of original bytes, or physical recovery records (maintenance, allocation, relocation; `format.lisp`), which need a stated compatibility boundary first;
- whole-record constraints (lengths, references, identity bindings), which sit beside the per-field relations;
- narrowing, which needs evidence that every required old record remains interpretable.

What is preserved is the required meanings and evidence, not every old encoding, since STORAGE reclaims placements. The compatibility boundary also says what a node does on an unknown required version, including when decoding the revision record itself (Astra's addition 3).

**(iv) Decide.** Two rules:
- *Crossing:* a Decide revision activates only when no command of the revised set holds a continuation in the domain, or the crossing command is revalidated under the new revision before commit (§1.5, Astra 6).
- *Compatibility:* the revision states a **named compatibility relation** per obligation kind. It must preserve authorized discharge, fencing, retry outcomes and retained promises, and mere expressibility of an evidence formula is not enough (replacing "authorized receipt" with `true` is expressible). This is checked when the revision is *built*, over the finite set of declared obligation and lease kinds. At commit, the revision record's Decide makes only a bounded check that no kind lacking a compatibility relation has outstanding instances, read from a per-kind count maintained as an ordinary fold, never an unbounded scan (Astra 7).

Waivers stay as STORAGE decision 3 limits them: an operator may waive only an unsatisfiable obligation.

**(v) Machine kinds.** A revision is a restart under an explicit shutdown contract, preserving borrows and uncertain commits. "Drain" cannot mean waiting indefinitely for long-lived connections, parked consumers and maintenance rows (Astra 16). Handles name an incarnation that the restart retires. `pin` and `migrate` (Kitsune-style generated per-row transformers) are deferred.

**(vi) Retention of interpretation artifacts** (Astra's addition 2). Declarations, converters, decoders and summaries remain available for exactly the historical answers and retries still promised.

**(vii) The scenario that gates it** (Astra's addition 1). Two prepared batches, an old activation, the revision's installation, a retry, and recovery at every persistence and install cut. The check: every outcome is attributed to its actual producer interpretation, and every retry returns the original outcome.

### 3.3 What the DSLs must record

| DSL | now (inside one release) | after the first release, if D68 is revisited |
|---|---|---|
| fold contract | `init`, `step` per event kind and `obs` as a constrained-function contract each representation instantiates; summaries carry the §3.1(i) certificate and a converter | migrations as certificates between interpretations |
| `defprojection` (PLANES §4.2) | the interpretation's manifest Name, once the projection plane is built; `version` as an alias | `migrates-from`; `on-source-revision`; per-reader compatibility |
| `deflayout` | nothing new: codec obligations already regenerate per layout | per-field relations, whole-record constraints, the compatibility boundary |
| `defmachine` | nothing new; the alias rule is mostly kept *(placement)* | the shutdown contract; later `pin` and `migrate` |
| Decide / command grammar | dependencies derived through the access boundary | the crossing rule; per-kind compatibility relations; the revision record kind (added with its producer, D46) |

Nothing here is a new checker (SEAT). The certificate is UC §2.2's HISTORY property in relational form, and the compositional check, if adopted, is a TRACE scenario.

---

## 4. Five experiments, specified

Placement. Experiments A and B are pure ACL2 with no fn2 dependency, and they go in `~/dev/acl2aiguide/examples/transport/`, certified with `examples/certify.sh transport/<book>.lisp` (ACL2 8.7, laptop, seconds each). Experiments C, D and E touch fn2's shapes and go in a lane worktree, `git -C ~/dev/fn worktree add build/lanes/fn2/x-transport -b fn2/x-transport fn2/main`, under `fn2/experiments/transport/` and `fn2/tests/`, certified with `fn2/tools/certify.sh`. None adds a checker (SEAT). Each experiment states its acceptance, its teeth as *evaluated witnesses* (a `must-fail` is supplementary, never the only tooth; §3.1(ii)), and what passing would and would not show.

| experiment | size | when |
|---|---|---|
| A. A fold and its summary, by a relational contract | a day | now |
| B. Column theorems carried by `propagate-iso` | a day | now (the DSL variant is a week, deferred) |
| C. A field-edit lens, laws at the view level | a day | when an editing consumer exists |
| D. Declared 2-cells between migration routes | a day | when two real migration routes exist (after the first release, under §3.2) |
| E. Wiring three components against the composite | a week | after layer D's machines and per-kind trace projection exist |

### Experiment A: a fold and its summary, related by a relational contract (a day; now)

**Idea tested:** §3.1(i)-(iii). Summary adequacy is transport between two representations of one interpretation, certified per event kind by a relation, and theorems stated through a constrained interface transfer by functional instantiation. The relation must be chosen *stronger than the observation*, and the experiment's main tooth shows why.

**The fold:** monotone read-state for one (consumer, group), a fold fn2 will have (UC §9.3, mailbox read-state). Events are `(:read n)` (article `n` read) and `(:catchup h)` (all articles `≤ h` read). There are two observations: `(obs-read s n)`, "is article `n` read?", and `(obs-count s b)`, the number of read articles `≤ b`. The second is the non-pointwise case Astra raised (11).

**Files and declarations** (`~/dev/acl2aiguide/examples/transport/`):
- `fold-contract.lisp`: the **relational** two-representation contract. One `encapsulate` exports `fc1-step`, `fc2-step`, `fc1-obs`, `fc2-obs`, `fc1-ok`, `fc2-ok` (admissibility) and `fc-rel`, with three constraints:
  - `fc-rel-step`: `(implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2)) (and (fc1-ok (fc1-step s1 e)) (fc2-ok (fc2-step s2 e)) (fc-rel (fc1-step s1 e) (fc2-step s2 e))))`;
  - `fc-rel-obs`: `(implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2)) (equal (fc1-obs s1 q) (fc2-obs s2 q)))`;
  - admissibility of the initial states, with `fc-rel-init`.

  `fc1-fold` and `fc2-fold` fold the steps over a list. The generic theorem `fc-rel-fold`, `(implies (and (fc1-ok s1) (fc2-ok s2) (fc-rel s1 s2)) (fc-rel (fc1-fold s1 j) (fc2-fold s2 j)))`, is proved once by induction on `j`. Its corollary `fc-obs-fold` says the observations agree after every suffix.
- `read-state-history.lisp`: the retained-history representation. The state is the event list itself, and `rs-h-obs-read` scans it, returning a Boolean (`(if (member-equal ...) t nil)`, since `member` returns a list tail, Astra 11).
- `read-state-summary.lisp`: the summary representation `(hwm . above)`, with `above` a sorted list of reads strictly above `hwm`, compacted after each step (drop entries `≤ hwm`, then advance `hwm` while `hwm + 1 ∈ above`). It defines the admissibility predicate `rs-s-ok` (sorted, strictly above `hwm`, compacted) and the converter `rs-summarize`, a fold of the summary step over a history.
- `read-state-transport.lisp`. Here `fc-rel` is instantiated as `rs-same-reads`, a `defun-sk` saying that the history and the summary agree on `obs-read` for *every* article. It contains:
  - the per-event-kind lemmas `rs-same-reads-of-read` and `rs-same-reads-of-catchup`;
  - `rs-obs-count-agree`: agreement on every article implies agreement of `obs-count`, by induction on `b`;
  - `rs-summary-adequate`, by `:functional-instance fc-rel-fold`: from any related pair, the two representations agree on both observations after every suffix;
  - the converter's correctness `rs-summarize-related`, `(rs-same-reads j (rs-summarize j))`.

**Teeth** (evaluated witnesses in `read-state-teeth.lisp`):
- *A relation equal to the observation is too weak.* Take `fc-rel` as "equal `obs-count` at every bound". The pair `s₁ = ((:read 1))` and `s₂ = ((:read 2))` (both as histories) has equal counts at bound 2, and after the suffix `((:read 1))` it has counts 1 and 2: `(assert-event (not (equal (obs-count (fold s1 '((:read 1))) 2) (obs-count (fold s2 '((:read 1))) 2))))`. This is the delayed-divergence case: equal now, different after one event. It is why the certificate's relation must be closed under the steps rather than mere equality of present answers.
- *A buggy summary.* `rs-s-bad-step` advances `hwm` when `hwm + 2 ∈ above`, an off-by-one in compaction. The witness: `(assert-event (equal (rs-s-bad-obs-read (rs-s-bad-fold (rs-s-init) '((:read 1) (:read 3))) 2) t))` while the history says `nil`. The supplementary `(must-fail (defthm rs-s-bad-same-reads-of-read ...))` records that the per-event-kind lemma does not go through.

**Acceptance:** the five books certify. `rs-summary-adequate` uses only the functional-instance hint and the per-event-kind lemmas. Both witnesses evaluate as stated.

**What it would show:** that STORAGE's summary obligation has a concrete, reusable proof shape (a relation, admissibility, one lemma per event kind, a converter), that the relation must be strictly stronger than the observation, and that fn2's fold theorems can be written once over a constrained interface. **What it would not show:** storage-level historical availability. The theorem is about future observations of the retained contract, not about which past `exactly-at` answers remain (Astra 11).

### Experiment B: column theorems carried across a representation change by `propagate-iso` (a day; now)

**Idea tested:** proof transport across *development* revisions. Under D68 the data is wiped, but theorems about a table's users must survive a change of the table's representation. The experiment also exhibits, as witnesses, the partiality of widened representations (Kappelmann) and the non-transport of a lossy change.

**The table:** a consumer cursor row. v1 is `(registration :u32) (position :u60) (generation :u60)`, in the shape of `defcolumns`' declaration language (`fn2/books/columns.lisp`). v2 splits the position into `(epoch :u32) (seq :u32)`, with `position = epoch · 2³² + seq`. The experiment works on the **logical row view** (an alist per row), never the stobj accessors: `propagate-iso` does not handle stobjs or mutual recursion (`propagate-iso-doc.lisp`), and the logical view is where fn2's theorems are stated (EXEC rule 1). A correspondence between the logical row and the served columns is a separate obligation, and this experiment says nothing about it (Astra 12).

**Files and declarations** (`~/dev/acl2aiguide/examples/transport/`):
- `cursor-v1.lisp`, in two layers.
  - **Base functions**: `cur1-rowp`, `cur1-position`, `cur1-generation`, `cur1-with-position`.
  - **Users**: `cur1-advance (row p)`, forward-only (returns `row` unchanged when `p < position`), and `cur1-accepts-token (row token)`, `(equal token (cur1-generation row))`. Their theorems are `cur1-advance-monotone`, `cur1-advance-idempotent`, `cur1-advance-rowp` and `cur1-advance-keeps-token`.
- `cursor-iso.lisp`:
  - `(include-book "kestrel/apt/propagate-iso" :dir :system)`;
  - the maps `cur1->cur2` and `cur2->cur1`, and `cur2-rowp` restricted to `epoch < 2²⁸`, so that its image is exactly the `u60` range;
  - `(defiso cur1-iso-cur2 cur1-rowp cur2-rowp cur1->cur2 cur2->cur1 :thm-enable :all-nonguard :hints ...)`, in the form of `kestrel/apt/propagate-iso-test-1.lisp`;
  - **the author-supplied part**: the v2 base functions and, for each base function, its two correspondence theorems, written by hand and listed in `fn-iso-specs` (`(cur1-position cur2-position cur1-position-->cur2 cur2-position-->cur1 (cur1-rowp) => *)` and the like);
  - `(propagate-iso cur1-iso-cur2 <fn-iso-specs> :first-event cur1-advance :last-event cur1-advance-keeps-token)`.
- `cursor-v3-lossy.lisp`: v3 drops `generation`. A `defmapping` from v1 to v3 records the one-way map, with no inverse theorem.

**Teeth** (evaluated witnesses):
- *Partiality.* With `cur2-rowp-unrestricted` admitting `epoch < 2³²`, the v2 row with `epoch = 2²⁸, seq = 0` maps under `cur2->cur1` to position `2⁶⁰`: `(assert-event (not (cur1-rowp (cur2->cur1 row))))`. This is the concrete failure of the backward image obligation that makes the unrestricted `defiso` inadmissible.
- *Lossy non-transport, tested against stale-incarnation rejection* (Astra 12). Two v1 rows differing only in `generation` map to one v3 row, yet they accept different tokens: `(assert-event (and (equal (cur1->cur3 r1) (cur1->cur3 r2)) (not (equal (cur1-accepts-token r1 5) (cur1-accepts-token r2 5)))))`. So no v3 version of `cur1-accepts-token` can exist, and the kernel of the lossy map is exactly the identification of generations.

**Acceptance:**
- `cursor-iso.lisp` certifies;
- `cur2-advance-monotone`, `cur2-advance-idempotent`, `cur2-advance-rowp` and `cur2-advance-keeps-token` exist in the world (`(assert-event (theorem-namep 'cur2-advance-monotone (w state)))`, with `std/system/theorem-namep`);
- the only hand-written v2 proofs are the base functions' correspondence theorems;
- both witnesses evaluate.

The report counts the hand-written lines against the propagated ones (Astra's addition 4: a real cost measurement).

**Deferred variant (a week; a layer-A quest, SEAT's one DSL owner):** `defcolumns` would emit the `defiso` and the base correspondence theorems from a `:representation-of` clause, so that development-time layout changes carry their users' theorems automatically. It is decided on B's measured cost ratio, not before.

**What it would show:** that theorems about a table's users can be carried across a representation change for the price of its base functions' correspondence; that the restriction to the image is required; and that a lossy change is detected by a concrete behavioural witness. **What it would not show:** that the logical row corresponds to the served columns, or that `propagate-iso` scales to fn2's generated accessor families.

### Experiment C: a field-edit lens, laws at the view level (a day; when an editing consumer exists)

**Idea tested:** UC §7.1 item 3's one candidate, the lens for field-level edits of a declared record schema whose lift is "append the edit events". Also Matsuda et al.'s merge of partial updates from two views. Astra (13) found the draft's PutPut false as stated. The corrected experiment fixes a *complete* field domain.

**Trigger:** a consumer that edits records: helm's room or premise records, or a collaborative document's metadata (UC §9.3). Without one, the experiment would settle a law nobody uses.

**Files and declarations** (lane `fn2/x-transport`):
- `fn2/experiments/transport/field-lens.lisp`:
  - `*fl-fields*`, a declared field list with a default per field;
  - `fl-recordp`, a total, canonical-order alist over exactly `*fl-fields*`;
  - `fl-get (j)`, the defaults overridden by the fold of `(:set field value)` events, latest per field;
  - `fl-diff (old new)`, one `:set` per field whose value differs, in declared order;
  - `fl-put (v j)`, `(append j (fl-diff (fl-get j) v))`.

  The theorems:
  - `fl-putget`: `(implies (fl-recordp v) (equal (fl-get (fl-put v j)) v))`;
  - `fl-getput`: `(equal (fl-put (fl-get j) j) j)`, which holds *at the journal level* for this language, because the diff is empty;
  - `fl-putput`: `(implies (and (fl-recordp v1) (fl-recordp v2)) (equal (fl-get (fl-put v2 (fl-put v1 j))) (fl-get (fl-put v2 j))))`, which holds now that records are total;
  - `fl-two-views-commute`: puts through two views with disjoint field sets commute at the view level.

**Teeth** (evaluated witnesses):
- *Outcome-owing puts.* `fl-put-with-outcome` appends `(:outcome op-id)`, as a consequential command must (UC §7.1). Then `(assert-event (not (equal (fl-put-with-outcome (fl-get j) j 7) j)))` for `j = nil`, while `fl-get` of it equals `(fl-get j)`. GetPut fails at the journal level *only* for commands that owe outcomes.
- *Overlapping views.* Two views that both own field `:title`, with puts `"a"` and `"b"`, give different results in the two orders.
- *Journal PutPut.* The journal after two puts differs from the journal after one, because the journal remembers `v1`.

**Acceptance:** the four theorems certify, the three witnesses evaluate, and a random test over the simulator's PRNG (`fn2/sim/prng.lisp`) finds no view-level violation in 10,000 cases.

**What it would show:** that the restricted, total-record language is a lawful lens at the view level. GetPut also holds at the journal level for it, and fails there exactly when puts owe outcomes. Only then, with the consumer in hand, would a `defrecord-edit` form be justified. **What it would not show:** anything for richer update languages (ordered insertion, moves), which need UC §5.4's occurrence identities.

### Experiment D: declared 2-cells between migration routes (a day; when two real routes exist)

**Idea tested:** §1.3's homotopical patch theory reading, as corrected (Astra 4, 14). Routes *declared* interchangeable must agree on observations for all future suffixes. Rollback needs a backward migration valid in the current state. A lossy step must satisfy its own migration law.

**Trigger:** fn2's first post-release migration that has two real routes, for example a direct converter beside a chain of two. Under D68 none exists. The toy family below tests the harness, not the idea, and is written only when the trigger arrives.

**The versions** (harness instance): read-state history (h), summary (s) and run-length (r) from Experiment A's family, plus a **fixed-domain lossy** version `w` that ignores reads of articles above a declared bound `N` and declares `obs-read` unavailable for `n > N`. The draft's windowed version violated its own migration law, because discarded reads become relevant as the window moves (Astra 14). A fixed domain does not.

**Files and declarations** (lane `fn2/x-transport`):
- `fn2/experiments/transport/version-graph.lisp`:
  - the graph as data, `(defconst *rs-graph* '((h s m-hs) (s h m-sh) (s r m-sr) (h r m-hr) (r w m-rw)))`;
  - the declared 2-cells, `(defconst *rs-2cells* '(((m-hs m-sr) (m-hr)) ((m-hs m-sh) ())))`, the second saying `m-sh ∘ m-hs` is the identity on observations;
  - the migration functions;
  - `rs-route`;
  - `rs-rollback (from to state graph)`, which returns `:refused` unless a backward edge is valid *for the given state*.
- `fn2/tests/version-graph-unit.lisp`: exhaustive over every journal of length ≤ 6 on `{(:read 1..4), (:catchup 0..4)}` (9⁶ = 531,441 journals) and every split. For each declared 2-cell, fold the source over the prefix, apply each route, fold the target over the suffix, and compare both observations at every suffix position. It also checks `m-rw`'s own law (`obs-read` agrees for `n ≤ N`, `:unavailable` above).

**Teeth** (evaluated witnesses): `m-hr-bad` ignores `catchup`, and the test prints its first counterexample, which is immediate for these pointwise dynamics. Delayed divergence belongs to Experiment A's count tooth, since pointwise read-state cannot exhibit it (Astra 14). A deliberately windowed `m-rw-bad` fails `m-rw`'s law on `W = 2`, `hwm = 0`, reads `{3}`, then `(:read 1) (:read 2)` (Astra's witness).

**Acceptance:** zero differences for the declared 2-cells and for `m-rw`'s law, and both bad migrations caught with their witnesses.

**What it would show:** that declared route equality is a cheap, decisive check that Cambria-style lens graphs lack. **What it would not show:** unbounded equality. Experiment A's theorem is the proof route; D is the refutation harness.

### Experiment E: three components wired, checked against the composite (a week; after layer D)

**Idea tested:** §1.2's compositional check and shared-state rule, with the composition semantics the draft lacked (Astra 15).

The real kinds are `fn2-listener` and `fn2-echo` (`fn2/books/machines-a.lisp`). Their interaction is not a capability on a wire. `fn2-listener-admit` (`machines-a-run.lisp`) reads `fn2-machine-free-head`, `fn2-machine-active-count` and `fn2-machine-connection-count`, reserves a pool slot with `fn2-core-reserve`, and writes the echo row. So the experiment models **three** components, with declared events:
- the listener;
- the echo kind;
- an **allocator** owning the machine free list, the active and connection counts and the pool reservation, with `request-row`/`grant-row(slot, gen)`/`refuse-row` and `release-row`.

**Composition semantics** (what makes the equality meaningful):
- a common timeline given by the scheduler's calendar visits (EXEC rule 4), which every component sees;
- stuttering steps allowed;
- completions correlated by operation identity (`fn2/books/vocab.lisp`);
- resource ownership and initialization stated per component;
- one global trace bound `L`, applied to the composite timeline rather than to each component separately.

**Files and declarations** (lane `fn2/x-transport`):
- `fn2/experiments/transport/wiring.lisp`:
  - `fn2-x-kind-trace (component trace)`, projecting a simulator trace onto one component's declared events with the calendar index kept;
  - `fn2-x-compose (b1 b2 b3)`, the relational composite over shared events on the common timeline;
  - `fn2-x-interface`, the declared events of each component.
- `fn2/tests/wiring-three.lisp`, on the tiny profile with exhaustive bounded schedules and fault choices (EXEC rule 10):
  - each component's behaviour under an environment offering every legal input;
  - the composite's behaviour from the real simulator;
  - the check `B_composite = fn2-x-compose(B_listener, B_echo, B_allocator)` up to `L = 12` on the common timeline, as sets.

**Teeth** (evaluated witnesses): a *two*-component composition that treats the capability as the wire and omits the allocator must fail. With connection capacity 1 it admits a second connection that the composite refuses, and the test prints that trace. A variant with two echo rows and one pool slot shows the pool as the shared state in the same way.

**Acceptance:** equality for the three-component composition, the two-component one refuted with its witness, and, as published information (never a gate), the state counts of the per-component explorations against the composite's.

**What it would show:** whether per-component checking is sound and smaller for fn2's real kinds once shared tables are components, which is the intended compositional reduction Astra asks to be named before the work. It would also make UC §1.2's footprints a soundness condition. **What it would not show:** anything about the fast plane until an external executor exists. The same harness applies there, with PLANES §4.5's records as the declared events.

---

## 5. The cost, and the risks

### 5.1 What fn2 uses of each idea, and what it does not build (in the style of UC §11)

| idea | too general because | fn2 uses | not built |
|---|---|---|---|
| univalence, HoTT, the structure identity principle | an axiom identifying equivalence with equality; higher paths at every level | the rule that theorems are stated through the declared interface | univalence; higher inductive types; cubical machinery |
| Trocq's graded parametricity | six classes per direction, computed per goal | the principle that a migration declares what it preserves, and each carried theorem is checked against that | a parametricity translation; grade labels as authorizations |
| partial Galois connections (Kappelmann) | relators for every type former | the witness that a widened representation is an isomorphism only onto its image (Experiment B) | per-field relators in `deflayout` (post-release, if D68 is revisited) |
| proof repair (Pumpkin Pi, quotient repair) | proof-term transformation for any equivalence | the certificate's shape: admissible states, initial relation, per-event-kind step preservation, observation agreement, a separate converter | a proof-term transformer: ACL2's functional instantiation and `propagate-iso` do the transfer |
| ornaments | ornament algebras over indexed datatypes | extension coherence on every admitted event, with new observations justified separately (post-release) | ornament-generic programming |
| categorical systems theory, double categories, polynomial functors | doctrines of systems, modules over double categories, behaviours of every shape | the rule that wired-behaviour composition needs shared state modelled as components; one bounded-trace check (Experiment E) | a systems-theory framework; other behaviour shapes; dynamic rewiring |
| homotopical patch theory | higher inductive types, interpretation into a universe | declared 2-cells checked on future suffixes (Experiment D, deferred) | path algebra; route search; automatic 2-cells; equivalence-only rollback |
| functorial data migration, the chase, co-evaluation | arbitrary schema functors; Σ by the chase | nothing before the first release; afterwards, supported mappings with author-supplied value maps | CQL; a Σ engine; a query language |
| lenses (Cambria, delta, edit, partial-state) | general view update, combinator libraries, lens graphs | the total-record field-edit lens when an editing consumer exists (Experiment C) | a lens library; upcasters (D68) |
| DSU (Kitsune, Theseus, world age, CRDT updates) | live update of arbitrary code and heap | restart under a shutdown contract; the alias rule; the Decide crossing rule (post-release) | live `pin` and `migrate`; continuation migration; resident dual revisions |
| build systems, incremental live programming | traces for every task; memoization over machine states | manifest Names as interpretation identity | early cutoff across revisions (false); Chordata-style shortcuts |
| up-to techniques, coinduction | companions, enhancement lattices | relational certificates closed up to all-future congruence | an up-to library; guarded or clocked types |

### 5.2 What is worth doing now, sized for 5.1.1 (amended by Astra 18)

| item | now | deferred | cut |
|---|---|---|---|
| summary certificate (relational, per event kind, with converter) | yes: STORAGE owes it | — | — |
| fold theorems over a constrained interface | yes: the C4 folds' declaration shape | a generic fold-theorem library | — |
| interpretation identity as a manifest Name | when the projection plane is built (an encoding decision for the checkpoint field) | machine-kind Names | a declaration-only hash |
| enforced dependencies | where a current check uses them | — | hand-written read lists |
| revision record kind, crossing rule, compatibility relations, retention of interpretation artifacts | — | after the first release, if D68 is revisited; the kind lands with its producer (D46) | — |
| migration grades, `on-source-revision`, upcasters, version graphs | — | same | grades as authorizations; equivalence-only rollback |
| early cutoff across revisions | — | — | cut (false) |

### 5.3 The risks

1. **The CQL failure, in small units** (UC §11; HN 30075577; Astra 18). The cost of an evolution discipline is in converter retention, dependency identity, activation ordering, historical interpretation, recovery, compatibility checking and resource accounting, not in file count. That is why D68 is worth keeping through the first release (decision 1), and why nothing in §3.2 is built before then.
2. **Labels mistaken for evidence.** A grade an author declares and nothing checks would let coverage be inherited on its say-so. The rule is that a label summarizes a certificate and never authorizes one (§3.2(ii)).
3. **Bounded checks mistaken for proofs.** Experiment D's journals and E's length-12 traces refute; they do not prove. A `must-fail` can pass because automation failed on a true statement, so every tooth is an evaluated witness (§3.1(ii)).
4. **A manifest Name that misses a dependency.** If the manifest omits a helper, a constant, a macro expansion or configuration state that the interpretation reads, two interpretations share a Name. The manifest is computed from the ACL2 world, never listed by hand, and its first test is a helper change that must change the Name.
5. **The draft's own error, kept as a warning.** The first draft of this note built a full version-to-version migration discipline against a KEEP ruling it had not read (D68). Any later proposal to build §3.2 starts by reopening D68 with ember.
6. **`propagate-iso`'s maturity.** It is a Kestrel tool with tests but without fn2-scale use. Experiment B measures it first, and the deferred DSL variant is decided on that measurement.

---

## 6. Five decisions for ember

1. **Keep D68 through the first release; specify, do not build, the evolution discipline.** Before the first release every revision is a wipe and rebuild, as ruled. §3.2 records what a post-release discipline needs:
   - revisions at definite durable boundaries;
   - a Decide crossing rule;
   - migrations as certificates, with coverage transported at the converted cut;
   - rollback by a valid backward migration;
   - declared 2-cells;
   - per-kind compatibility relations with a bounded commit check;
   - a shutdown contract for machine kinds;
   - retention of interpretation artifacts;
   - the crash scenario that gates it.

   No revision record kind is added before its producer (D46). *Recommended yes*: transport between versions has a real and large lifecycle cost (Astra 18), ember's ruling already prices it at zero before release, and §3.2 keeps the design ready for the day D68 is reopened.
2. **Adopt the relational per-event-kind certificate for summaries now.** A summary rule is admitted with admissible states, an initial relation, per-event-kind step preservation up to all-future congruence, observation agreement for the retained contract's observations, and a separate converter with its correctness. The three evidence levels stay distinct, and only a proved certificate permits discarding history (as STORAGE already requires). *Recommended yes*: STORAGE owes these proofs, this is their shape, and Experiment A shows why the relation must be stronger than the observation.
3. **Identify interpretations by a manifest Name, when the projection plane is built.** The Name is the content Name of the declaration plus the normalized transitive closure of its dependencies, computed from the ACL2 world. It is recorded as the simulator's revision and bound by the checkpoint claim's fold/schema field (an encoding change from `(:id schema)`), and `version` becomes an alias. *Recommended yes, scoped*: it makes "never an in-place change" a fact, and it is a component with its own test (a helper change must change the Name), not a macro line.
4. **State fold theorems through a constrained interface, and carry representation changes by ACL2's own transport.** Fold contracts are constrained `init`, `step` and `obs`, instantiated per representation. Development-time representation changes carry their users' theorems by functional instantiation or `propagate-iso`, and layout changes under a fixed logical view by abstract-stobj correspondence. *Recommended yes*: it is how the owed statements survive the DSLs' churn during development, the proof-repair problem fn2 actually has under D68.
5. **Run Experiments A and B now; E after layer D; C and D on their triggers.**
   - A and B go in `acl2aiguide/examples/transport/`, a day each, and B reports its hand-written-to-propagated cost ratio.
   - E is a week, on the real listener and echo kinds with the allocator as a third component, once layer D's machines and the per-kind trace projection exist. It is the one experiment that answers ember's "what is worth composing with the server" question with a measurement.
   - C waits for an editing consumer, and D for two real migration routes.
   - None of the frameworks of §5.1 is built.

   *Recommended yes*: two days decide decisions 2 and 4 on evidence, and E is the composition question asked concretely.

---

## 7. Astra's round, folded in

One round, `codex exec -m gpt-6-astra -s read-only` on the first draft, detached with a PID file. The prompt is `fn2/transport-astra.prompt`, the answer `fn2/transport-astra.md` (Astra's words), and the log `fn2/transport-astra.log`. Astra's verdict, verbatim: "**Do not adopt §6 as written.** The useful core is a version-specific simulation certificate and an explicit activation boundary. The note repeatedly turns sufficient proof techniques into mandatory machinery—the mistake UC §13 rejected." Six findings were fatal and twelve material, and all eighteen are accepted. The largest consequence came from item 18: the draft had missed ember's KEEP ruling D68, and the note now keeps it (decision 1) and splits the discipline into a part for now (§3.1) and a specified part for after the first release (§3.2).

| # | Astra's attack | severity | disposition | where |
|---|---|---|---|---|
| 1 | extension coherence only on old event kinds does not preserve old theorems; `φ ∘ ℓ = id` says nothing about new fields' history; Hazel retains closures | **fatal** | accepted: coherence on every admitted event with declared old meaning; new observations justified separately; Hazel analogy limited | §1.1, §1.5, §3.2(ii) |
| 2 | "equivalence" conflates behavioural equivalence, isomorphism and an executable converter; up-to must mean all-future congruence; four labels are not a restriction of Trocq | material | accepted: relation certificate plus a separate converter; all-future congruence; labels are fn2's proposal | §1.1, §1.4, §3.1(i) |
| 3 | coverage transfers at the converted state's cut, not the revision position; kernels are identification relations; a summary is not lossy | **fatal** | accepted | §1.3, §2.3(a), §3.2(ii) |
| 4 | rollback needs a valid backward migration, and equivalence is only sufficient; only declared routes must agree; the HPT interpreter needs the path laws' images supplied | material | accepted | §1.3, §3.2(ii), Experiment D |
| 5 | a format revision is an alphabet map only for restricted semantic changes: framing, bounds, authentication and physical records are outside it; whole-record constraints; narrowing; meanings, not encodings, are preserved | material | accepted, and moot before the first release under D68 | §1.1, §1.3, §2.3(b), §3.2(iii) |
| 6 | the revision-vector Fold misattributes a pinned r17 Decide committing after r18; position and interpretation are separate coordinates | **fatal** | accepted: Decide crossing rule; reads name both coordinates | §1.5, §2.4, §3.2(i), §3.2(iv) |
| 7 | "expressible" evidence formulas preserve nothing; the Π-check is an unbounded scan | **fatal** | accepted: named per-kind compatibility relation checked at build time over finite kinds; bounded commit check from a per-kind count fold; waivers as STORAGE limits them | §3.2(iv) |
| 8 | a fold revision in a read set need not change Decide semantics; hand-written read lists miss dependencies; downstream readers discharge their own compatibility | material | accepted: conservative, enforced dependencies trigger compatibility checks | §1.3, §3.1(v) |
| 9 | a declaration hash misses changed helpers; the checkpoint field is `(:id schema)`, not a digest | **fatal** | accepted: manifest Name over the transitive closure; an encoding decision | §1.3, §3.1(iv), decision 3 |
| 10 | equal output digests do not justify early cutoff across revisions | **fatal** | accepted: cut | §1.3, §5.1 |
| 11 | Experiment A's pointwise transition is a restricted lemma; `member` is not Boolean | material | accepted: relational contract; pointwise read-state as an instance; a non-pointwise count observation; Booleanized membership | Experiment A |
| 12 | `propagate-iso` needs supplied base correspondence theorems; the unrestricted tooth needs a concrete witness; lossy should be tested on stale-token rejection; the logical row says nothing about served columns | material | accepted | §1.1, Experiment B |
| 13 | the unconditional PutPut is false (`v1 = {x:1}`, `v2 = {}`); `fl-getput` holds at journal level, so the blanket claim contradicted the experiment | material | accepted: total records over a declared field domain; journal GetPut fails only for outcome-owing puts; C waits for a consumer | Experiment C |
| 14 | the windowed lossy version violates its own law; delayed divergence cannot occur in pointwise dynamics | **fatal** | accepted: fixed-domain lossy version; delayed divergence moved to A's count tooth; Astra's witness used as D's lossy tooth | Experiments A, D |
| 15 | variable sharing also composes; Myers's construction is lax; E lacks timeline, scheduler, ownership, correlation, stuttering and a global bound; `fn2-listener-admit` is an allocation protocol | material | accepted: three components with the allocator; the composition semantics stated | §1.2, §3.1(vi), Experiment E |
| 16 | the state-spill rule is neither necessary nor sufficient; "drain" cannot wait indefinitely | material | accepted: no untracked representation-dependent aliases; restart under a shutdown contract | §1.5, §3.2(v) |
| 17 | owed statements and failed proofs promoted into evidence; `must-fail` can pass on a true statement | material | accepted: three evidence levels; evaluated witnesses for every tooth | §3.1(ii), §4 |
| 18 | the cost table repeats the CQL failure in smaller units; "formats will change before release" establishes no compatibility duty, especially under D68; several items restate STORAGE, EXEC and PLANES | material | accepted whole: D68 kept (decision 1); §5.2 resized to Astra's keep/defer/cut; restatements marked *(placement)* | §0, §2, §3, §5, §6 |

**Astra's verdicts on the draft's decisions, and where they went.** All five were "amend":
- revision events become decision 1's specified post-release discipline, with Astra's producer binding realized as the crossing rule;
- grades become decision 2's certificate, with labels as summaries of evidence;
- content Names become decision 3's manifest;
- the Decide read set and Π-check become §3.2(iv)'s compatibility relation and §3.1(v)'s enforced dependencies;
- the experiments become decision 5's schedule.

**Astra's four additions, all adopted:** the revision crash scenario (§3.2(vii)); the retention contract for interpretation artifacts (§3.2(vi)); the explicit compatibility boundary (§3.2(iii); before the first release D68 is that boundary); and a real cost measurement, which Experiment B reports as its hand-written-to-propagated ratio, and on which B's DSL variant is decided.

**Where this note and Astra still differ.** On one point of scheduling. Astra would defer Experiment E "until ... intended exploration reduction exist[s]". This note names that reduction (per-component exploration of listener, echo and allocator against the composite) and schedules E for when layer D's machines exist, because E is the only experiment that answers ember's question about composing with the server with a measurement rather than an argument. On substance there is no remaining difference.

---

## 8. Bibliography

All sources are in `~/paperbin/` under the filenames cited inline. The 46 fetched for this note (44 PDFs with `.txt` beside each, two web texts) are annotated with what each predicts for fn2, or why it is cut, in the "Transport and higher categories" section of `~/paperbin/README-fn2-20261028.md`.

**Transport, univalence, proof transfer.** `cohen-crance-mahboubi2024-trocq-proof-transfer-for-free.pdf`; `kappelmann2023-transport-via-partial-galois-connections-equivalences.pdf`; `ringer2021-proof-repair-across-type-equivalences-pumpkin-pi.pdf`; `cosmo-ringer2023-proof-repair-across-quotient-type-equivalences.pdf`; `dagand-mcbride2012-transporting-functions-across-ornaments.pdf`; `tabareau-tanter-sozeau2021-marriage-univalence-parametricity.pdf`; `hott2013-homotopy-type-theory-univalent-foundations-book.pdf`; `rijke2022-introduction-to-homotopy-type-theory.pdf`; `ahrens-north-shulman-tsementzis2021-univalence-principle.pdf`; `vezzosi-mortberg-abel2021-cubical-agda-dependently-typed-univalence-hits.pdf`; `kaufmann-moore2013-abstract-stobjs-isa-modeling.pdf`.

**Categorical systems theory.** `double-operadic-theory-of-systems2025-2505.18329.pdf`; `myers2023-categorical-systems-theory-book-draft.pdf`; `myers2020-double-categories-of-open-dynamical-systems.pdf`; `double-categories-open-systems-cospan-approach2025-2509.22584.pdf`; `baez-courser2020-structured-cospans.pdf`; `patterson2023-structured-decorated-cospans-double-category-viewpoint.pdf`; `libkind2020-algebra-of-resource-sharing-machines.pdf`; `nondeterministic-behaviours-double-categorical-systems-theory2025-2502.02517.pdf`; `niu-spivak2023-polynomial-functors-mathematical-theory-of-interaction.pdf`; `shapiro-spivak2022-dynamic-categories-dynamic-operads.pdf`; `compositional-program-verification-polynomial-functors-dtt2026-2604.01303.pdf`; `capucci-gavranovic-hedges-rischel2021-towards-foundations-categorical-cybernetics.pdf`.

**Migrations, versions, lenses.** `living-databases2026-continuous-schema-evolution-versioning-2605.00676.pdf`; `schema-evolution-interactive-programming-systems2024-2412.06269.pdf`; `wisnesky2024-relational-to-rdf-migration-query-coevaluation.pdf`; `aguinaldo2024-robot-task-plans-functorial-data-migrations.pdf`; `meyers-spivak-wisnesky2022-fast-left-kan-extensions-chase.pdf`; `angiuli-morehouse-licata-harper2014-homotopical-patch-theory.pdf`; `exelmans2024-operation-based-versioning-live-executable-models-sosym.pdf`; `litt-vanhardenberg-henry2020-project-cambria-translate-data-with-lenses.txt`; `lenses-partially-specified-states2026-2601.04573.pdf`; `online-schema-evolution-almost-free-snapshot-databases2022-2210.03958.pdf`; `unison2026-docs-the-big-idea-content-addressed-code.txt`; `mokhov-mitchell-peytonjones2018-build-systems-a-la-carte.pdf`; `dsu-using-crdts2026-2606.10920.pdf`.

**Simulation and equivalence.** `wang-dillig-lahiri-cook2018-verifying-equivalence-database-driven-applications.pdf`; `wang2019-migrator-synthesizing-database-programs-schema-refactoring.pdf`; `abstract-account-up-to-techniques-inductive-behavioural2024-2412.07351.pdf`; `bahr-grathwohl-mogelberg2017-clocks-are-ticking-clocked-type-theory.pdf`.

**Live programming and dynamic update.** `chordata2026-incremental-live-programming-shortcut-memoization-2603.19560.pdf`; `omar2019-hazelnut-live-live-functional-programming-typed-holes.pdf`; `mayer2018-sketch-n-sketch-bidirectional-evaluation-direct-manipulation.pdf`; `belyakova2020-julia-world-age-in-julia.pdf`; `hayden2012-kitsune-dynamic-software-updating-for-c.pdf`; `boos2020-theseus-operating-system-structure-state-management.pdf`.

**Reused from earlier passes.** `coglio2020-acl2-apt-isomorphic-data-type-transformations.pdf`; `hardin2015-acl2-codewalker-llvm.pdf`; `diskin-xiong-czarnecki2011-delta-based-bidirectional-transformations.pdf`; `mimram-digiusto2013-categorical-theory-of-patches.pdf`; `spivak2010-functorial-data-migration.pdf`; `rutten2000-universal-coalgebra-theory-of-systems.pdf`. ACL2 8.7 system books: `kestrel/apt/propagate-iso.lisp` and its `-doc` and tests, `kestrel/apt/isodata.lisp`, `std/util/defiso.lisp`, `std/util/defmapping.lisp`, `std/testing/must-fail.lisp`, `std/system/theorem-namep.lisp`; the worked example `~/dev/acl2aiguide/examples/books/encapsulate-fi.lisp`.

**Practitioner threads** (Scry over `hackernews.items`): 24699615 (Project Cambria); 4885466 and 9811095 (Kitsune; comments 4886332 and 9813906 quoted in §1.5); 27652677 (Unison); event-versioning comments 13344350, 17821626, 28703963 and 38930591 (quoted in §1.5); 30075577 (CQL, UC §11's cautionary case).

**Gaps.** Huffman-Kunčar's "Lifting and Transfer" (CPP 2013), Pous's "Coinduction All the Way Up" (LICS 2016), Hofmann-Pierce-Wagner's "Edit Lenses" (POPL 2012), Williams-Rémy's ML ornaments (POPL 2018), Hur et al.'s paco (POPL 2013) and Young's *Versioning in an Event Sourced System*; their stand-ins are named in the README section.

---

## 9. Experiments A and B: results

Both experiments were run on 2026-10-28, and they are in `~/dev/acl2aiguide/examples/transport/` (public, github.com/emberian/acl2aiguide). There are nine books, all certified with `examples/certify.sh` (ACL2 8.7, laptop), each in under 6 s. The directory's `README.md` holds the full account. B needed APT's closure certified on the laptop for the first time: about 160 community books, in 62 s at `-j 4`.

**Experiment A: done, and the idea holds.** `fold-contract.lisp` proves `fc-rel-fold` and `fc-obs-fold` once, from an `encapsulate` whose relation is a parameter. In `read-state-transport.lisp`, the relation is `rs-same-reads`, a `defun-sk` saying history and summary agree on `obs-read` for every article. The instance costs three per-event-kind lemmas (`:read`, `:catchup`, and malformed events) and `rs-obs-count-agree` (the non-pointwise count, by induction on the bound). Then `rs-summary-adequate` is two `:functional-instance` hints and nothing else: from a related admissible pair, `(:read n)` and `(:count b)` agree after every suffix. The converter is a separate theorem, `rs-summarize-related`. Sizes: the contract is 58 code lines, written once; the read-state instance is 43 + 117 + 92.
- Tooth 1, *the relation must be stronger than the observation.* Take the observation "count read up to 2". `((:read 1))` and `((:read 2))` both give 1, and after `(:read 1)` they give 1 and 2. This is evaluated, and proved as `rs-count2-rel-not-step-closed`. The functional instance's own step obligation is proved false at that pair (`rs-count2-rel-step-obligation-false`), and the instance `rs-count2-rel-fold` is refused.
- Tooth 2, *a buggy summary.* `rs-s-bad-step` has an off-by-one in compaction. It says 2 is read after `(:read 1) (:read 3)`. `rs-bad-step-breaks-relation` proves that a related pair steps to an unrelated one, and `rs-s-bad-same-reads-of-read` is refused.

**Experiment B: done; transport works, and at toy scale it saves nothing.** v1 is `((:registration . r) (:position . p) (:generation . g))` as a logical alist row. v2 splits the position into epoch and seq. `apt::propagate-iso` generated 15 events with their proofs, and no hint was written for any of them. They are `cur2-advance` and `cur2-accepts-token`; the v2 versions of all 9 v1 theorems in the range, including `cur2-advance-monotone`, `-idempotent`, `-rowp` and `-keeps-token` (checked by `theorem-namep`); and both directions of the correspondence for each new function. The only hand-written v2 proofs are the 6 correspondence theorems of the 3 base functions.

| | code lines |
|---|---|
| hand-written (v2 base functions 25, maps 11, `defiso` and theory 6, correspondence theorems 20, the `propagate-iso` call 10) | **72** |
| generated statements and definitions, 15 events | **71** |
| generated full expansion with proof instructions | 1,242 printed |
| v1 source those 15 events were generated from | 42 |

**The pessimistic number:** 72 lines were written to obtain 71. The hand-written part is about 15 lines per base function and is mechanical. The generated part grows with users and their theorems. So the measurement supports the deferred `defcolumns :representation-of` variant only where users far outnumber base functions, which is to be counted on fn2's real tables before that week is spent.
- Tooth 1, *a widened representation is an isomorphism only onto its image.* With the epoch a full u32, the row with epoch 2^28, seq 0 maps to position 2^60, outside `cur1-p`. This is proved as `cur2-wide-witness` and `cur2-wide-beta-image-false`. DEFISO `cur1-iso-cur2-wide` is refused at `:beta-image`. Restricting the epoch to u28 makes the image exact.
- Tooth 2, *dropping the generation breaks stale-token rejection.* v3 has no generation, and `defmapping cur1-to-cur3` records the one-way embedding. DEFISO `cur1-iso-cur3` is refused at `:beta-of-alpha`, so there is nothing to propagate along. The rows `(7 100 5)` and `(7 100 6)` share one v3 image but answer token 5 differently. `no-v3-token-check` proves this for an unconstrained `cur3-accepts-token`, so it holds for every function on v3 rows.

**Three findings for the deferred variant's design:**
1. A theorem transports only if its hypotheses put the row in the isomorphism's domain. An unconditional v1 theorem failed to propagate, so `defcolumns`-generated theorems should be stated under the row recognizer.
2. Generated names substitute the codomain predicate's name for the domain's, after a trailing `-P` is dropped. Recognizers must be named `<t>-p` for the names to come out right.
3. Correspondence theorems must be stored disabled (`defthmd`), or the next proof loops through the maps.

Every `must-fail` was rerun unwrapped and its failure read. One had first "passed" on a lambda syntax error, which is why each tooth is an evaluated witness or a theorem that its obligation is false, as §3.1(ii) requires.

**What neither shows** (unchanged from §4): storage-level historical availability (A); that the logical row corresponds to the served columns, or that `propagate-iso` scales to generated accessor families (B).

