# The metatheory in Lean, the instances in ACL2: the division of labour (2026-10-28; Opus designer and Lean author with Astra as co-author; present state)

Brief: `build/coordinator/briefs/LEAN-METATHEORY-20261028.md`. Ember, verbatim: "is acl2 actually an appropriate and powerful enough tool to perform the metatheory? or do we need to do some reasoning about this in lean and then implement the theory in acl2 as part of our engineering?"

Read against: `DSL-METATHEORY.md` §1-3, §5, §9; `COHERENCE.md` §2-4; `HIGHER-STRUCTURES.md` entries 1 and 4; `EXECUTION-MODEL.md` §4; `TRANSPORT.md` §9; `MODAL-KERNEL.md` R4; the registry on `origin/fn2/main` at `137695dfc` (`fn2/books/machines.lisp`, `machines-a.lisp`, `columns.lisp`, `core-children.lisp`, `core-children-a.lisp`, `owed.lisp`, `tools/owed-export.lsp`); minidregg's `ATLAS.md` §6 and `docs/COORDINATION-2026-10-27.md`; nanodregg's `Spec/README.md`. Mathlib's source at the pinned revision `1c2b90b1` (`CategoryTheory/Category/RelCat.lean`, `Data/Rel.lean`) for every Mathlib name used.

The project: `fn2/meta/` on branch `fn2/lean-meta` (worktree `/Users/ember/dev/fn/build/lanes/fn2/lean-meta`). Astra's three sessions: `fn2/lean-meta-astra-1.md` (sections A-E of this note, drafted as co-author; adopted where marked **(A1)**), `fn2/lean-meta-astra-2.md` (a line-by-line elaboration review of the Lean against the 4.30 and Mathlib sources, with statement corrections and stronger witnesses, all applied; marked **(A2)**) and `fn2/lean-meta-astra-3.md` (a review of the additions, §9).

**Scope of what this note claims, in one sentence.** Every Lean theorem named below as proved is written and reviewed but **has not been typechecked**: the build box the brief names, `dregg-build`, and the lanes' second box, `dregg-ref`, no longer exist in the hcloud project (`hcloud server list`, 2026-10-28 23:0x EDT: only `dregg-anchor-fsn1`, `dregg-workhorse-fsn1`, `dregg-demo`), and the rules forbid a Lean build on the Mac and anything on hbox; so "proved" in this note means "a proof is written, with no `sorry`, awaiting its first `lake build`" until §7's command has run.

## Contents
0. The answer in one page
1. The decision rule: what is a Lean theorem, what is an ACL2 instance
2. What `fn2/meta` states and proves
3. The tenth artifact: what the DSL emits for Lean
4. How a Lean theorem licenses an ACL2 check
5. The trust story, and the mutation controls
6. What is not claimed
7. Where it runs, and what is blocked
8. Five decisions for ember
9. The Astra sessions, and where the two authors differ

## 0. The answer in one page

**ACL2 is the right home for the instances and the wrong engineering home for the frame.** Every generated square, every kit instance, every functional instantiation (the theory morphism of fn2's kits), APT's `propagate-iso`, SOFT where it qualifies, and ATC's lowering are statements about named functions of one world, and ACL2 proves them where the code is. The frame-level theorems quantify over declarations, over theories as objects and over diagrams built from squares; ACL2's first-order logic can encode those as data, but fn2 would have to build and maintain the encoding, its induction principles and its categorical vocabulary itself (A1 amends the coordinator's "ACL2 is wrong for the frame" to exactly this: wrong as an engineering home, not wrong in logic). Lean with Mathlib holds them, and the DSL emits each declaration's Lean presentation from the same registry, so the Lean model is generated data, never a transcription.

**What exists after this lane** (counts at `137695dfc`):
- a Lean project `fn2/meta` (Lean 4.30.0, Mathlib at minidregg's pin) with the fourteen declaration kinds and the registry as structures (`Fn2.Decl`), the thin double category of squares with Mathlib's `RelCat` as its tight category (`Fn2.Square`), the coherence theorem for a toy frame with its satisfiable instance and Astra's accept/close false diamond as its teeth (`Fn2.Coherence`), conservativity of an `ext`-grade revision with a faulty revision as teeth (`Fn2.Conservative`), and representation independence for clients that never inspect the representation with a peeking client and a dropped premise as teeth (`Fn2.Param`); 62 theorems in 1,375 hand-written lines, none with `sorry` or an axiom, none yet typechecked (§7);
- the emission experiment: `fn2/meta/emit/print-registry.lsp` prints layer A's four world tables from ACL2, `emit_lean.py` emits `Fn2/Instances/LayerA.lean`: **43 declarations** (3 machines, 9 columns tables, 9 core children, 22 owed rows) over a 376-symbol alphabet, and **31 machine-owned Q1 cases** (22 continuation phases + 9 observed events); the other 8 of Q1's 39 labels (router fallback, the executor's seven) are not in the registry today and are declared by hand in the facts file, flagged (§3.4);
- three mutation controls on `defmachine` (§5): a row-only mutation (the row drops each kind's first observed event) changes the emitted model in 17 lines, 31 cases to 28, breaks the pinned case counts, and is also refused by ACL2 itself at `assembly.lisp`; a field-width mutation (`deadline` u60 to u32) changes exactly the 6 rows that carry it and breaks no control; a behaviour-only mutation (`NAME-OBSERVES-P` stops excluding `:retired`) leaves the printed registry byte-identical, which is the measured limit of a table-only exporter (A1's prediction).

**What the Lean side licenses.** "If the generators commute then every route agrees" becomes `Fn2.Coherence.coherence` and `Fn2.Instances.LayerA.q1_licensed`: ACL2 owes one G1 square per catalogue case and one diamond per declared-independent pair; Lean proves that those, with a G0-related start, give equal observations along every schedule and every trace-equivalent schedule of the reference. The licence is an implication; it discharges nothing on the ACL2 side, and a checked-but-unproved ACL2 row stays owed (§4).

**What it does not do.** It does not prove the frame completeness conjecture (COHERENCE §3.2's second statement); it does not interpret any ACL2 formula; and it is not a gate (§8 decision 1).

---

## 1. The decision rule: what is a Lean theorem, what is an ACL2 instance

*Astra's section A (A1), adopted with the Opus wording of the rule's first line.*

A seat classifies a new obligation by its **subject**, without asking:

1. **About named ACL2 functions, one generated representation, one concrete square or one admitted book: ACL2.** The applicability conditions of a functional instantiation, a converter's relation, guard obligations, arithmetic bounds, preservation of outputs and effects. "Quantifies over every execution" alone does not move a statement to Lean: ACL2 proves a named machine's theorem for every admitted execution.
2. **Quantifies over declaration presentations, theories, interpretations, clients of an abstract interface, or constructions of diagrams: Lean.** Its hypotheses are stated as the properties the ACL2 instances supply.
3. **About the correspondence between an exported row and its ACL2 subject: the bridge** (§5), neither an execution theorem nor a categorical one.
4. **About physical execution, environmental evidence or eventual progress: neither becomes a coherence theorem by being registered.** X rows, liveness and fairness keep their adapter, persistence and fairness premises explicit (COHERENCE §2.3).

| obligation | ACL2's instance | Lean's theorem | what the combination establishes |
|---|---|---|---|
| **the 39 Q1 dispatch cases** | one statement per case about `fn2-transition`, `fn2-exec-account-work` and `fn2-ref-transition` under the normalised loop relation (DSL-METATHEORY §3.3); selector coverage and the exclusions | `Sq.paste_cover`, instantiated as `q1_licensed`: squares for the catalogue's cases are squares for every word over the catalogue | the 39 labels are a catalogue, not 39 proofs or 39 independent guarantees; a missing selector or unbound contract stays a missing premise (`uncovered_case_fails` is the tooth) |
| **`fn2-turn-refinement`** | its actual statement (`reference.lisp:242-255`): equal status, observation, visit and action counts, both cores well formed, the representation relation, the action and work bounds | the composition from local steps along the loop (`Sq.paste`); nothing about the instance's accounting, stopping or overflow | discharged only when its actual antecedent and every conclusion are established in ACL2; EXECUTION-MODEL §4's broader obligation stays broader |
| **the accept/close G2 candidate** | construct both legal orders at a reachable state and compare the client-visible contract; the allocator is shared (`machines-a-run.lisp:81-106`, `:126-146`) | `trace_run` (valid diamonds suffice) and its teeth `acceptClose_not_diamond`, `acceptClose_routes_disagree`, `acceptClose_footprint_dependent` | no diamond is licensed by distinct machine identities; a false candidate is classified dependent, never assumed |
| **Q9, the v3/v4 revision** | for the implemented converter and event interpretation: G0, `π(step₄(s,e)) = Fold₃(π s, h e)`, the lifting of base events | `conservative`: under that certificate every base property of runs holds of the revision iff of the base | behavioural conservativity; model expansion and converter correctness are separate obligations (A1), the new thread observations are outside it |
| **DSL-METATHEORY decision 1 (shared handlers)** | the precise refinement claim, and an independent semantic contract where one is needed | `abstraction`: clients in a declared interface language cannot tell related representations apart; its tooth `peek_breaks_abstraction` | sharing a declaration supports representation and compiler refinement; Q1 alone does not validate the shared handlers' behaviour (A1) |

## 2. What `fn2/meta` states and proves

Statement-first, per nanodregg's `Spec/README.md` and ATLAS §6 law 2: each top-level statement below has a satisfiable witness (its premises inhabited by a non-trivial instance) and teeth (a broken sibling where the conclusion fails), both as theorems. Lemmas under a top statement are not separately audited. "Proved" carries §0's scope sentence: written, reviewed, not yet typechecked.

| file | top-level statement | status | satisfiable witness | teeth |
|---|---|---|---|---|
| `Fn2.Square` | the thin double category: `Sq.seq` (along transitions), `Sq.stack` (along relations), `Sq.idLoose`, `Sq.idTight`, `Sq.interchange` (by thinness), `Loose.id_comp`/`comp_id`/`assoc`; the tight category is `RelCat` (`Tight.toRelCat_comp`, `Iff.rfl` against Mathlib's composition) | proved | `sumCorr.step`, `acIdCorr.step` are squares | structural laws, not claims about fn2 execution (A2); `Sq.iff_le_restrict` is a weakest precondition, **not** a cartesian lift, so no framing is claimed (A2's counterexample) |
| `Fn2.Square` | `Sq.paste`: vertical pasting with a stuttering label interpretation (TR Experiment A's `fc-rel-fold`) | proved | `sumCorr` (one label to one reference step) | `uncovered_case_fails` for the catalogue form |
| `Fn2.Square` | `Sq.paste_cover`: squares for a catalogue's cases cover every word over it | proved | `q1_licensed` over the emitted 39 | `uncovered_case_fails`: a case outside the catalogue is not covered |
| `Fn2.Coherence` | `trace_run`: equal two-step partial runs for declared pairs make trace-equivalent words run alike (Godefroid 3.10) | proved | `twoRecv_routes_agree`: two distinct words, one run | `acceptClose_routes_disagree`: under "different machines" the words are trace-equivalent and the runs differ |
| `Fn2.Coherence` | **`coherence`**: G0 + G1 per label + G2 on the implementation transport every successful run along `w` to a successful reference run along any trace-equivalent `w'`, observations equal | proved | `twoRecv_coherence_witness` (the whole premise package and conclusion at one state: zero counters, both orders, counters one, total two); `twoRecv_coherent` | **`acceptClose_without_g2`**: a correspondence with its G1 squares and edge, a related start, trace equivalence and a successful run, and the conclusion fails (admitted 0 against 1) (A2's restatement) |
| `Fn2.Coherence` | `footprint_independent` (from `footprint_diamonds` and `footprint_enabled`): footprint-respecting actions with disjoint footprints commute and neither enables nor disables the other (HI derived from the declaration, Godefroid 3.1 in full) | proved | `twoRecv_diamonds` (`Action.incr` respects its footprint, `incr_indep`) | for footprints: `acceptClose_footprint_dependent`, both actions respecting their own (`accept_respects`, `close_respects`); for `Respects`: `liar_indep`, `liar_not_respects`, `liar_not_diamond` (A2) |
| `Fn2.Conservative` | **`conservative`** and its content **`runs_exactly`**: under an `ext`-grade certificate (G0, a G1 square per revised event, lifting of base events) the base runs are exactly the projected, translated revised runs, so every base property of runs holds of the revision iff of the base | proved | `revision_counts`: thread annotations inherit "count = number of posts" over every word | `badRevision_breaks_counts` at one annotation, and `badRevision_annotate_not_square`: the certificate fails exactly there (A2 would also package them as one statement; not done) |
| `Fn2.Param` | **`abstraction`** / `independent`: related primitives give every non-inspecting client the same result | proved | `counter_doubled_clients` over every client (a count against twice the count) | `peek_breaks_abstraction`: one inspecting primitive separates the related pair; `drop_exec_breaks`: without command preservation a permitted client separates them (A2) |
| `Fn2.Instances.LayerAFacts` | `registry_wf` (recorded-row and cross-row consistency, the part of the macro guard the row can express, A2), `ids_qualified`, `declaration_counts`, `q1_case_counts`, `q1_square_count` | checked by evaluation (`decide +kernel`): witnesses, not theorems about the subject (law 9) | the emitted registry | the mutation controls of §5 |
| `Fn2.Instances.LayerAFacts` | `q1_licensed`: the Lean side of Q1 | proved (a specialisation of `Sq.paste_cover`; conditional on the correspondence's transitions, relation, interpretation and per-case squares) | — | `uncovered_case_fails` |
| (not stated) | the frame completeness conjecture (COHERENCE §3.2) | **not stated in Lean**; §6 says why | | |

Counts: 62 theorems (Square 15, Coherence 25, Conservative 8, Param 6, LayerAFacts 6, Decl 2), by `grep -c '^theorem'`; 0 `sorry`; 0 axioms; 1,375 hand-written lines and the 1,340-line generated `LayerA.lean`.

**The toy, concretely.** One domain of scalar positions `P → V`; an action declares `reads` and `writes`, a guard and an update; `Respects` is the frame condition (enabledness and written values depend only on reads; nothing outside writes changes); independence is `footIndep` (neither writes what the other reads or writes). Astra's witness is three positions: the allocator's free count, one echo row with an outstanding close, the admissions the client sees. `accept` reads and writes the free count and the admissions; `close` reads and writes the occupied row and the free count. Declared independent "because different machines", the diamond fails: accept-then-close refuses the connection (admitted 0), close-then-accept admits it (admitted 1). Declared by footprints, the pair is dependent at the free count, and the theorem never claims it. `Diamonds` alone (equal two-step partial runs) does not say that neither label enables or disables the other, since two labels that each disable the other satisfy it vacuously (A2); `IndependentDiamonds` adds that clause, and the footprint theorem establishes both.

## 3. The tenth artifact: what the DSL emits for Lean

*Astra's section B (A1), condensed; the structures are the ones built.*

### 3.1 Three layers, kept apart

```text
ACL2 world tables  --(print-registry.lsp, emit_lean.py)-->  Lean presentation data (Fn2.Instances.LayerA)
                    --(an explicitly supplied interpretation)-->  squares, frames, correspondences (Fn2.Square, Fn2.Coherence)
```

The first arrow preserves names, payloads and order and is generated. The second assigns meaning and is a hypothesis of every theorem that uses it (`q1_licensed` takes `stepA`, `stepB`, `h` and `R` as parameters). Fusing the arrows would make an opaque handler name look like a proof of its behaviour (A1).

### 3.2 The presentation of each kind

`Fn2.Decl` holds the four kinds layer A's world writes today, field for field, and names the other ten in `Kind`:

| kind | Lean structure | fields (the ACL2 table keys) | today's table |
|---|---|---|---|
| `machine` | `MachineDecl S` | `name states columns accounts budget continuations observes capacity initial` | `fn2-machine-kinds` (`machines.lisp:234-240`); `:layout` (a duplicate of `:columns`), `:packed`, `:obligations` (deleted by DSL-METATHEORY §5.2) and `:calling-convention` (not authoritative until R5e) omitted **by name** |
| `columns` | `ColumnsDecl S` | `name columns rowsBound extraFields initName` | `fn2-columns` (`columns.lisp:602-605`); the two `*-reasons` keys omitted by name |
| `core-child` | `CoreChildDecl S` | `field stobj init profilep reference order why` | `fn2-core-children` (`core-children.lisp:38`) |
| `owed` | `OwedDecl S` | `name vars formula teeth doc status` | `fn2-owed` (`owed.lisp:18`) |
| `square` | `SquareDecl S` | `schema owner case` (DSL-METATHEORY §3.1 reduced to what the model checks) | none yet: `bindG1` computes what `defsquare` would bind |
| the other nine | named in `Kind`; structures added with each kind's first consumer (DSL-METATHEORY decision 4), following A1's per-kind field table (`lean-meta-astra-1.md` §B) | | |

Symbols are a parameter `S`; the emitted registry instantiates it with its own finite alphabet `Sym` (376 constructors), so every well-formedness fact is decidable by evaluation, and `Sym.acl2` maps each constructor back to the ACL2 spelling the world printed. The encoding is injective (the emitter suffixes collisions and refuses an unreadable symbol); all symbols are in the `ACL2` package today, and a symbol from another package would print with its prefix and stay distinct (A1 asked for injectivity on package-qualified names).

`MachineDecl.WF` is the part of `defmachine`'s expansion guard (`machines.lisp:243-258`) the recorded row can express (it does not check symbol classes, initial-value syntax, the first column's name or the common columns; A2); `Registry.WF` adds the cross-row promises: qualified identities unique, every machine's own `defcolumns` row present with the same columns (`machines.lisp:213`), every core child's stobj declared.

### 3.3 Opaque terms are an honest boundary

A capacity `(FN2-PROFILE-ACCEPT-CREDITS PROFILE)`, an initialiser and an owed `:formula` are emitted as `Opaque` (their printed text), never as Lean terms. That preserves which term a row names, whether two rows name the same term, and whether it changed; it establishes nothing about what the term computes or whether it is true. There is no fallback that turns an unsupported formula into `True`, an axiom or a dropped row (A1). Today's `defthm-owed` stores the untranslated formula only (`owed.lisp:11-20`); the translated body the bridge needs (§4) must come from the world or from DM1's store.

### 3.4 The case catalogue and the squares

`MachineDecl.cases` gives one `CaseLabel.phase` per continuation and one `CaseLabel.event` per observed event: 31 for layer A (listener 2 + 2, echo 6 + 4, scribe 14 + 3). The router's fallback and the executor's seven labels (`CaseLabel.routerFallback`, `CaseLabel.executor`) are **not in the world today**; they are declared by hand in `LayerAFacts.nonRegistryCases`, in the hand-written facts file and never in the generated one, until the executor registers its case source (DSL-METATHEORY §3.2). A1 is right that writing them in the generated file would defeat the rule; writing them beside it, flagged, is the honest interim. `q1Cases` is the 39, `q1Squares = bindG1 "fn2-q1" q1Cases` the 39 rows `defsquare fn2-q1` would bind, and a square denotes `Sq R (stepA c) (run stepB (h c)) R` under the correspondence's interpretation.

### 3.5 How it is run

```sh
fn2/tools/certify.sh books/reference.lisp      # the registry's books (3.5 min on the laptop at 137695dfc; assembly 109 s)
fn2/meta/emit/emit.sh                          # ACL2 prints the tables; Python emits Fn2/Instances/LayerA.lean
```

The emitter refuses any row key that is neither consumed nor named as omitted, so a macro that starts recording something new stops the emission instead of being silently dropped.

## 4. How a Lean theorem licenses an ACL2 check

*Astra's section C (A1), adopted; the Lean names are the ones built.*

**The precise sentence.** For the stated frame and observation contract, if its local generators and compatibility obligations hold, every diagram constructed from those generators preserves that contract. "Every route agrees" adds a premise: the routes are connected by such a diagram (here, `TraceEq` under the declared independence). Showing that every intended interchangeable pair is so connected is completeness, a separate theorem (§6).

**Who supplies what.**

```text
Lean kernel:  coherence / q1_licensed       (the implication; parameterised by the premises)
ACL2:         one theorem per bound case     (a premise; admitted, or owed with check evidence)
the bridge:   binds that theorem's translated statement to that premise
```

Nothing is imported: no ACL2 proof object enters Lean, and no Lean axiom is generated from a proof-status row (A1). The Lean theorem stays parameterised by realisations of its premises, and the owed export records, per premise, an ACL2 proof, check evidence, or nothing.

**What crosses the boundary**, per bound obligation: the qualified owner and case identity; template, boundary and contract identity; the endpoint and helper function names (`FN2-TRANSITION`, `FN2-EXEC-ACCOUNT-WORK`, `FN2-REF-TRANSITION`, and DSL-METATHEORY §3.3's `fn2-q1-*` helpers once they exist); formals and calling convention; the source and translated formula; the proof reference (an admitted theorem whose formula is the translated one, never a matching name); the check reference (revision, profile, domain, horizon, counts, verdict); and the dependencies. A theorem proving only `fn2-core-wfp`, or the claim under an extra unestablished hypothesis, is not a match.

**When the ACL2 side is checked, not proved.** The row stays owed. A checked G1 instance is a fact about the recorded related states and transition; a checked G2 instance about the two orders exercised at that state; Lean's implication then yields a conclusion **about the runs the checks covered**, only where the intermediate states, interpretations and contracts actually join (A1's fused/unfused example: a shared recorded trajectory, never an intersection of seed numbers). A general Lean theorem never promotes finite observations to a universal premise.

**The licence for Q1, exactly.** `q1_licensed h R cases : ∀ w, (∀ c ∈ w, c ∈ q1Cases) → Sq R (run stepA w) (run stepB (expand h w)) R`, from `cases : ∀ c ∈ q1Cases, Sq R (stepA c) (run stepB (h c)) R`. With `stepA` the concrete transition selected by case, `stepB` the reference transition, `R` the normalised loop relation: if ACL2 establishes the 39 case squares, every turn word over them is a square. The entry, exit, termination, accounting and selector-coverage rows of DSL-METATHEORY §3.3 remain ACL2's, and `fn2-turn-refinement` is their composition, not a consequence of the licence alone.

## 5. The trust story, and the mutation controls

### 5.1 The one new assumption (A1, adopted)

Let `W` be the recorded ACL2 world, `E` the export (`print-registry.lsp` then `emit_lean.py`), `P = E(W)` the emitted presentation and `J` the interpretation a theorem takes as parameters. The assumption:

> For every declaration, case and obligation a claimed result uses, `P` identifies the corresponding subject in `W` without omission or conflation; and the premise `J` gives it is the property the recorded ACL2 formula states about that subject, with the same domains, boundaries, outputs, effects and observation contract.

Its clauses: **identity** (qualified names designate the same declarations, functions and events), **payload** (values and order retained; unsupported payloads explicit), **artifact** (the subjects are what was actually admitted, including assembly-section artifacts), **obligation** (catalogue entries become the intended case statements; coverage is never inferred from a catalogue's existence), **semantic** (the premise means what the formula states; opaque names do not discharge this clause), **evidence** (proof and check records belong to that subject and revision). This is the bridge's assumption, not the system's only one: ACL2's and Lean's kernels, the execution model's environment assumptions and native execution keep their own.

### 5.2 Control 1: a row-only mutation changes the model

Mutation: `defmachine`'s registry row records `:observes ,(cdr observes)` (`machines.lisp:236`), so each kind's row drops its first observed event. Run: `fn2/meta/emit/mutations/observes-row.sh` (re-certify, print, emit, restore, re-certify; its logs and mutant files land in the worktree's `build/lean-meta-scratch/`).

- **ACL2 refuses the mutant first**: `certify.sh books/reference.lisp` fails at `assembly.lisp`, in the guard proof of the generated router `FN2-MACHINE-OBSERVE` (`build/lean-meta-scratch/mut-certify.log:217`), because the router is generated from the row. The world can still be loaded without proofs, and the printer reads it.
- **The emitted model changes**: 17 changed lines (`emit/mutations/observes-row.diff`): three `observes` entries gone (`:accept-result`, `:receive-result`, `:write-result`), two symbols gone (376 to 374), events 9 to 6, machine-owned cases 31 to 28; **`q1_case_counts` (31, 39) no longer holds**, so the facts file stops typechecking by name. The diff also reorders `Sym`'s constructors (first-occurrence order), which a reviewer reads past.

**Control 1b, a field-width mutation ACL2 accepts (A1's control 1).** Mutation: the common `deadline` field narrows from `:u60` to `:u32` (`machines.lisp:8`). ACL2 certifies the mutant. The emitted model changes in exactly the 6 rows that carry the field, 12 changed lines (`emit/mutations/deadline-width.diff`): the three machine rows and the three machines' own `defcolumns` rows; `:layout` and `:packed`, which also change in the world, are omitted from the model by name. **No control fails**: the diff is the evidence, and a reviewer checks that both identities of each machine changed and nothing came from a hand-maintained fixture.

### 5.3 Control 2: a behaviour-only mutation does not (A1's prediction, measured)

Mutation: `NAME-OBSERVES-P` stops excluding the `:retired` phase (`machines.lisp:230`); the row is untouched. Run: `fn2/meta/emit/mutations/retired-behaviour.sh`.

ACL2 certifies the mutant. **The printed registry is byte-identical to the unmutated one, so the emitted model is unchanged** (0-line diff; `build/lean-meta-scratch/mutation2.log`): a table-only exporter cannot see a change to generated behaviour. This is the measured limit A1 predicted, and the case for decision 3: the `:generated` manifest must bind each emitted name to its admitted body (opaque text with a fingerprint) before the export can claim artifact fidelity.

**What a reviewer looks for.** For a row-visible mutation: both identities that carry the changed field changed (a machine row and, where it shares the field, its `defcolumns` row), every affected row was emitted, nothing was copied from a hand-maintained Lean fixture, and a pinned control fails by name. For a behaviour-only mutation: the export must either show a changed artifact payload (once the `:generated` manifest of DSL-METATHEORY §2.2 binds names to admitted bodies, emitted as opaque text with fingerprints) or report the artifact as uncovered by name. A source-revision change alone invalidates freshness but shows no artifact was captured.

### 5.4 What Lean can never establish here

Soundness of ACL2 or of its implementation; the truth of an opaque formula; that a `defthm` named in a row has the advertised statement because the name exists (only a carried translated formula makes the comparison mechanical, and even then the semantic clause needs a justified interpretation); completeness of a case catalogue because every emitted row typechecks; universal validity from bounded checks; durability, fairness or environmental integrity from simulation squares; that every intended fn2 route equality follows from the toy's generators (A1).

## 6. What is not claimed

- **Frame completeness** (COHERENCE §3.2: every pair of intended interchangeable routes is connected by generated diagrams plus declared route equations). Not stated in Lean: its "intended interchangeable" relation is a design decision per contract that no document has fixed for any fragment, and a Lean `Prop` over an invented relation would be a mirror. For the toy it would be Mazurkiewicz's projection characterisation (equal dependence-clique projections ⇒ `TraceEq`), a known theorem worth about two days; it becomes useful when a fragment (summary replacement with admitted suffixes, or one class of environment reorderings) has its relation declared.
- **State-dependent independence, residuals and the cube condition** (COHERENCE §3.3): the toy's independence is static; `Diamonds` is Godefroid's static Definition 3.1.
- **Model expansion** for Q9 (A1): every model of `T₃` expanding to a model of `T₄` with the same reduct is a different statement from `conservative`'s behavioural form and is not proved here.
- **Mixed pasting with a relation on both sides (HM) and honest loss (HQ)**: `coherence` uses G2 on the implementation side only, which needs neither; the general schema with `≈_A`, `≈_B` and `R ; ≈_B ⊆ ≈_A ; R` is the next statement (about a day).
- **Nondeterministic specifications** (Q15, Q16): frames here are deterministic; refinement into a set is containment, not equality (COHERENCE §3.2), and is not modelled.

## 7. Where it runs, and what is blocked

The rules: Lean builds on `dregg-build` under `swarm-build` as a lane under `/build/lanes/fn2-lean-meta`, never on the Mac (its `.lake` is stale), nothing on hbox. **`dregg-build` and `dregg-ref` time out on port 22, and `hcloud server list` no longer lists them**: both were torn down. So nothing in `fn2/meta` has been elaborated. The ACL2 half (certification, printing, emission, the three mutation controls) ran on the laptop, where fn2's ACL2 always runs.

In place of the elaborator, Astra's session 2 read every Lean line against Lean 4.30's and the pinned Mathlib's sources (`lean-meta-astra-2.md`) and found **no definite elaboration or proof-script failure**, citing the sources for each point that worried the author: `decide +kernel` exists in 4.30 (`Init/Tactics.lean:1315`) and is kernel reduction, not `native_decide`; the derived `DecidableEq` of a 376-constructor enum compares constructor indices (`Elab/Deriving/DecEq.lean:264`); `Tight.toRelCat_comp` is `Iff.rfl` against Mathlib's composition order (`RelCat.lean:49`, `Data/Rel.lean:148`); `subst` eliminates the right-hand variable first (`Meta/Tactic/Subst.lean:173`); it regenerated `LayerA.lean` in memory and matched the file byte for byte. A reading is not a build: execution cost (the kernel's evaluation of `registry_wf`) and resource limits are untested. Session 3 reviewed the additions made after session 2 (§9).

The command for the first box that exists (the lane's whole build; Mathlib comes from the cache):

```sh
ssh <box>; cd /build/lanes/fn2-lean-meta && git fetch origin && git checkout fn2/lean-meta
cd fn2/meta && lake exe cache get && nohup swarm-build lake build > build.log 2>&1 < /dev/null & echo $! > build.pid
grep -n "error\|sorry" build.log; grep -c "^theorem" Fn2/*.lean Fn2/Instances/*.lean
```

A red there is fixed forward on `fn2/lean-meta`; nothing here should be cited as proved before that build is green.

## 8. Five decisions for ember

*Astra's section E (A1) is the source of rows 2-4 and the pessimistic figures; row 1 is the brief's, and row 5 is the box.*

| # | decision | recommendation | pessimistic cost, and what it forecloses |
|---|---|---|---|
| 1 | **Does the Lean metatheory become a gate?** | **Not before the first release.** It is information, like certify: a failed Lean check stops an artifact being called proved; it is no shipping prerequisite. A1's qualification adopted: "information" describes release policy, not logical status (an admitted ACL2 theorem, a Lean theorem, a translated owed row and a passing check are different kinds of assurance, reported separately) | 2 engineer-days for the advisory report (freshness of the emitted model, theorem status, instance bindings, named failures); forecloses nothing; a later gate needs a concrete consumer and a measured cost |
| 2 | **What is the Lean foundation's scope?** | Presentations, the square double category, generated-diagram soundness, one `ext` revision, restricted-client parametricity (this lane's content), then the general mixed-pasting schema and the toy completeness theorem (§6) | 8 engineer-days for the foundation qualified on a box (A1), of which this lane wrote the first draft in one; forecloses using Lean for instance proofs, which stay ACL2's |
| 3 | **How strong is the bridge before an ACL2 theorem is reported as realising a Lean premise?** | Exact translated-statement binding and generated-artifact provenance (the `:generated` manifest with admitted bodies as opaque text and fingerprints); an unbound row stays visible; no axioms from proof-status rows | 7 engineer-days (A1), inside or beside DM0a/DM1; without it, control 2 shows a behaviour change passing unseen |
| 4 | **What does the emitter cover next?** | The four implemented families now (done), `fn2-layouts` when B merges, `fn2-squares` with DM1, the executor's case source with DM2; each kind's structure with its first consumer | 5 engineer-days (A1) for the B tables, identity and order checks and deterministic serialisation; forecloses emitting planned kinds before their tables exist |
| 5 | **Where do lanes build Lean now that `dregg-build` and `dregg-ref` are gone?** | Ember's call (money): reuse an existing box, or allow `fn2/meta` on the Mac (a fresh project, Mathlib from `lake exe cache get`, no stale `.lake`; its whole build is five small files and one 1,340-line generated file) | a new ccx33 is about €50/month (spend rule); the Mac exception costs nothing but breaks a standing rule; until then, every theorem here is unchecked |

## 9. The Astra sessions, and where the two authors differ

Two read-only sessions of `codex exec -m gpt-6-astra -s read-only -C /Users/ember/dev/fn`, each detached with a PID file under `build/coordinator/fn2/`.

- **Session 1** (`lean-meta-astra-1.prompt`, answer `lean-meta-astra-1.md`, log `lean-meta-astra-1.log`, PID file `lean-meta-astra-1.pid`) drafted sections A-E of this note against the code at `137695dfc`, with file:line citations. Adopted: the decision rule and its five rows (§1); the three-layer emission and the opaque-term rule (§3); the licence sentence, the boundary table and the checked-not-proved rule (§4); the faithfulness assumption and its six clauses, both mutation controls, the shared-handler control and the list of what Lean cannot establish (§5); the decisions' figures (§8). No capacity or authentication error.
- **Session 2** (`lean-meta-astra-2.prompt`, answer `lean-meta-astra-2.md`, log, PID file `lean-meta-astra-2.pid`) reviewed every Lean line as an elaborator would, against the 4.30 and Mathlib sources, and the statements for vacuity: no elaboration blocker; four overclaims corrected in docstrings (`restrict` is not a cartesian lift; `Diamonds` does not give enablement preservation; `coherence` is about successful runs; `registry_wf` checks only what the row can express); stronger witnesses proposed and built (`twoRecv_coherence_witness`, `acceptClose_without_g2`, the `liar` teeth for `Respects`, `drop_exec_breaks`, `IndependentDiamonds` with `footprint_enabled`, `runs_exactly`); the packaging of the revision teeth as one statement proposed and not done.
- **Session 3** (`lean-meta-astra-3.prompt`, answer `lean-meta-astra-3.md`, PID file `lean-meta-astra-3.pid`) reviewed only the additions and the `Sq.run` to `Sq.paste` rename (made because a `theorem Sq.x` body opens the `Sq` namespace, where `run` could resolve to `Sq.run`). ASTRA3-RESULT

| issue | Opus position | Astra position | state |
|---|---|---|---|
| ACL2's fitness for the frame | wrong tool for frame-level theorems | wrong engineering home; first-order logic can encode it, and generic relational folds already fit ACL2 | **converged** on Astra's wording (§0) |
| the eight non-registry Q1 labels | hand-declare them beside the generated file, flagged, and count 31 emitted | writing them by hand in `LayerA.lean` defeats the tenth-artifact rule; they need their own registered case sources | **converged**: they are outside the generated file and the emission count is 31; the executor's registration (DM2) removes them |
| "every route agrees" | the brief's sentence | needs its route restriction (connected by a generated diagram); completeness is separate | **converged** (§4, §6) |
| the mutation control | one row-visible mutation suffices to show the model is generated | a table-only exporter cannot see a behaviour-only mutation; run both | **converged**: both run (§5.2, §5.3) |
| `conservative` as Q9's theorem | behavioural conservativity is the content | model expansion, converter correctness and behaviour preservation are three obligations | **converged**: `conservative` is the third; the others are named in §6 |
| witness packaging | a satisfiable instance and a broken sibling per top statement | each tooth should package every retained hypothesis with the failed conclusion, and each premise should have its own tooth | **converged** for `coherence`, `footprint_*` and `abstraction` (A2's statements built); **open** for the revision teeth, which stay two theorems |
| the double category's framing | HIGHER-STRUCTURES' "framed double category", with `restrict` as the cartesian lift | `restrict` is a weakest precondition; for partial transitions restrictions do not compose, so it is not cartesian | **converged** on Astra's: no framing claimed |
| completeness in Lean now | not stated, for want of a fixed relation | (not addressed) | **open**, decided by whether a first fragment's interchangeability relation is declared (§6) |
