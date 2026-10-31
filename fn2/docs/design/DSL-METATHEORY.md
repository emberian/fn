# A metatheory for fn2's declarations (2026-10-28; Opus designer with Astra as co-author; present state 2026-10-31)

Brief: `build/coordinator/briefs/DSL-METATHEORY-20261028.md`. Ember, after COHERENCE.md: "it sounds like maybe we need to be rethinking how our macros work, then, and maybe even have a metatheory of these things. it sounds like we potentially could be doing things more uniformly and systematically where we've been extremely adhoc."

Read against, whole: the macros on `origin/fn2/main` at `957b018c1` (`fn2/books/columns.lisp` 753 lines, `machines.lisp` 602, `core.lisp` 451, `core-children.lisp` 73, `core-children-a.lisp` 32, `assembly.lisp` 22, `owed.lisp` 49, `reference.lisp` 238, `reference-state.lisp` 212, `machines-a.lisp`, `machine-dispatch.lisp`, `machines-directory.lisp`, the head of `machines-a-run.lisp`; `sim/check.lisp`, `sim/check-trace.lisp`; `tools/certify.sh`; `docs/a-pool-host-sim.md`); `origin/fn2/b-durability` at `b4d422f99` (`fn2/books/layout.lisp` 1,069 lines with `deflayout`, `format.lisp`'s 37 layouts, `tuple.lisp`, `docs/b-durability.md`); `REVIEW-SINS-20261028.md` (sin 2 and items A11-A23, B1, B3, B6, B9, B12, T5); `REVIEW-20261028.md` (closing findings 4-5); `COHERENCE.md` §1-2 and §5-7; `TRANSPORT.md` §3.3, Experiment B and §9; `MODAL-KERNEL.md` §4.1-4.2 and §5-6; `UNIVERSAL-CONSTRUCTIONS.md` §10.1; `EXECUTION-MODEL.md` whole; `REALMS-FROM-DREGG.md`; the A seat's continuation and the prewritten prompts R5e, R7 and W1 with the R5a pass-3 report; the sprint's `FOUNDATION-GAPS.md` at `8e3488fcb`; the guide's `humans/03-modelling-data.md` and `ai/01-form-shapes.md` whole, `humans/04-modelling-systems.md` §4.1, §4.3-4.8 (§4.2, crash models, skimmed: it bears on no declaration form); and in the community books (`~/tools/acl2-fn/acl2-8.7/books`, the `ACL2_SYSTEM_BOOKS` that `fn2/tools/certify.sh` uses): `kestrel/soft` (documentation, `defunvar`, `workshop-paper-examples.lisp`), `kestrel/event-macros` (input processing, applicability conditions), `kestrel/apt/propagate-iso-doc.lisp`, `centaur/fty` (`fty-discipline`, `defprod`, `defbitstruct`), `std/util` (`define`, `defaggregate`, through the guide). The SOFT paper was absent from `~/paperbin` and is now there: `coglio2015-acl2-soft-second-order-functions-theorems.pdf` (arXiv 1509.06080), indexed in `README-fn2-20261028.md` §4.

**Scope of what this note claims.** It is a design, written against the macros at the revisions named above; §7 records what of it has landed on dev (to origin/dev 747afb64c) and what remains. Certify-time figures quoted as measured are the seats' own (R5a pass-3 report, W1's red list), at the named revisions. The machine form's redesign (MACHINE-FORM-20261030.md, binding) is this metatheory's machine kit finished: it turns R7's arm-contract checker into a generator (§5.2-5.3). Ember accepted the five decisions of §8 as recommended (10-28: "regarding the five decisions, i'm inclined to take your recommendations").

## Contents
0. The answer in one page
1. The notion of declaration
2. The registry
3. The obligation table and its consumers
4. The generic lemma library
5. The existing forms as instances, and the planned forms
6. The guards against the old sins
7. The refactor plan for A
8. Five decisions for ember
9. The Astra sessions, and where the two authors differ

## 0. The answer in one page

**Yes: fn2's six declaration forms are one notion, and the ad-hoc part is that each form invented its own row, its own obligation story and its own proof pattern.** Today `defcolumns`, `defmachine`, `defmachine-callback`, `defcorechild`, `defthm-owed` (on main) and `deflayout` (on B) write seven world tables with seven row shapes, and nothing records what each form emitted; `defmachine` lists seven obligation category names that nothing states (`*fn2-machine-obligations*`); the core hand-writes an obligation generator (`fn2-core-owe-refusal`) beside the declarations; about seventeen hand macros restate the same preservation theorems (SINS A17); B's layouts emit 74 owed rows whose teeth are prose that main's `defthm-owed` now refuses; and a guard-verified list interpreter for layouts still runs beside the generated codecs. Each fix so far (R5a's three passes, R5c's registry, B's BR1) was right and local.

**The design, in five sentences.**
1. A declaration is a presentation `(kind, name, signature, laws, provenance)` of one of fourteen kinds in four families (data, behaviour, relation, obligation), with a qualified identity such as `(:machine fn2-echo)`, and each kind generates a fixed list of nine artifacts (carrier, access, codec, logical view, registry row, obligations, simulator hooks, owed stubs, ATC lowering) of which nothing may be hand-written beside it; its laws are stated per capability, not as a decorative external square (§1).
2. Every form adds one set of common keys (identity, layer, requirements, a `:generated` manifest of what it actually emitted) to the row it already writes, read through one API; requirements resolve in stages, libraries declare, and the assembly's sections instantiate, report coverage and lint, each behind its own seal (§2).
3. One obligation store, `fn2-squares`, holds every obligation with COHERENCE's schemata plus `:bound`, `:invariant` and `:assertion` for those that are not squares, with proof status and check evidence as two separate dimensions; machines, the router and the executor contribute **case catalogues**, and a correspondence (`defsquare`) binds one statement per case only once its contract exists, so a missing contract is reported by name instead of hidden behind a placeholder; layer A's 39 dispatch cases become 39 bound loop-iteration cases instead of one monolithic owed statement (§3).
4. Per-declaration theorem families are instances of twelve kits proved once (functional-instantiation kits in fn's `def-loop` style, constrained functions only where abstraction is needed, with single-valued adapters at stobj boundaries; SOFT only after a qualification, because its function variables cannot take stobjs or return multiple values), held to an affine cost contract in fields, arms and children that a structural gate and a prover-step gate can refute (§4).
5. The six existing forms become front ends over one internal `fn2-declare` helper and gain eight guards that refuse the old sins at expansion or at assembly (§5, §6), in a convergence whose first three quests are DM0a (identities and manifest, after W1 and R5b, before R5e), DM1 (the obligation store) and DM0b (callbacks, staging and seals) after R7, each certifying with the driver unchanged (§7).

**What it does not do.** It does not generate the reference side of the Q1 square (TRACE's reference stays hand-written and independent in selection; how far sharing a declaration may go is one of the three open positions of §9). It proves nothing by itself: it states each obligation once, enumerates its cases, and makes the gaps visible. Layer A gains two user forms only, `defsquare` (DM2) and `defshape` (DM7), each with a consumer at once (R5e's ruling of no new form stays binding on R5e itself); the other planned forms (projection, summary, command, port, migration) are declared now and built with their first consumers.

**Where it stands.** The first three quests (DM0a, DM1, DM0b), the case catalogue with `defsquare` and Q1 bound per case (R7 1/n), and DM3's binding with per-case teeth and the four-way controls are on dev; the machine kit is being finished as MACHINE-FORM; the rest is §7.2's list, in order, unpriced (ember 10-29: "it won't take a hundred engineer-days, that's just a bad estimate, it'll take a few dozen swarmcycles"; "pricing isn't something we usually bother to do"). Three disagreements between the authors stay recorded (§9).

---

## 1. The notion of declaration

*Drafted by the Opus author; corrected against the macros by Astra's session 1 (`fn2/dsl-astra-1.md`, "Astra on sections 1-3"), whose corrections are adopted where marked (A1).*

### 1.1 One notion

A **declaration** is a presentation

```text
D = (kind, name, signature, laws, provenance)
```

in MODAL-KERNEL §4's sense (`T = (Σ, Ax)` over the base), specialised to what an ACL2 event macro can check:

- **kind** is one of fourteen, in four families:
  - *data*: `columns` (resident struct-of-arrays tables), `core-child` (the embedding of a columns table into the core: field, initialization, profile condition, reference treatment, stratum; A1: the draft had folded it into `columns`, but `defcorechild` declares all of these and none is a property of the table, `core-children.lisp:25-40`), `layout` (byte encodings), `shape` (logical tuples for models and checkers, never served);
  - *behaviour*: `machine` (a bounded resumable coalgebra with a budget), `callback` (one named arm or handler of a machine, or a core operation with a refusal contract), `command` (one grammar entry: syntax, protocol states, Decide);
  - *relation*: `projection` (a fold contract over a stream), `summary` (a fold that replaces retained history), `port` (a theory morphism with its reduct), `migration` (a representation certificate), `correspondence` (any other square between two representations of one meaning, with its case sources);
  - *obligation*: `owed` (a translated statement with named evaluating teeth), `square` (one case of a correspondence: a schema row of COHERENCE §2).
- **signature** is what the declaration introduces, as data: its fields (name, carrier kind, width, enum or reference target), its operations (name, formals with their types, results, stobj inputs and outputs, result positions), and for behaviour its transition labels (phases, observed events, commands).
- **laws** are what it obliges, stated **per supported capability**, not as a fixed external square (A1): the shape laws a carrier needs (proved by generation), the invariants it maintains, and the case catalogue it contributes to correspondences.
- **provenance** is where it came from and why: book, owning layer, every `:why`, the declarations it requires by qualified identity, and its position in its kind's order.

Its identity is **qualified**: `(:machine fn2-echo)`, `(:columns fn2-echo)`, `(:core-child fn2-echo-table)`. A1: `defmachine fn2-echo` emits `defcolumns fn2-echo` (`machines.lisp:213`), so the draft's bare-name key would have made one row overwrite the other.

The rule from nanodregg's law 1 ("a second shape of an existing thing is a defect"; REALMS item 10) becomes concrete: **everything a declaration's kind generates is generated by the declaration; nothing of that list may be hand-written beside it.** A hand-written put generator beside `defcolumns`, a hand-written shape-lemma macro beside `defmachine-callback`, a guard-verified layout interpreter beside `deflayout`'s generated codec, and a positional tuple beside a `shape` are each a second shape; §6 makes the macros refuse the ones they can see.

### 1.2 What every kind generates

The fixed list has nine artifacts, in this order for every kind:

1. **carrier**: the storage that holds instances (a SoA `defstobj`, rows of an existing table, a list, or nothing);
2. **access**: internal readers and updaters with bounds and widths in their guards; **checked boundary** writers that validate at run time and record refusals, where the boundary is the point (A1: `machines.lisp:118-140, 514-535` are deliberately of the second kind);
3. **codec**: the byte encoding, when the kind is persistent or on the wire;
4. **logical view**: the representation theorems are stated about; the restriction is **no served caller**, not "never executed" (A1: B's list codec runs in tests);
5. **registry row**: §2's common keys and the `:generated` list;
6. **obligations**: the shape laws it proves, the invariant and case rows of §3 it contributes, each with its schema;
7. **simulator hooks**: what each checker or the generator mode reads from the declaration;
8. **owed stubs**: the `defthm-owed` statements it emits, with named evaluating teeth;
9. **ATC lowering**: the flat, finite-tag, explicit-fuel form of EXECUTION-MODEL §5, recorded as an **unmet capability** until a flat endpoint exists (A1: a translated Q2 square over fictional functions is worse than an honest missing requirement), or a refusal when the kind has none.

"Today" marks what `957b018c1` (or `b4d422f99` for `deflayout`) already emits; everything else is to be built.

| kind (form) | carrier | access | codec | logical view | registry row | obligations | simulator hooks | owed stubs | ATC lowering |
|---|---|---|---|---|---|---|---|---|---|
| **columns** (`defcolumns`) | SoA `defstobj`: one resizable typed array per column, `rows`, and extra fields (scalars, arrays, nested stobjs, hash tables), unbounded or wide ones with `:why` (today) | `NAME-COL`/`NAME-SET-COL` with `wfp`, `i<rows` and width in the guard (today); enum count in the guard (R5e); `NAME-PUT`, `-SNAPSHOT`, `-COPY`, `-DIFF`, `-PRESERVES` (R5e) | none; a persisted table names a `layout` through a correspondence | `NAME-row-view`/`NAME-view`, `defun-nx` alists by column name (today); optional `:logical` abstract stobj | `:columns (name kind)`, `:column-reasons`, `:rows-bound`, `:extra-fields`, `:init-name` (today), plus the common keys | shape laws: `create-wfp`, `init-wfp`, per setter `preserves-wfp/type/rows` (proved, today, kit instances); Q3 correspondence only with `:logical` (owed) | reference clone and copy/diff (today, generated in `reference-state.lisp` from this row); exploration checkpoint copy/restore (COHERENCE §5.1's missing facility) | Q3 with `:logical` | one integer array per column by width; unmet capability until an endpoint exists |
| **core-child** (`defcorechild`) | a field of `fn2-core` | the parent's `stobj-let` binding; the read-over-write facts (today an H×H matrix of equations, `core.lisp:28-49`) | none | the parent's logical view | `:stobj :init :profilep :reference :order :why` (today) | `fn2-core-init-type/-wfp` (proved, today, in the assembly); the indexed read-over-write kit replaces the matrix (§4) | reference clone unless `:reference :environment` with its reason (today) | none | the parent struct's member |
| **layout** (`deflayout`, B) | none: rows `base + *NAME-FIELD-f*` of `fn2-fields` | `*NAME-FIELD-f*`, `*NAME-PHASE-f*`, `*NAME-NUM-FIELDS*`, `*NAME-MAX-SIZE*`; its own phase and field enum events (today on B) | generated `NAME-encode/-size/-check-values/-start/-decode/-decode-step` from per-field steps (today on B) | the list codec `fn2-layout-octets`/`-parse` (logic, test-run, no served caller) and `fn2-layout-values` (`defun-nx`) | `:layout` (the field specifications), `:fields` (a count), `:value-width`, `:phase`, `:max-size`, the export names (today on B; read by B's generated test dispatch, `tests/format-roundtrip.lisp:8-11`) | `roundtrip` and `canonical` about the generated exports, against the list codec (owed, today, prose teeth); primitive per-field-kind laws and a list composition (§4) | B's differential drivers: generated codec vs list codec | `NAME-roundtrip`, `NAME-canonical` with named teeth | unmet capability: the generated scanner recurses and restores fields on unwind, and the exports take nested stobjs (`layout.lisp:967-978`), so "generated" establishes neither ATC admissibility nor bounded stack (A2) |
| **shape** (planned `defshape`; today B's `fn2-cm-defreaders`) | a true list, logic and test only | named readers and `update-` writers (today on B, no lemmas) | none | itself | `:fields`, `:served nil` | reader-of-writer laws (proved) | the checkers' records (SINS S6, B12) | none | refused: a shape cannot reach a served path |
| **machine** (`defmachine`) | a `columns` table: phase enum, seven common columns, fields (today) | per-kind `PUT`/`PUT-CORE` with cross-kind refusal, `CHARGE`, observation acceptance, preparation (today); snapshots, run entries, router and callbacks are **later assembly or callback artifacts** (A1: `machines.lisp:296-354`) | none now; `:persist` layout for durable continuations later | the step coalgebra `Observation → X × Actions` under a cap (UC §10.1) | `:states :columns :accounts :budget :continuations :observes :capacity :initial :layout :packed :calling-convention :obligations` (today); `:calling-convention` is recorded but the generators reconstruct formals from `:columns` (A1: authoritative only after R5e) | shape: `prepare` and every callback preserve `corep` and `wfp` (proved, today); a **case catalogue**: one label per continuation phase and per observed event, contributed to the Q1 correspondence and any other that cites `:machine-continuations` or `:machine-observations` (§3); per arm a bound and a frame **requirement**, statements bound only when R7 supplies their contracts (22 run-arm budget cases and 9 handler-cost cases, distinguished; A1, A2) | generator mode enumerates the catalogue; TRACE per-case counts; WORK per-arm cost (R7, R5b); successor phases checked (R7) | frame per arm with R7 | dispatcher over finite kind and phase tags with explicit fuel; unmet capability |
| **callback** (`defmachine-callback`, `defmachine-run`; the core's `fn2-core-issue-wrapper`, `-pool-wrapper`) | none | the scalar calling convention (today); `fn2-call` forwarding (R5e) | none | none of its own | none today (A2: `defmachine-callback` emits a `defun` and shape lemmas only, `machines.lisp:320-333`); proposed: a callback map under its owner's row (a machine, or the operation owner for core operations), keyed by function name, with `:args :returns :row-bindings :writes :cost :refusal` and the emitting section | shape (proved, today); frame over `:writes` (owed); for operations, the refusal statement (owed, today hand-generated by `fn2-core-owe-refusal` ×9; A1: these compare one operation's before and after core, they are not simulations) | WORK cost per call; OWN where it touches the pool | frame, refusal | a C function over scalar parameters and the core |
| **command** (planned `defcommand`) | rows of its machine's table | parser arms as callbacks | the token grammar as a layout-like declaration | Decide over the logical store view | `:protocol-states :occasion :syntax :decide :retry :pre :post :refusals :disclosure :reads` | command simulation under its port, independent post-condition, refusal-no-op, retry (Q14) (owed) | WIRE fixtures; the fuzzer's diff mode; generated model command table (SINS H4) | post, refusal, retry | table dispatch over command tags |
| **projection** (planned `defprojection`) | a `columns` table for materialised state | its readers; `catch-up` | the summary's page layout (B) | `init`, `step` per event kind, `obs` as a constrained contract (TR §3.3) | `:stream :state :init :step :obs :coverage :read-fallback` | per event kind the summary step, the converter, G1q for a declared loss (owed) | HISTORY paired runs | per event kind | the fold's step arms |
| **summary** (planned, a projection with `:replaces`) | as projection | as projection | as projection | as projection, with the history fold it replaces | as projection, plus `:replaces :relation :converter` | Q4: per-event-kind steps, converter, observation agreement; lifted by `fc-rel-fold` (proved on a toy, TR §9) | HISTORY scenario 3 | as projection | as projection |
| **port** (planned `defport`, MK §5.1) | none | the reduct's reads | the protocol's rendering | `j : T_foreign → T_target`, `V = j*` | `:foreign :target :interpretation :observes :kernel :commands` | snapshot factorisation; future congruence where promised; command simulation (owed) | WIRE | per axiom and command | none |
| **migration** (planned `defmigration`, TR §3) | the target representation | generated for users by `propagate-iso` | the target layout | `defiso` maps restricted to the image | `:from :to :alpha :beta :base :loss` | converter, per base operation, route equations when two routes exist (owed) | paired executions | base correspondences (`defthmd`, TR §9 finding 3) | none |
| **correspondence** (planned `defsquare`, COHERENCE §5.2) | none | none | none | the contract's relation and observation | `:template :contract :sides :cases-from :checker :teeth-from :composition` | binds one statement per case of its case sources once its contract functions exist (§3) | the generator mode's case table | one per bound case | none |
| **owed** (`defthm-owed`) | none | none | none | the `$OWED` `defun-nx` (today) | today `fn2-owed` `(:vars :formula :teeth :doc :status)` | itself | `fn2-assert-owed-teeth` (today) | itself | none |
| **square** (bound by a correspondence) | none | none | none | none | a `fn2-squares` row (§3.1) | itself | the generator mode | its statement | none |

Three things the table settles before any macro changes.

1. **Laws are per capability.** `columns` and `shape` carry only shape laws, provable by generation, and need no invented second representation (A1). A machine contributes a *case catalogue*: it cannot know the reference relation, the matching word or the observation contract of a square it belongs to, so it names its cases and leaves their statements to the correspondence that binds them (A1; §3.2). This replaces the draft's "every arm emits refinement, invariant, frame and flat rows", which would have produced statements over relations that do not exist yet.
2. **A declaration does not generate the oracle of its own consequential claims.** `reference.lisp` shares harvest and the machine handlers on purpose and is independent only in selection (COHERENCE §1 point 3); TRACE is therefore a scheduler-refinement check, and the machines' semantics need independent oracles (OWN, the client oracle). What sharing a declaration permits and forbids is one of the two open positions of §9: the Opus author holds that a square whose two sides are generated from one declaration is vacuous for any semantic claim; Astra holds that generated representation views and compiler-correctness statements legitimately share a declaration, and that the test is a shared-handler mutation.
3. **ATC lowering is a recorded requirement.** EXECUTION-MODEL §5 calls ATC a qualification task; the column records the Q2 requirement per kind so that the qualification has a subject, and no row pretends a flat endpoint exists.

### 1.3 What a declaration may not do

- Take code fragments that refer to the generator's private names (SINS A23). Behaviour declarations name functions; initial values are constants or named functions of declared formals (today, since R5a pass 3).
- Register an obligation category without a statement or a case source (`*fn2-machine-obligations*` today lists seven names with nothing behind them; §3 replaces it).
- Emit an executable twin of its own logical view outside `mbe` (guide §3.3: "A twin that is a second callable function is two paths").
- Be read by position: consumers use emitted names (SINS sin 2).

---

## 2. The registry

### 2.1 What exists today

Seven world tables (six on main, one on B), written by five forms and the assembly, each with its own row shape:

| table | written by | row today | read by |
|---|---|---|---|
| `fn2-columns` | `defcolumns` | `(:columns :column-reasons :rows-bound :extra-fields :extra-field-reasons :init-name)` | `fn2-ref-state-events`, `defcorechild`'s existence check, `deflayout` (the `value` width of `fn2-fields`) |
| `fn2-machine-kinds` | `defmachine` | `(:states :columns :accounts :budget :continuations :observes :capacity :initial :layout :packed :calling-convention :obligations)` | through `fn2-machine-property`: index, child registration, run, callback, snapshot, router and field-access generators |
| `fn2-core-children` | `defcorechild` | `(:stobj :init :profilep :reference :order :why)` | through `fn2-core-child-property`: `fn2-core-events`, `fn2-reference-state-events` |
| `fn2-core-instance` | `fn2-core-events` | `:assembled t`, a seal | `defcorechild` |
| `fn2-owed` | `defthm-owed` | `(:vars :formula :teeth :doc :status)` | `fn2-assert-owed-teeth`, `tools/owed-export.lsp` (a post-certification driver doing top-level I/O) |
| `fn2-obligation-generators` | nothing | name only | `defmachine`'s `:obligations` check |
| `fn2-layouts` (B) | `deflayout` | `(:layout :value-width :phase :fields :max-size :encode :decode :decode-step :start :size :roundtrip-hyps)` | B's generated test dispatch (`tests/format-roundtrip.lisp`, `tests/layout-unit.lisp`) |

Each reader knows its table's plist keys, and nothing records what a form emitted except the form's source. R5e's coordinator ruling already asks for a `:generated` list in each row; this section generalises it.

### 2.2 One row shape over the existing tables

*Converged: the draft proposed one physical table `fn2-decl`; Astra proposed common readers over the existing tables with qualified identities; the note adopts Astra's, with physical consolidation only if it later removes code or invariants (§9).*

Every existing owner adds the common keys to the row it already writes; authors never call the registration helper:

```lisp
(table fn2-machine-kinds 'fn2-echo
  '(:states (...) :columns (...) ...             ; the existing payload, unchanged
    :decl-id (:machine fn2-echo)
    :layer :a :book "books/machines-a"
    :requires ((:declaration (:columns fn2-echo))
               (:function fn2-connection-reply :at :callbacks)
               (:function fn2-echo-observe-send :at :callbacks))
    :generated ((:columns (:columns fn2-echo) :section :declaration)
                (:macro fn2-echo-put-core (:formals (id &rest fields)) :section :declaration)
                (:function fn2-echo-charge (:formals (bytes steps descriptors))
                           (:results 3) :section :declaration)
                (:theorem fn2-echo-prepare-wfp :visibility :exported :section :declaration)
                (:function fn2-echo-run (:formals (id budget fn2-core)) (:stobjs-in (fn2-core))
                           (:results 5) :section :run)
                ...)
    :cases ((:phase :free) (:phase :command) ... (:event :receive-result) ...)))
```

- `fn2-decl-row` and `fn2-decl-rows` (in a new `fn2/books/declare.lisp`, included by `columns.lisp`) are the one read interface: `(fn2-decl-row '(:machine fn2-echo) world)`, `(fn2-decl-rows :machine world)` in declaration order. Table lookup is centralised there; `fn2-machine-property (name key world)` becomes a call of it, while `fn2-core-child-property (entry key)` stays an entry accessor (it takes no world). The other direct readers move with them: `fn2-machine-names` (`machines.lisp:270-275`), `fn2-core-child-registry` and the existence checks (`core-children.lisp:14-19, 32-36`), the obligation validator's `fn2-owed` lookup (`machines.lisp:187`) and the test mutations in `tests/machines-a-unit.lisp:307-311` (A2).
- Registration refuses a conflicting qualified identity, two **conflicting** definitions under one name, and a malformed signature (A1); an identical re-emission (B re-emits shared enum definitions per layout, `format.lisp:16, 27-28, 45-46` through `layout.lisp:916-918`) is recorded as a dependency, not refused (A2).
- A `:generated` entry records the artifact's **actual emitting section**, its formals, stobj inputs and outputs, result count and positions, and theorem visibility; a local helper theorem is not advertised as exported (A1). A reader of the world finds every emitted name without reading the macro.

### 2.3 The orders it induces

*Corrected (A1): the draft derived one global order and immediate dependency resolution; both were wrong.*

The assembly needs four distinct orders, and none is a global cross-kind counter:

1. **machine registration order**, for kind tags and global-ID ranges: declaration order within `fn2-machine-kinds`, the include order of the registration books (`fn2-machine-names`, `machines.lisp:269-272`);
2. **child strata, then order within each stratum**: the explicit `:foundation`, `:machine`, `:extension` sort (`core-children.lisp:8-19`). Layer and kind do not determine a child's stratum, so `:order` stays;
3. **staged resolution of function references**: a machine declaration names callbacks that are defined *after* the core exists (`machines-a.lisp` names `fn2-connection-reply`; `machines-a-run.lisp` defines it inside `fn2-machine-a-events`, which assembly expands after `fn2-core-events`), and child initialisers name index functions emitted during assembly (`core-children-a.lisp:17-18`). So declaration requirements (`:declaration` entries) resolve immediately, and function requirements resolve at the section named by `:at`;
4. **a frozen snapshot per instance section**: each section of the assembly reads the registry once and records which rows it consumed.

### 2.4 Library and instance, and the seals

A **library** declaration emits only what depends on itself and its declaration requirements: its stobj, accessors, codec, shape laws, and its case catalogue. Including a library book creates no instance and closes nothing (today's rule for pool, vocab, sched, machines and machines-a; `a-pool-host-sim.md` §5).

An **instance** artifact ranges over all rows of a kind and is emitted by one assembly section:

| instance section | consumes | today emitted by |
|---|---|---|
| `:index` | machine rows | `fn2-machine-index-events` |
| `:directory` | machine rows | `fn2-machine-directory-events` |
| `:core` | child rows (foundation, then one per machine row, then extensions) | `fn2-core-events` |
| `:access`, `:callbacks` | machine rows | `fn2-machine-access-events`, `fn2-scribe-events`, `fn2-machine-a-events`, other layers' continuation macros |
| `:dispatch` | machine rows | `fn2-machine-dispatch-events` |
| `:reference` | child rows and their columns rows | `fn2-reference-state-events` |
| `:coverage` (new) | every correspondence's case sources, after the reference and checker books load | nothing |
| `:lint` (new, §6) | `:generated` entries and functions defined in registration books | nothing |

**Seals are per input, not one blanket seal** (A1): machine inputs are sealed before `:index`, children before `:core` (today's `fn2-core-instance`), and evidence coverage after the reference and checker books load. A single seal at the end of `assembly.lisp` would refuse the executor's case registration, because `executor.lisp` includes `assembly` and `reference.lisp` includes `executor` (`executor.lisp:3`, `reference.lisp:3`). W1 is splitting `assembly.lisp` (106 s at `957b018c1`) along exactly these sections; the sections are therefore separate macro calls (`(fn2-assemble :section :core)`), one per book in include order. The test instance `tests/core-child-assembly.lisp` calls the same sections over a test registration, as today.

---

## 3. The obligation table and its consumers

*Section 3.1's row schema and the separation of proof from evidence are Astra's (A1), adopted; the 39-case table is the Opus draft corrected by Astra.*

### 3.1 The rows

One store, `fn2-squares`, holds every obligation: those `defthm-owed` states by hand and those a correspondence binds per case. A bound simulation case is:

```lisp
(table fn2-squares 'fn2-q1/echo/reply
  '(:schema :g1                          ; :g0 :g1 :g1q :g2 :route :crash :bound :invariant :assertion
    :template :q1-loop-iteration
    :owner (:correspondence fn2-q1)
    :origin (:machine fn2-echo)
    :case (:run fn2-echo :reply)
    :boundary :loop-iteration
    :contract (:pre fn2-q1-loop-invp :enabled fn2-q1-continuep :casep fn2-q1-casep
               :relation fn2-q1-loop-relatedp :observation fn2-q1-effects-agreep)
    :sides (:concrete (fn2-transition fn2-exec-account-work) :reference (fn2-ref-transition))
    :statement fn2-q1/echo-reply$owed    ; a defun-nx over :vars, emitted by the template
    :vars (ctx concrete reference lists)
    :formula <untranslated body> :translated <admitted body>
    :requires (<obligation ids>)
    :checker (:function fn2-check-q1-case :case (:run fn2-echo :reply))
    :teeth (:positive fn2-q1-echo-reply-positive :negative fn2-q1-echo-reply-negative)
    :proof (:owed)                       ; (:owed) | (:proved THM) where THM's formula is :translated
    :checks ()))                         ; evidence records, a separate dimension
```

- **Schemas** are COHERENCE §2.1 and §2.5's (G0, G1, G1q, G2, route equations, crash cases), plus three for the obligations that are not squares, because COHERENCE §5.3 found that most of today's owed list is not: `:bound` (work and resource bounds), `:invariant` (one- or two-state contracts: pool generation, result reservation, byte fill), and `:assertion` (the migration default for an unclassified row, rather than a fabricated classification; A1).
- **Variants carry different payloads**: a simulation case has two sides and a relation; a preservation row has a predicate and an operation; a bound has an accounting contract; a quotient has its kernel and retained observations. None manufactures a second representation it does not have (A1).
- **Proof and evidence are two dimensions** (A1, converged in §9): `:proof` is `(:owed)` or `(:proved THM)`, and `:proved` must cite an admitted theorem whose formula is the stored `:translated` formula, not merely an existing name. `:checks` is a list of evidence records (contract identity, revision, profile, input domain, horizon and its unit, reached and exercised counts, verdict, evidence location). A successful check never changes `:proof`; a checked row stays owed, with its scope visible.
- **`defthm-owed` becomes the author's view of this store**: `(defthm-owed NAME VARS FORMULA :schema S :contract C :from (:operation OP) :teeth (FN...) :doc "one line")` emits the same `$OWED` statement and one row with `:proof (:owed)`. The migration moves `fn2-owed-names`, the teeth check and the exporter to the store, then deletes `fn2-owed`; no mirrored writes (converged).

### 3.2 Who contributes cases, and who binds them

| contributor | contributes | to |
|---|---|---|
| `defmachine` | its catalogue: one label per continuation phase and per observed event (`:machine-continuations`, `:machine-observations`) | any correspondence citing them; Q1 first |
| the generated router (assembly `:dispatch`) | the unrouted-event label (`:router-fallback`) | Q1 |
| the executor (one case-source registration in `executor.lisp`, with named selector predicates over the hand-written executor) | seven labels: clock, signal, four service visits, empty principal visit (`:executor-cases`) | Q1 |
| `defcolumns`, `defmachine-callback` | shape-law rows, already proved (`:invariant`, `:proof (:proved ...)`) | no correspondence |
| `deflayout` | `roundtrip` and `canonical` rows | the codec correspondence (§4) |
| `defthm-owed` | hand-stated rows | no correspondence unless `:from` names one |

**The executor is not a machine** (A1, converged): registering it as `:kind :machine` would promise a columns carrier, a capacity, a phase enum and a dispatch entry it does not have. It contributes a case source to the correspondence, and the proof obligation that its seven selectors partition the loop's non-machine transitions under the loop invariant; otherwise coverage reports the gap.

A correspondence binds statements only once its contract functions exist:

```lisp
(defsquare fn2-q1
  :template :q1-loop-iteration
  :cases-from (:machine-continuations :machine-observations :router-fallback :executor-cases)
  :contract fn2-q1-loop-contract        ; names pre, continuep, casep, relation, observation
  :checker fn2-check-q1-case
  :teeth-from fn2-q1-case-fixtures)
```

It refuses unresolved endpoints, incompatible signatures, a case with no binding, and a case owned twice. `fn2-squares-close` (the `:coverage` section) **reports** unmatched requirements by name; it never inserts a `t` statement. A newly added machine therefore produces a precise missing-contract report, not a nominally complete table of placeholders (A1). Teeth and checker adapters resolve in the evidence books, keeping today's deliberate forward-reference arrangement (`owed.lisp`: production books do not include their tests).

### 3.3 What a generated Q1 case actually states (Astra's construction, adopted)

The concrete loop accounts work after every transition; the reference loop carries bytes and steps in arguments and writes them into its core only on exit (`executor.lisp:104-142`; `reference.lisp:126-144`). So neither raw core equality nor the turn-boundary `fn2-representation-relation` is the intermediate relation. With `ctx = (fuel h k a obs visits actions ref-bytes ref-steps)` behind named proof-only accessors:

```text
loop-related(ctx, c, r, lists) =
  representation-relation(c, normalize-reference-work(r, ctx.ref-bytes, ctx.ref-steps), lists)
```

where `normalize-reference-work` is logical only and replaces exactly the two work counters. A case row's statement is then:

```lisp
(implies
 (and (fn2-q1-loop-invp ctx concrete reference lists)
      (fn2-q1-continuep ctx concrete reference lists)
      (fn2-q1-casep '(:run fn2-echo :reply) ctx concrete lists))
 (mv-let (o v d b s concrete1) (fn2-transition t (fn2-q1-budget ctx) concrete)
   (mv-let (ro rv rd rb rs lists1 reference1) (fn2-ref-transition (fn2-q1-budget ctx) lists reference)
     (let ((concrete2 (fn2-exec-account-work b s concrete1))
           (ctx1 (fn2-q1-advance ctx o v d rb rs)))
       (and (equal (list o v d b s) (list ro rv rd rb rs))
            (fn2-q1-effects-agreep concrete reference concrete2 reference1)
            (fn2-q1-loop-invp ctx1 concrete2 reference1 lists1))))))
```

The hand-written contract defines its helpers once; the template substitutes only the case. `continuep` establishes both loop guards and `obs < h`, which justifies `allow-observation = t`. Separate rows connect turn entry, the loop invariant, termination and status, the reference's counter finalisation and the existing `fn2-turn-refinement`, whose antecedent is not silently strengthened and whose action and work conclusions are not dropped; the concrete side's u60-overflow stop, absent from the reference accumulation, is either excluded by the stated domain or exposed as a mismatch. `fc-rel-fold` can lift an established iteration relation once, for the composite relation; it is not one run theorem per label, and it does not supply the boundary and accounting proofs.

### 3.4 Who reads the rows

1. **The generator mode** (`fn2-sim-run-generators`, COHERENCE §5.1) reads every bound row with a `:checker`, enumerates its cases at reached states, and appends evidence records; reached, exercised, rejected, unexercised and unimplemented cases are reported separately ("missing evidence and unimplemented checks are never passing results", `sim/check.lisp`).
2. **The owed export** lists every row whose `:proof` is `(:owed)`, grouped by owner and schema, each with its check evidence beside it; checked rows stay in the owed list (converged).
3. **The proof route** chooses by `:template`: loop-iteration rows are lifted by one `fc-rel-fold` instance for the composite relation; `:iso` rows by `defiso` and `propagate-iso` (TR Experiment B); kit rows by the instances of §4; diamond rows need COHERENCE §3.2's hypotheses and have no library yet.
4. **TRACE** attributes each turn's transitions to bound cases and reports per-case counts, so "TRACE passed" becomes "these cases were exercised this many times", and an unexercised case is visible.

### 3.5 Layer A's 39 cases, by owner

COHERENCE §2.4 counted 39 dispatch cases for Q1 at `957b018c1`; A1 confirmed the machine counts against `machines-a.lisp:17-60`.

| cases | count | owner of the label | today | after this design |
|---|---:|---|---|---|
| listener phases `:accepting :closing` (both `fn2-listener-step`) | 2 | `defmachine fn2-listener` | the named arm; the seven-name `*fn2-machine-obligations*` list as data; one turn-level owed statement | two labels in the catalogue, bound by `fn2-q1` |
| echo phases `:free :command :reply :closing :draining :retired` | 6 | `defmachine fn2-echo` | as above; `:free` and `:retired` share `fn2-connection-idle` | six labels; the row records one implementation serving two cases |
| scribe phases (14, `:free` through `:stopped`) | 14 | `defmachine fn2-scribe` | as above | fourteen labels |
| routed observations (listener 2, echo 4, scribe 3) | 9 | the three `defmachine` `:observes` | named handlers with generated shape lemmas | nine labels |
| unrouted observation | 1 | the generated router, inside the executor's harvest transition | generated router, hand-written refusal helper | one label; its contract is the **composite** effect: harvest has already changed operation and pool state, and executor wake and accounting surround the router (A1: "changes only the refusal counter" describes the helper, not the case) |
| clock observation, sticky signal | 2 | the executor's case source | hand-written on both sides | two labels |
| service visits 0-3 | 4 | the executor's case source | hand-written on both sides; services 0, 2 and 3 have no application body in layer A | four labels, **exercised and counted normally**: they advance the calendar, clear service flags and consume visit and work counts (A1); "no application body" is metadata |
| empty principal visit | 1 | the executor's case source | hand-written on both sides | one label |
| **total** | **39** | 31 machine labels, 1 router label, 7 executor labels | 0 case rows, 1 monolithic owed statement (`fn2-turn-refinement`), seven category names | 39 bound loop-iteration cases plus the entry, exit, termination and accounting rows of §3.3; `fn2-turn-refinement` the composition row |

Three qualifications (A1). The 39 is a **catalogue** count, not a theorem count: stopped or invalid-ID dispatch, invalid phases and the no-transition branch (`machine-dispatch.lisp:9-17`, `machines.lisp:347-352`, `executor.lisp:101`) need a classification or an exclusion theorem under the loop invariant, because `wfp` alone does not exclude them. Shape facts (`corep`, `wfp`) support case proofs and discharge none of them; the draft's "39 invariant rows proved today" is withdrawn. And there is no Q2 statement until a flat endpoint and its relation exist; the requirement is recorded as unmet.

What the design replaces that is hand-written today:
- `*fn2-machine-obligations*` (`machines.lisp:174-177`), `fn2-machine-obligationsp` (`:178-192`) and the empty `fn2-obligation-generators` table: seven names per kind with nothing behind them, replaced by the catalogue and the binding correspondence;
- `fn2-core-owe-refusal` and its nine calls (`core.lisp:367-383`): a private obligation generator, replaced by `:operation` callbacks whose refusal rows the generator emits (they stay `:invariant` statements about one operation's before and after core, not simulations; A1);
- TRACE's verdict without case attribution: kept as the composition check, with per-case counts added.

Reference **transition selection** stays hand-written (`fn2-ref-transition`); the reference carriers and copy/diff functions are generated today (`reference-state.lisp:100-109`), as representation views may be (A2).

The other layer-A squares have their own case sources (COHERENCE §2.4): Q20's OWN shadow by the operations OWN observes, Q21's client oracle by per-connection bytes; §7 schedules them after Q1.

Today's 22 owed rows (A1: 22 in total, `fn2-turn-refinement` among them) migrate with schemas: the nine issue-refusal rows `:invariant`; `fn2-turn-refinement` the composition row; `fn2-turn-bounds` and `fn2-sched-starvation` `:bound`; the five pool, four vocabulary and the byte-fill rows `:invariant`. Their statements do not change shape (COHERENCE §5.3).

---

### 3.6 Q1's honest classification (decision 1 applied to Q1, with DM10's oracles; statement in lanes/a-dm4-q1-classification.md, accepted by main 2026-10-30; built in DM3)
fn2-ref-transition calls the same harvest, router, dispatch and grant service as the concrete loop; only selection and accounting are independent. So every Q1 case row is a representation refinement of the scheduler over shared handlers, and the rows become :claim :representation with their :shared declarations named per label. The consequential claim about what a machine does lives in one independent contract per kind (conn: WIRE, ACCOUNT, OWN; echo: the client oracle; scribe: read-back; listener: the admission ledger; commit: B's crash differential and HISTORY), named by each of the kind's case rows, and one shared-handler mutation control per kind (a one-site mutation of the generated handler under which TRACE-per-case still passes and the kind's oracle fails, plus the unmutated run passing both), recorded as evidence. A kind lacking either is reported by name, never filled in. This is not the metatheory's DM4 (the column and core kits).

## 4. The generic lemma library

*Co-written: the Opus draft's kit table and count check, merged with Astra's session-1 draft (A1) and corrected by session 2 (`fn2/dsl-astra-2.md`, marked A2) (`fn2/dsl-astra-1.md` §4: the additional families, the single-valued adapters, the affine cost contract with its two gates, and the codec split into kernels and realization). Marked (A1) where Astra's text is adopted.*

### 4.1 The principle

A per-declaration theorem family is written **once**, over constrained functions, and each declaration owes only an instance whose obligations are its own definitions and applicability lemmas under the substitution (the guide §4.6; fn's `def-loop`: "no instance induction, no instance hint"). The library eliminates repeated **proof arguments**; it does not remove the concrete applicability proofs, and "a template emitter is not a trusted proof rule: ACL2 admits every resulting theorem" (A1). The failure it prevents is the one R5a measured: a generator whose per-field theorems are proved by the prover's search over the whole table cost 104.72 s and 21 GB allocated for one 41-storage-field declaration before pass 3, 4.42 s and 1.9 GB after (R5a3 report, "Pass 3: declaration cost").

A **kit** is a theorem family, its applicability contract, an emitter and a cost contract, with a row in a `fn2-kits` table naming the theorems, the substitution keys, the template version and its cost constants; it uses an `encapsulate` with constrained functions only where abstract functions are needed, and an ordinary indexed first-order lemma otherwise (K3, K5; A2). Kits live in `fn2/books/kits.lisp`, which mentions no fn2 stobj.

### 4.2 SOFT, and what replaces it at stobj boundaries

SOFT's function variables are `defstub`s of arity `(* ... *) => *`: single-valued, with no stobj inputs or outputs (`kestrel/soft/defunvar.lisp`; SOFT's own future-work list names "multiple-value results and single-threaded arguments and results"). So neither a callback `(... fn2-core) → (mv bytes steps descriptors runnable fn2-core)` nor a codec export `(... fn2-fields fn2-pool) → (mv code next fn2-pool)` can be a SOFT parameter (A1).

At that boundary the generator emits **single-valued logical adapters** and uses ordinary functional instantiation (A1):

```lisp
(defun-nx fn2-listener-step$post (args core)        ; proof-only; never served
  (mv-nth 4 (fn2-listener-step (fn2-args-id args) (fn2-args-budget args) core)))
```

with the adapter's connection to the actual function and the applicability lemmas; guard verification stays on the real stobj and `mv` function. Stobj-free constrained signatures carry the kit:

```lisp
(encapsulate (((kit-invp *) => *) ((kit-prep * *) => *) ((kit-step * *) => *) ((kit-observe * *) => *))
  ...)   ; constraints: preservation and frame; local witnesses establish consistency
```

**SOFT's place (converged).** Keep the existing `:functional-instance` templates as the implementation. SOFT is not certified on this laptop (`kestrel/soft/*.cert` absent); its closure (`std/util`, `xdoc`, `kestrel/utilities`) would enter every book above `kits.lisp`, the include cost the guide records against `std/util` (§3.1); and the installed syntax already differs from the paper (`defun2` without the explicit function-parameter list, `workshop-paper-examples.lisp:43-51`; A1). SOFT gets one optional qualification quest, adopted only if it removes substitution and dependency bookkeeping across two real families, the codec composition and the fold contract being the candidates, since both are genuinely second-order and list-level.

### 4.3 The kits

| kit | constrained signature | generic theorems | today | per-instance work |
|---|---|---|---|---|
| K1 typed array contents | `(?valuep x)`, `all-valuesp` | nth membership, bounded update, resize preservation | **today**, `columns.lisp:18-32`, instantiated per array column at `:191-213`; consolidating it is not itself a gain (A1) | 4 events per array column |
| K2 heterogeneous record type | `(?slotp tag x)`, `(?recordp schema xs)` | one indexed update theorem, one recognizer bridge per table | **today**, `:34-43, :238-266` | 1 bridge per table, then field instances |
| K3 column-length invariant | `fn2-columns-shapep` (first-order, defined) | index-parametric update, one WFP bridge per table | **today**, `:45-53, :402-450`: R5a pass 3's fix | 1 bridge per table |
| K4 field accessor facts | `(?rd i st) (?wr i v st) (?len st) (?rows st) (?wfp st) (?typep st) (?fitp v)` with read-over-write, length, rows, wfp and type constraints | per column `-natp`, `-bound`, `-preserves-wfp`, `-preserves-type`, `-nth`, `-rows` | each is a per-column `defthm` with a `:use` of K1 (`:476-518`): instance-shaped but stated per column | 8 events per column, each an instance in a pinned theory; DM4's first control establishes that `:functional-instance` accepts stobj accessors and updaters as replacements, else the K4 instances go through adapters |
| K5 core child access and frame (A1) | `nth`/`update-nth` and `?slotp` for child predicates | indexed read-over-write for the core's children with named reader and writer bridges | the nested loops of `fn2-core-child-facts` emit an **H×H** matrix of equations for H children (`core.lisp:28-49`) | linear in H instead of quadratic |
| K6 initialization countdown (A1) | `(?inv st)`, `(?admissible i ctx st)`, `(?row-step i ctx st)`, `(?rows st)` | countdown preservation once, from row-step preservation, bound stability and row-count preservation | each machine kind's `-INITIALIZE-ROWS` repeats the induction (`machines.lisp:40-77`) | one instance per kind and a correspondence of the stobj initializer to it |
| K7 operation composition (A1) | `(?pre x st)`, `(?post-state x st)`, `(?inv st)`, indexed observation `(?get k st)` | lift leaf preservation and frame facts through sequential and conditional composition | about seventeen hand macros restating preservation (SINS A17: `fn2-core-shape-lemmas`, `fn2-pool-shape-lemmas`, `fn2-machines-shape`, `fn2-exec-direct-shape`, ...) | per wrapper or callback, the instance from its leaves' facts; **arbitrary callback bodies still need leaf contracts**: naming a callback proves nothing (A1) |
| K8 frame per arm | K7 with a declared write set `W` | `get-of-step` for every `k ∉ W` | none; R7 asks for the frame obligation per arm | one row per arm, proved when the arm is a composition of declared writes, owed otherwise |
| K9 layout field composition (A1) | `(?valid k v)`, `(?encode k v)`, `(?parse-result k bytes)` returning one logical record `(status value rest)` | prefix roundtrip and canonical consumed prefix composed over a field list, once | none: B owes 74 per-layout rows (37 layouts × roundtrip, canonical) | the primitive law per field kind: `valid(k,v) ∧ octets(tail) ⇒ parse-result(k, append(encode(k,v), tail)) = (:ok v tail)`, plus canonicality of accepted consumed prefixes; fixed little-endian, canonical varint, bounded one-byte tags, tagged digest, length-prefixed octets, zero padding; `:id` and `:u60` reuse the varint argument |
| K10 fold contract | `?init ?step ?obs ?rel` (TR Experiment A's `fold-contract.lisp`) | `fc-rel-fold`, `fc-obs-fold` | in the guide's `examples/transport/`, not in fn2 | the instance's step lemmas per event kind, two `:functional-instance` hints |
| K11 abstract-stobj obligations | `defabsstobj-missing-events`' printout | generated obligations with one uniform hint (guide §3.9, fn's `def-representation`) | none in fn2 | one obligation per export |
| K12 run invariant | `?inv ?okp ?step` (fn's `def-carried`, guide §4.4) | `run-carries` | none: no shape fact is lifted to runs | one instance per machine |

K9 is the composition only. The generated pool-and-fields code needs **refinement bridges** to the list codec covering pool-range validity, non-overlap, field offsets, refusal behaviour, fuel, suspension and resumption, and the decoder's unwind restoration on refusal (`layout.lisp:969-978`) and one-shot fuel condition (`:849-870`); the shape facts at `:821-834` establish none of that (A1). Those bridges are separate quests (§7, DM8 and DM9), and they expose failed statements rather than promise that every current owed formula proves unchanged.

### 4.4 The cost contract, and how it is kept

**Stated (A1's form).** For fixed supported field kinds, with `F` storage or layout fields, `A` declared arms and handlers, and `H` core children:

```text
generated theorem count ≤ c0 + cF·F + cA·A + cH·H
generated prover steps  ≤ b0 + bF·F + bA·A + bH·H
```

"Constant per kind" means a constant number of **generic theorem families**, plus linear specialisation; it cannot mean constant total work for an arbitrarily large declaration (A1). The constants belong to a named template version and toolchain. Application-specific semantic proofs and the first proofs of the codec kernels are reported separately. R5a pass 3's counts already show the affine shape for machines: 456, 696 and 984 theorems for 19, 29 and 41 storage fields, exactly `24 × storage-fields`.

**Kept by three rules and two gates.**
1. Every generated proof runs in a pinned theory (minimal theory plus the instance and the named definitions), never the includer's current theory: R5a pass 3's captured `fn2-columns-proof-theory`, generalised (the guide §4.4: one recognizer left open gave 1,082 subgoals where the closed proof took 0.30 s).
2. Whole-table recognizers (`NAME-P`, `NAME-WFP`, `fn2-corep`, `fn2-core-wfp`) are closed at their definition and opened only in their named bridges.
3. Each declaration gets at most **one linear-sized bridge per family** (the existing bridges carry a declaration-sized schema and unfolding hints, `columns.lisp:257-260, 407-414`), and no other generated statement mentions a whole-table predicate opened or repeats whole-record reasoning **per field** (A2 corrected the draft, which forbade every growing term and would have rejected the working templates) (R5a's superlinear family: "the raw/public setter WFP and type proofs, which repeatedly expanded the entire table recognizer").
4. **Structural gate** (A1, with the Opus count check): an event-tree auditor counts the *admitted* expansion events, local and exported (not entries the generator chose to list), checks that every family the kit promises is present, compares the count with `c0 + cF·F + cA·A + cH·H`, and refuses child-pair matrices, unregistered theorem emitters, more than one whole-record bridge per family and declaration, and any per-field theorem whose submitted event (`get-defun-event`/`get-event`) carries a hint other than its kit instance or its family's named applicability hint in a pinned theory.
5. **Cost gate** (A1): the 10-, 20- and 32-application-field declaration fixtures that exist (`fn2/tests/columns-cost-unit-10.lisp`, `-20`, `columns-cost-unit.lisp`), plus a 64-field one, several preceding machine kinds, a core-loaded world and an extra-field fixture; fixed affine prover-step budgets published from a qualification run and failed when exceeded (prover steps are deterministic; wall time is published, never a gate, beside the binding W1 rule of no book over 60 s). Splitting books does not excuse growing per-declaration proof work. A new field kind needs its own applicability and cost qualification.

### 4.5 What R5a's pass 3 did by hand that this does once

Pass 3 found repeated expansion of whole table recognizers in the setter WFP and type proofs, introduced one indexed shape argument, aligned the bridge's conjunction order, kept WFP opaque, captured a small proof theory for declarations without extras, and deleted two redundant local raw-`nth` facts per array column (R5a3 report). Those are already generator changes, finished, and the library keeps and enforces them (A1). It also split `fn2-sim-advance` into stages with the same six preservation contracts each and composed them (593.22 s to 50.79 s for that family): a common composition emitter (K7) removes the repeated contract machinery, but it does not find a good semantic stage boundary by itself (A1).

What changes is who carries the lesson. Today it lives in one generator's source after one quest found it under a 402-second, 85-GB sprint declaration. With the library, `defmachine`, `deflayout`, the core's child facts and every planned form instantiate kits only, inherit the pinned theory and the closed recognizers, and are held by the same two gates. The next generator does not need its own pass 3.

---

## 5. The existing forms as instances, and the planned forms

*Drafted by the Opus author; corrected against the macros by Astra's session 2 (`fn2/dsl-astra-2.md`, "Astra on sections 5-7"), adopted where marked (A2).*

Every form becomes a front end over one internal registration helper, `fn2-declare` (in a new library book `fn2/books/declare.lisp`, included by `columns.lisp`; authors never call it), in the Kestrel event-macro shape (`kestrel/event-macros`): (1) **input processing**, decidable, with soft errors naming the offending input; (2) **requirement check**: declaration requirements resolved now, function requirements recorded for the section named by `:at`, and the seal of the declaration's **consumed input set** not set; (3) **generation** of the kind's artifacts of §1.2; (4) **contribution** of shape-law rows and the case catalogue; (5) **registration** of the common keys and the `:generated` manifest in the row the form already writes, its payload keys left in place; (6) the §6 checks, as a trailing `make-event` after admission (A2). Forms keep their user-facing names.

### 5.1 `defcolumns` (and `defwide-columns`)

- **Signature.** `(defcolumns NAME COLUMNS &key rows-bound extra-fields init-name logical)`. Two changes: every `:extra-fields` entry requires `:why` (a **policy change**: today only unbounded and u64-reaching extras need one, `columns.lisp:161-170`, and extras include arrays, nested stobjs and hash tables, `:705-721`); `:logical` (optional) names a logical-view contract for an abstract stobj (Q3), off by default.
- **Generated list, added.** `*NAME-E-COUNT*` per enum, and enum setters guarded by it (today setters enforce width, not cardinality, `:471-475`; R5e item 1); `NAME-COPY`, `NAME-DIFF`, `NAME-PRESERVES` (R5e item 3); a per-row snapshot under the distinct name `NAME-ROW-SNAPSHOT`, because the assembly already emits `NAME-SNAPSHOT (id core)` for machine kinds (`machines.lisp:296-310`; A2); `NAME-PUT` emitted once by a **shared emitter** carrying the machine's phase-validation policy when the table is a machine's, because `defmachine` already emits `NAME-PUT` (`:214-215`) and two declarations must not emit incompatible definitions under one name (A2); `*NAME-FLAT*`, a constant describing the would-be flat arrays, recorded beside the unmet Q2 requirement; the manifest; shape-law rows naming the theorems it proves.
- **Stays.** The stobj layout and every generated name; `NAME-view`; the generic templates (consolidated in `kits.lisp`, §4).
- **Deleted.** The non-local `(in-theory (disable update-nth))` (`columns.lisp:57`, R5e item 5); `fn2-columns-nth-update-nth`, which duplicates ACL2's `nth-update-nth` (`columns.lisp:10-12`; A2 checked it against `acl2-8.7/axioms.lisp`); the local example's exotic fields (A22) move to `tests/columns-unit.lisp` **together with the local functions and assertions that use them** (`:705-753`). The `RAW-NTH` families are **not** deleted wholesale (A2): the extra-array rules use array-length bounds (`:308-323`) and the public-column rules use WFP and row bounds for guard inference (`:488-505`); each required interface is replaced before its family goes.
- **`defwide-columns`** operates on its own stobj: `-COMPARE` returns one value and `-INCREMENT` returns `(mv code table)` (`:673-694`). Its two operations move to a **carrier-parameterised operation emitter** placed below `columns` and `machines` (to avoid an include cycle), which the core's wrappers and the machines' callbacks also use (A2); its shape lemmas come from kit K7.

### 5.2 `defmachine`

- **As built through R7.** Arm contracts (`:cost` with `defcost` for outside calls, `:writes`, `:tables`, `:next`, `:uses`, `:holds`, resource effects, `:on-refusal`) entered the registry and a checker (`arms.lisp`) compared hand-written callback bodies against them, with a `:language :unchecked` escape; the case catalogue of §3.2 (one label per phase and per observed event) and `defsquare` bound Q1 per case (R7 1/n, 5d809cb94); `:obligations` and the seven-name list were deleted. That is the shape this metatheory's own law (§1.2: nothing a kind generates may be hand-written beside it) still violated: the body restated the contract, refusals were routed by hand, a kind could not certify alone, and the target's 32-value limit leaked into kinds.
- **As redesigned (MACHINE-FORM-20261030.md, binding; §6 there is the syntax).** One `defmachine` is the whole of a kind: `:phases :fields :budget :holds :capacity :initial`, `:admission` or `:taken`, `:genesis`, `:sub` (an inner state machine), `:subarms`, and `:arms` and `:observes` written in a step language (`:let :do :set :next :cond :if :case :issue :park :charge :stop :halt :goto`). The generator derives each arm's cost (the max over its terminals' charges), writes, tables, next phases, uses and refusal posture, and refuses at expansion: a path without exactly one terminal, an operation answer left unrouted, a `:do` of an operation with no `defcost` or of a per-octet export, a cost over budget, an `:issue` under a zero descriptor cap, and a hand `defthm` in a kind's book that is not about a declared operation. The run-time certificate stays, as a check of the generator. Placement P1-P4 makes a kind's book certify alone and the assembly a registry (§7).
- **Registry.** `fn2-machine-kinds` rows carry the common keys, `:cases`, the derived arm contracts (table `fn2-machine-arm-contracts`), the callback map of §1.2, `:calling-convention`, and `:mutation-sites` (one generated site per arm, so the four-way Q1 control is generated per kind and only its oracle is named by hand).

### 5.3 `defmachine-callback`, `defmachine-run`, and the core's wrappers

- **`defmachine-callback`** is deleted with the last hand callback: G1 (d04660248) deleted A's 32 by declaring listener, echo and scribe in the step language; the other kinds follow MACHINE-FORM §4's order (conn, commit, recovery-machine, upload, txn, sealer; the cursor is written in the new form from the start). `fn2-arm-walk-list`, the body checker, goes with it.
- **`defmachine-run`** stays the generated per-kind run entry and builds `K-RUN`, the certificates, teeth and owed rows from the derived contracts; under P4 it is emitted into the kind's own book over its declared children, and the assembly adds one wrapper and one rewrite per kind.
- **Core operations** (`fn2-core-pool-wrapper`, `fn2-core-issue-wrapper`, the refusal statements) use the carrier-parameterised operation emitter under their own owner row, `(:operation-set fn2-core-issue)` (DM0b, d8ec35855); under P2 each gets a body over the children it touches and the `fn2-core` face becomes a generated one-`stobj-let` wrapper.
- **Deleted earlier.** The private preservation macros of SINS A17, replaced by `NAME-PRESERVES` (kit **K7**).

### 5.4 `defcorechild`

- **Signature.** Unchanged: `(defcorechild FIELD STOBJ :init FORM :profilep FORM :why "..." [:reference :environment] [:order :foundation|:machine|:extension])`. `:order` stays (layer and kind do not determine a stratum; A1).
- **In the notion.** Its own kind, `core-child`, identity `(:core-child FIELD)`, requiring `(:columns STOBJ)`; its artifacts are owned by the assembly's `:core` and `:reference` sections.
- **Deleted.** The H×H read-over-write matrix (`core.lisp:28-49`), replaced by kit K5.

### 5.5 `deflayout` (B, on `b4d422f99`)

- **Signature.** `(deflayout NAME LAYOUT-EXPRESSION &key embeds)`. The expression is still evaluated at expansion, but an evaluated list keeps no provenance (`fn2-format-prefix` takes and returns plain field lists, `format.lisp:19-25`; `deflayout` evaluates an arbitrary expression, `layout.lisp:1059-1068`), so `:embeds ((PREFIX LAYOUT-NAME) ...)` is **explicit** metadata, validated against the flattened fields, under the common `:requires` key (A2: the draft said "recorded automatically", which the code cannot do).
- **Teeth.** The counts check out (A2): 37 layouts, 74 generated obligations, 32 prose `:teeth` occurrences in source, all refused by main's `defthm-owed` on merge. `deflayout` emits a positive fixture per layout that satisfies the **whole** antecedent, including the 4096-transition condition (`layout.lisp:849-858`), from the layout's own field kinds (a digest-only layout such as `fn2-format-frame-trailer`, `format.lisp:60-61`, has no u8 or varint to perturb); each negative witness names the hypothesis it removes and falsifies the remaining implication; the evaluating functions live in evidence books, keeping production books free of tests (`owed.lisp:3-4`).
- **Kind codes.** `1..11` (`fn2-layout-kind-code`, SINS B1's second enum system) become an enum `fn2-layout-kind` declared through the columns enum machinery.
- **The interpreter.** Deleted in a **consumer-bearing convergence quest**, not by decree (A2, agreed on the endpoint): B's `tests/layout-unit.lisp:123, 140-206` still calls the generic encode, decode, start and step functions, and the sprint's C code calls them (`8e3488fcb:fn2/sprint/c/seal.lisp:95-123`, `c/page-lookup.lisp:11, 21, 55`). The quest declares C's layouts, ports those callers and their continuation tests, then deletes the interpreter's functions, proofs and its two owed rows (`fn2-layout-roundtrip`, `fn2-layout-canonical`), and **keeps the shared helpers** the generated codecs still call: `fn2-layout-range-code`, `fn2-layout-store` and the specification result predicates (`layout.lisp:857, 865, 877, 973-978, 1040`).
- **Registry.** `fn2-layouts` rows gain the common keys and `:requires ((:columns fn2-fields) ...)` (its value width is read from `fn2-columns`, `layout.lisp:1062-1065`); B's test dispatch keeps reading the export keys.

### 5.6 `defthm-owed`

- **Signature.** `(defthm-owed NAME VARS FORMULA :teeth (FN...) [:schema S] [:contract C] [:from OWNER] [:doc "one line"])`; `:schema` defaults to **`:assertion`** during migration (A1, A2: the draft regressed to `:invariant` here). `:doc` is one line.
- **What it is.** The author's view of `fn2-squares` (DM1). `fn2-owed` is deleted once `fn2-owed-names`, the teeth check, the obligation validator and the exporter read the store.
- **Stays.** Translation of the statement, named teeth, `fn2-assert-owed-teeth`, and the **local test fixture** `fn2-owed-sample` (`tests/owed-unit.lisp:7-11`; A2: already a test fixture, not production).

### 5.7 The planned forms, declared now and built with their first consumer

Each is specified so that it is an instance by construction; each macro is built with its first consumer (EXECUTION-MODEL §5), and none is counted as delivered before then (§8 decision 4).

```lisp
(defshape fn2-history-batch            ; logic and test tuples only (SINS S6, B12)
  ((number :nat) (predecessor :nat) (records :true-list) (dependencies :true-list))
  :semantic fn2-history-batch-semanticp  ; positivity, duplicate freedom: field types are not enough
  :served nil)
;; emits: readers and update- writers with today's malformed-input behaviour (tuple.lisp:7-25),
;; reader-of-writer laws (:invariant :shape, proved); refuses a served caller (section 6, guard 6.6)
;; replaces: fn2-cm-defreaders (tuple.lisp:28); B already named its log-model and history readers

(defprojection fn2-group-numbers       ; a fold contract over a stream (TR 3.3, UC 2.1)
  :stream fn2-journal :state fn2-group-number-table
  :init fn2-group-numbers-init
  :step ((:article-acceptance fn2-group-numbers-accept) (:withdrawal fn2-group-numbers-withdraw))
  :obs (fn2-group-number-of) :coverage :cut :read-fallback :gap)

(defsummary fn2-read-state :of fn2-read-history       ; Q4: a projection replacing history
  :relation fn2-read-same-reads :converter fn2-read-summarize)   ; lifted by fc-rel-fold (kit K10)

(defcommand fn2-nntp-article           ; one grammar entry (UC 10.1, MK 5.1)
  :machine fn2-nntp-connection :protocol-states (:command) :occasion :read
  :syntax fn2-nntp-article-syntax :decide fn2-nntp-article-decide :retry nil
  :pre (fn2-nntp-group-selected) :post (fn2-nntp-article-reply-shape)
  :refusals (:no-group :no-article :bad-number) :reads :derived)

(defport fn2-room-news :foreign t-news :target t-room+news   ; MK 5.1's fields
  :interpretation fn2-room-news-j :observes fn2-news-read-contract
  :kernel fn2-room-news-identification :commands ())

(defmigration fn2-cursor-v2 :from fn2-cursor-v1 :to fn2-cursor-v2   ; TR Experiment B
  :alpha cur1->cur2 :beta cur2->cur1
  :base ((cur1-position cur2-position) (cur1-generation cur2-generation)) :loss nil
  :events (:first cur1-advance :last cur1-advance-keeps-token))
;; staged (A2): registers the maps and the base correspondences as owed rows first; emits defiso and
;; the propagate-iso call only once the inverse laws and base correspondences are admitted theorems

(defsquare fn2-q1 :template :q1-loop-iteration     ; section 3.2
  :cases-from (:machine-continuations :machine-observations :router-fallback :executor-cases)
  :contract fn2-q1-loop-contract :checker fn2-check-q1-case :teeth-from fn2-q1-case-fixtures)
```

`defsquare` binds what `defmachine` catalogues: a machine names its cases, a correspondence states them.

### 5.8 The migration's invariants

- No step adds a form beside one it supersedes; each step deletes what it replaces in the same commit, after porting its consumers (CLAUDE.md "the derived path is the only path"; A2's interpreter correction is this rule applied).
- A step that changes a registry row moves every reader of that row in the same commit (§2.2 lists them).
- A step's acceptance includes the certify-time table for every touched book and includer against the **actual post-W1 baseline**; every expected time in §7 is a qualification target, not a forecast (A2: a linear theorem count does not predict wall time).
- Generated statements are compared before and after; a step that changes one says so with its reason.
- The 39 layer-A Q1 labels and the cost fixture's 17 are pinned regression controls (`machines-a.lisp:17-60`, `tests/columns-cost-unit.lisp:7, 20-21`), not a freeze on future catalogue sizes (R6's postures will add cases).

---

## 6. The guards against the old sins

*The Opus table, corrected for ACL2 8.7 feasibility by Astra's session 2 (A2), which verified the premises in the installed sources.*

**The mechanism.** The checks read **submitted** forms, not translated bodies. A translated body inlines a constant's value, so an enum comparison and a literal comparison are indistinguishable there; the event's stored form keeps the constant. Measured at the laptop REPL (ACL2 8.7, `acl2-literal-4g-tls64k`, 2026-10-28): after `(defconst *k-two* 2)` and `(defun f (x) (declare (xargs :guard t)) (equal x *k-two*))`, `(get-event 'f (w state))` printed `(DEFUN F (X) (EQUAL X *K-TWO*))` while `(body 'f nil (w state))` printed `(EQUAL X '2)`. A2 confirmed from the implementation that `get-event` retrieves the event tuple's stored form (`acl2-8.7/translate.lisp:3288`, form extraction at `:2626-2630`), and recommends `get-defun-event` (`:6558`) for function inspection, since it handles mutual recursion and stobj-related events. Further, from A2:
- A certified lint book can inspect exported definitions of included books; it cannot recover vanished local events, and a function emitted during assembly is not identifiable by its registration book's file name. So generation **records producer and section provenance** in the manifest, local events are audited inside their generating `encapsulate`, the assembled-world audit runs after the callbacks exist, and the evidence audit after the evidence books load.
- Term walkers stay in logic mode (the installed `kestrel/utilities/my-get-event.lisp` helpers are `:program`, `:36-37, 58-59`, and are not imported for convenience).
- Cost: one world traversal collects the relevant events, then one walk of their syntax and call edges, with indexed membership: linear in inspected entries, syntax size and edges, never a full-world scan per function. No time is promised before DM6 measures it.
- Every rejection control has a **positive control** beside it (a named enum comparison, legal representation access, a test-only specification caller, a late evidence registration must all survive).

Every guard is a soft error (Kestrel input processing); hard errors remain for generator bugs.

| # | sin it refuses | where | what it checks | refusal text | controls |
|---|---|---|---|---|---|
| 6.1 | a declaration that obliges nothing (`*fn2-machine-obligations*`, SINS A23) | `fn2-declare` step 6 as a **trailing `make-event` after admission**; the `:coverage` section | the declaration contributes its kind's required laws (shape laws for carriers; a non-empty case catalogue for a machine); every `:statement` and `:contract` names an admitted function; every `(:proved THM)` cites a theorem whose formula equals the stored translated proposition, accounting for the `$owed` wrapper; an owed row names a tooth; at `:coverage`, every case of every cited source is bound or reported by name. A non-empty catalogue proves neither exhaustiveness nor reachability; those remain explicit obligations (A2) | "Declaration ~x0 contributes no ~x1." / "Case ~x0 of ~x1 has no binding in ~x2." | refuse: a machine with an unlabeled phase; pass: the three layer-A kinds |
| 6.2 | positional access (SINS sin 2, B3, B12) | step 6, over generated forms | **consumers** never read a declared record or tuple by a constant list position (`nth`/`update-nth` with a constant index); the **representation owner's** own implementation may (a generated shape updater necessarily contains `update-nth`, `tuple.lisp:23-25`); `mv-nth` result positions are part of a function's signature and are not list positions (A2) | "~x0 reads ~x1 of ~x2 by position; use ~x3." | refuse: a consumer's `(nth 6 record)`; pass: the shape's own updater |
| 6.3 | an enum compared as an integer (A13, A14, B9) | `:lint` section, over functions reachable from declared served roots and over generated forms | with an environment mapping accessors, formals and local bindings to **enum identities**: no comparison (`equal`, `=`, `eql`, `<`, `<=`, `>`, `>=`, either argument order) or `case` key between an enum-valued term and an integer or quoted integer; a named constant must belong to the **right** enum, not merely carry the right value. The generated dispatch emits numeric phase keys itself (`machines.lisp:26-30, 347-350`): either its template changes or that internal encoding is classified explicitly (A2) | "~x0 compares enum ~x1 with ~x2; use ~x3." | refuse: `(equal row-phase 2)`; refuse: a constant of another enum with the same value; pass: `(equal row-phase *fn2-echo-state-reply*)` |
| 6.4 | `:extra-fields` without `:why` (SINS A29) | `defcolumns` input processing | every extra field has a non-empty `:why` (a new policy: bounded extras needed none before) | "Extra field ~x0 of ~x1 requires a nonempty :why." | refuse: a bounded extra without a reason; pass: today's eleven justified extras |
| 6.5 | a callback forwarding row fields positionally (R5a pass 3's finding) | `defmachine-callback` input processing, over `BODY` | feasible: the body reaches the emitter quoted, before translation (`machines.lisp:332-333`; A2). With callback registration in place, a binding-aware walk skipping quoted data refuses any call of a registered callback with explicit `ROW-` arguments; such calls are `(fn2-call CALLEE extra...)`. Only supported body macros are expanded; arbitrary macros and aliases can hide a call, so this is a check of the common case, and it does not by itself solve stale snapshots (§5.2) | "~x0 calls callback ~x1 with positional row fields; use (fn2-call ~x1 ...)." | refuse: today's `fn2-listener-step` body; pass: the same with `fn2-call` |
| 6.6 | a specification or interpreter on a served path (SINS B1) | `:lint` section | no function **reachable from a declared served root** (the host entries and the turn) calls a function registered with `:role :specification` or `:served nil`; reachability is computed on translated call edges, literal provenance on source forms (A2: "every guard-verified function" was wrong, since tuple readers and tests are guard-verified too; and passing a layout constant is not itself interpretation, while an interpreter given a variable evades a literal test) | "~x0, reachable from served root ~x1, calls specification ~x2." | refuse: a served function calling `fn2-layout-octets`; pass: a test calling it |
| 6.7 | the absorbed refusal and the lying read (SINS sin 1, A3, A9) | step 6, for known generator templates | an **internal** generated setter's width and field-presence checks are in its guard (the internal `PUT`, `machines.lisp:514-519`); a **checked boundary** writer (`WRITE-*`, `:527-535`) validates at run time and emits the named refusal behaviour, which is generated and checked, never inferred from the presence of an `if` (A2); a boundary reader returns `(mv code value)` | "Generated setter ~x0 checks ~x1 at run time without a recorded refusal." | refuse: the pre-R5a silent setter shape; pass: today's checked `WRITE-*` |
| 6.8 | a declaration after its inputs were consumed | step 2 | the seal of the declaration's **consumed input set** (machine inputs before `:index`, children before `:core`, evidence after the evidence books) is not set; there is no global seal (A2; agrees with §2.4) | "~x0 is declared after section ~x1 consumed its inputs." | refuse: a machine after `:index`; pass: a late evidence registration |

**What the lint does not do (both authors).** It checks submitted spelling and the common cases. A literal reached through a helper or an unexpanded macro passes, and FTY could not make source spelling or oracle independence a theorem either, since translation erases the distinction between a named constant and its value (A2). Where the plan promises a *complete* property (an arm's writes, resources and cost), the lint is not enough: that is §8 decision 2.

---

## 7. The plan, as it stands

*The quest list was the Opus draft re-ordered by Astra's session 2 (`fn2/dsl-astra-2.md`). Its day budgets are withdrawn (ember 10-29); what accepts each quest, what it deletes and what it waits on are the plan.*

### 7.1 What has landed (origin/dev 747afb64c)
- **DM0a** identities and the `:generated` manifest (4cf85c4a8); **DM1** the obligation store `fn2-squares`, `defthm-owed` as its view, proof and check evidence as two dimensions (9cc09f2bf); **DM0b** callback maps, one operation emitter, `fn2-call`, staged requirements, input seals (d8ec35855).
- **DM2** the case catalogue, `defsquare`, Q1 bound to the dispatch cases (R7 1/n, 5d809cb94), with R7's arm contracts (R7 1/n-4/n).
- **DM3** Q1's binding: per-case teeth, one positive and one negative fixture per catalogue label (b1422d632); D's sim-layer-d under A4's instruments (a95b2c88e); OWN at the range primitives (fac32c58b); Q1's honest classification (§3.6) with an independent contract and a shared-handler control per kind (84e6bb293, b58ca579d and the per-kind contracts that followed).
- **DM4, the machine kit, in progress as MACHINE-FORM**: the core's well-formedness closes per child (867e87a23); the generator G1 (d04660248); the placement probe (6f05dbba0).

### 7.2 What remains, in order
| quest | what it does | deletes | waits on |
|---|---|---|---|
| **MACHINE-FORM P1-P4** (DM4's machine kit finished) | row control into the directory; operations over their children; arms over declared children in the kind's own book; the assembly a registry with per-kind wrappers and rewrites | `defmachine-callback`, `fn2-arm-walk-list`, the per-kind case split in every guard, the H×H frame matrix | G1 (landed) |
| **the kinds' ports** | conn, commit, recovery-machine, upload, txn, sealer, each from its arm table; the cursor in the new form only | every hand callback; `:language :unchecked`; the 27 `assert$?` of commit.lisp and alloc.lisp | P1 for the syntax; P3/P4 for certifying alone |
| **DM5 composition kits** | carrier and result adapters; callback and frame integration, shape facts separated from semantic contracts | the preservation macros R5e left | P2 |
| **DM6 the lint** | the included-book and source-inspection control; checks 6.2-6.5 and 6.7; served reachability for 6.6 | every literal enum comparison it finds, or a numbered red | none |
| **DM7 `defshape`** | generator and totality laws; A and B consumers migrated | `fn2-cm-defreaders`; `fn2-check-field` | none |
| **DMBC B and C convergence** | teeth for B's generated and hand-written rows; the layout interpreter's consumers ported and the interpreter deleted | the generic interpreter | none |
| **DM8 codec kernels**, **DM9 codec realization** (with B) | fixed and tag kernels, variable-length kernels, composition; the encode, decode-and-rollback and resume bridges, failing statements exposed | the per-layout owed rows they prove | DMBC |
| **DM10 OWN and client-oracle bindings** | separate OWN and client-oracle correspondences over their own case sources | none | DM3's classification |
| SOFT qualification (optional) | certify `kestrel/soft` and its closure; compare on two real families | none | none |

### 7.3 The target's 32-value limit (a generator rule, recorded 2026-10-30)
ACL2 returns at most 32 values from one mv. It bit the generators twice: first the whole-row snapshot a callback received (fixed at 6b2f6ef5b: a callback takes only the fields its body reads), then the generated fn2-core-init over all core children (33 children broke assembly-init; fixed by nesting, 6bde0055b). Rule for every generator: a generated mv over a collection (fields, children, kinds, slots) nests from the first version, in groups that keep the per-element facts closing per element; a generator that emits a flat mv over a declared collection is a defect. Under MACHINE-FORM the representation of a row's read set is the generator's business, so no kind ever sees a 32.

---

## 8. Five decisions for ember

*Astra's session-2 draft (`fn2/dsl-astra-2.md` §8), adopted with the Opus positions recorded where they differ. Astra replaced the Opus candidate "SOFT, functional-instantiation kits or FTY" (they are not alternatives at one level; the answer is settled in §4.2: functional-instantiation kits now, SOFT an optional 5-day qualification, FTY a separate data-model choice not recommended) with decision 2 below.*

| # | decision | recommendation (accepted by ember, 10-28) | what it requires, and what it forecloses |
|---|---|---|---|
| 1 | **May both sides of a correspondence derive from one declaration?** | **Yes for representation and compiler refinement** (generated views, generated codecs against their list codec), recording in the row what is shared, with **independent contracts for consequential behaviour** and a required control: a mutation of a shared handler under which Q1 may still pass while OWN or the client oracle must fail (Astra). The Opus position, stricter, is in §9 | provenance, adapters and the controls, inside DM3 and DM10 (built in DM3: §3.6); forecloses claiming independent semantic validation from a shared implementation; forbids no compiler-correctness claim |
| 2 | **Are arm contracts a checked language, or annotations on arbitrary Lisp?** | **A restricted arm language** wherever the plan promises complete `:writes`, `:uses`, `:holds`, resource or cost checking, with a declared escape for outside calls whose contracts stay owed until discharged; the source lint stays for ordinary surrounding code (Astra) | R7's expanded contract-language work beside DM6's lint, and now MACHINE-FORM's step language, which makes the restricted language a generator rather than a checker and retires `:unchecked`; forecloses accepting arbitrary callback bodies while claiming complete cost or frame checking. A helper-hidden foreign-table write, a stale row read and an undeclared resource effect must each be refused or classified unchecked |
| 3 | **How does generated coverage appear in the owed export?** | **Separate counts** for requirements, bound statements, admitted proofs and check coverage, grouped by correspondence and case source; a checked row stays owed; the turn-composition obligation is listed beside its cases, and 39 cases are not reported as 39 independent semantic guarantees (converged) | inside DM1 (built); forecloses both hiding generated debt and inflating progress by multiplying cases |
| 4 | **How much of the planned declaration family is built now?** | **Each with its first real consumer**: `defsquare` with Q1 (DM2, DM3), `defshape` with A's and B's tuples (DM7); projection, summary, port, migration and command stay specified designs (§5.7) until their consumer quests bind endpoints, refusals and acceptance controls (converged) | the remaining interface sketches, beyond DM3's and DM7's work; no implementation total is promised for the five deferred forms before their consumers are scoped; forecloses stabilising speculative interfaces and counting declarations as delivered capabilities |
| 5 | **How much metatheory precedes R5e and R7?** | **Astra:** only DM0a before R5e (after W1 and R5b); the store, callback, staging and catalogue migration after R7. **Opus:** the same, except DM1 also before R7, so that R7's arm obligations are created in the store with their schema and contract once | settled by the order that ran (DM0a, R5e, DM1, DM0b, R7): Astra's position; R7's rows were migrated into the store by DM1 |

---

## 9. The Astra sessions, and where the two authors differ

Two read-only sessions of `codex exec -m gpt-6-astra -s read-only -C /Users/ember/dev/fn`, each detached with a PID file under `build/coordinator/fn2/`.

- **Session 1** (prompt `dsl-astra-1.prompt`, answer `dsl-astra-1.md`, log `dsl-astra-1.log`, PID file `dsl-astra-1.pid`, session `01a1855c-a493-78a2-a84e-8e2c438b1a39`) received §1-3. It checked them against the macros line by line and corrected eleven claims (the missing `core-child` kind; the bare-name key collision; that callbacks reconstruct formals from `:columns`; that `fn2-layouts` has test consumers and `:fields` is a count; the prose teeth; that logical views run in tests; that shape lemmas are not semantic invariants; the 22-row count), replaced the registry with qualified identities over the existing tables and staged resolution with per-input seals, wrote the obligation store's row schema with proof and evidence separated, wrote the generated Q1 case statement with its normalised loop relation, refused the executor-as-machine registration, and drafted §4's additional families, adapters, cost contract and gates. No capacity or authentication error; three MCP transport error lines from a local server codex could not reach, which did not affect the answer.
- **Session 2** (prompt `dsl-astra-2.prompt`, answer `dsl-astra-2.md`, logs `dsl-astra-2.log`, `-r1.log`, `-r2.log`, PID files `dsl-astra-2.pid` and `dsl-astra-2-retry.pid`, session `01a18571-3f0c-7e12-be7b-b359e67f4768`) received §0-7. The first launch and the first resume stopped on "Selected model is at capacity"; a retry loop resumed the same session by id after five minutes and the second resume completed. It checked §1-4's fidelity to session 1 (four qualifications and two regressions, all corrected here), corrected §5-7 against the macros (callbacks have no registry row; the `NAME-PUT` and `NAME-SNAPSHOT` collisions; the impossible macro rebinding of stale `ROW-` variables; the 14-scalar forwarding; R7's and R6b's larger contract schema; explicit `:embeds`; whole-antecedent tooth fixtures; the interpreter's consumers and shared helpers; `fn2-owed-sample` already a test fixture; that generated codecs are not yet a flat form), verified §6's premises in the ACL2 8.7 sources (`get-event`, `get-defun-event`, included-book inspection, `make-event` replay), split DM0 and added a B/C convergence package, corrected R5b's disjointness, and drafted §8.

Astra's words are in those files; the note quotes or adopts them where marked A1 and A2.

| issue | Opus position, and its reason | Astra position, and its reason | state |
|---|---|---|---|
| kinds | thirteen, `defcorechild` folded into `columns` | fourteen: a core child is an embedding with its own initialization, profile condition, reference treatment and stratum | **converged** on Astra's (§1.1) |
| registry | one physical table `fn2-decl` with a global counter | common keys over the existing tables with qualified identities; consolidate only if it removes code or invariants | **converged** on Astra's (§2.2) |
| orders and seals | one global order, immediate resolution, one seal at the end of assembly | four distinct orders, staged function requirements, per-input seals (the executor includes assembly) | **converged** on Astra's (§2.3, §2.4) |
| machine obligations | every arm emits refinement, invariant, frame and flat rows | a machine contributes a case catalogue; statements bind only when their contract exists; shape facts are not invariants; no Q2 statement without an endpoint | **converged** on Astra's (§1.2, §3) |
| executor | an internal `:kind :machine` declaration | a case source in the Q1 correspondence; the executor does not meet the machine contract | **converged** on Astra's (§3.2) |
| checked versus owed | three disjoint statuses | proof and evidence are two dimensions; a checked row stays owed | **converged** on Astra's (§3.1) |
| `defthm-owed` | a view of the store | the same, with `:assertion` as the migration default | **converged** (§5.6) |
| SOFT | plain kits; SOFT later for second-order families | the same, SOFT an optional qualification; not an alternative to FTY at one level | **converged** (§4.2) |
| proof form of generated theorems | only kit-instance hints; no statement term grows with the declaration | one linear-sized bridge per family and declaration with named applicability hints; refuse repeated per-field whole-record reasoning; the Opus rule rejected its own working templates | **converged** on Astra's (§4.4) |
| interpreter removal | delete it with the `deflayout` migration | the same endpoint, after a consumer-bearing quest ports B's tests and C's callers | **converged** on Astra's (§5.5, DMBC) |
| cost | the Opus draft priced the plan | Astra re-priced it larger | **withdrawn** by ember (10-29: "it won't take a hundred engineer-days, that's just a bad estimate, it'll take a few dozen swarmcycles"); the plan is §7's order and acceptance |
| **shared declaration on both sides** | a square whose two sides are generated from one declaration is vacuous for any semantic claim, because a shared mistake passes both sides; so the declaration generates statements and cases, never the oracle | sharing does not make refinement vacuous; independence must concern the semantic judgment being checked, and generated representations may share syntax | **open**: decided by stating each claim precisely and running the shared-handler mutation against Q1 and an independent semantic oracle (§8 decision 1 adopts Astra's recommendation with that control) |
| **enforcement strength** | submitted-form lint, with its macro and helper escapes acknowledged, keeps the implementation small | adequate for style, not for the promised complete cost, frame and resource discipline: restrict the arm language where completeness is claimed | **open**: decided by whether a helper-hidden foreign-table write, a stale row read and an undeclared resource effect are rejected or classified unchecked (§8 decision 2) |
| **refactor timing** | DM0a and DM1 before R7, so R7's obligations land in the store once | only DM0a before R5e; let R6 and R7 reveal the actual contracts before the broad migration; R5b is not disjoint | **open** on DM1's place only; decided by the rewritten R7 prompt's diff with and without the store (§8 decision 5) |

What the collaboration changed, measured: §1 gained a kind and qualified identities; §2's single table, global order and blanket seal were replaced; §3's per-arm rows became case catalogues bound by correspondences, and its schema and Q1 statement are Astra's; §4 gained five kit families, the adapters and the two gates, and lost a rule that would have rejected the working templates; §5-6 were corrected throughout against the macros and the ACL2 sources (each correction marked A2); §7's plan split DM0 in two, a B/C convergence package was added, and the first quest moved from "DM0-DM2 before R5e" to "DM0a after W1 and R5b"; §8 is Astra's draft. Three disagreements stay open.
