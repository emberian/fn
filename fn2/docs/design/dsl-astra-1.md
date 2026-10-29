## Astra on sections 1-3 (corrections)

Citations below use `A = 957b018c1:fn2/` and `B = b4d422f995:fn2/`. Proposed forms and functions are designs, not admitted events.

**Corrections to the generated-artifact and registry tables**

| Draft claim | Correction grounded in the macros |
|---|---|
| Thirteen declaration kinds cover the existing forms. | `defcorechild` is missing. It declares an embedding, initialization, profile condition, reference treatment and assembly order; it is neither another columns declaration nor a machine. Add `:core-child`, with generated artifacts owned by the assembly instance. (`A/books/core-children.lisp:25–40`; `core.lisp:14–24,78–117`.) |
| A columns carrier has scalar extras with reasons. | Extras can also be arrays, nested objects, hash tables or unrestricted fields. Today only unbounded/wide extras require `:why`; bounded numeric extras do not. (`A/books/columns.lisp:119–170,705–721`.) Requiring reasons for **every** extra is a proposed policy change. |
| `wfp` preservation supplies the machine’s `Inv` preservation. | Generated `wfp` checks array lengths and row bounds; core `wfp` combines child shapes and the control-row count. Callback shape lemmas prove `corep` and this `wfp`, not ownership, reservation, protocol or reference invariants. Register them as `:invariant/:shape`; semantic preservation stays owed. (`A/books/columns.lisp:560–563`; `core.lisp:78–84,121–130`; `machines.lisp:320–329`.) |
| `defmachine` emits snapshots and callback preservation. | It emits columns, puts, charge, observation acceptance, preparation and its registry row. Snapshots are later assembly artifacts; callback/run definitions and their shape lemmas are separate events. Preserve these emission phases in `:generated`. (`A/books/machines.lisp:203–240,296–354`; `assembly.lisp:8–17`.) |
| Callbacks obtain their calling convention **from the stored key**. | The key is recorded at `machines.lisp:238–239`, but callback, snapshot and run generators reconstruct formals from `:columns` at `296–350`. R5e makes `:calling-convention` authoritative; it is not authoritative today. |
| `fn2-layouts` has no consumers. | B’s generated test dispatch reads it, including `:encode`, `:decode`, `:decode-step`, `:start` and `:roundtrip-hyps`. (`B/tests/format-roundtrip.lisp:8–11`; `tests/layout-unit.lisp:315–318`.) |
| Layout `:fields` is a field list; layouts depend on separately declared enums. | Today `:fields` is a **count**; `:layout` contains the field specifications. `deflayout` reads the value-column width from `fn2-columns`, but emits its phase and field enum events itself. (`B/books/layout.lisp:915–918,1054–1068`.) |
| Layout roundtrip/canonical obligations are already compatible with A’s owed machinery. | B emits the two statements, but passes prose strings as teeth. A rejects those. Convergence must replace strings with evaluating functions, not merely move the rows. Roundtrip additionally assumes encoded bytes plus empty-field transitions fit 4096 steps; canonicality concerns the **consumed prefix**, not all input bytes. (`B/books/layout.lisp:849–881`; `A/books/owed.lisp:12–22`.) |
| Logical views are uniformly `defun-nx`, never executed. | B’s list encoder/parser are ordinary logic functions used by tests; `fn2-layout-values` is `defun-nx`. The useful restriction is **no served caller**, not “never executed.” (`B/books/layout.lisp:445–496`.) |
| Reference code sharing a declaration makes a square `P → P`. | Too strong. Generated storage views and compiler-correctness statements legitimately share a declaration. Moreover, today’s independent **scheduler** deliberately shares harvest, machine handlers and other semantics. The claim is scheduler/refinement agreement, not independent validation of those handlers. Keep independent OWN/client contracts for that. (`A/books/reference.lisp:77–123`.) |
| Every generated access checks bounds only through guards. | Checked boundary writes deliberately validate and record refusals at runtime. Distinguish internal guarded access from checked boundary access. (`A/books/machines.lisp:118–140,514–535`.) |
| Every kind needs an external square, and columns discharge all obligations today. | Neither follows. Columns’ shape laws are useful without an invented second representation; the same table also proposes an owed Q3. State a required law set **per supported capability**, rather than requiring a decorative external square. |
| The existing owed list has “22 remaining” rows after the refinement row. | It has **22 total**, including `fn2-turn-refinement`: 21 others. The nine issue-refusal statements compare one operation’s before/after core; moving them does not turn them into representation simulations. (`A/books/core.lisp:367–383`; `reference.lisp:225–238`; COHERENCE §5.3.) |

**Registry construction: common readers over existing tables**

Keep the existing tables and add common metadata in place. Use qualified identities:

```lisp
(:columns fn2-echo)
(:machine fn2-echo)
(:core-child fn2-echo-table)
```

This is necessary even if we later choose one physical table: `defmachine fn2-echo` emits `defcolumns fn2-echo`, so the draft’s bare-symbol key would overwrite one row. (`A/books/machines.lisp:213,234–240`.)

Existing forms call an internal registration helper; authors do not write `fn2-declare`:

```lisp
; Expansion emitted by the existing owner, schematic:
(table fn2-machine-kinds 'fn2-echo
  '(:states (...) :columns (...) ...       ; existing payload stays in place
    :decl-id (:machine fn2-echo)
    :requires ((:declaration (:columns fn2-echo))
               (:function fn2-connection-reply :at :callbacks))
    :generated
      ((:macro fn2-echo-put-core
        (:formals (id &rest fields)))
       ...)))
```

`fn2-decl-row` and `fn2-decl-rows` provide the common read interface. Registration refuses conflicting qualified IDs, conflicting artifact ownership and malformed signatures. An artifact entry records its actual emitting section, formals, stobj inputs/outputs, result positions and theorem visibility; a local helper theorem is not advertised as an exported theorem.

The assembly needs:

- machine registration order for tags and global-ID ranges;
- explicit child strata, then order within each stratum;
- staged resolution of callback/function references;
- a frozen declaration snapshot for each emitted instance section.

Those are different orders. Machine order comes from `fn2-machine-names`; child order explicitly sorts `:foundation`, `:machine`, `:extension`. Neither requires a global cross-kind counter. Layer and kind do not determine a child’s stratum. (`A/books/machines.lisp:269–275,416–434`; `core-children.lisp:8–19`.)

Immediate dependency resolution is also wrong: machine declarations name callbacks emitted **after** the core exists, and core initialization contains forms referring to index functions emitted during assembly. (`A/books/machines-a.lisp:25–26,38–42`; `core-children-a.lisp:17–18`; `assembly.lisp:8–16`.) Resolve declaration dependencies immediately and function dependencies at their named section.

Keep section macros. Seal machine inputs before index generation, children before core generation, and evidence coverage after reference/checker books load. A blanket seal at the end of `assembly.lisp` would prevent the proposed executor registration: `executor.lisp` includes assembly, and `reference.lisp` includes executor. (`A/books/executor.lisp:3–4`; `reference.lisp:3`.)

**The 39 cases: corrected ownership and scope**

| Case catalogue | Count | Owner |
|---|---:|---|
| Listener continuation phases | 2 | Listener declaration |
| Echo continuation phases | 6 | Echo declaration |
| Scribe continuation phases | 14 | Scribe declaration |
| Declared observation routes | 9 | The three machine declarations |
| Unrouted observation | 1 | Generated router, inside the executor’s harvest transition |
| Clock and signal | 2 | Executor |
| Service visits | 4 | Executor/calendar |
| Empty principal visit | 1 | Executor/calendar |
| **Total** | **39** | **31 machine labels + 1 router label + 7 executor labels** |

The machine counts match `A/books/machines-a.lisp:17–60`. There are eight **non-machine** cases, not eight executor cases after separately counting the router.

Three qualifications change the proposed rows:

1. **Services 0, 2 and 3 are not trivial agreement checks.** They advance the calendar, clear service flags and consume visit/work counts. Exercise and count them normally; “no application service body” is descriptive metadata. (`A/books/executor.lisp:70–100`; `reference.lisp:101–116`.)
2. **“Unrouted changes only the refusal counter” describes the refusal helper, not the composite G1 case.** Harvest has already modified operation/pool state; executor wake and accounting surround the router. The composite contract must include those effects. (`A/books/machines-a-run.lisp:50–54`; `executor.lisp:16–27`; `core.lisp:302–330`.)
3. **39 is a catalogue count, not an exhaustive theorem count.** Stopped/invalid-ID dispatch, invalid phases and the no-transition branch require classification or an exclusion theorem under the selected invariant. `wfp` alone does not exclude them. (`A/books/machine-dispatch.lisp:9–17`; `machines.lisp:347–352`; `executor.lisp:101`.) Entry, exit, coverage and accounting obligations are additional.

Delete the promised totals of 39 semantic-invariant proofs and 39 flat-transition statements. Shape facts can support case proofs but do not discharge them. Q2 statements require an actual flat endpoint and relation; until then record an unmet capability requirement, not a translated square with fictional functions. Likewise, distinguish 22 run-arm budget cases from nine handler-cost cases before promising “31 bounds.”

**`fn2-squares`: statement ownership, not category names**

Use one obligation store, with schema-specific payloads. A simulation row has:

```lisp
(:schema :g1
 :template :q1-loop-iteration
 :owner (:correspondence fn2-q1)
 :origin (:machine fn2-echo)
 :case (:run fn2-echo :reply)
 :boundary :loop-iteration
 :contract
   (:pre fn2-q1-loop-invp
    :enabled fn2-q1-continuep
    :casep fn2-q1-casep
    :relation fn2-q1-loop-relatedp
    :observation fn2-q1-effects-agreep)
 :sides
   (:concrete (fn2-transition fn2-exec-account-work)
    :reference (fn2-ref-transition))
 :statement fn2-q1/echo-reply$owed
 :vars (ctx concrete reference lists)
 :formula <untranslated-body>
 :translated <admitted-statement-body>
 :requires <obligation-ids>
 :checker (:function fn2-check-q1-case :case (:run fn2-echo :reply))
 :teeth (:positive fn2-q1-echo-reply-positive
         :negative fn2-q1-echo-reply-negative)
 :proof (:owed)
 :checks ())
```

The template generates `:vars`, both formula representations and `$owed`; authors do not maintain copies. Other variants require different fields: preservation has a predicate and operation; bounds have an accounting contract; a quotient has its kernel and retained observations. They need not manufacture two representation sides.

Separate **proof status** from **check evidence**. A checked obligation remains owed until proved. Each check record carries source/contract identity, profile, domain, horizon and its unit, reached/exercised counts, verdict and evidence location. A successful run cannot overwrite `:proof (:owed)`. A proved status must reference an admitted theorem establishing the exact stored formula, not merely an existing theorem name.

`defmachine` can emit its case catalogue immediately. It cannot infer a reference relation, matching word or observation contract. Bind those later:

```lisp
(defsquare fn2-q1
  :template :q1-loop-iteration
  :cases-from (:machine-continuations :machine-observations
               :router-fallback :executor-cases)
  :contract fn2-q1-loop-contract
  :checker fn2-check-q1-case
  :teeth-from fn2-q1-case-fixtures)
```

This emits translated obligations only after the contract functions exist. It refuses unresolved endpoints, incompatible signatures, missing case bindings and duplicate case ownership. `fn2-squares-close` reports unmatched requirements; it does not insert `t` statements. Required checker adapters and teeth resolve in the evidence books, preserving today’s deliberate forward-reference arrangement. (`A/books/owed.lisp:3–4,29–38`.)

For the executor, register the seven labels in this **correspondence’s case source**, using named selector predicates over the hand-written executor. Do not register it as `:kind :machine`: that would falsely promise a columns carrier, capacity, phase enum and machine dispatch entry. The router contributes the eighth non-machine label. Prove the case partition exhaustive under the loop invariant; otherwise closure reports incomplete coverage.

**What a generated Q1 statement actually says**

The concrete loop accounts work after every transition; the reference loop holds bytes/steps in arguments and writes them into its core only on exit. (`A/books/executor.lisp:104–142`; `reference.lisp:126–144`.) Therefore neither raw core equality nor the existing turn-boundary relation is the intermediate relation.

Let `ctx = (fuel h k a obs visits actions ref-bytes ref-steps)`, represented by named proof-only accessors. Define:

```text
loop-related(ctx,c,r,lists) =
  representation-relation(c,
    normalize-reference-work(r,ctx.ref-bytes,ctx.ref-steps),
    lists)
```

`normalize-reference-work` is logical only; it replaces exactly the two work counters. The invariant also states admissible counters, queue/calendar validity and the bounds needed for accounting. A case row expands to:

```lisp
(implies
 (and (fn2-q1-loop-invp ctx concrete reference lists)
      (fn2-q1-continuep ctx concrete reference lists)
      (fn2-q1-casep '(:run fn2-echo :reply) ctx concrete lists))
 (mv-let (o v d b s concrete1)
   (fn2-transition t (fn2-q1-budget ctx) concrete)
   (mv-let (ro rv rd rb rs lists1 reference1)
     (fn2-ref-transition (fn2-q1-budget ctx) lists reference)
     (let ((concrete2 (fn2-exec-account-work b s concrete1))
           (ctx1 (fn2-q1-advance ctx o v d rb rs)))
       (and (equal (list o v d b s) (list ro rv rd rb rs))
            (fn2-q1-effects-agreep
              concrete reference concrete2 reference1)
            (fn2-q1-loop-invp ctx1 concrete2 reference1 lists1))))))
```

The handwritten contract defines those helpers once; the generator substitutes only the case. `continuep` must establish both loop guards and `obs < h`, justifying `allow-observation = t`.

Separate obligations connect turn entry, this loop invariant, termination/status, reference counter finalization and the existing turn theorem. Account for concrete u60-overflow stopping, absent from reference accumulation: prove it excluded by the stated domain or expose a mismatch. Do not silently strengthen `fn2-turn-refinement`’s antecedent or drop its action/work conclusions. (`A/books/reference.lisp:225–236`.)

`fc-rel-fold` can help lift an established iteration relation. It does not supply these boundary and accounting proofs, and needs one instantiation for the composite relation—not one independent run theorem per label.

**`defthm-owed`: retain the form, make it a view**

I agree with one authoritative obligation store:

```lisp
(defthm-owed name vars formula
  :schema :invariant
  :contract named-contract
  :from (:operation operation-name)
  :teeth (positive negative)
  :doc "...")
```

It emits the same translated `$owed` statement and a `fn2-squares` row with `:proof (:owed)`. During migration, omitted classification means `:assertion`, not a fabricated invariant or simulation. Update `fn2-owed-names`, teeth checking and the exporter to query the store, then delete the old table. No mirrored writes.

The exporter remains a post-certification driver: today it performs ordinary top-level I/O, explicitly outside certifying events. (`A/tools/owed-export.lsp:35–55`.) Checked-but-unproved rows stay in its owed view, with check evidence alongside them.

## 4. The generic lemma library (Astra's draft)

The library should eliminate repeated **proof arguments**, while retaining the concrete applicability proofs. R5a already implements this approach; SOFT is an optional mechanism for managing substitutions.

**4.1 Families and concrete signatures**

| Family | Generic functions/parameters | Generated instances and remaining work |
|---|---|---|
| Typed array contents | `valuep : * → *`; `all-valuesp : * → *` | Nth membership, bounded update and resize preservation. Already proved once at `A/books/columns.lisp:18–32` and functionally instantiated at `191–213`. SOFT can manage this family; replacing working instantiations is not itself a gain. |
| Heterogeneous record type | `slotp : (*,*) → *`; `recordp : (schema,record) → *` | One indexed update theorem and one recognizer bridge per table, then field instances. Already present at `columns.lisp:34–43,238–266`. |
| Column-length invariant | Ordinary `shapep(n,rows,record)` | One index-parametric update theorem, one WFP bridge per table, then setters. This is first-order; it needs no function-variable machinery. Already present at `columns.lisp:45–53,402–450`. |
| Core child access/frame | Ordinary `nth/update-nth`, plus `slotp` for child predicates | Replace the generated child-by-child matrix with indexed read-over-write and named reader/writer bridges. Today the nested loops emit **H²** equations for H children. (`A/books/core.lisp:28–49`.) |
| Initialization countdown | `inv : * → *`; `admissible : (*,*,*) → *`; `row-step : (*,*,*) → *`; `rows : * → *`, arguments `(index,context,state)` | Prove countdown preservation once, assuming row-step preservation, bound stability and row-count preservation. Instantiate the loop, then prove the generated stobj initializer corresponds to it. Current machine initialization repeats the induction per kind. (`A/books/machines.lisp:40–77`.) |
| Sequential/conditional operation composition | `pre : (*,*) → *`; `post-state : (*,*) → *`; `inv : * → *`; indexed observation `get : (*,*) → *` | Lift leaf preservation/frame facts through composition. This covers wrappers and generated callback plumbing. Arbitrary callback bodies still need leaf contracts; naming a callback does not prove them. (`A/books/core.lisp:121–142,221–229`; `machines.lisp:320–352`.) |
| Layout field composition | `valid : (*,*) → *`; `encode : (*,*) → *`; `parse-result : (*,*) → *`, arguments `(field-kind,value-or-bytes)` | Prefix roundtrip and canonical-consumed-prefix composition over a field list. Prove primitive codec laws separately, then the list composition once. Connect generated pool/fields code by explicit refinement bridges. (`B/books/layout.lisp:445–486,842–881`.) |

For the codec family, `parse-result` returns **one logical record** containing status, value and rest. Its primitive law is:

```text
valid(k,v) ∧ octets(tail)
⇒ parse-result(k, append(encode(k,v),tail)) = (:ok v tail)
```

Canonicality is a separate law about every accepted consumed prefix. The primitive proof work comprises fixed-width little endian, canonical varints, bounded one-byte tags, tagged digests, length-prefixed octets and zero padding. Widths, enum counts and length limits remain parameters; `:id` and `:u60` reuse the varint argument. These are substantive arithmetic/parser proofs, not consequences of the composition theorem.

Generated-code refinement additionally covers pool-range validity, non-overlap, field offsets, refusal behavior, fuel, suspension/resumption and rollback. The decoder’s unwind restoration at `B/books/layout.lisp:969–978` and one-shot fuel condition at `849–870` cannot disappear inside a “roundtrip kit.” Shape facts at `821–834` establish none of that.

**4.2 SOFT’s boundary**

SOFT’s function variables currently have single-valued results and no stobj arguments/results. The installed implementation accepts only `(* ... *) => *` (`kestrel/soft/defunvar.lisp:61–74,96–98`); this limitation is also explicit in the [SOFT documentation](https://acl2.org/doc/index-seo.php?xkey=SOFT____SOFT-FUTURE-WORK).

Consequently, neither this callback signature nor the codec exports are direct SOFT parameters:

```text
callback(..., fn2-core) → (mv bytes steps descriptors runnable fn2-core)
encode(..., fn2-fields, fn2-pool) → (mv code next fn2-pool)
```

Use single-valued logical adapters and ordinary functional instantiation at that boundary:

```lisp
(defun-nx fn2-example$post (args core)
  (mv-nth 4 (fn2-example (fn2-args-id args)
                        (fn2-args-budget args)
                        core)))
```

The generator emits the adapter, its connection to the actual called function, and the concrete applicability lemmas. Proof-only argument/result records never enter served code. Guard verification remains on the actual stobj/MV function.

For constrained templates, an ordinary `encapsulate` supplies signatures such as:

```lisp
(((kit-invp *) => *)
 ((kit-prep * *) => *)
 ((kit-step * *) => *)
 ((kit-observe * *) => *))
```

Its constraints state preservation and frame behavior; local witnesses establish consistency. Every functional instance must discharge the substituted constraints. With SOFT’s unconstrained variables, equivalent requirements appear as explicit second-order hypotheses. Neither route converts an owed preservation premise into a theorem.

Keep existing `:functional-instance` templates as the initial implementation. SOFT is not certified on this laptop, so budget a separate qualification quest. Its value must be demonstrated by removing substitution/dependency bookkeeping across two real families. The installed syntax also differs from the paper: its `defun2` examples omit the paper’s explicit function-parameter list (`workshop-paper-examples.lisp:43–51`).

**4.3 Macro interface and refusal behavior**

The existing declaration generators call one internal emitter:

```lisp
(fn2-kit-instance-events
  :family :record-update
  :owner '(:columns fn2-echo)
  :substitution '((kit-slotp . fn2-echo-field-p)
                  (kit-recordp . fn2-echo-record-p))
  :bridge 'fn2-echo-as-record
  :exports '(fn2-echo-update-field-type)
  :world world)
```

It emits applicability events, local bridge/helper events, theorem instances and `:generated` metadata naming family and visibility. It refuses:

- missing family premises or incompatible signatures;
- a promised theorem absent from the emitted event tree;
- an exported theorem depending on an unavailable local interface;
- direct SOFT substitution of an unsupported stobj/MV signature;
- per-instance induction for a family whose induction belongs in the library.

For callbacks, this is a composition facility over established leaf facts. For columns, it reuses the existing indexed templates. For core children, it removes the quadratic theorem matrix. For layouts, it initially emits owed semantic obligations while reusing proved shape families; semantic status changes only after the codec bridges certify.

A template emitter is not a trusted proof rule. ACL2 admits every resulting theorem.

**4.4 Cost contract**

“Constant per kind” means a constant number of **generic theorem families**, plus linear specialization work. It cannot mean constant total work for an arbitrarily large declaration.

For fixed supported field kinds:

```text
generated theorem count ≤ c0 + cF·F + cA·A + cH·H
generated proof steps    ≤ b0 + bF·F + bA·A + bH·H
```

Here F counts storage/layout fields, A counts declared arms/handlers, and H counts core children. Constants belong to a named template version and toolchain. Application-specific semantic proofs and first proofs of primitive codec kernels are reported separately. Macro expansion, guard verification, compilation, allocation and wall time are measured too; a linear theorem count alone does not imply linear certification time.

Enforcement has two parts:

1. **Structural gate.** An event-tree auditor counts local and exported theorems, checks expected family coverage and rejects child-pair matrices, unregistered theorem emitters and repeated whole-record bridge proofs. Generated hints keep recognizers opaque except in their named bridges. Count admitted expansion events, not entries the generator chose to list.
2. **Cost gate.** Reuse the 10/20/32-field declaration fixtures; add 64 fields, multiple preceding machine kinds, a core-loaded world and an extra-field fixture. Publish fixed affine prover-step budgets from the qualification run and fail excesses. Run both small and polluted-world probes. Keep the ten-second iteration target and the fn2 quest’s sixty-second book ceiling; splitting books does not excuse growing per-declaration proof work.

The budgets are established once from the implementation and published with the template contract, not regenerated from each run. A new field kind requires its own applicability and cost qualification.

**4.5 What R5a pass 3 already did**

Pass 3 identified repeated expansion of whole table recognizers in setter WFP/type proofs, introduced one indexed shape argument, aligned the bridge’s conjunction order, kept WFP opaque and captured a small proof theory for declarations without extras. It also removed two redundant local raw-`nth` facts per array column. These are already generator changes, not unfinished per-declaration edits. The library should retain and enforce them.

Its recorded declaration curve was:

| Application fields | Storage fields | Before | After | Theorems after |
|---:|---:|---:|---:|---:|
| 10 | 19 | 8.76 s | 1.64 s | 456 |
| 20 | 29 | 30.42 s | 2.44 s | 696 |
| 32 | 41 | 104.72 s | 4.42 s | 984 |

Those three theorem counts are exactly `24 × storage-fields`. The 41-field core-loaded probe took 5.91 s; the report explicitly calls these single-run local measurements, not controlled benchmarks. ([R5a3 report](/Users/ember/dev/fn/build/coordinator/fn2/lanes/a-quests/R5a3.REPORT.md:204).)

Pass 3 separately split `fn2-sim-advance` into stages, proved the same six preservation contracts for each stage and composed them, reducing that family from 593.22 s to 50.79 s. A common preservation/composition emitter removes the repeated contract machinery. It does **not** discover a good semantic stage boundary automatically. (Same report, lines 218–231.)

**4.6 Quests**

These estimates are pessimistic engineer-days for implementation, controls and integration; no timings below are measured forecasts.

| Quest | Concrete completion criterion | Days |
|---|---|---:|
| Registry | Qualified identities and common readers over existing tables; R5e manifests; staged references; unchanged assembly ordering with collision/late-binding controls | 4 |
| Obligation store | Exact statement rows; proof/check separation; `defthm-owed`, teeth and exporter migrated; all 22 A obligations preserved; B prose teeth repaired | 4 |
| Column/core kits | Existing indexed templates consolidated; child matrix replaced; narrow public interfaces and cost gates | 6 |
| Machine composition | Initialization and wrapper composition templates; callback shape versus semantic contracts separated; actual stobj/MV bridges | 6 |
| Q1 binding | Loop relation, case ownership/partition, entry/exit obligations and generated statements connected to TRACE adapters | 6 |
| Codec kernels | Primitive roundtrip/canonical-prefix arguments and generic list composition | 8 |
| Codec realization | Generated scanner/emitter bridges, fuel/resume/rollback obligations, migration of all 37 layouts | 10 |
| SOFT qualification, optional | Certify the dependency and compare two real families against existing functional instantiation | 3 |

The mandatory work totals **44 engineer-days pessimistically**. Q1 binding supplies part of COHERENCE’s twelve-day generator experiment; it does not include replay exploration, its campaigns or all mutation controls. The codec quests should split by kernel and bridge into readable diffs. They must expose failed statements rather than promise that every current owed formula will prove unchanged.

## Two positions

| Issue | Opus position and reason | Astra position and reason | What decides |
|---|---|---|---|
| One declaration table | Move to `fn2-decl` when squares need cross-kind dependencies; one traversal and order simplify consumers. | Keep common readers over existing tables. Dependencies require staged resolution, not one total order; the proposed key already collides between machine and columns. | Implement registry and Q1 consumers with qualified IDs. Consolidate physically only if it removes real code or invariants. |
| Automatically generated G1 rows | Every arm produces refinement, invariant, frame and flat rows, making coverage systematic. | Automatically enumerate cases and required capabilities. Emit a statement only after its contract/endpoints bind; shape facts are not semantic invariants and absent flat code supplies no endpoint. | A newly added machine must produce a precise missing-contract error, not a nominally complete table of placeholders. |
| Executor registration | An internal machine declaration gives the executor the same catalogue machinery. | Register its seven cases in the Q1 correspondence; use the router’s own case source for the eighth non-machine case. The executor does not satisfy the machine declaration contract. | Whether assembly can consume the row without an `:executor` exception. If it needs that exception, the proposed kind is wrong. |
| Checked versus owed | Disjoint statuses prevent a test result being confused with proof. | Separate dimensions prevent that confusion **and** preserve proof debt. A row may be checked and still owed. | Export a successfully checked, unproved row: it must remain in the owed list with its check scope visible. |
| Oracle independence | Never generate both sides from one declaration, because shared mistakes can pass. | Preserve independence of consequential semantic judgments; allow shared schemas and generated representation views. Compiler refinement is meaningful despite sharing syntax. | State the exact claim and run a shared-handler mutation: Q1 may pass, while the independent semantic oracle must detect it. |

On `defthm-owed`, the positions converge: retain the author-facing form, use one obligation store, and preserve the exact statements and evaluating teeth.