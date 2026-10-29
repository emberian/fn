## Astra: amendments to section 5

**5.1. Replace the opening paragraph.**

At `957b018c1`, the acceptance driver runs 10,000 tiny-profile and 1,000 near-limit **pool scenarios**, whose rounds issue operations directly and run OWN. These are not 11,000 dispatcher traces. The same driver separately runs the scribe scenario and an echo workload starting at seed `20261028`, targeting 1,000 completed or attributed-dropped connections, followed by a 200-connection bounded-completion run. The echo workload runs TRACE per turn. Coverage figures must name the workload, checked contract and execution boundary; action-kind and fault-kind masks do not measure schedule or diamond coverage.

**5.1. Replace “The mode.”**

`fn2-sim-run-generators` should separate two activities: enumerating local obligations at reached states, and systematically reaching states. Neither requires a partial-order reduction initially.

1. **G1 checks.** Compare `fn2-transition` with `fn2-ref-transition` at corresponding boundaries. Preserve the independent reference queues and calendar. Import adapter effects only at their actual boundary, never by copying concrete post-transition machine state into the reference. The driver must explicitly align remaining budgets, return values, accumulated work and turn initialization and termination. The present loops update work accumulators differently, so replacing a turn call with two transition calls is insufficient. Keep the existing per-turn comparison as a composition check.
2. **G2 checks.** At each reached state, enumerate every applicable declared-independent pair of concrete occurrences. Execute both legal routes, including their emitted effects and residual occurrence correspondence. Compare the declared endpoint relation and observation histories. A short matched continuation search can refute future closure; passing it does not establish H≈.
3. **Reachability.** First replay recorded prefixes and exhaust the finite choices at selected boundaries. Add bounded prefix enumeration over an explicitly listed input domain. “Exhaustive” means all declared instances at those states, or all prefixes within that domain and horizon. The tiny resident profile alone does not define a manageable exhaustive search.
4. **Evidence.** Report reached, exercised, rejected, unexercised and unimplemented cases separately. Every declaration needs a nonvacuous positive fixture and an appropriate negative control. G0 and future G1q checks enter through the same registry, with their own executable adapters.
5. **No pruning in the first experiment.** Passing sampled or bounded diamond checks does not authorize removing schedules from an exhaustive search. Later pruning needs a sound dependence model and a reduction algorithm that preserves the chosen bound. Ordinary DPOR combined naively with preemption bounding can miss executions within that bound. [Coons, Musuvathi and McKinley](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/bpor-oopsla-proofs-2013.pdf).

A completion occurrence includes its operation, generation, result cell, payload and fault choice. Reusing a seed after swapping two completions can attach the next random fault or payload to a different operation. Corresponding continuations must preserve those identities, or explicitly report that the proposed correspondence is illegal. The current simulator’s earliest-due selection and release-order protocol also constrain which choices can be exchanged.

**5.1. Replace “What it needs that does not exist.”**

Much of the copying machinery already exists in `reference-state.lisp`: `fn2-ref-state-events` generates congruent child stobjs, array copies and field differences, and `fn2-ref-copy-core` assembles a core copy. The missing facility is a complete, independently restorable **exploration checkpoint**. `fn2-core-children` registers the core’s children, not the whole simulator. `fn2-sim` has nested network and storage stobjs, PRNG state, clocks, pending flights and fault state; `fn2-own` has additional arrays; the scenario carries client records, reference queues, counters and other ordinary arguments outside those three stobjs. Recovery exploration adds its own state.

`defcolumns` records enough layout information to generate much of a checkpoint implementation, including extra fields, but the generator must recursively handle registered nested stobjs, array lengths and supported nonnumeric fields. Unsupported field kinds must fail generation. A row view is not a checkpoint, and a shallow copy of mutable arrays is not an independent branch. Copy, restore and branch-isolation controls are required. For the first experiment, replaying a prefix into fresh initialized states avoids making generic checkpoint generation a prerequisite.

The semantic difference function is a separate obligation. Generated field traversal can implement exact comparison and useful diagnostics; it cannot infer an observation contract or a future-closed equivalence. Today’s reference comparison deliberately omits the reference’s unused intrusive scheduler and compares only relevant pool bytes, with a separate scheduler relation. Those exclusions cannot simply be reused for two concrete executions. A G2 comparison must account for both concrete schedulers, pending operations, live bytes, client-visible outputs, ownership evidence and relevant environment state. Any permitted renaming of allocated identifiers needs an explicit correspondence. Ignoring a field requires a reason tied to the contract, not merely its absence from today’s output.

**5.1. Replace the estimate and counts paragraph.**

Budget **12 engineer-days pessimistically for the scoped layer-A experiment in §6**, using replay, finite boundary choices, transition-level comparison, independent oracles and mutation measurements. Four to five days is plausible for an initial paired-replay demonstrator, not the full mode described here. General recursive checkpoints and state-space deduplication would be a separate **eight-day pessimistic extension for the current layer-A state layouts**, undertaken only if replay cost warrants it.

The **741 coarse candidate pairs cover only the 12 completion kinds and 26 fault classes**, before occurrence parameters, legality and reachability; they are not 741 independence laws. The 39 dispatch cases remain a useful partition, not a complete theorem count or a count transferable unchanged to OWN and the client oracle. Layer D’s **1,000 pessimistic schemata remain provisional sizing for the catalogue in §2.4**, not an exploration estimate.

The proposed transition estimate undercounts both routes. For two one-step branches followed by `k` one-step continuations on each side, the work is `2(2+k)`, before replay, copying, reference execution and checks. Even under the draft’s restricted assumption of 28 pairs at each of 960,000 states, `k = 8` gives about **538 million branch transitions for those pair checks alone**. But 960,000 pool rounds are not 960,000 dispatcher states, and eight operation rows do not bound all completion, fault, clock and submission choices by 28. Each operation has two result cells, whose joint legality must be checked. Publish actual branch lengths, replay work, comparison work and memory use instead of calling this arithmetic an upper bound on the experiment.

**5.1. Replace “What sampling keeps.”**

Keep sampling, deterministic scenarios and bounded systematic exploration for both independent and dependent interactions. Bugs are often in dependent orders, and systematic search can explore those too. Local diamond checking asks whether a claimed interchange is valid; schedule exploration asks whether an execution violates a contract. These are different questions, not an allocation of independent behavior to one mode and dependent behavior to the other. Bounded completion scenarios retain their explicit environment assumptions. Every performance result is published, never a release gate.

**5.2. Replace the opening and the claim that the proposed form already unifies six shapes.**

Use one registration mechanism with several obligation templates. Do not make every property fit a binary simulation record. `defsquare` is useful if it connects an existing contract to implementations, generates concrete obligations and gives a checker or proof generator enough information to consume them. It is a second specification if authors must restate the machine’s transition catalogue, observations and admissibility rules in it.

The form should reference the existing machine, event or operation registry and an existing named contract. Authors still supply the genuinely additional mathematics: the relation, invariant, matching transition or word, admissibility conditions and any observation or occurrence correspondence. Generation must check coverage against the authoritative registry. G2 declarations additionally need a legal-choice enumerator, residual correspondence and endpoint relation. A function name in `:observes` does not supply those things.

A proposed minimal envelope is:

```lisp
(defsquare name
  :contract       existing-contract
  :sides          (implementation-a implementation-b)
  :template       :simulation
  :cases-from     existing-transition-registry
  :correspondence existing-matching-definition
  :check          executable-check-adapter
  :teeth          (positive-witness negative-witness)
  :composition    applicable-library-theorem)
```

This is proposed syntax, not an existing macro. Templates may add required fields. A snapshot quotient, a simulation, a diamond and an isomorphism transformation do not have identical obligations.

**5.2. Replace “It emits three things.”**

Each supported instance emits:

- Concrete `defthm-owed` formulas, or references to existing formulas, with named executable teeth. The generator cannot manufacture meaningful witnesses from a relation name. Today `fn2-assert-owed-teeth` runs named zero-argument functions; it does not establish that they exercise every newly generated case.
- Executable case records with applicability conditions and an actual checker entry point. A quantified ACL2 relation need not itself be executable. Its finite checks need an explicit interpretation.
- Composition or transformation events only where a library theorem’s premises have been supplied.

`:checked` must identify the revision, profile, input domain, horizon and exercised instances. It is not interchangeable with `:proved`. An unimplemented checker remains unimplemented even if its future name appears in a registration table. TRACE needs a new entry point for this mode; HISTORY, CONSUMER, WIRE, IDENTITY and RECOVERY are still placeholders at the pinned revision. “No new checker” is therefore false as an implementation claim.

**5.2. Replace the instance table and experiment paragraph.**

| Instance | What a real consumer can use |
|---|---|
| Machine preservation | An invariant-preservation template over declared arms. Frame properties additionally compare pre-state and post-state; output correspondence needs a specified output meaning. Neither follows from equality on the invariant’s diagonal. |
| Q1 refinement | Matching concrete and independent-reference transitions, initialization, output and work correspondence, followed by a turn-composition theorem. TRACE consumes executable cases. |
| Q4 summary | Event-step preservation, converter correctness and observation agreement, instantiated into relational fold induction. |
| Q5 materialization | A composite consumer relation including poll, deduplication, reasons, cursors and acknowledgments. Schedule diamonds are additional obligations where actually valid. |
| Q13 read port | Snapshot factorization for the retained observations. Future congruence is required only for a promised future interface; command translation adds simulation obligations. |
| Q23 representation change | Domain and image conditions, inverse laws and base-function correspondences consumed by `defiso` and `propagate-iso`. This is more than a G0 initialization check. |

Experiment A is the first convincing composition-template instance. Its reusable contract is 58 code lines; the instance still includes the event lemmas, converter theorem and observation work, including `rs-obs-count-agree`. The functional instantiations do not eliminate those obligations. Calling it B is justified only for the stated deterministic, common-input interface and the required matching directions.

Experiment B is a transformation-template instance. **Its measured toy cost remains 72 handwritten lines for 71 generated statement-and-definition lines**, with 15 generated events. Registration does not improve that ratio by itself. `propagate-iso` consumes the isomorphism and base correspondences; `fc-rel-fold` is not its universal composition engine. Neither experiment yet establishes correspondence to fn2’s served columns.

**5.3. Replace the subsection.**

The engineering objective is reusable composition lemmas plus explicit local obligations. The three pasting shapes are a useful organization, not a demonstrated complete proof API for E, S, B, L, Q and T. `fc-rel-fold` handles its relational fold contract. General simulations with matching words, emitted effects, crashes or nondeterministic targets need appropriate extensions and instantiation obligations. Horizontal and mixed composition also need the hypotheses in §3.2. Their ACL2 cost is not established by citing an external theorem.

The present count is stale. RELEASE-PLAN §4 lists 21 obligations, but **the pinned code contains 22: five pool, four vocabulary, ten core, two executor and one scheduler obligations**. The core has nine issue-refusal instances, including entropy, plus harvest-byte-fill.

They are not all local invariants. `fn2-pool-no-reuse` and generation relate before and after; stale and refusal properties specify preservation and returned decisions; result-reservation covers enqueue, acknowledgment and posting; harvest-byte-fill starts from an actual adapter-write trace. An invariant on a structure’s diagonal does not express all of these contracts. They can remain in their existing forms or acquire appropriate templates. Renaming them squares does not reduce their proof work.

`fn2-turn-refinement` is the clearest existing candidate for decomposition, but “39 squares plus vertical pasting” is incomplete: initialization, boundary compatibility, termination/status and work accounting remain. At this revision `fn2-turn` calls `fn2-concrete-turn`, while `fn2-ref-turn` independently implements list scheduling. Their correspondence is no longer merely equality by definition.

Keep T3’s bounds and T4’s bounded visitation statement explicit. Counters, monitors and compositional cost arguments can help prove them, but observational equality alone does not. Also correct the release-plan mapping: **T7 is acknowledged durability and T9 is exact identity**, not a generic crash-refinement theorem and a storage-summary theorem. Summary adequacy can support those contracts only through explicit client obligations.

**5.4. Replace the “does not buy” list.**

- **The actual environment.** Nondeterminism does not prevent simulation proofs; they can establish containment in a nondeterministic specification. What remains outside such a proof is the claim that real disks, networks and adapters satisfy the modeled assumptions. Native experiments provide evidence, not universal containment.
- **Foreign implementations.** A command port needs a foreign-side model and an outcome correspondence. Finite safety can be refined across that boundary; eventual replies additionally need progress assumptions.
- **Crash coverage for free.** Enumerate submitted-action prefixes, persistence states, faults, evidence and recovery transitions. Phase count times fault count is not the cut space. Transitive closure composes matched recovery steps; it does not match missing cuts. How much reduction is available must be established for a particular crash model.
- **Runtime parallelism from declarations alone.** Shared scheduler and allocator effects constrain independence. Disjoint footprints are sufficient in suitable models, not necessary: shared operations may themselves commute. A conflict-free implementation still has to be built.
- **Progress and resource bounds from equality alone.** Bounded visitation can be checked as finite safety, and costs can compose through explicit accounting. Neither follows merely because two routes return equal values. Wall-time performance remains measured.
- **Independent semantics from shared handlers.** TRACE can miss a bug shared by both executors. OWN, the client oracle and other semantic contracts retain independent work.
- **Completeness or unbounded correctness from bounded checks.** The mode can refute declarations and expose omitted cases. It neither proves their universal validity nor establishes a complete coherence basis.
- **Automatic speedup.** Local branching may detect bugs sooner or may spend most of its time replaying and comparing states. The experiment decides which occurred.

## 6. The verdict, and five decisions for ember

**Coherence is a useful foundation for a more powerful way to build, check and change fn2; a universal higher-categorical frame for fn2 remains an intellectual exercise.**

The useful part makes substitutions and reorderings accountable. A summary can replace history for a stated interface. A generated representation can inherit clients through proved correspondences. A fused executor can replace a reference segment. A declared independent pair can be challenged by two executions from the same state. These are broader and more useful applications than moving a world between versions.

The gain is not the word “square.” It is that an author states the relationship once, generated cases expose its omissions, and a real checker or transformation consumes it. Experiment A demonstrates reusable composition on a toy. Experiment B demonstrates transport but also demonstrates that, at toy scale, it saves no handwritten work. The next experiment must establish a benefit on fn2 itself.

There are two positions on the runtime claim. **Opus’s position** is that this is a foundation for checking and declaration, not runtime behavior; that accurately describes the immediate deliverable. **Astra’s position** is that “not runtime” is too permanent: certificates can later authorize useful implementation choices, including summary replacement and fusion. The deciding evidence is a real implementation generator or optimizer consuming a certificate while preserving a user-facing contract. Until then, claim better checking, not a more capable runtime.

The four named kinds of carried data are concrete reasons to compare routes. They do not themselves require a higher-category library. Nor are they an exhaustive list of useful equations: duplicate absorption already supplies a non-permutation equation with a consumer.

**The first build and its scope.**

Build a replay-based driver that exhausts applicable local cases and bounded choice windows in layer A. Use the actual pool, echo and scribe workloads. Preserve the concrete scheduler; enumerate legal environment choices and submission or harvest boundaries. Do not arbitrarily permute internal continuations.

The first finite domain should include distinct small client payloads, full and short transfers, delayed completions, reset, early and late borrow release, stale and duplicate results, and selected descriptor-handoff deaths. Record every admitted value and boundary in the experiment manifest. Keep the broad existing random workload as a separate baseline; do not call the restricted experiment exhaustive over all 26 fault classes.

Use both initialization-based exploration and replayable prefixes reaching crowded or nearly retired states. Report those separately. A supplied deep prefix is useful for testing a local claim, but it is not evidence that a search discovered that state.

**Freeze this mutation set before timed runs.**

These are proposed mutations to qualify, not bugs claimed to have been executed already. Each admitted mutant needs a legal witness on which the original passes and the mutant violates a named contract. Compilation errors and unreachable mutants are reported separately.

| Mutation | Concrete change | Distinguishing contract |
|---|---|---|
| Premature listener/reclamation reuse | Move publication of an echo row onto the free chain from successful `fn2-connection-release` into `fn2-echo-observe-close`, before outstanding borrows have drained. | Close, release and a new accept can expose a row to reuse while the old incarnation still owns outstanding work. Check allocator partition and incarnation ownership, then the client continuation. |
| Head insertion | Change `fn2-sched-make-runnable` to insert at the principal FIFO’s head, maintaining structurally valid links. Leave `fn2-ref-enqueue` unchanged. | Two wakes produce a different runnable order. TRACE should fail; the listener/reclamation fixture supplies an admission consequence. |
| Lost early borrow release | In `fn2-harvest-one`, suppress `fn2-pool-release-out` for `borrow-released` when the terminal cell has not yet been harvested. | Early release leaves a borrow retained after both cells have been consumed; late release does not. Check ownership/release accounting and subsequent reset or reclamation. |
| Premature operation recycling | Remove the leading terminal-not-harvested case from `fn2-op-harvest-phase`. | An early release can mark the operation done before its terminal result arrives. OWN and the later completion expose recycled identity or lost completion evidence. |
| Wrong short-send accumulation | In `fn2-echo-observe-send`, assign `off = count` instead of `off = old-off + count`. | Multiple short sends can repeat bytes or prevent completion. The independent client byte oracle detects this even when concrete and reference handlers agree. |
| Incomplete independence footprint | Omit shared allocator state from a declaration covering listener admission and echo reclamation, retaining the false declaration as a checker input. | The original legal race refutes the declaration. Count this as a declaration defect, not a runtime defect. |

The unchanged listener/reclamation example is a **negative independence control**, not a server bug: admission may legitimately depend on whether reclamation ran first. Likewise, early and late release are legal protocol alternatives, not automatically a co-enabled G2 pair. Explore their legal paths without inventing an independence premise.

Both modes receive the same independent monitors. Where the existing OWN checker does not cover the machine free chain, add an explicit allocator-consistency monitor and give it to both modes. Do not credit systematic exploration for being given an oracle withheld from sampling.

**What counts as found.**

A finding is a saved, replayable legal execution that violates a named contract, with the first failing boundary identified. A failed diamond additionally records the common prefix, both routes, occurrence correspondence and first distinguished observation or endpoint condition. An arbitrary raw-field difference is not a semantic finding.

A timeout is censored measurement, not a counterexample. A bounded-completion violation counts only under the stated bounded-completion environment. Duplicate witnesses count once per mutant or independently identified defect. Seeded mutations and newly discovered defects in unmodified code are reported separately.

**Make the comparison attributable.**

Run three configurations:

1. The existing random driver and existing oracle cadence.
2. Random choice using the new explicit-choice interface, transition checks and shared monitors.
3. Exhaustive local cases and bounded prefix enumeration using that same interface and those same checks.

The second comparison separates a search improvement from better instrumentation. An optional random-prefix-plus-diamond configuration measures the local checker’s contribution without changing prefix discovery.

Use one designated box, the same runtime image, resource allocation, profile and input domain. Precommit seeds, enumeration orders and workload order. Use 20 campaign seeds or orderings per mutant with a ten-minute wall-time budget per campaign. Publish every trial, detection fraction, median, tail and censored runs. Rotate execution order to reduce warm-cache bias.

Measure time from scenario initialization to first detection, including replay, checkpointing, comparisons and garbage collection. Publish image preparation separately. Count actual executed core transitions, reference transitions, adapter steps and replayed-prefix work separately; also publish their total. Both branches count. Report distinguishing trace length separately from total search effort. Compare detection curves at common wall-time and transition budgets.

Interpret the result as follows:

- **Same bugs found faster:** the common-oracle systematic configuration finds the same qualified defect set with lower detection cost. State whether the improvement is in wall time, transitions or both.
- **New bugs found within the budget:** it finds a qualified defect that the common-oracle random configuration misses under the precommitted budget. This is a bounded result, not a claim that sampling cannot find it. Discovery of an unmodified-code defect is a separate, stronger practical result.
- **No demonstrated difference:** detection sets and costs show no useful improvement, or only the instrumentation change helps. Then this generator-mode proposal remains an exercise for the measured layer-A workload. Retain useful controls and better diagnostics; do not infer that summary composition or representation transport is useless.

Budget **12 engineer-days pessimistically for this scoped experiment**: three for explicit choices and replay, three for transition correspondence and semantic comparison, three for controls and mutation qualification, and three for bounded enumeration, measurement and fixes. The repeated campaigns may consume several additional machine-days. This estimate excludes generic recursive checkpoints, POR and a universal declaration DSL.

**Five decisions for ember.**

| Decision | Recommendation | Cost, complexity and what it forecloses |
|---|---|---|
| 1. Build the measurement first? | Yes. Build the replay-based layer-A experiment above. | **12 engineer-days pessimistically for that scope**, plus machine time. Adds a test driver and explicit-choice interface. Forecloses claiming a payoff before measuring one. |
| 2. Adopt one universal declaration now? | Adopt one registry with separate simulation and diamond templates first. | **Four additional days pessimistically for those two templates and two real consumers.** Some explicit adapters remain. Forecloses forcing lenses, isomorphism transforms and progress into an inadequate common record. |
| 3. Which equality should the checker use? | Keep exact Q1 correspondence distinct from each semantic G2 contract. Include histories and future-relevant state. | **Two days within decision 1’s budget** for the initial contracts and controls. Adds explicit comparison definitions. Forecloses one permissive comparator that silently discards inconvenient effects. |
| 4. Start pruning after bounded checks pass? | No. Keep pruning separate until a sound dependence model and bound-preserving algorithm are implemented. | **Zero additional days now; 12 days pessimistically for a later narrowly scoped reduction prototype**, excluding a general dynamic completeness proof. Forecloses an immediate coverage claim based on tested footprints. |
| 5. Invest next in runtime use or categorical completeness? | Choose one real consumer, preferably summary replacement or order-preserving fusion, before a route-normalization framework. Keep D68. | **Ten days pessimistically for one scoped integration experiment after its consumer exists**, excluding that consumer’s construction. Forecloses a general migration framework and global coherence claim for the present release. |

On decision 2, **Opus favors one form immediately** because shared registration and enumeration should remove repeated work. **Astra favors a common registry with specialized templates first** because the present form omits substantive premises and proposes consumers that do not yet exist. Two real instances decide: count handwritten semantic declarations, generated obligations and checker adapters, including the machinery needed to make both instances work. A single public form is welcome if it reduces that total without concealing obligations.

## Astra: on the note’s adoption of session 1, and the open disagreements

**Adoption of session 1.** Sections 2.5 and 3.1 through 3.4 largely preserve my position. Three compressions need correction. Section 2.4 cannot automatically repeat Q1’s 39 dispatch cases for OWN and the client oracle; those contracts have different boundaries. Section 3.0 should apply prefix closure to safety properties, and its exclusions of timing and turn counts to the proposed T quotient, not every fn2 contract. Section 4.7 overstates “non-coherent”: the exhibited implementations or full response contracts fail particular equations, while a corrected merge can make a narrower publish/notify square valid. A missing G1 does not make arbitrary harvest-boundary movement valid. The older Q12 derivation still needs idempotence, and the Q13 read-view row still demands stronger future congruence than §2.5 permits.

**Section 3.5’s additions.** Replace the PCT comparison: **PCT guarantees at least `1/(n k^(d−1))` detection probability per run for its scheduler and stated thread, step and bug-depth model**. This is a lower bound, not an “at best” probability; fn2’s scheduler inherits no such bound, and two exchanged completions do not establish depth two. A local diamond check guarantees neither reaching the enabling state nor a detection probability. [Burckhardt et al.](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/paper-83.pdf). COMMUTER is relevant, but SIM commutativity includes response validity and indistinguishability under future operations, with a prefix condition. It is stronger than an endpoint-value diamond and does not automatically parallelize fn2. [Clements et al.](https://people.csail.mit.edu/nickolai/papers/clements-sc.pdf). DPOR likewise uses a dependence model and sound backtracking rules; it does not learn universal independence from the absence of observed conflicts.

**Q1 as the containing square.** I reject containment as a correctness claim. Q1 connects two executors that share machine semantics. It can faithfully execute a wrong summary, retry rule or byte handler. Those semantic obligations require their own models and relations. The short-send mutation supplies a concrete discriminator: agreement between executors can coexist with a client-oracle failure.

**Q5’s “if and only if.”** The adopted qualification is right. The whole consumer contract must be established, including poll, deduplication, reasons and cursor behavior. A separate primitive poll generator is one decomposition; a generic merge theorem could discharge the same obligation. Neither decomposition is mathematically necessary. Judge it by the actual composition theorem and its consumers.

**Q7.** Splitting the same induced transition word is fold composition. Moving harvest or submission boundaries can change that word and admission outcomes. The listener/reclamation witness defeats an unconditional boundary-invariance claim. State the correspondence premise and prove it where valid; retain order dependence elsewhere.

**Q22.** Adding the allocator repairs one omitted interaction. It does not establish composition while scheduler, operation correlation, initialization or other shared effects remain implicit. Forward component simulations give containment, not equality of behavior sets. Experiment E needs an explicit common timeline and a composition rule covering every shared boundary.

**Owner separation as a G2 condition.** Keep it as a candidate condition, never a certificate. Different owners can still share the posted FIFO, allocator, quotas, scheduler services and environment resources. Even disjoint direct writes may have different responsive continuations. A valid declaration names the boundary, retained observations and shared effects, and survives both legal routes with corresponding occurrences.