## 3. The coherence conjecture for fn2's frame

The useful claim is that **local certificates compose into correctness claims for whole executions**, and that declared independence lets us avoid checking every permutation of the same execution. It is not that every route through fn2's frame commutes. Some routes represent different decisions. Others forget information that a later operation needs.

We should separate two statements:

1. **Soundness of generated diagrams.** Every diagram assembled from valid G0, G1, G1q and G2 instances preserves its declared observations.
2. **Completeness of the proposed generators.** Every pair of routes we intend to call interchangeable can be connected by those generators.

The first has an elementary proof once the compatibility conditions below hold. The second is the actual coherence conjecture for fn2. A finite list of transition kinds does not establish it.

### 3.1 Schedules and observations

Fix an implementation revision, supported profile `P`, fault profile `F`, and initial state satisfying `Inv`.

A schedule is a **finite legal execution of the composite core and modeled environment**. Its labels identify transition instances, including their parameters, operation identities and generations, completion payloads, fault choices and targets. Internal steps obey the specified calendar, posted FIFO and principal FIFOs. A schedule is not an arbitrary permutation of individually enabled machine continuations.

For the theorem, consider all finite schedules. For the simulator, restrict to a declared finite input domain and horizon `H`, recording precisely what `H` counts. A small resident profile alone does not make the exploration small: payload values, generations, disk states and execution length still need explicit bounds or proved abstractions.

Two schedules are equivalent, written `σ ~I τ`, when one can be transformed into the other by finitely many **legal adjacent swaps certified by G2**, preserving the identities of the occurrences being swapped. For state-dependent independence, the swapped steps may have residual forms:

```text
s --t--> s_t --u/t--> s_tu
s --u--> s_u --t/u--> s_ut
```

The residual notation records which occurrence survives the swap. It is especially relevant when steps allocate identifiers or translate positions.

The environment must admit both routes. A swap cannot change a fault from one operation to another, move a completion before its submission, or move a crash across a persistence boundary merely because the resulting words have the same labels. Adaptive environments also require care: a client that chooses its next request from an observed reply must remain a legal client after the proposed swap.

For static independence, let `Σ` be the alphabet of fully distinguished actions, `I` a symmetric, irreflexive relation, and `D = Σ² \ I`. Define:

```text
qI : Σ* → M(Σ,I) = Σ* / (tu = ut when t I u)

ΠD(w) = (πC(w))C
```

Here the `C` are dependence cliques covering every dependent pair, and `πC` erases letters outside `C`. Equality of these projections characterizes trace equality. This is the precise use of `mazurkiewicz1995-introduction-to-trace-theory.pdf`, §1.5.

An admitted observation factors through this quotient:

```text
Obs(w) = Obs̄(qI(w)).
```

An admitted finite safety property is a set of observations that is downward closed under trace prefixes. Equivalently, its language of schedules is prefix closed and invariant under the certified swaps. Equality at the diamond's final state alone is insufficient: the observation must include relevant emitted history, or the safety monitor must itself be included in the checked state.

Examples include each connection's ordered output, each domain's journal, operation outcomes, and ownership violations, provided the chosen independence preserves them. Global interleavings, timing and turn counts are outside the proposed T quotient.

**There cannot be one observation class that both preserves arbitrary connection byte streams and excludes article numbers.** NNTP replies can contain article numbers. Q1 and WIRE must preserve those bytes. Q12's peer-convergence claim may instead observe validated facts and forget local article numbering. Two POSTs that exchange assigned article numbers are dependent for the former claim, even if their accepted fact sets agree for the latter. Each relation declaration must name the contract it preserves.

For state-dependent independence, dependence-clique projections are not automatically available. First establish a consistent occurrence structure, or use the explicitly generated path equivalence without claiming the static trace-monoid representation.

### 3.2 The theorem schema

Let each representation `A` have invariant states, labeled transitions and an observation map into a **common declared observation quotient** `O`. Include emitted observations in the semantic state when needed.

A representation edge `A → B` supplies a relation `R_AB` and a label interpretation `h_AB`, where a source transition may be interpreted as a finite target word. An E edge may use a function; an S edge supplies matching executions; a B edge supplies matching behavior in both directions. Q edges restrict the observable contract through their declared kernels. L edges additionally carry their lens equations. X entries are assumptions about the environment and are not representation edges discharged by this theorem.

The hypotheses are:

**H0. Entry and invariant preservation.** G0 establishes admissibility and `R_AB` at initialization or conversion. Every participating transition preserves its invariant. Every matching target word is legal from the related target state.

**H1. Transition and output preservation.** For every source transition instance:

```text
R_AB(a,b) ∧ a --t/o--> a'
  ⇒ ∃b'. b --h_AB(t)/o'--> b'
           ∧ R_AB(a',b')
           ∧ o ≡O o'.
```

This includes refusals and output effects, not just successful state updates. If a target word hides intermediate steps, its intermediate observations must be accounted for. Every externally distinguishable submitted-action prefix and death cut remains a boundary obligation.

**H≈. Future closure.** Every endpoint equivalence `≈_A` used in a G2 square agrees on current observations and is preserved by corresponding future transitions, including their enabledness and effects. Equality of today's displayed value is not enough.

**HI. Valid independence.** Every G2 instance has both legal routes, preserves the participating occurrences, and gives equal observations with `s_tu ≈_A s_ut`. For a static relation, this validity must hold throughout the invariant. For dynamic independence, declarations additionally provide the residual and consistency laws needed by the intended reduction.

**HM. Compatibility of representation changes with rescheduling.** The mixed pasting condition proposed in §2 is:

```text
R_AB ; ≈_B ⊆ ≈_A ; R_AB.
```

Read composition from left to right. If `a R_AB b` and `b ≈_B b'`, there must be an `a' ≈_A a` with `a' R_AB b'`. If pasting is used in both directions, supply the corresponding opposite inclusion or use an explicitly saturated relation:

```text
R̄_AB = ≈_A ; R_AB ; ≈_B.
```

Then prove the required G0, G1 and observation properties for `R̄_AB`.

This relation condition is not the entire mixed obligation. The label interpretation must also respect the declared swaps:

```text
t I_A u
  ⇒ h_AB(t) h_AB(u) ~I_B h_AB(u) h_AB(t),
```

with residual versions for state-dependent interpretations. Otherwise a representation edge can map independent source actions to dependent target behavior.

**HQ. Honest loss.** All routes being compared land in the same observation quotient `O`. Each Q edge preserves the observations that factor through its kernel, and its transition language respects that kernel when future behavior is claimed. Different losses cannot be silently treated as one equivalence.

**H2. Coherent route data, when used.** Any position maps, converted cuts, event identifications or loss descriptors consumed by later operations agree along routes declared interchangeable. This is separate from equality of values returned through a smaller read interface.

Under these hypotheses:

> **Generated-diagram theorem schema.** Starting from a G0-related pair, every finite diagram obtained by composing the certified G1 squares, legal G2 swaps and certified mixed pastings preserves observations in `O`. Therefore any two executions connected by such a diagram have equal `O` observations and agree on every prefix-closed, trace-invariant safety property over `O`.

For a one-way S relation into a nondeterministic specification, the conclusion is **behavior containment**, not equality between arbitrary allowed behaviors. Two implementations that each refine an abstract specification allowing either `0` or `1` need not agree with one another. Equality requires a common determined behavior, a matching B relation, or another explicit uniqueness argument.

This distinction matters for Q15 and Q16. An uncertain commit can refine a specification containing several evidence-compatible outcomes without making those outcomes equal.

The proof of the schema is induction on the construction of the diagram. The nontrivial fn2 conjecture is:

> **Frame completeness conjecture.** For each declared interchangeable-route contract, every pair of legal finite routes satisfying that contract is connected by the generated diagrams above, together with the explicitly declared data-carrying route equations.

We should not claim this conjecture globally. Establish it first for one useful fragment: summary replacement followed by arbitrary admitted suffixes, or a precisely delimited class of environment reorderings.

### 3.3 What is free, and what must be earned

The following are free **after their premises have been supplied**:

- G1 extends along words by induction.
- Relations compose associatively.
- An equivalence generated by legal swaps is an equivalence.
- Equality of observations is transitive.
- A static symmetric, irreflexive `I` defines a trace monoid.
- Kernels of composed functions compose by pullback.

The following are not free:

- The converter establishes the relation.
- A hidden difference stays hidden after every future input.
- A declared independent pair preserves enabledness, outputs and scheduler behavior.
- A state-dependent independence declaration has consistent residuals.
- Representation changes preserve the chosen schedule equivalence.
- The observation class captures the promises users actually rely on.
- Every intended route equality is generated.
- Data chosen along different routes agrees.
- A bounded search covers every instance of a schema.

The cube condition deserves a precise scope. Pairwise G2 checks suffice to preserve observations along an **explicit finite sequence of validated swaps**. A cube axiom is not needed merely to take that sequence's transitive closure. It becomes necessary when we claim that dynamic swaps describe the linearizations of a consistent partial order, that occurrence identities transport independently of the chosen swap sequence, or that a reduction algorithm may infer unexamined permutations from the declaration.

For three occurrences, the two three-swap routes reversing their order must exist consistently and induce the same occurrence identification. This is a check on data carried by the squares, not just their endpoint values.

### 3.4 The theories that predict something

**Mac Lane: structural coherence, not arbitrary program equivalence.** Associate each typed interface with an object, each certified component with an arrow, and composition of independent interfaces with tensor. The interpretation is:

```text
F : free monoidal syntax of declared components → semantic components
```

`F` maps reassociation and unit insertion to the actual interface rearrangements. The pentagon and triangle, with naturality, ensure that structural rebracketing has one meaning. Strictification permits list-shaped interfaces and strictly associative syntax, provided the semantic interpretation carries the corresponding coherence.

Most fn2 squares are thin. Once a proposition `Obs(route₁) = Obs(route₂)` is proved, there is no further operational distinction between its proofs in the proposed ACL2 interface. Mac Lane does not remove the obligation to prove that proposition. The substantial case is a structural transformation that carries a position map, cut conversion or occurrence bijection. Those maps can disagree and must be compared.

**Prediction:** normalize structural wiring, and compare the carried maps where route data is used. The analogy to migration routes otherwise remains a footnote. Sources: `maclane1963-natural-associativity-commutativity.pdf`; `selinger2009-survey-graphical-languages-monoidal-categories.pdf`, especially the structural coherence discussion and Theorem 3.12. [Mac Lane, *Natural Associativity and Commutativity*, 1963](https://www.mscs.dal.ca/~selinger/papers/papers/graphical-bib/public/MacLane-natural-associativity-and-commutativity-1963.pdf).

**Mazurkiewicz: the immediate schedule quotient.** The morphism is `qI` above, followed by the interpretation of a trace as an action on invariant states modulo `≈`. What is checked is exactly that the action respects each equation `tu = ut`.

Static independence makes the algebraic quotient well defined. It does not establish that fn2's execution semantics factors through it. That is G2, including enabledness. Independence is not required to be transitive. Dependence must include allocator, quota, scheduler, output and environment effects where they matter.

**Prediction:** an independence declaration has a condition, observation contract and executable diamond obligation. Dependence-clique projections provide a concrete comparison representation where the static model applies. Source: `mazurkiewicz1995-introduction-to-trace-theory.pdf`.

**Pous and Sangiorgi: a sound way to make the relation smaller.** For deterministic input-indexed machines, define the progression operator:

```text
b(X) = {(a,b) |
          obs_A(a) = obs_B(b)
          and every corresponding input leads to a pair in X}.
```

For partial machines, include enabledness and refusal agreement. Behavioral equivalence is `νb`. An up-to function `f` is compatible when it is monotone and:

```text
f ∘ b ⊆ b ∘ f.
```

Then `R ⊆ b(f(R))` is a sound proof pattern. The fn2 instance maps the two fold implementations to this machine coalgebra and uses a certified closure on their relations. Up to the appropriate bisimilarity is sound; arbitrary present-observation equality is not.

Experiment A's tooth 1 is exactly the missing closure check: histories `read 1` and `read 2` both have count 1 at bound 2, but the suffix `read 1` produces counts 1 and 2. Its implemented theorem, `rs-count2-rel-not-step-closed`, refutes the proposed relation. The experiment itself uses direct relational induction; invoking up-to theory is useful only when an actual closure reduces the proof obligation.

**Prediction:** `:up-to` names a closure with a compatibility theorem, never an unrestricted comparison callback. References: Damien Pous and Davide Sangiorgi, *Enhancements of the Bisimulation Proof Method*, in *Advanced Topics in Bisimulation and Coinduction*, 2012; their [account of compatible enhancements](https://www.cs.unibo.it/~sangio/DOC_public/hist_enha2019.pdf). `abstract-account-up-to-techniques-inductive-behavioural2024-2412.07351.pdf` supplies related generalizations.

**Winskel and Nielsen: occurrence identity across a diamond.** Starting with the transition system, identify opposite edges representing the same occurrence across certified squares:

```text
(s --t--> s_t) ∼ (s_u --t/u--> s_ut).
```

Events are equivalence classes of such parallel transitions in the appropriate unfolding. A morphism `(f,h)` maps states and transition labels while preserving transitions and independence. A G1 label-to-word interpretation needs an expansion before it becomes this kind of morphism; it is not automatically one.

Check uniqueness and consistency of residual occurrences, completion of the required diamonds, and preservation of independence under event identification. Then a run maps to a configuration, and a cursor maps to a down-closed set of events. Conflicting admission choices and compatible observations of those choices remain different kinds of event.

**Prediction:** event correspondence belongs in a dynamic G2 certificate; multi-domain cuts must remain down-closed across that correspondence. Sources: `winskel1987-event-structures.pdf`; `winskel-nielsen1995-models-for-concurrency.pdf`, §12. [Winskel and Nielsen, *Models for Concurrency*](https://www.cl.cam.ac.uk/~gw104/winskel-nielsen-models-for-concurrency.pdf).

**Goubault: a geometric realization of the same checked swaps.** Construct a directed complex `K` with invariant states as vertices, transition instances as edges and certified G2 squares as faces. The realization sends a schedule `σ` to a directed path `|σ|`; a G2 swap becomes a deformation across its face.

For the corresponding discrete PV progress models, combinatorial dihomotopy is generated by these adjacent swaps. This is the precise trace-equivalence connection. A blanket identification of arbitrary continuous dihomotopy with fn2 schedule equivalence would require an additional representation theorem.

**Prediction:** a shared-resource obstruction means there is no certified face across which to move the schedule. The useful artifact is the failed diamond or resource-acquisition condition. Computing topology adds no immediate checker beyond that. Sources: `goubault2000-geometry-and-concurrency-users-guide.pdf`; `goubault2003-geometric-perspectives-concurrency-theory.pdf`, §§3 and 5. The geometric language is currently a footnote to G2, not another implementation requirement.

**Games: coherence must survive interaction.** Map environment completions and faults to Opponent moves, and core decisions and actions to Proponent moves. Map a complete legal interaction to a play in the asynchronous graph; map each permitted rescheduling to a permutation tile.

What must be checked is that the core's permitted plays and the environment contract remain closed under the claimed tiles, with consistent residuals and the cube property where a partial-order interpretation is claimed. Determinism under one input order does not establish that closure.

**Prediction:** an environment-side independence declaration must say which responsive core behavior it preserves. Otherwise “different client” is an unsound independence test. Melliès and Mimram make the cube requirement explicit in *Asynchronous Games: Innocence without Alternation*, CONCUR 2007, §2. [Paper](https://www.irif.fr/~mellies/papers/MelliesMimram07.pdf). The broader innocent-strategy machinery is a footnote unless fn2 uses its additional conditions; `mellies2006-asynchronous-games-2-true-concurrency-innocence.pdf` is background.

**Symmetric monoidal coherence and string-diagram rewriting: useful for generated wiring.** Let `Σwire` contain typed component operations. Interpret:

```text
J : FreeSMC(Σwire) → Rel
```

with interfaces mapped to behavior spaces, boxes to relations, composition to composition over shared boundary records, and tensor to independent interfaces. Allocator and scheduler interactions must be explicit boundary records. Two components sharing an undeclared allocator are not independent tensor factors.

Structural symmetry and reassociation can then be normalized without changing meaning. A semantic rewrite still needs `J(lhs) = J(rhs)`. The Bonchi, Gadducci, Kissinger, Sobociński and Zanasi results explain why arbitrary graph rewriting is not automatically sound for string diagrams: the interfaces and, for general symmetric monoidal theories, convexity restrictions matter.

**Prediction:** a wiring optimizer retains typed boundaries and checks each nonstructural rewrite; it does not copy or discard ownership wires without a declared operation. Sources: `selinger2009-survey-graphical-languages-monoidal-categories.pdf`; `bonchi-gadducci-kissinger-sobocinski-zanasi2022-string-diagram-rewrite-theory-II.pdf`. [String Diagram Rewrite Theory II](https://arxiv.org/abs/2104.14686). Until fn2 has such an optimizer, this is a design constraint for Q22, not a reason to build a diagram library.

**Squier and Newman: closer to the ambitious completeness claim.** Suppose route expressions have a terminating rewrite system. Map each expression to its semantic route, and each rewrite to a certified route equation. Newman's lemma makes local confluence sufficient for confluence under termination. Squier's theorem goes further: for a convergent presentation, resolutions of critical branchings generate a homotopy basis; a finite convergent string presentation has finitely many such branchings. [Guiraud and Malbos, *Polygraphs of Finite Derivation Type*, §4.3](https://math.univ-lyon1.fr/homes-www/malbos/Art/ihdr.pdf).

**Prediction:** if fn2 builds a route normalizer, enumerate overlaps between its rewrite rules, compare their carried maps, and provide a decreasing measure. This is closer than Mac Lane to “all intended route equalities follow from a finite basis.” fn2 has not supplied that presentation.

Even sorting independent actions is not automatically convergent. Let `a < b < c`, with `a I b`, `b I c`, but `a` dependent on `c`. Orient independent descending pairs toward ascending order:

```text
cba → bca
cba → cab.
```

Both results are irreducible under those rules. A normalizer needs a better representation or additional rules and critical-branching resolutions. The server itself is not a terminating rewrite system merely because each turn has a budget.

**Partial-order reduction and movers: the nearest engineering applications.** For POR, map a full execution to its dependence order and choose representative linearizations. Soundness requires valid dependence and a search rule that retains representatives of the required behaviors. G2 validates swaps; it does not itself implement persistent sets, DPOR backtracking or source sets.

The immediate prediction is a separation between **checking independence declarations** and **using them to prune exploration**. Start with the former. Flanagan and Godefroid dynamically discover backtracking points; Abdulla and coauthors' source sets and wakeup trees improve which representatives are explored. Sources: `godefroid1995-thesis-partial-order-methods-verification-concurrent-systems.pdf`; `flanagan-godefroid2005-dynamic-partial-order-reduction.pdf`; `abdulla-aronis-jonsson-sagonas2014-optimal-dynamic-partial-order-reduction.pdf`; [Abdulla et al., *Source Sets*, JACM 2017](https://doi.org/10.1145/3073408).

For Lipton reduction, map a concrete segment consisting of right movers, a central action and left movers to an abstract atomic action. Check the directional commutations, gates, invariants and permitted observation boundaries. This directly predicts a certificate for reordering fusion. It does not authorize hiding a submitted action from a crash between submissions.

Sources: `lipton1975-reduction-method-proving-properties-parallel-programs.pdf`; `kragl-qadeer2018-layered-concurrent-programs.pdf`. Civl's layered refinement is particularly close to fn2's desired generated implementation and local correspondence obligations.

Finally, a bounded search must preserve its bound under reduction. Swapping adjacent steps preserves word length; changing turn packing, preemption counts or expansion lengths may not. Coons, Musuvathi and McKinley's *Bounded Partial-Order Reduction* gives an explicit warning: simply combining a bound with ordinary DPOR can omit behaviors within that bound. [OOPSLA 2013 paper](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/bpor-oopsla-2013.pdf).

## 4. The diagrams that do not follow

These cases divide into false independence claims, missing composite-transition obligations, and comparisons that become valid only after narrowing the observation contract.

### 4.1 Live publication between installation and notification

Take one durable item `D` installed at position `p`, and one transient item `L` published afterward in the same stream.

```text
route A: install(D,p); publish(L,(p,1)); notify(D)
route B: install(D,p); notify(D); publish(L,(p,1)).
```

A delivery path that forwards notifications in arrival order can emit:

```text
A: L, D
B: D, L.
```

One durable item and one transient item suffice. Two streams add a separate witness: per-stream live sequence numbers can tie, so they do not define an exact multi-stream order.

**Verdict:** the arrival-order implementations do not commute on delivered order. UC §5.3's amendment makes the desired order a contract:

```text
D sorts at (p,0)
L sorts at (p,s), s > 0.
```

That contract creates a missing **G1 obligation for the composite delivery transition**:

```text
delivered prefix = a prefix of the declared ordered merge,
with typed gaps and no cursor beyond an unexamined required item.
```

Notification may then be treated as a hint. Publish and notify can receive a G2 certificate only after the actual merge implementation preserves this contract.

Do not add `install I publish`: publishing before installation gives `L` a different happened-after stamp and may change the intended order.

**Cost:** the reader needs enough frontier and source information to avoid releasing `L` ahead of undiscovered durable predecessors. Bounded catch-up, retained merge state or waiting may be required. Choosing notification-arrival order instead is cheaper but abandons the exact mixed order promised by Q17. A node-wide sequence adds cross-stream ordering state; a per-stream sequence limits the claim to one stream.

### 4.2 Lossy maps and future operations

**The moving window.** Let `qW` retain only read-state information in a window of width 2 above the high-water mark. Start with:

```text
hwm = 0
above = {3}
suffix = read(1); read(2).
```

Compare:

```text
route A: apply suffix to the full state; then qW
route B: qW first; then apply the suffix.
```

Route A compacts through article 3. Route B discarded the read of article 3, so it reaches only 2. Article 3 has become relevant inside the new window.

**Verdict:** this is a failed G1q congruence, not an additional migration-route equation. The proposed quotient does not support its own future transition language. Experiment D's fixed-domain replacement repairs the claim: queries above fixed `N` remain unavailable instead of later becoming available with invented answers.

**Cost:** retain the potentially relevant information, support an explicit unavailable region, or restrict future queries. Declaring a kernel does not recover discarded information.

**The dropped generation.** Experiment B supplies a smaller, immediate witness:

```text
r1 = (registration 7, position 100, generation 5)
r2 = (registration 7, position 100, generation 6)
q(r1) = q(r2).
```

For token 5:

```text
route A: check token in v1; translate the answer
route B: erase generation; check token in v3.
```

Route A accepts in `r1` and rejects in `r2`. Route B receives the same row and token in both cases.

**Verdict:** observation factorization already fails. No v3 function can preserve stale-token rejection for both states. Add a G1q edge obligation for every retained observation, including authorization and refusal results, not just stored values.

**Cost:** keep generation or equivalent distinguishing evidence. Dropping stale-token rejection would change the contract, not optimize its representation.

**Composition of losses.** For:

```text
q(x,y) = x
r(x) = x mod 2
```

the composite kernel is:

```text
κ_(r∘q)(s,t) ⇔ κ_r(q(s),q(t)).
```

Thus `(0,0)` and `(2,0)` are identified by the composite even though `q` distinguishes them. The two kernels live on different spaces; “union their losses” is not a typed composition rule.

**Verdict:** pullback composition is free for actual functions. Dynamic preservation follows from composing valid G1q squares with compatible input interpretations. What remains separately checkable is that the reported loss, position map and converted cuts denote that composite. `unavailable`, `estimate` and `omitted-fields` are other D4 variants, not kernel relations to union.

For Q13, a snapshot read reduct need not be a congruence under every room command. That stronger requirement begins when the port promises future command behavior. Otherwise the note would reject valid read-only views for hiding information their interface never uses.

### 4.3 Revision and position

The withdrawn expression:

```text
[adopt] ⟨≥p⟩ φ ↛ ⟨≥p⟩ [adopt] φ
```

should remain withdrawn. `⟨≥p⟩` names a read operation with a returned position and interpretation; it was not defined as a modal operator on formulas.

The operational comparison is:

```text
route A: read-at-least(p,query); adopt(r→r')
route B: adopt(r→r'); read-at-least(p,translated-query).
```

The smallest witness changes no application value. The first read returns a result stamped with `r`; the second returns one stamped with `r'`. Adoption may also change the available position, authorization or refusal. Equal values alone do not make these responses equal.

**Verdict:** generally non-coherent as full commands. Keep the order and producer interpretation observable.

A narrower missing G1 obligation is meaningful:

```text
R_m(s,s')
  ⇒ obs_(f@r)(s,q)
       = obs_(f'@r')(s',ρ(q))
```

for a declared preserved query at corresponding snapshots, with transferred coverage at the converted cut. It requires availability and authorization conditions appropriate to that query. An arbitrary `at-least` choice on either side does not select corresponding snapshots automatically.

**Cost:** pin or identify the query interpretation and cut, retain whatever history the exact query requires, and handle crossing Decide continuations through MK R3's drain-or-revalidate rule. Forgetting revision stamps yields a weaker value-only comparison and cannot justify outcome attribution or authorization.

### 4.4 Uncertain commit and retry

Let operation `op` have a batch whose persistence may have completed, while its barrier completion is lost.

```text
route A: resolve persistence evidence; retry(op)
route B: retry(op) while unresolved; resolve persistence evidence.
```

If route B treats uncertainty as refusal and executes `op` anew, one operation can receive two effects or incompatible outcomes. A single operation, one lost completion and one retry suffice.

Under the intended protocol, route A can return the established original outcome. Route B initially returns or retains `uncertain` with a resolution handle. These response histories are observably different even when they eventually resolve identically.

UC's ack scenario adds a distinct witness:

```text
original proposal P advances to cut 10, with outcome O_P
its reply is lost
a later proposal advances to cut 20
retry P.
```

The current cursor 20 establishes coverage. It does not establish `O_P`, its original position or its original decision.

**Verdict:** resolve and retry are dependent on the full outcome contract. Add the following G1 obligations to Q14-Q16:

```text
unresolved(op) ⇒ retry cannot create a fresh execution of op;

resolved(op,p0,out) ⇒ retry returns that recorded out;

same op with contradictory binding ⇒ op-reused;

summary/recovery preserve the evidence needed by those branches.
```

The abstract commit specification needs an unresolved state or an evidence-compatible set of possible histories. Acceptance, refusal and uncertainty must remain distinct.

**Cost:** retain operation binding, outcome or resolution evidence, fence unresolved work, and reserve the associated resources. Evidence retirement requires the explicit identity-fencing rule in STORAGE decision 1. Liveness still depends on obtaining sufficient recovery evidence.

At most, a narrower comparison can equate the eventual durable effects after the same resolution. It must not erase the observable distinction between `uncertain` now and an established answer now.

### 4.5 Disposition at a fork

Q19 identifies historical events through the fork cut. It does not identify current ownership or authority.

Take one outstanding external-effect obligation `o` at cut `c`, and one valid discharge receipt `e`. Compare the intended authority-changing operations:

```text
route A: fork(c, disposition(o)=child); discharge_parent(o,e)
route B: discharge_parent(o,e); fork(c, disposition(o)=child).
```

If assigning `o` to the child transfers its live authority, route A must prevent the parent from spending that authority afterward. In route B, the already-consumed authority cannot be transferred again. The documents specify total disposition and held effects, but do not yet fully specify this stale-disposition case. We should not manufacture an existing refusal word for it.

There is also a direct effect witness:

```text
route A: discharge through the authoritative parent's adapter
route B: carry the historical obligation into the fork; replay discharge.
```

MK O8 requires route B's external effect to remain held. A historical receipt or copied obligation row cannot authorize another external execution.

**Verdict:** disposition and discharge are generally dependent. The missing generators are G1 obligations for the composite `fork` and `promote` transitions:

```text
every obligation in the named fork snapshot has one disposition;

each disposition satisfies its kind's authority/resource contract;

split consumes the original allocation and creates only authorized shares;

fork execution emits no held external effect;

promote re-decides against current parent state and authority.
```

Totality alone does not prove conservation. A disposition assigning one unit to each branch still fails O9 even if it is represented by one syntactic `split` choice.

My proposed decision is to distinguish **historical fork disposition** from **transfer of live authority**. The former can be evaluated at `c`; the latter must validate current authority in the parent's commit order. A stale transfer is refused by a named binding or authority failure. Promotion always re-decides.

**Cost:** retain snapshot identity and disposition evidence, maintain current authority separately, and allow promotion or transfer to refuse after the parent advances. The cheaper alternative is to keep all external authority in the parent and make the child entirely observational until promotion. Either decision preserves useful counterfactual forks; neither gives an unconditional fork/discharge diamond.

### 4.6 Further diagrams the basis must expose

**Harvest boundaries are not arbitrary turn reassociation.** Q7 is free when it only splits a fixed legal reference word:

```text
run(s,σ1σ2) = run(run(s,σ1),σ2).
```

But:

```text
post(a); run; post(b); run
post(a); post(b); run
```

need not induce the same reference word. `fn2-ref-transition` prioritizes posted observations over calendar visits. Changing the harvest boundary can change which machines are queued before a visit, which resource becomes available, or whether admission succeeds.

**Verdict:** Q7 needs a G1 correspondence between the actual induced words, and G2 for any required reordering. The cost is an explicit boundary condition on turn splitting. The listener/reclamation witness below prevents an unconditional claim.

**Compaction and a historical read.** A latest-only fold at `cov = 2` may retain value 1 after a history whose value at position 1 was 0:

```text
route A: exactly-at(1); compact
route B: compact; exactly-at(1).
```

Returning 1 on route B is wrong. Returning unavailable is honest but differs from route A if the historical read was still promised.

**Verdict:** G1 for compaction must preserve every unexpired retained contract, including in-flight reads, or require expiration before evidence removal. Coverage is not history. The cost is retained version state, replay material or a narrower declared historical window.

**A returned loan and cancellation.** Compare:

```text
route A: observe target completion/release; reclaim
route B: observe cancel-not-found; reclaim.
```

A single outstanding borrowed buffer is enough to refute treating these as equivalent. Cancellation can fail or race without returning the target's loan.

**Verdict:** the G1 ownership transition must consume actual release evidence. Cancel and target completion are not independent merely because they use different operation rows. The cost is retaining the target operation and borrow until its own protocol permits reuse.

**Duplicate delivery is not a permutation.** Q12 compares delivery words with different multiplicities, such as `f` and `ff`. G2 preserves length and cannot derive their equality.

**Verdict:** add an explicit idempotence equation, or factor both words through a validated-fact-set E abstraction and prove its G1 preservation. The cost is deciding the scope: final Bindings can agree while per-offer replies, admission charges and journals differ.

## Astra: a better generating set, and two-position disagreements

I would retain the names G0, G1, G1q and G2, but make their roles more precise.

- **G0:** entry, conversion and invariant establishment.
- **G1:** matched transitions of the composite, including outputs, refusals, invariant preservation and the named observation edge.
- **G1q:** a diagnostic specialization of G1, adding observation factorization and future-kernel preservation when future behavior is promised.
- **G2:** legal swaps of transition instances, with enabledness, effects, scheduler consequences, residual occurrence maps and the selected observation contract.
- **Compatibility obligations:** future closure, mixed pasting and, when claimed, cube/residual consistency.
- **Declared route equations:** data-carrying Q10 cells and equations such as Q12 duplicate absorption that are not permutations.

The last two entries are not another list of machine transition kinds. They are the conditions and extra equations needed to justify the proposed presentation.

Crash obligations can remain G1 instances in the mathematics, but deserve a separate generated coverage table in the engineering. Index them by submitted-action prefix, persistence state, fault choice, evidence and recovery transition. “Eleven phases times fault classes” does not enumerate every physical cut inside a phase. The fact that `→_C` is defined as a transitive closure only lets already-matched crash steps compose; it does not establish that recovery simulation matches each step.

The general form of the poll lesson is:

> Generators belong to transitions of the composite semantic machine, including its synchronization and shared-resource protocols. Component certificates discharge composite cases only through an explicit composition rule.

That includes the allocator, scheduler, admission, merge, retry resolution and fork disposition. It does not mean every helper needs its own manually maintained theorem.

| Issue | Draft's position and reason | Astra's position and reason | What decides |
|---|---|---|---|
| Three families suffice | G0, G1 and G2 cover transition preservation and permutations. | They suffice for generated thin diagrams under compatibility hypotheses. They do not establish completeness, idempotence or equality of carried data. | A formal definition of route syntax and intended equality, followed by a completeness proof for a useful fragment. |
| G1q is separate | Its failures have a recognizable kernel shape. | Keep it as a declaration/checker variant, not an independent mathematical primitive. Separate snapshot factorization from future congruence. | Whether it produces clearer witnesses for the window and generation examples without duplicate author declarations. |
| Mixed pasting is the one non-free condition | Vertical and horizontal pasting are structural. | Future closure, valid enabledness, label correspondence, dynamic consistency and adequate observations are also non-free. Some are already hidden inside the definitions. | State every premise of a machine-checked pasting lemma. |
| Q1 contains every row | Everything executes through the reference scheduler. | Q1 connects the dispatcher to shared machine semantics. A bug shared by both sides passes TRACE, so Q20, Q21 and semantic contracts remain independent evidence. | Mutate a shared machine handler so concrete and reference agree but the client oracle fails. |
| Q5 needs poll as a generator | Per-edge correctness cannot establish dedup, reasons or cursor completeness. | Agreed as a practical decomposition. “If and only if” is too strong: a proved generic merge theorem could discharge poll without an independent primitive axiom. | A real composition theorem covering the whole consumer contract. |
| Q7 follows from the action law | Splitting a word does not change its fold. | Correct only for the same induced word. Different harvest boundaries can change the word and outcomes. | The listener/reclamation scenario and a precise boundary-correspondence premise. |
| Q22 follows once allocator is a component | This repairs the known hidden sharing. | Necessary, not sufficient. Scheduler, operation correlation, initialization and all remaining shared effects must also be represented. Component S certificates generally give containment, not equality of behavior sets. | Experiment E's common-timeline comparison, with each shared boundary accounted for. |
| Safety observations omit article numbers | This permits peer convergence despite local numbering. | Correct for that semantic view, incompatible with unrestricted raw NNTP byte equality. Observation contracts must differ by claim. | Two POSTs to one group, compared both as replies and as validated facts. |
| Independent owners give completion diamonds | Different principal FIFOs avoid enqueue conflicts. | Owner separation is a candidate condition. Posting still writes one FIFO; harvesting and later allocation may retain order effects. | Specify the boundary of the proposed diamond and check both routes plus a distinguishing suffix. |

The count in §2.4 should become a count of **schemata**, followed by a separate count of tested instances.

A defensible dispatch partition is:

```text
22 continuation-state cases
 9 routed observation cases
 1 unrouted-observation case
 2 clock/signal cases
 4 service cases
 1 empty-principal visit
--------------------------------
39 dispatch cases.
```

This treats harvesting as part of the observation cases. Counting “harvest” again gives 40. Idle/stop behavior and adapter-boundary operations still require their own coverage classification. Some continuation cases share an implementation, while a single case may contain several semantically distinct branches. Thus 39 is neither a theorem count nor a complete primitive-action count.

Likewise, `12·13/2 = 78` counts unordered event-kind pairs allowing equal kinds. It does not count independent pairs. Independence relates distinct **occurrences**; two receive completions may be dependent or independent depending on owners, principals, resource state and observation scope.

The estimate `78 + 26·12 = 390` omits fault/fault pairs. At the same coarse kind-pair level, including those gives:

```text
38·39/2 = 741 candidate pairs.
```

That is a pessimistic candidate-pair count for **12 completion kinds plus 26 fault classes only**. It excludes posting/execution boundaries, clock and signal interactions, concrete parameters, dynamic residual checks and reachability. Many pairs are illegal or dependent and must be classified, not silently counted as passing generators. It is not a runtime estimate.

The useful workload report is:

```text
G1 instances = Σreachable states s
                Σrelation contracts R
                  enabled covered transition instances at s

G2 instances = Σreachable states s
                declared-independent enabled occurrence pairs at s.
```

Add separate counts for entry checks, nonvacuous declaration witnesses, dynamic triple checks and declared route equations. Measure reachable states, executed instances, rejected independence candidates and time. Do not promote the layer D estimate of about 620, or its pessimistic 1,000, from provisional schema sizing into an exhaustive coverage claim before those declarations exist.

This leaves a useful foundation: a common certificate mechanism for E, S, B and Q, reusable composition proofs, and an explicit place for T reductions and L equations. X remains a named environment boundary. It is broader than version transport without pretending that every correctness obligation is equality.

## Astra: what the generator mode checks that sampling does not

For a declared finite input domain and horizon, generator mode visits each reachable state and checks every applicable G1 instance and both routes of each claimed G2 instance, including enabledness, outputs and the named endpoint relation. It reports unreachable or unsatisfied declaration conditions separately. It checks dynamic triples only where the declaration claims cube consistency. Positive and deliberately false declarations provide controls.

Ten thousand seeded runs do not ensure that the same reachable state is exercised in both orders. Action-kind and fault-kind masks do not measure that coverage. Exhaustive bounded checks can refute these contracts; passing them does not prove the unbounded laws. TRACE also shares machine semantics with the concrete executor, so the independent ownership and client oracles remain necessary.

A concrete false diamond follows from layer A at `957b018c1`. Use one occupied echo row, generation below retirement, no remaining borrow, and an outstanding Close for that row. A listener has an outstanding Accept. Both belong to principal 0; their runnable FIFO is empty.

```text
AcceptResult; CloseResult; harvest both
  ⇒ principal FIFO [listener, echo]

CloseResult; AcceptResult; harvest both
  ⇒ principal FIFO [echo, listener].
```

`fn2-post-result` preserves posting order. `fn2-ref-transition` harvests that order, and `fn2-ref-enqueue` appends each wake. On successive principal-0 calendar visits:

- Listener first: `fn2-listener-admit` finds no free echo row and enters `:closing`; the old echo then releases its row.
- Echo first: `fn2-connection-release` frees the row; the listener then admits the new capability.

The first route closes the new connection; the second can echo its bytes. This is a code-traced witness, not an executed test result. It refutes “different machines imply independence” with two completions and two relevant visits. The scribe supplies another shared-resource boundary: it reserves from the pool and parks on exhaustion, while listener admission closes on exhaustion. Generator mode should discover these distinctions before using any of them to prune schedules.