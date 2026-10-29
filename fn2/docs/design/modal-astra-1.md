## 3. The existing logics whose metatheory we would otherwise reinvent

The useful inheritance is a collection of small calculi and proof routes. It is not a completeness theorem for their combination. Each imported result retains its hypotheses, and each translation into fn2 needs its own preservation argument.

The table distinguishes an available mathematical result from a checker fn2 has actually implemented. The law numbers identify the corresponding fn2 obligations, not claims that the papers already prove fn2 correct.

| Logic or theory | What is available | Adoption cost and corresponding laws | Verdict |
|---|---|---|---|
| ABLP, *A Calculus for Access Control in Distributed Systems*, **TOPLAS 1993** | A calculus of principals, `says`, delegation and `speaks-for`; soundness and completeness results for specified fragments | Translate scoped authority and justify credential introduction. Signatures, expiry and revocation remain separate. A2–A4 | **Adopt scoped speaks-for**, not the entire principal algebra |
| Garg–Pfenning constructive authorization; PCFS | Constructive proof rules, cut elimination and authorization non-interference results; PCFS has a correctness theorem for conditional proof verification | Define the accepted proof grammar, trusted premises, state conditions and revocation cuts. A1–A4, C2 | **Adopt bounded proof checking**; use the metatheory as a proof route |
| DKAL | An executable authorization language over a substrate; polynomial basic-query evaluation when nesting depth and rule-variable count are bounded | Its substrate and communication semantics exceed a grant-chain checker. A2–A4 | **Footnote** unless distributed policy evaluation becomes an implemented requirement |
| NAL/Nexus | Principal-indexed reasoning, restricted delegation and mechanically checkable authorization derivations | A richer policy language and explicit treatment of changing facts and guards. A2, A4, C2 | **Use as proof route** for scoped delegation and admission guards |
| SecPAL; Li–Mitchell Datalog with constraints | Sound, complete, terminating evaluation for SecPAL’s safe fragment; tractable constraint families for structured resources | Safety restrictions, constrained rule shapes and a specified constraint solver. A2–A4, A9 | **Adopt a decidable caveat fragment** |
| Dynamic logic, Hoare logic and Kleene algebra with tests | Relational program semantics, compositional pre/postcondition rules; KAT equational reasoning is PSPACE-complete | Bind program atoms to actual transitions, including refusal outputs. C1–C5, L3 | **Adopt the pre/postcondition fragment**; use KAT offline |
| Separation logic | Local reasoning through separating conjunction and the frame rule | Establish ownership composition, footprints and the frame side conditions. C3; EXEC §4’s frame and ownership obligations | **Use as proof route** for OWN and concrete refinement |
| Governatori–Rotolo contrary-to-duty logic | An ordered reparation connective and a Gentzen calculus | Its full metatheory is not supplied by the cited paper; deadline, violation and discharge semantics still need definitions. O1, O2, O5 | **Adopt finite declared continuation chains** |
| Artemov justification logic | Explicit evidence terms and operations on evidence | Distinguish derivation, authenticated assertion and consumable authority. A5, A6, O2, O3 | **Adopt typed evidence constructors**, not a general justification prover |
| Halpern–Moses common knowledge | A semantics of distributed knowledge and impossibility results under stated communication assumptions | Local evidence does not establish common knowledge. A6, A8 | **Footnote**; cut a separate knowledge modality |
| Past-time LTL; Halpern–Shoham interval logic | Efficient monitors for propositional past-time formulas; interval relations with sharply varying decidability | A trace monitor checks one execution; cuts need causal semantics; clock uncertainty is not interval-modal satisfiability. P1, P5–P7, P9 | **Adopt past-time monitors and endpoint comparisons**; cut general HS |
| Blackburn hybrid logic | Named states, satisfaction operators and a standard translation into first-order logic | Specify exactly what a name denotes; rigidity inside a model does not establish persistence between models. P2–P4 | **Adopt typed `@`**, without binders or a general satisfiability service |
| Bounded linear logic; graded effects and coeffects | Resource-sensitive typing; compositional grades and sound models of effect/coeffect interaction | Choose concrete units, grade operations and cost semantics. Polynomial time is insufficient for EXEC’s per-run bound. E5, O9 | **Adopt concrete cost grades**; use the larger theories as proof routes |
| Contextual modal type theory; Hazel lineage | Explicit contexts, contextual substitution and typed hole closures | Extract complete supports, including negative dependencies, and check substitutions between contexts. P8, R7 | **Adopt contextual read certificates** |
| HoTT univalence | Transport along equivalences for appropriately structured types | Establish the actual equivalence and its observed structure. R4, R5 | **Use the proof route already scoped in TRANSPORT** |
| Goguen–Burstall institutions, 1992 | Sentence translation, model reducts and the satisfaction condition; theory composition under stated hypotheses | Fix a specification language and prove translations admissible. R4, R5 | **Adopt the theory-morphism discipline** |
| Specware/Kestrel | Mechanical specification colimits, morphism obligations and refinement constructions | Supply presentations, mappings and proofs; general consistency is not decided. R4, R5, C2, C3 | **Adopt the construction pattern**; evaluate the tool on the room example |
| ACL2 `encapsulate`, functional instantiation, `defattach`; APT | Witnessed abstract interfaces, theorem reuse under checked substitutions, executable attachments and proof-generating transformations | Encode sorts by predicates, discharge constraints and guards, and connect the concrete served function. R4, R5, S1′; EXEC §4 | **Adopt as the implementation proof route** |

**ABLP.** Interpret `K ⇒_s L` as the family of implications `(K says φ) → (L says φ)` for `φ ∈ s`. Composition checks directly: if `φ ∈ s ∧ t`, apply the first delegation and then the second, obtaining A2 at scope `s ∧ t`. The paper separates authentication, “who made a statement,” from authorization, “who is trusted?” A signed A3 statement still needs a hand-off or policy rule that authorizes the delegation; a signature alone does not remove the surrounding `I says`. The journal citation is TOPLAS 15(4), 1993, not JACM. [ABLP](</Users/ember/paperbin/abadi-burrows-lampson-plotkin1993-calculus-access-control-distributed-systems.pdf>)

**Constructive authorization and PCFS.** Translate fn2’s evidence derivation into a judgment `Γ_(r,p,c) ⊢ K says permitted(α)`, with revision, position and revocation cut fixed in the context. Rule checking establishes authorization relative to that context; admission separately checks that the context is the one required now. Garg–Pfenning supply a “cut elimination theorem and the subformula property.” PCFS’s Theorem V.1 connects checked proofs and residual time/state conditions to valid authorization. It does not make revocation automatic: the paper states, “The current implementation of PCFS does not support revocation.” fn2 must supply A4’s cut discipline and a separately charged proof checker. [Constructive authorization](</Users/ember/paperbin/garg-pfenning2006-non-interference-constructive-authorization-logic.pdf>), [PCFS](</Users/ember/paperbin/garg-pfenning2010-proof-carrying-file-system.pdf>)

**DKAL.** The nearest translation is `p knows t ↦ p holds an admitted fact t`, with fn2’s typed records supplying the substrate. This is not `t is true`, nor does it identify DKAL’s communication rules with fn2 receipts. The 2008 paper bounds its basic-query algorithm by a polynomial in `ℓ^(δ+w)`, where `δ` is assertion nesting and `w` the maximum variable count: “when δ and w are bounded, the runtime is polynomial.” That is a conditional algorithmic result, not a constant-cost admission check. No additional fn2 mechanism follows from adopting the rest of DKAL here. [DKAL](</Users/ember/paperbin/gurevich-neeman2008-dkal-distributed-knowledge-authorization-language.pdf>)

**NAL/Nexus.** Map a guard’s authorization goal to C2’s `auth(α)` and its credentials to the admitted assertions at `c(α)`. Restricted speaks-for maps to A2; checking one restricted delegation verifies that authority outside its predicate is not imported. NAL explicitly allows the guard to “check a NAL derivation rather than generating its own.” Its warning about changing facts matters equally: a proof about a lock, membership or revocation state needs an admitted current-state premise. NAL is a useful proof route, but does not require a second policy engine alongside the chosen constructive fragment. [NAL](</Users/ember/paperbin/schneider-walsh-sirer2011-nexus-authorization-logic-nal.pdf>)

**SecPAL and constraint Datalog.** Translate a grant edge into a delegation clause and each caveat into a predicate on the requested action and pinned context. Construct attenuation as `scope_child(x) = scope_parent(x) ∧ caveat(x)`; inclusion then follows by conjunction elimination, without asking a solver to discover arbitrary implication. SecPAL gives “polynomial data complexity” for safe policies with fixed rules and queries and polynomial ground-constraint evaluation. Li–Mitchell’s stronger program-size result fixes a bound on rule size and uses specified tractable domains, including hierarchical and range domains. Adopt those finite, typed caveats first; adding arbitrary integer arithmetic invalidates the inherited bound. [SecPAL §§7–8](</Users/ember/paperbin/becker-fournet-gordon2010-secpal-decentralized-authorization-language.pdf>), [Li–Mitchell §§2–3](</Users/ember/paperbin/li-mitchell2003-datalog-constraints-trust-management.pdf>)

**Dynamic logic, Hoare logic and KAT.** Interpret a command atom as its reference transition relation and translate `{P} α {Q}` to `P → [α]Q`; in KAT the corresponding partial-correctness assertion is `P · α · ¬Q = 0`. Sequential composition checks by relational composition. Kozen reports that the equational theory is “actually PSPACE-complete.” This licenses offline reasoning about the command skeleton, not unbounded reasoning in Decide. C2’s first-failure behavior requires explicit refusal-producing branches: commuting Boolean tests may preserve acceptance while changing the refusal word. Termination and per-run cost remain separate obligations. [Kozen §4.3](</Users/ember/paperbin/kozen1997-kleene-algebra-with-tests.pdf>)

**Separation logic.** Interpret `P * Q` through UC §8’s partial ownership composition, not through a partition of the entire semantic state. The frame check is concrete: a transition owning `P` must preserve a compatible fragment `R`, giving `{P * R} α {Q * R}` under the variable and ownership side conditions. Reynolds describes the frame rule as enabling “local reasoning” about the heap. fn2’s outstanding I/O loans belong in the ownership interpretation; a generation number does not make two duplicated current tokens disjoint. This proof route serves OWN and EXEC §4 without adding a user-facing modality. [Reynolds](</Users/ember/paperbin/reynolds2002-separation-logic-shared-mutable-data.pdf>)

**Contrary-to-duty.** Compile the restricted chain `o ▷ o'` into an obligation transition: a committed violation of `o` records that violation and creates `o'` atomically. Check O5 by evaluating that transition, including retry and crash recovery; do not claim an interpretation of the entire Gentzen calculus. Governatori–Rotolo describe how “the violation of B1 can be repaired by B2,” but list proving soundness and completeness as future work. Expiry is a violation only when the obligation declaration says so. A successful discharge creating the next custody leg is a different continuation. The Prakken–Sergot comparison remains a gap in the gathered local packet; no result from it is imported here. [Governatori–Rotolo §§2, 6](</Users/ember/paperbin/governatori-rotolo2006-logic-of-violations-gentzen-contrary-to-duty.pdf>)

**Justification logic.** Map evidence constructors into checked judgments: signature verification yields an authenticated assertion; `receipt(t_sig,t_incl)` yields inclusion under the named checkpoint; `pair(t₁,t₂)` checks joint evidence; a tagged injection checks an alternative. Artemov’s application principle is `s:(F → G) → (t:F → (s·t):G)`. Thus A5’s dot notation requires an actual checked implication from the checkpoint statement and inclusion proof to the receipt claim. There is no rule from `t : K says φ` to `φ`. Nor does the classical evidence operation `+` make a custody token duplicable. [Artemov §§2–3](</Users/ember/paperbin/artemov2008-logic-of-justification.pdf>)

**Common knowledge.** The proposed translation `witnessed_k(φ) ↦ common-knowledge(φ)` fails. Deliver a valid quorum certificate to one node while delaying all messages to another: the first holds the certificate, but the second need not know that it exists. Halpern–Moses distinguish this from knowledge strong enough for “absolutely simultaneous coordination,” and explain assumptions under which common knowledge is unattainable or useful in an abstraction. fn2 needs the local rule A8 and a versioned quorum policy, not an unconditional assertion that common knowledge is impossible in every system. [Halpern–Moses §§8–10](</Users/ember/paperbin/halpern-moses1990-knowledge-common-knowledge-distributed-environment.pdf>)

**Temporal and interval logic.** Map one domain’s committed prefixes to trace indices. For `z = φ S ψ`, the monitor recurrence is `z_j = ψ_j ∨ (φ_j ∧ z_(j−1))`, with the initial case declared. This gives linear work in trace length for a fixed propositional formula, or `O(N·|φ|)` with formula size explicit; atomic query costs are additional. Havelund–Roșu describe memory “constant, also depending on the size of the formula.” Cuts are causally closed configurations, not arbitrary interleavings. P9 needs only `t⁻ ≥ δ` and `t⁺ ≥ δ`; it imports no HS satisfiability procedure. The gathered `bresolin2011...` file actually contains Marcinkowski–Michaliszyn’s *The Last Paper on the Halpern–Shoham Interval Temporal Logic*, including undecidability over discrete structures. [Past-time monitoring](https://fsl.cs.illinois.edu/publications/havelund-rosu-2002-tacas.pdf), [gathered interval paper](</Users/ember/paperbin/bresolin2011-last-paper-halpern-shoham-interval-logic.pdf>)

**Hybrid logic.** Translate `@a φ` to evaluation of `φ` at the semantic snapshot named by `a`; Blackburn’s standard translation replaces the current-state variable by the variable denoting `a`. His defining condition is that nominals are “true at exactly one point in any model.” This checks P3 inside a fixed interpretation. To obtain fn2’s persistence claim, additionally prove that append, recovery and migration preserve the named snapshot and its interpretation. A domain position does not name the whole multi-domain machine state, and a node’s inability to retrieve a snapshot is not falsity at that snapshot. [Blackburn §3](https://carlosareces.github.io/content/papers/files/areces00logic.pdf)

**Grades, effects and coeffects.** Map a bounded run to a cost grade `q`, for example a vector of bytes visited, structural steps and action descriptors; sequential upper bounds compose by addition. Map required reservations to preconditions on the resource context, and check that actual consumption stays within the declared grade. Gaboardi et al. distinguish effects that change a context from coeffects that “make demands on the context.” Bounded linear logic supplies a route to polynomial resource guarantees, but a polynomial computation can still monopolize fn2’s executor. Stock conservation, peak occupancy, accumulated work and scheduling share require distinct interpretations; none follows merely from writing quantities as obligation fields. [Gaboardi et al.](</Users/ember/paperbin/gaboardi-katsumata-orchard2016-combining-effects-coeffects-grading.pdf>), [bounded linear logic](https://repository.upenn.edu/bitstreams/8d684b34-672f-48f7-875c-f11cc8d7a0ad/download)

**Contextual modal types.** Interpret `@c [Ψ] v` as a result accompanied by a derivation whose free assumptions are the pinned support judgments in `Ψ`. Reuse at `c'` supplies a checked substitution from those assumptions into the new context. Identical supports provide the identity substitution; a proved equivalence can provide another. This is the substitution mechanism of Nanevski–Pfenning–Pientka, specialized to read dependencies. Hazel uses contextual modal types as “a logical basis for hole closures,” not as a database invalidation theorem. fn2 must extract supports itself, including the version of a searched fibre when the result depended on finding nothing. [CMTT §2](</Users/ember/paperbin/nanevski2008-contextual-modal-type-theory.pdf>), [Hazelnut Live](</Users/ember/paperbin/omar2019-hazelnut-live-live-functional-programming-typed-holes.pdf>)

**Univalence.** The applicable mapping and its limits are already in TRANSPORT §§1.1 and 3.1: relate admissible representations through `init`, `step` and declared observations, then transport statements expressed through that interface. The useful check is the commuting step/observation diagram, not the presence of HoTT vocabulary. No univalence axiom enters ACL2, and observational equivalence does not become literal equality of representations. [TRANSPORT](</Users/ember/dev/fn/build/coordinator/fn2/TRANSPORT.md>)

**Institutions.** Write `m:T→T'`, sentence translation `σ_m`, and model reduct `m*`. The law is `M' ⊨ σ_m φ ⇔ m*M' ⊨ φ`. Goguen–Burstall summarize it as “Truth is invariant under change of notation.” Section 4 checks it on the room port. R4 additionally needs a certificate relating the actual old model to the reduct of the actual new model; the institutional law alone does not certify a migration. [Goguen–Burstall §§1–2](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf)

**Specware and especs.** Srinivas–Jüllig require that a specification morphism translate “axioms … to theorems.” Smith’s colimit construction identifies mapped symbols and collects translated axioms. The especs line adds behavior: guarded transitions and simulation must accompany structural mappings. The gathered `pavlovic-smith2001...` file is a differently titled three-author manuscript, including Matthias Anlauff; the 2001 reference is *Composition and Refinement of Behavioral Specifications*. The later *Guarded Transitions* paper makes the relevant distinction explicit. Section 4 uses structural colimits for wiring and simulation for execution; it does not equate the two. [Srinivas–Jüllig](https://www.kestrel.edu/research/specware/papers/specware/specware.pdf), [Smith](</Users/ember/paperbin/smith2006-composition-by-colimit-formal-software-development.pdf>), [guarded transitions](https://www.kestrel.edu/people/pavlovic/papers/GTES.pdf)

**ACL2 and APT.** Map an abstract operation to a constrained function, its laws to exported theorems, and a realization to a functional substitution whose constraints are proved. `encapsulate` supplies local witnesses; functional instantiation transports theorems to the realization. `defattach` supplies execution, not a new logical equality: Kaufmann–Moore explicitly say “attachments are not invoked during proofs.” APT’s `isodata` and `propagate-iso` generate transformed functions and relationship proofs after their applicability conditions are discharged. Section 4.6 gives the room instance. [ACL2 encapsulate](https://acl2.org/doc/index-seo.php?xkey=ACL2____ENCAPSULATE), [defattach](</Users/ember/paperbin/kaufmann-moore2011-how-can-i-do-that-acl2-defattach.pdf>), [APT](</Users/ember/paperbin/coglio2020-acl2-apt-isomorphic-data-type-transformations.pdf>)

## 4. Worlds as theories

A room’s revision presents a theory. A running room is a model of that theory, observed at `w = (d,p,r,i,n)`. Keeping those distinct prevents a schema mapping from being mistaken for movement of a live world.

Use presentations `T = (Σ, Ax)` over B. A theory morphism `m:T→T'` maps sorts and operations and makes every translated source axiom a target theorem. Its sentence translation is the draft’s `σ_m`; its model reduct goes the other way.

These constructions extend B’s language without changing its old operations. The conservative expansion disables optional installations, has one revision and incarnation, no migration or wiring events, and no foreign credentials. Fresh identifier sorts may contain an inactive sentinel; active rows are empty. Existing B predicates and operations retain their interpretations. Selecting a particular room application then imposes that application’s contract. It does not establish that every B model was already a helm room. Replacing an old authorization or command policy remains a separately flagged decision.

### 4.1 A helm room as a presentation

Let `T_room` instantiate B with one room stream in domain `d`. It uses B’s positions, events, content Names, folds, relations, frontiers and obligations. Additional sorts are application identifiers, not new kernel mechanisms:

```text
Room, Seat, Dispatch, Wait
MessageID, ArticleNo                  distinct from Name and Pos

member       : State × Seat × Room → Bool
entry        : State × Room × Pos → Option Event
cursor       : State × Seat × Room → Pos
coverage     : State × FoldId → Pos
wait         : State × Wait → Option (Seat, Room, Pos)
dispatch     : State × Dispatch → Option (Seat, Name, ObligationId)
status       : State × ObligationId → Status
check        : State × Evidence × EvidenceFormula → Bool

roomDecide   : State × RoomCommand → Outcome × Event*
roomFold     : State × Event* → State
```

`Status` has disjoint constructors `outstanding`, `discharged(t)`, `cancelled(t)`, `waived(t)` and `expired`. Which terminal constructors are legal is declared per obligation kind. `roomDecide` is the application instance of Decide, not a second admission authority.

The presentation includes these axioms:

1. **History and folding.**

   ```text
   roomFold(s, ε) = s
   roomFold(roomFold(s, x), y) = roomFold(s, xy)
   e@p → G e@p
   ```

   Covered observations agree with this fold. Missing historical state produces a typed unavailable answer, not a reconstructed guess. These are L2, P1 and S1.

2. **Seats and waits.** Membership is a Span. Cursors advance only through admitted cursor operations and never pass unread required entries. A wait names a threshold and query context. A wake changes eligibility to run; delivery still checks the threshold and query at the installed state. These instantiate P5 and P6, including the whole-consumer condition from UC.

3. **Owed replies.** Creating dispatch `j` creates exactly one obligation `o_j` whose evidence formula is:

   ```text
   ev(o_j) = reply-for(j) ⊕ authorized-cancellation(j)
   ```

   Only an admitted command can change its status. A transition from `outstanding` to `discharged(t)` requires `check(s,t,ev(o_j))` and authorized discharge. A terminal status cannot be replaced by another terminal status. This is O1 and O2, with evidence tied to the dispatch identity.

4. **Retries and publication.** Retrying the same dispatch operation returns its original outcome; contradictory reuse is refused `op-reused`. A durable reply is published only after the commit machine establishes its durable outcome. These are S1″ and L3.

A nontrivial model has one seat, one membership edge, one parked wait and one outstanding dispatch. Appending an authorized reply advances the room frontier and discharges that dispatch. The wait becomes runnable, then rechecks before delivering. A second discharge attempt cannot change the recorded first outcome. This model exercises the obligation and wake axioms; an empty room alone would not.

### 4.2 A port is a theory morphism, with a reduct that forgets

Take a declared read fragment `T_news` containing groups, article placements, Message-IDs, headers, bodies and the corresponding read results. Define:

```text
j : T_news → T_room+news

Group                  ↦ exported Room
ArticlePlacement       ↦ exported article placement in the room
MessageID              ↦ exact retained Message-ID octets
ArticleNo              ↦ per-group article number
article(g,a)           ↦ lookup exported placement(room(g), a)
body(g,a)              ↦ payload of that placement, or its declared gap
```

`T_room+news` is the room presentation plus the publication mapping. Article numbers are not journal positions; Message-IDs are not content Names. The mapping introduces no equivalence between those sorts.

The reduct `j*M_room` is the NNTP view. For every sentence `φ` in the declared news fragment:

```text
M_room ⊨ σ_j φ   ⇔   j*M_room ⊨ φ.
```

A concrete obligation is article-number uniqueness. The news axiom

```text
placement(g,a,e₁) ∧ placement(g,a,e₂) → e₁ = e₂
```

translates to uniqueness of the room’s exported placement at `(room(g),a)`. It follows from that mapping’s admitted allocation rule, not from content hashing. WIRE must additionally check that rendered replies denote this reduct.

The port’s loss is the identification relation

```text
M ≈_j N   iff   j*M ≅ j*N
```

over models with the same public identity interpretation. Two room states can have identical articles but different seat memberships, parked waits or outstanding dispatches. The reduct forgets those differences. This is a kernel pair in the model-view sense, not an inverse translation and not a numerical amount of loss.

For a port with commands, strengthen the comparison to the declared future observations under translated command traces. A current snapshot’s equality is insufficient if a hidden difference changes a later visible refusal. Adding `POST`, for example, needs a command simulation and an outcome mapping as well as the read reduct. Parsing, framing and resource bounds remain separate port obligations.

### 4.3 Two worlds composed along a shared stream

Let `T_S` present a boundary stream with its event schema, identity and owner:

```text
stream : Stream
owner  : Stream → Domain
```

The total function expresses exactly one owner domain. Let the worlds expose compatible boundary interpretations:

```text
             f
      T_S ───────→ T_A
       │             │
     g │             │ i_A
       ↓             ↓
      T_B ───────→ T_A ⊔_(T_S) T_B
             i_B
```

The pushout identifies the interface symbols through `f` and `g` and includes both worlds’ translated axioms. A compatible pair of world models must agree on the shared stream’s schema, history interpretation and owner.

The ownership counterexample is small. Give the common identity theory two distinct domain constants:

```text
a ≠ b.
```

Let `T_A` assert `owner(stream)=a` and `T_B` assert `owner(stream)=b`. Each presentation has a model separately. Their pushout entails `a=b`, contradicting the shared identity axiom. Without `a≠b`, the presentation might merely identify the domains, so the distinction must be explicit.

For fn2’s restricted wiring grammar, this yields the important admission check: unifying stream endpoints must not unify conflicting owner declarations. Refuse `stream-owner-conflict` and identify both declarations. The receiving world consumes the owner’s stream; it does not acquire append authority by being connected to it.

This check does not decide consistency of arbitrary combined theories. Other shared axioms can conflict. The restricted grammar earns its stronger claim only when its remaining combinations have a construction that produces a joint model. Neither the colimit nor a successful ownership check creates cross-domain atomic commitment; C3 still applies.

### 4.4 Adding threads in v4

Let `T₃` be the room theory. Let `T₄` retain its sorts and operations and add thread annotations, a new concrete state representation and their observations:

```text
State₄       = State₃ × ThreadAnnotations
π(s, a)      = s
convert(s)   = (s, empty)
thread(e)    = unknown, unless an admitted annotation supplies it

m : T₃ →_ext T₄
```

The signature map `m` is inclusion on the old interface. Old observations lift through `π`:

```text
obs₄_old(s₄) = obs₃(π(s₄)).
```

Give the new event alphabet an old interpretation `h:E₄→E₃*`: an old event maps to its singleton word; a pure thread annotation maps to `ε`. The preservation obligation is:

```text
π(step₄(s₄,e₄)) = Fold₃(π(s₄), h(e₄)).
```

Together with initialization, this establishes agreement of old observations after every admitted suffix. It is stronger than checking the converted state once.

Every `T₃` model expands: retain its old interpretations, add finite annotation maps, choose the empty initial annotation map and interpret unannotated entries as `unknown`. Forgetting the added structure recovers the old model. Thus this `ext` migration is a conservative extension in the discipline’s model-expansion sense.

The qualifier matters. Requiring every old post to have a distinct earlier thread parent rejects an old model containing only its first post. That version of v4 is not conservative. Likewise, promising complete historical threads requires a justified backfill or a coverage gap; `convert(s)=(s,empty)` does not establish it.

The migration record names the converter, event interpretation, preserved observations and coverage at the converted cut. R4 is supported by the equations above. R1 records when the new interpretation becomes active. Neither changes the producer revision of an old outcome.

### 4.5 Transport is a theory isomorphism plus a model transfer and a fence

For a pure move between nodes, the theory morphism is the identity:

```text
m : T_r ≅ T_r.
```

For a genuine isomorphic revision change, provide `m:T_r→T_r'` and an inverse with the declared equations. If only observational equivalence has been proved, call it that; a simulation between two representations need not be an isomorphism of their full theories.

The theory-level evidence establishes translation of laws and observations. The model-level operation must still:

- transfer a state related to the source state by the certified relation;
- preserve or explicitly map positions, cuts, identities, outstanding obligations and retry outcomes;
- establish the successor incarnation and fence the source incarnation;
- install the destination through its persistence protocol before publishing success.

For a historical observation in the preserved interface, the required check is:

```text
M,w ⊨ @p φ
    ⇔
M',w' ⊨ @ρ(p) σ_m φ,
```

where `ρ` is the recorded position map. If domain positions are preserved, `ρ` is the identity.

A node address, transferred bytes, successor incarnation and fence receipt are model or execution data. They are not consequences of an isomorphism. An identity migration can still have a broken fence. R9 therefore combines two independently checkable obligations: semantic preservation and authoritative succession. The crash scenario must interrupt the handoff before and after each fence, persistence and installation boundary.

### 4.6 What Specware and ACL2 would actually do

Specware can construct the room and stream presentations, calculate the pushout’s symbol identifications, collect its axioms and expose morphism proof obligations. For `j`, an obligation is the translated article-number uniqueness law. For `m`, it is preservation of the old room interface. Its refinement machinery can organize the corresponding implementation development. The 4.2 manual names “colimits, extraction of proof obligations” and external theorem proving among its operations. It does not provide a general procedure deciding whether the resulting colimit has a model. [Specware 4.2, §3.1](</Users/ember/paperbin/kestrel2004-specware-4.2-user-manual.pdf>)

ACL2 can realize the same obligations without implementing a general institution library:

```text
abstract interface:
    room-init, room-step, room-obs, room-inv

exported constraints:
    initialization establishes room-inv
    room-step preserves room-inv
    observations satisfy the named room contracts

realization:
    substitute concrete init, step, obs and invariant functions
    prove the substituted constraints
```

A nontrivial `encapsulate` admits these constraints using local witness definitions. That establishes their satisfiability relative to ACL2’s admitted theory. It does not establish that every B model expands, nor that the witness implements the intended room. Conservativity needs the expansion argument; usefulness needs the nontrivial room instance and its observations.

Functional instantiation carries an abstract room theorem to a concrete implementation once the substituted constraints are proved. `defattach` can execute an admitted realization of constrained functions, but does not make the attachment definition available as a logical axiom. APT can automate applicable representation transformations. The final refinement still connects the host-called `fn2-turn` to the reference transitions, actions, statuses, bounds and crash cuts of EXEC §4.

WR’s additions therefore merge as follows:

- **Revision** names a presentation and its implementation artifacts.
- **Equiv** is a certified invertible or observationally equivalent mapping, with the distinction recorded.
- **Port** is a view interpretation plus any required command simulation.
- **Wire** is a diagram of boundary interpretations and its composed presentation.
- **Transport** uses those mappings inside an ordinary fenced Decide and persistence protocol.
- **Receipt** remains evidence about a particular model occurrence. It may attest an installation or transfer, but is not a theory morphism.

The first four share one specification-and-mapping mechanism. Transport composes that mechanism with existing execution machinery. Receipt belongs with M3’s typed evidence. Forcing all six into one kind would erase exactly the distinction the checker needs.

## Astra: proposals and two-position disagreements

**1. Keep the six labels, but call them six judgment families.** The draft’s position is that named frame classes such as S4 and S5 expose reusable laws. That is useful when the operator and frame really match. My position is that the table currently mixes satisfaction operators, temporal operators, translated languages, evidence judgments and resource predicates. `@^r` is not an S5 box merely because equivalences form a groupoid; the groupoid first gives coherent translations between languages. Keep M1–M6 for navigation, but make their typed judgments and checked laws normative. The deciding proof is an explicit semantics validating each advertised modal axiom for the actual operator, not for a nearby reachability relation.

**2. Name snapshots without identifying entire fork worlds.** The draft identifies parent and child worlds throughout their common prefix so that positions are nominals. My position is that shared history should identify event occurrences and historical snapshots, while parent and child retain distinct current authority and obligation dispositions. Otherwise a formula about the current owner or held effects can distinguish worlds the frame declares identical. Use a canonical historical reference behind `@p`, with domain and interpretation supplied by its type. The deciding scenario forks with different obligation dispositions: past event observations must agree while present authority differs. P3 then requires stability of historical interpretation across model extension, not only hybrid rigidity inside one model.

**3. Separate a threshold read from an existential property of the past.** The draft identifies `at-least(p)` with `⟨≥p⟩φ` and says threshold reads become permanently true. My position is that only the coverage predicate is necessarily monotone. A balance may exceed ten at one installed position and fall below ten later. A served read should return `(q,r,v)` with `q≥p`, adequate coverage and `v=obs_(f@r)(q)`. It should not search for any convenient past `q` satisfying the caller’s proposition. The deciding scenario reads after a debit while retaining an older qualifying snapshot. Also replace P8’s reuse “iff” by a sufficient identity-support rule, with other reuse allowed through checked contextual substitution.

**4. Distinguish authenticated speech from derivable affirmation.** The draft reads `K says φ` as an assertion and also gives it the lax unit `φ→K says φ`. My position is to use `says` for the chosen authorization calculus and distinguish signature leaves from derived evidence by constructor. Otherwise the unit appears to manufacture a signed utterance from a theorem. A3 also needs an explicit hand-off rule, not just a signed statement containing `speaks-for`. The deciding negative cases are an unsigned tautology presented as a checkpoint, an expired delegation, and a scope-widening child grant. All must fail the relevant evidence check even when some corresponding formula is derivable.

**5. Repair the operational formulas before assigning modal classes.** The draft uses `[tell(x,φ)]⊤ → □_Dφ` for L3. But `[α]⊤` is valid in ordinary dynamic logic, including when `α` refuses. My replacement is an output correspondence property:

```text
emitted(α, durable-assertion(x,φ)) → established-durable-evidence(φ).
```

L1 should constrain authoritative premises, not every input to Decide: a newly received command and a volatile capacity reservation need not already be durable facts. E8 should classify what recovery evidence establishes, rather than identify actual crash successors with the executor’s uncertainty. Keep pure Decide deterministic; let the commit protocol report `uncertain` when its evidence cannot establish either durable acceptance or definitive nonacceptance. The deciding scenario loses a barrier completion after storage may have persisted the batch, then retries after recovery.

**6. Preserve TRANSPORT’s corrected revision rules.** The modal draft’s position is that activations finish under their starting revision, rollback requires `≡`, and outstanding evidence need only remain expressible. The current TRANSPORT note supplies stronger engineering distinctions: a crossing Decide drains or revalidates before commit; rollback needs a valid backward migration for the current state and retained contracts; obligation compatibility preserves authorized discharge, fencing and retries. My position is to adopt those corrections in R3, R6 and R8. The deciding scenario combines an old activation, revision installation, a changed authorization rule, an outstanding obligation and a retry. A migration that changes `authorized-receipt` to `true` must fail even though the new formula is expressible.

**7. Linear obligations do not make every proof linear, and conservation does not prove service.** The draft merges evidence, obligations and Meter through a linear-resource reading. My position retains that merge for consumable authority and lifecycle transitions, while allowing immutable receipts to be reused unless a contract explicitly consumes them. Quantity claims need allocation identities so one receipt cannot fund two transfers. Separately, E5’s protected scheduling share follows from the calendar and eligibility rules, not O9’s conservation equation. The deciding pair of scenarios reuses one historical receipt legitimately for two observations, then attempts to spend one reservation twice; a third conserves every quantity while starving a principal. ACCOUNT and FAIR must distinguish them.

**8. One loss envelope can carry several different kinds of loss.** The draft merges crash loss, migration kernels, port loss and covariance into D4. My position keeps the common read field but gives it typed variants with distinct composition rules. A projection kernel identifies states; an unavailable historical interval identifies missing access; a covariance describes uncertainty under a particular estimator. None can stand in for another. The deciding example composes a port that omits seat membership with a sensor fold reporting covariance. The result must retain both meanings, not collapse them into one scalar or an untyped `κ`.

These changes also narrow §2.8’s claims. A conservative expansion must preserve **every old interpretation**, not merely exhibit a convenient root-grant deployment. A concrete local witness proves consistency, not conservativity. Each extension should therefore carry its expansion construction, while each policy replacement states the old observation it changes. The first such observations are refusal ordering, disclosure and obligation discharge.

## Astra: synthesis

UC already gives fn2 the algebra of histories, folds, identity, relations, frontiers and obligations. The modal reading adds a discipline for stating **where a claim holds, what supports it, and which translation preserves it**.

That discipline earns its place through a small set of concrete results:

- A read certificate records its revision, returned cut and pinned supports. CONSUMER can reject `supports-moved` or inadequate coverage without pretending the historical answer became false.
- An authorization derivation names its policy and revocation context. Decide checks the supplied derivation and current side conditions; its outcome preserves the context needed to explain the decision.
- A migration certificate names the old observations, event interpretation and state relation. HISTORY can refute present-answer equality that fails after a future event.
- A port declaration defines its reduct and forgotten distinctions. WIRE checks that bytes implement that view.
- A wiring declaration identifies shared streams and their owners. Composition can fail with `stream-owner-conflict` before execution.
- A transport combines semantic preservation with a separately checked fence and persistence handoff. An identity theory mapping does not hide an unsafe move.

The DSL need not expose a general modal language. Its existing declarations can carry these contracts: a command’s pre/postconditions, a projection’s contextual read result, a port’s interpretation, and a revision’s certified mapping. The same declarations should generate the relevant checker inputs and proof obligations.

The gain is fewer independent mechanisms and more precise failures. It is not permission to replace the running system with a catalogue of logics. No completeness theorem transfers without its translation; no signature establishes the truth of its payload; no colimit establishes consistency; no resource equation establishes progress; no observational equivalence supplies a fence. The note succeeds when these distinctions make a room usable, portable and accountable while leaving the one-node, one-revision B model intact.