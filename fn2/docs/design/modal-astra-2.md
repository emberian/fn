## Astra session 2: section 5 (co-written)

**Paste as replacement section 5.** The declaration fields below are proposed fields, not claims about implemented macros. They extend the existing generators. They do not introduce a second specification beside the executable declarations.

The useful construction is a **contract with a checked interpretation**. A machine supplies transitions, a port interprets observations and commands, and a representation certificate relates executions. They share declarations and proof infrastructure while retaining different obligations.

**5.1 Declarations and records**

`defmachine` presents the machine’s declared interface. For an execution machine, that interface includes observations, scheduler steps, continuations and actions. It cannot consist only of journal events: parsing, borrowed buffers and uncertain commits have meaningful states before an event becomes durable.

A schematic declaration is:

```lisp
(defmachine room-command
  :state room-command-fields
  :input command-observations
  :protocol room-command-protocol
  :init room-command-init
  :transitions room-command-transitions
  :invariant room-command-invariant
  :observes existing-room-contract
  :acquires command-admission-bundle
  :linear (reservation input-loan output-loan)
  :budget command-run-budget
  :dependencies :derived)
```

The generator emits the realization, its logical interface, and correspondence obligations. `:observes` references existing contract observations. It is not a separately maintained list of everything a machine might expose. Dependencies are derived through the access boundary, as TRANSPORT §3.1(v) requires.

The executable definitions can supply local witnesses for an `encapsulate`. This proves the declared constraints for those witnesses. It does not make a postcondition meaningful merely because the generator can prove it by unfolding. Consequential commands retain independently stated output and effect contracts, with positive examples and evaluated counterexamples.

A command declaration needs:

```text
protocol states
command kind and occasion
argument and request-binding schema
Decide interpretation
authorization policy
ordered semantic preconditions
retry identity and retained outcome contract
observable postconditions
refusal constructors and disclosure policy
derived read dependencies
```

Preconditions belong to the **command and occasion together**. `write` does not give POST, cancellation and cursor acknowledgement the same precondition. The occasion selects an applicable rule family; the command supplies its particular contract.

A port has two parts:

```lisp
(defport room-news
  :foreign T_news
  :target T_room+news
  :interpretation j
  :protocol news-read-protocol
  :observes news-read-contract
  :kernel room-news-identification
  :commands ()
  :proofs room-news-obligations)
```

Here:

```text
j : T_news → T_room+news
V = j* : Mod(T_room+news) → Mod(T_news)

κ_j(M,N)  iff  V(M) ≅ V(N)
```

The kernel identifies target models that the foreign view cannot distinguish. It is **not** the set of world sentences absent from the foreign language.

The required checks are:

1. Each translated foreign axiom follows from the target contract.
2. Rendered and parsed protocol observations implement the reduct.
3. Any claimed kernel agrees with the declared observations.
4. A command-bearing port additionally supplies a command interpretation, a state relation and an outcome simulation.

For example, adding POST requires:

```text
translate-command : NewsCommand → RoomCommand*
translate-outcome : RoomOutcome* → NewsOutcome
R_port            : NewsState × RoomState → Bool
```

The simulation preserves the protocol’s accepted results, named refusals, retry behavior and declared persistence outcomes. Internal steps may stutter. A finite-trace safety simulation alone does not establish that a required reply eventually arrives; that needs the execution and environment assumptions.

Composition uses reduct composition. For `k:T_outer→T_news`:

```text
(j ∘ k)* = k* ∘ j*

κ_(j∘k)(M,N)  iff  κ_k(j*M, j*N).
```

The kernels are not combined by union. They relate different model spaces. For a simple example, compose `(x,y) ↦ x` with `x ↦ x mod 2`. The composite identifies `(0,0)` and `(2,1)`, although the first map distinguishes them. The second map’s kernel must be pulled back through the first map.

An omitted-field list can remain a useful diagnostic, but its composition must follow the mappings and must not masquerade as the exact kernel.

Revision, Equiv, Port and Wire share a declaration mechanism with **typed variants**:

| Variant | Required content |
|---|---|
| Representation certificate | Admissible states, initial relation, step correspondence, preserved observations, proof references; converter separately |
| Port | Source and target presentations, interpretation, view identification relation, protocol contract; command simulation when applicable |
| Revision migration | Representation certificate, event correspondence, converter, coverage at the converted cut, retained-contract compatibility |
| Wiring | Boundary presentations, endpoint mappings, stream identities and owners; declared shared-state components |

A grade is a summary of the applicable evidence. Not every variant requires the same grade field. A stream inclusion in a wiring diagram is not naturally a lossy migration.

Transport uses these artifacts inside the fencing, transfer and persistence protocol. A receipt records evidence about an occurrence. Neither is another theory morphism.

**5.2 Authorization in Decide**

Use one small, explicitly specified authorization fragment. Its admission judgment is:

```text
Γ_(r,p,c) ⊢ K says permitted(α)
```

Here `K` is the policy authority, `α` includes the request binding, and `Γ` fixes the policy interpretation, local decision context and foreign evidence cuts.

The initial proof grammar needs authenticated credential leaves, named policy premises, scoped delegation, conjunction of caveats, and threshold evidence for one bound statement. Attenuation is constructed as:

```text
scope_child(x) = scope_parent(x) ∧ caveat(x).
```

The checker verifies this construction rather than solving arbitrary predicate implication. Signature evidence and derived affirmations have distinct constructors. A use of A1’s unit cannot produce a signed credential or checkpoint.

Start with ground caveats:

```text
principal and command equality
membership in a named scope
range and interval comparisons
generation and incarnation equality
membership or non-membership at a pinned Span version
```

Each primitive has a declared access method and cost. Absence requires coverage or a complete indexed lookup at the named version. It cannot be inferred from an incomplete search.

Stratified Datalog is a possible later evaluator, not a prerequisite for this checker. Stratification and polynomial data complexity do not establish an EXEC quantum bound. A query over a large Span can still require substantial work.

The records need these fields, either directly or through retained named records:

| Record | Fields relevant here |
|---|---|
| Grant | Issuer, holder, parent grant, scope, caveats, delegation permission, incarnation, validity domain and bounds, validity rule, revocation handle, authenticated statement |
| Authorization context | Policy interpretation Name, request binding, credential references, proof Name, local support versions, issuer-indexed revocation cuts, time observations, freshness-policy identity |
| Outcome | Existing operation identity and request binding, actual Decide interpretation, authorization-context reference, result and decision position |
| Read result | Query identity, interpretation, returned position or cut, coverage, supports, availability and typed declared loss |
| Check continuation | Request binding, interpretation, proof cursor, accumulated checked results, retained supports, reserved resources and remaining work |

A Name alone does not preserve replayability. The referenced proof, policy and evidence must remain obtainable for the audit or retry contract that promises their use.

Decide accepts only a checked derivation whose residual conditions hold at its admission boundary. Work that exceeds a run budget yields a continuation. It does not become `unauthorized` merely because the quantum ended. Parsing and checking have reserved resources before they run; an anonymous requester cannot consume unbounded work while the node tries to establish its authority.

C2’s order therefore applies to the **declared semantic preconditions after bounded input handling and resource admission**. It does not forbid the preliminary reservations required to check `auth`.

Use named results such as:

```text
proof-format
unauthorized(reason = signature | issuer | scope | expired | revoked)
authorization-context-stale
revision-moved
```

A failing link identifier is diagnostic data subject to the command’s disclosure policy. It need not be revealed to an unauthenticated caller. Existing `fenced`, `supports-moved` and resource-exhaustion results retain their own meanings.

The cost statement is:

```text
checking cost
  ≤ proof traversal
    + credential verification
    + charged support lookups
    + constraint evaluation
    + consumption checks.
```

It is linear in encoded proof size only under explicit bounds on those primitive operations and the representation of shared subproofs. A bounded, resumable implementation is required either way.

A useful optimization is **checked static evidence plus residual conditions**. Cache the checked derivation under its policy, proof and credential identities; recheck its changing state, time and revocation conditions at admission. PCFS’s conditional verification theorem supports this division of work. Its implementation did not supply fn2’s revocation protocol. [PCFS, §V](</Users/ember/paperbin/garg-pfenning2010-proof-carrying-file-system.pdf>)

Authorization and obligation evidence should share codecs, authenticated leaves, support tracking and bounded traversal. They need distinct checking judgments:

```text
Γ ⊢ t : K says permitted(α)

Γ ; Δ ⊢ t : ev(o) ⊣ Δ'
```

`Γ` contains reusable facts and receipts. `Δ` contains consumable allocations or authority. Joint evidence requires disjoint consumed allocations where the obligation contract demands consumption. Reusing an immutable receipt for two historical observations remains legal.

This is one implementation substrate with typed entry points. Calling both inputs “proof terms” does not justify erasing their different resource rules.

**5.3 What the simulator checks**

The simulator performs three different jobs:

- monitors a concrete execution;
- exhaustively explores a declared finite profile and schedule horizon;
- compares related executions.

Only a subset is propositional past-time monitoring. A monitor may also retain indexed state proportional to obligations, principals, supports or witnessed frontiers. A finite exploration result states its profile, horizon, environment assumptions and explored fault choices.

| Property | Check and scope | Existing checker |
|---|---|---|
| Append stability, producer attribution, fencing, ordered refusals | Transition and prefix invariants, including delayed completions and crossing continuations | TRACE, HISTORY |
| Frontier monotonicity, cut closure, read coverage, support validity | Indexed state checks; cut closure uses recorded dependencies | CONSUMER |
| Time-domain anchors and release conditions | Recorded time observations, re-anchoring, pauses and firing revalidation | TRACE |
| Obligation lifecycle and fork disposition | At most one authorized terminal transition; disposition over the versioned outstanding set | HISTORY, RECLAIM |
| Quantities, reservations and loans | Conservation, disjoint consumption, reservation lifecycle and borrow preservation | ACCOUNT, OWN |
| Scheduling share and progress | Bounded service under continuous eligibility; dependency progress under the declared completion environment | FAIR, WORK |
| Witness freshness and equivocation | Bound checkpoint statements, policy versions, retained frontiers and conflicting evidence | RECOVERY, IDENTITY |
| Summary, migration and route preservation | Paired executions from related states under corresponding suffixes; finite horizons are refutation tests | HISTORY |
| Port behavior and wiring | View and command simulation; endpoint types and owner compatibility | WIRE, TRACE |
| Persistence and reclamation | Every submitted-action prefix and death cut, including uncertain batches and outstanding borrows | RECOVERY, RECLAIM, OWN |
| Mixed durable/transient delivery | Declared order despite install-before-notification, pagination, overruns and epoch changes | CONSUMER |

Owner uniqueness is a wiring condition, not a decision procedure for colimit consistency. Compositional execution checks also expose allocator, pool and account state as components, following TRANSPORT Experiment E.

Likewise, route coherence “at every suffix” is an unbounded proof obligation. Exhaustive suffixes up to length `L` establish only the bounded instance. TRANSPORT Experiment D says this explicitly.

The transport demonstration is a scenario family across these checkers. It must exercise semantic preservation **and** succession: source fencing, destination installation, carried obligations, retry evidence, cuts and death cuts. A conjunction of read-equality tests does not establish the handoff.

**5.4 The proof route**

Use ordinary ACL2 functions and induction for finite proof checking, trace monitors, indexed invariants and relational simulation. Use Boolean reasoning or bit-blasting for genuinely finite subproblems: tag compatibility, fixed-width arithmetic, finite ownership cases and quorum-set calculations. Cryptographic verification remains at its declared boundary; bit-blasting a quorum predicate does not prove signatures unforgeable or witnesses honest.

Functional instantiation reuses a theorem after the substituted constraints have been established. It does not automatically discharge a port’s foreign axioms or a wiring diagram’s consistency obligations. KAT and separation logic remain optional offline proof routes where an actual commutation or frame theorem consumes them.

EXEC §4 is a **relational execution refinement**. It is not automatically a signature substitution from abstract states to concrete states.

For the general relation `R(C,S)`, introduce a proof-only linked presentation:

```text
             T_link
             /    \
      reduct/      \reduct
           v        v
         Core      Ref
```

Its states contain related pairs `(C,S)`. A concrete turn is linked to the allowed reference sequence `σ`, including scheduler and observation order. The concrete projection must lift every admissible concrete execution; merely constructing some convenient linked executions is insufficient.

The central obligation remains:

```text
R(C,S) ∧ Inv(S) ∧ BoundaryCompatible(E)
  ∧ fn2-turn(C,E) = (C',A,status)

⇒ ∃σ,S',Aref,statusref.
     allowed-reference-run(S,E,σ,S',Aref,statusref)
   ∧ R(C',S')
   ∧ Inv(S')
   ∧ A = encode-actions(Aref)
   ∧ status = statusref.
```

Initialization, guards for arbitrary client octets, cost, action bounds, continuation progress, ownership, byte-fill and crash composition accompany it. They are not consequences of observation equality.

When there is a proved functional abstraction `abs(C)=S`, this construction simplifies to an interpretation `Ref→Core` through `abs`. The relational form remains the general case required by TRANSPORT §3.1.

**5.5 Words and answers people use**

Keep the existing operations. Add qualifiers where they express a supported contract:

| User expression | Meaning |
|---|---|
| `as-of p` | Exactly the named historical observation, or an explicit unavailable result |
| `at-least p` | An answer at a returned `q≥p`, complete at `q` |
| `under r` | The interpretation used, distinct from the position |
| `signed by K` | An authenticated statement by `K` |
| `authorized by …` | A checked policy derivation |
| `witnessed by k of G` | A checkpoint certificate under a named witness policy |
| `owes` | An outstanding obligation with a stated discharge contract |
| `in fork f` | A branch with its own authority and effect disposition |
| `durable` / `transient` | The item’s persistence contract |

Do not make `says` and `signed by` synonyms. A derived affirmation can lack a signature.

A read can return:

```text
value, returned-cut, interpretation, coverage,
supports, availability, declared-loss
```

An accepted command reports its operation identity, position and actual producer interpretation. An unresolved persistence operation reports `uncertain` with its resolution handle. Neither word choice nor a proof term turns that into refusal.

`reconsider` uses the existing dependency relations and resumable folds. It records reassessment under a policy; it does not silently rewrite old claims or promise that every consequence has been repaired.

## Astra session 2: section 6

**Paste the following corrections into the cost table.** These assess every current row; the “too general” column should name the machinery being declined rather than attach a blanket undecidability claim to an entire research area.

| Current row | Disposition and replacement |
|---|---|
| Hybrid temporal logic with past | **Amend.** Typed historical references and fixed propositional monitors. Runtime monitoring, finite-state model checking and unbounded verification have different costs. Remove the blanket claim about all hybrid logics with `↓`; it is unnecessary to justify omitting binders. |
| Halpern–Shoham interval logic | **Keep, narrow.** Two endpoint comparisons under a declared time interpretation. No interval-modal satisfiability service. |
| Institutions, Specware | **Amend.** One declared presentation language, typed mappings and checked instances. Owner compatibility is one wiring check, not “the colimit check.” General consistency remains outside the node. |
| HoTT, univalence | **Keep as a proof-route reference.** Interface-based theorem transport and supplied coherence obligations. Observational equivalence does not require literal theory isomorphism. |
| ABLP, Garg–Pfenning, NAL, DKAL | **Amend.** Explicit scoped-credential proof grammar and its soundness translation. The present §5.1 grammar is not adequately specified by calling it “Horn.” No general principal algebra or distributed policy engine. |
| SecPAL, Datalog with constraints | **Replace the adopted machinery.** Begin with ground typed caveats and charged indexed predicates. Add a restricted rule evaluator only when needed. Integers, intervals and Span predicates do not collectively constitute a bounded-cost constraint domain. |
| Dynamic logic, KAT, Hoare, separation logic | **Keep with two subjects.** Pure Decide is deterministic; persistence execution has environmental choices. Contracts, simulation and frame proofs are used offline. Small syntax does not itself make KAT reasoning cheap. |
| Deontic logic | **Amend.** Obligation lifecycle plus declaration-selected terminal transitions and continuations. At-most-once termination is safety; eventual discharge is separate. Immutable evidence need not be linear. |
| Justification logic | **Replace “application and sum.”** Typed constructors for authenticated statements, inclusion, conjunction, alternatives and thresholds, with reusable and consumable premises distinguished. The full justification algebra is not implemented. |
| Epistemic logic | **Cut from the implementation table; retain a footnote.** Local certificates do not establish common knowledge. Do not claim a universal impossibility independently of communication and initial-knowledge assumptions. |
| Graded modalities, bounded linear logic, coeffects | **Amend.** Distinguish persistence grade, stock quantities, peak occupancy, accumulated work and service guarantees. Their operations and proof obligations differ. A two-point durability grade is not a cost algebra. |
| Contextual modal type theory | **Keep, narrow.** Support certificates and checked reuse, including negative dependencies and authorization context. No first-class contextual type language. |
| Counterfactual logic | **Cut the separate row.** Constructed forks and promotion belong under command execution. |
| Belief revision | **Cut the separate implementation row.** Dependency invalidation and reassessment belong under supported reads and folds. No AGM operators are proposed. |

**Add two rows:**

| Construction | fn2 uses | Cost and boundary |
|---|---|---|
| ACL2 relational refinement | Constrained interfaces, functional instantiation, concrete correspondence and converter correctness | Proof obligations remain per realization; generators do not certify themselves |
| Finite exploration and paired simulation | Tiny-profile schedule/death-cut exploration and related-execution comparison | Reports the explored bounds; unbounded preservation requires induction or another proof |

The decoration test should remain **checker OR refusal OR record**, but require a concrete subject and a counterexample. A name in a table is insufficient.

**Paste as the replacement decoration table:**

| Family | Concrete subject that earns its place | Scope correction |
|---|---|---|
| M1 | Read result, cut validation, time-domain transition, support reuse | A cut need not be a standalone durable record in every deployment |
| M2 | Mapping certificate, interpreted observation, migration or wiring check | Declarations and proof artifacts are not automatically journal record kinds |
| M3 | Credential, policy derivation, checkpoint or receipt | Authentication, authorization and witnessed coverage remain distinct judgments |
| M4 | Obligation transition and consumed allocation identities | RECLAIM checks release; ACCOUNT checks quantities; FAIR remains separate |
| M5 | Command contract, stable outcome and allowed execution | Pure decision and persistence protocol have distinct semantics |
| M6 | Publication grade, dependency contract and typed loss report | `gap` is a result constructor, not necessarily a refusal; durability is assumption- and contract-scoped |

Keep the current cuts of `K_i`, SDL `O`, Lewis counterfactuals and interval-modal operators. Merge witness checking into M3 without advertising a new graded-modal calculus.

Amend the incarnation merge: a lease record may carry succession authority, but **fencing also requires enforcement at the commit authority and protected sinks**. Recording a grant with an epoch does not establish that an old writer has stopped.

For each retained row, record whether its evidence is a tested implementation, a recorded obligation or a proved theorem. This is TRANSPORT §3.1(ii), not an additional evidence system.

## Astra session 2: the five decisions

I would keep five decisions, but replace decision 2’s identification of conservativity with migration grades. The other four need amendments.

1. **Amend: adopt six judgment families and the typed merges.**

   **Paste:** “Use M1–M6 to organize contracts over B. Revision, Equiv, Port and Wire share presentation-and-mapping infrastructure with distinct certificate variants. Transport combines a mapping with transfer, fencing and persistence. Credentials, claims, receipts and witness certificates share authenticated-evidence infrastructure. Obligation and reservation lifecycles share resource accounting where their contracts agree. Scheduling share remains a separate FAIR property.”

   This preserves the useful compression without claiming that `@^r` is an S5 box or that every named addition has become the same mathematical object.

2. **Replace: separate conservative language growth from behavior-preserving execution changes.**

   **Paste:** “A claimed conservative extension supplies an expansion of every B model that preserves the old interpretations. A change to an old observation or command contract is stated explicitly as a decision. A migration supplies admissible states, event correspondence, a relational certificate, an executable converter and retained-contract obligations. Its grade summarizes that evidence. Neither behavioral equivalence nor an `ext` label alone proves model-conservative extension.”

   A conservative theory can have a faulty converter. A correct migration of the actual reachable states need not expand every model of its source presentation. These are different tests serving different purposes.

3. **Amend: adopt bounded authorization checking with explicit context and disclosure.**

   **Paste:** “Add the scoped-credential checker with the consumer authentication and capability path. Freeze its proof grammar, primitive caveats, cost accounting and context-validity rules. Derive dependencies through the access boundary. Retain or name the evidence required to explain an outcome. Define semantic refusal order and public diagnostics explicitly. Scope query evaluation and its observable metadata according to the authorization contract.”

   Do not infer that AUTHINFO must issue a portable signed root grant. It can establish a local authenticated premise. Do not claim that moving a filter necessarily changes replies: the observable difference depends on selection, pagination, counts and disclosure. Decide those behaviors with fixtures.

4. **Amend: make obligation lifecycle linear, with typed evidence use.**

   **Paste:** “Every created obligation is outstanding or has exactly one authorized terminal transition allowed by its kind. Discharge checks the declared evidence and authority at the applicable admission boundary. Immutable receipts are reusable unless the contract consumes a separately identified allocation. Expiry creates a contrary-to-duty continuation only when the declaration makes expiry a violation. Witness requirements are declared per evidence contract. Operator waiver remains limited to unsatisfiable obligations, as STORAGE requires.”

   This keeps the existing mechanism and corrects both blanket evidence linearity and accidental eventual-discharge promises.

5. **Amend: build contracts with their consumers; retain D68 until explicitly revisited.**

   **Paste:** “Generate contracts and correspondence obligations from the existing DSLs where a current proof or checker consumes them. Use ACL2 for offline proofs and bounded typed checking in the node. Keep TRANSPORT’s present schedule: representation certificates now; runtime revision, migration and shutdown machinery only when D68 is revisited and producers exist. Expose the supported read, evidence and persistence vocabulary without requiring users to learn the modal classification.”

   I recommend beginning with the existing summary contract and one real port. A compulsory new `encapsulate` and observation inventory on every machine is not established by the current need. A reserved field is not exempt from having a producer, meaning and consumer.

## Astra session 2: interactions and conservativity

**Absorption of the eight first-session proposals**

| Proposal | Assessment |
|---|---|
| 1. Six judgment families | **Partly absorbed.** Decision 1 now says this, but §§1.1–1.4 still classify `@^r` as S5 and lossy translation as S4. Remove those classifications unless a separate box and its semantics are defined. |
| 2. Historical snapshots, not whole fork worlds | **Mostly absorbed in §1.3.** The frame table still says fork-of “identifies worlds,” and P2 still says one world per position. Both must say historical occurrence or interpretation-indexed snapshot. |
| 3. Threshold reads and contextual reuse | **Mostly absorbed.** P8’s sufficient rule is correct. P4 still permits coverage below the returned position, and P6 still treats the threshold-read notation as a proposition whose truth guarantees delivery. |
| 4. Authenticated speech versus affirmation | **Partly absorbed.** A1’s constructor distinction is good. The notation still equates `says` with authenticated assertion, and A5 still uses unjustified evidence application. |
| 5. Operational formulas | **L3 absorbed correctly.** L1 improved. E8’s first sentence is right, but its crash-successor explanation is not generally right. C1 still puts persistence uncertainty inside pure Decide. |
| 6. Corrected revision rules | **R3, R6 and most of R8 absorbed correctly.** R7 and §2.9 are stale against completed TRANSPORT. Coverage, dependency changes and interpretation-at-position need the corrections below. |
| 7. Resource linearity and service | **O9 and E5 improved correctly.** O3’s title, §2.8’s holds row, and §5.3’s identical-checker claim contradict those improvements. |
| 8. Typed loss envelope | **Absorbed correctly in D4.** Section 5’s kernel-as-missing-sentences and union-composition claims reintroduce the conflation. |

**Paste as replacement section 2.9**

**Obligation, evidence and authority.** An accepted discharge requires the obligation kind’s evidence judgment and discharge authority at the applicable admission context:

```text
accepted(discharge(o,t), p)
  ⇒ outstanding_before(o,p)
   ∧ authorized_discharge(o,p)
   ∧ check_ev(Γ_(r,p,c); Δ, t, ev(o), Δ').
```

A foreign receipt may satisfy the contract without any cosignature. Another contract may require a policy-accepted witnessed checkpoint, including for evidence about the local domain. Foreign origin alone neither entails nor exhausts the witness requirement.

An immutable receipt may be reused. A quantity-bearing discharge names the allocation consumed, and the transition checks that allocation has not already been consumed. Evidence checking does not replace fencing, retry handling or the obligation’s current status.

**Revision and historical observation.** An event or outcome retains its recorded producer interpretation. Installing a new interpretation does not re-decide it. A historical observation is identified by its domain, position, interpretation and query:

```text
(d, p, r, query).
```

Position determines the journal’s active-revision selection where that selection is defined. It does not determine every projection interpretation under which someone can ask a question.

A migration certificate relates actual source and destination states. For related states and preserved observations:

```text
R_m(s,s')
  ⇒ obs_(f@r)(s,q) = obs_(f'@r')(s',ρ(q)).
```

Step preservation extends this agreement over corresponding admitted suffixes. The institutional satisfaction condition explains the sentence translation; the relation certificate connects the actual models.

Coverage transfers at the **converted state’s cut**. Coverage of added observations requires its own justification. Neither conversion nor inherited coverage creates a historical snapshot.

A new interpretation may also be evaluated over retained old history without a preservation certificate. That produces a new interpretation-indexed answer, not a claim that it equals the old answer.

Consequently, remove:

```text
[adopt] ⟨≥p⟩ φ ↛ ⟨≥p⟩ [adopt] φ
```

The note defines `⟨≥p⟩` as a read operation, not a modal operator on arbitrary formulas. More substantively, preserved coverage does not make adoption and reading commute as commands. They can differ in returned revision, authorization, availability and refusal. State the observation-agreement equation for the declared query instead.

**Authorization and changing state.** Proof checking is monotone relative to a fixed proof context. Selecting the context for a new admission is not monotone: credentials expire, scopes change and revocation cuts advance.

A4 therefore needs both:

```text
check_auth(Γ_(r,p,c), t, α)
context_admissible_now(Γ_(r,p,c), α).
```

Recording an old cut makes a past decision reproducible. It does not authorize choosing that cut for a new command after revocation has become relevant. The policy must state the required local context and the accepted freshness of foreign evidence. During disconnection, the node cannot silently substitute “latest issuer state” for “latest state established by the evidence I hold.”

After a continuation yields, relevant changing premises are pinned or revalidated before admission. Retry recovery returns the original outcome within its retained contract; it does not reauthorize and execute the old operation anew. Any authorization to disclose that retained outcome is a separate read question.

The outcome binds the policy and actual Decide interpretation, request, proof and support evidence, time observations and revocation cuts, directly or through an authorization-context record. `c(α)` is not the only context field needed.

**Additional axiom corrections required by those interactions**

| Law or claim | Corrected statement |
|---|---|
| P4, coverage | For a complete answer at returned `q`, require `q≥p` **and completeness at `q`**. A latest-only materializer normally answers at its own covered state. Node head `q=100` with materializer coverage `80` cannot answer “at 100” merely because requested `p=70`. |
| P6, wake | A wake makes a consumer eligible to recheck. Delivery requires successful current checks, resources and scheduling. It is not an immediate “iff” consequence of a threshold becoming true. |
| P3, observation permanence | Preserve the meaning of a stamped historical observation. Current retrieval availability, authorization and physical placement can change. STORAGE’s historical-read contract determines whether the node can still return it. |
| R7, dependencies | A changed dependency manifest changes the composed interpretation identity and triggers compatibility checks. It need not change Decide’s command semantics. Dependencies are derived, not handwritten read lists. |
| R4, `lossy κ` | Preserved observations are constant on the identification classes and have a compatible target interpretation. “Outside the kernel” is not the right characterization of a relation on pairs of states. |
| R6, admission | A valid backward migration is the semantic compatibility requirement, not the sole sufficient condition for admission. Authority, resources and lifecycle checks still apply. |
| R9, transport | Carry semantic state and retained contracts, and establish authoritative succession plus destination persistence. A source-side fence bit alone is insufficient. |
| A5, receipt construction | Use `receipt(checkpoint-evidence, inclusion-proof, bound-statement)`. Check the statement’s history, incarnation, cut, root and policy bindings. A signed checkpoint is not itself a proof of an implication to which an inclusion proof can simply be applied. |
| A6, threshold evidence | Count distinct accepted witness principals for the **same bound checkpoint statement** under a named policy version. Counting signatures on `count≥n` alone omits root and lineage compatibility. |
| A8, freshness | Reject a candidate authoritative head or recovery state below accepted independent frontier evidence. An explicitly historical read or old inclusion receipt below that frontier remains legal. |
| A-IF, rollback evidence | Surviving acceptable independent evidence can establish a lower bound. Detection does not require that the evidence have precisely the `W(w,o)` cosignature form, nor does any untrusted `says` establish it. |
| O1, lifecycle | Outstanding or exactly one authorized terminal transition. Include declared cancellation. Do not use strong “until” to require eventual discharge. |
| O5, reparation | Create the continuation when the declaration’s violation condition commits. Expiry is a violation only for kinds that say so. |
| C1 and E8 | Pure Decide returns a deterministic decision or proposal. Persistence reports established acceptance, definitive refusal/nonacceptance, or uncertainty. Uncertainty concerns histories compatible with held evidence, not necessarily multiple crash successors of the actual physical state. |
| C6 and D3 | Guard successful postconditions by successful admission or established publication. A refused fork creates no child; a commit request alone establishes no durable record. |
| D1 and `□_D` | State the fault assumptions and retained contract. A durable publication is not a promise to retain every payload forever, nor that every damaged recovery can reconstruct acknowledged data. Recovery must not manufacture a normal success from insufficient evidence. |

Two further frame repairs keep the notation honest. Immediate succession `i→i+1` is neither reflexive nor transitive; its reflexive-transitive closure is. Similarly, distinguish direct `fork-of` from ancestry. Declare `→_C` to be the permitted crash/recovery closure if its box is to inherit reflexivity and transitivity.

**Paste as the corrected conservativity table**

The table must describe expansions, not merely convenient deployments. Optional features have inactive values, and their laws are guarded by activation. Old operations retain their meanings.

| Extension | Expansion or boundary | Conclusion |
|---|---|---|
| M1 cuts | Embed the one-domain position as a singleton cut | Conservative |
| P8 supported reads | Add a certificate wrapper whose old observation is its value projection; a whole relevant snapshot and interpretation can be the conservative support | Conservative as an added interface. Changing old reads to refuse introduces a behavior change |
| P9 intervals | Map each old time reading to `[t,t]`, retaining the old expiry policy | Conservative. Imposing a new release rule on old obligations is a separate decision |
| Incarnations | One active incarnation, no succession operations in the B fragment | Conservative |
| M2 revisions | One interpretation, identity mappings, inactive runtime revision operations; preserve old observation functions | Conservative under the corrected laws. An encoded wire-field change is not dismissed merely by calling it metadata |
| M3 receipts and witnesses | Preserve existing authenticated evidence; no active witness requirements, with positive thresholds for active policies | Conservative as optional evidence machinery |
| M3 authorization | Preserve B’s admission predicate through an interpretation, or identify the exact changed accepted/refused traces | Proof checking is not inherently non-conservative. The proposed replacement policy and refusal ordering require a decision unless equivalence is proved |
| M3 scoped visibility | Compare query results, selection, pagination, counts and diagnostics under the old and new interfaces | A changed implementation method alone proves neither conservativity nor non-conservativity |
| M4 parties, quantities, continuations and thresholds | Preserve old obligation kinds and terminal rules; activate new fields and laws only for kinds declaring them | Conservative as a guarded extension. “Quantity 1” alone does not establish all conservation laws |
| M4 reservation interpretation | Relate existing volatile reservations to resource fragments without requiring new journal writes | A refinement obligation. Protected scheduling share remains independent |
| M5 occasions and optional commands | Preserve old commands; added fork, promote and relaw operations are inactive in the expansion | Conservative after successful-postcondition guards are repaired |
| M6 loss reports | Embed old gaps unchanged in the typed envelope | Conservative. New retention or availability policy is a separate change |

Remove the conclusion that **exactly two clauses of M3 are the only possible non-conservative changes**. The defensible conclusion is that the corrected optional interfaces admit the stated expansions, while changes to old admission, disclosure, release, availability or wire observations must be assessed explicitly.

Finally, §4.4’s thread example needs one qualification I should have supplied in session 1. Keep the old logical state sort and its interpretation; introduce `State₄` as an additional representation with projection `π`. Replacing an old sort’s carrier by `State₃×ThreadAnnotations` is not literally an expansion preserving every old interpretation. The step equation proves behavioral preservation; the separate expanded presentation establishes conservativity.

## Astra session 2: two-position disagreements

The positions below include the reasons for the Opus construction, my replacement, and the evidence that decides between them.

| Issue | Opus position and reason | Astra position and reason | What decides |
|---|---|---|---|
| Revision as S5/S4 | Equivalences form a groupoid and migrations compose, suggesting familiar modal laws | `@^r` translates and evaluates an interpretation-indexed sentence. It is not the box over that groupoid. Lossy mappings also change the preserved language | Define the proposed box and prove its axioms for that operator, or remove the classification while retaining R4 |
| Generated machine contracts | Every machine already declares enough structure to emit a presentation uniformly | Generate contracts where consumed, using existing observations. EXEC machines need observation/action and continuation semantics, not just event folds | Apply the generator to a parser or commit machine and show useful obligations without a duplicate specification |
| Port loss | Missing foreign expressivity gives a loss signature; union makes bridge composition simple | The exact kernel is an identification relation. Composition pulls the later kernel back through the earlier reduct | The `(x,y)↦x↦x mod 2` example refutes union; the revised composition equation must hold |
| Authorization language | A common stratified-Datalog fragment could serve grants, selections and evidence | Shared ground predicates and proof infrastructure suffice initially. Query evaluation and resource consumption need different contracts | Implement a real capability path and measure traversal, lookup, signature and resumption costs; demonstrate that a rule evaluator removes actual duplication |
| “Only compatible” proof placement | Client proof search plus linear checking protects the executor | Bounded local evaluation and cached static proofs with residual checks are also compatible. Linear cost requires primitive-cost assumptions | Compare full checking and residual checking under changed revocation, cold pages and large supported proofs |
| One evidence checker | Authorization and discharge both check proofs of propositions | Share machinery, but distinguish reusable evidence from consumable allocations and current obligation status | Reuse a receipt for two reads, then attempt to spend one allocation twice. The first must pass and the second fail |
| All properties as past-time monitors | Existing checkers could absorb the laws with small uniform monitor costs | Relational preservation, finite exploration, indexed safety and conditional liveness are different tasks | A migration agreeing through the explored horizon and diverging later demonstrates the boundary; report monitor state and exploration bounds |
| Conservative extensions as migration grades | One discipline for kernel growth and world evolution is simpler | Model expansion, actual-state conversion and future-behavior preservation are separate obligations | A conservative target with a faulty converter, and a correct reachable-state migration without all-model expansion, separate the tests |
| Revision and temporal commutation | Preserved grade plus inherited coverage should make reads agree across adoption | Agreement requires related states and a declared observation. Adoption can still change returned metadata, authority and availability; new observations need coverage evidence | Convert a lagging projection, add an observation dependent on discarded history, and issue both exact and threshold reads |
| Foreign evidence and witnessing | Foreign evidence needs the stronger witnessed form | The obligation’s trust contract selects the evidence. A signed foreign receipt can suffice; a local claim can require witnesses | One kind accepting a trusted peer receipt and another requiring a quorum must both be expressible without changing the evidence engine |
| Freshness | Refuse every presented count below a held witnessed count | Refuse authoritative rollback, while allowing historical observations | Hold a checkpoint at 100, request a valid receipt at 60, then attempt recovery at 60. Only the recovery candidate is stale |
| Authorization conservativity | Grants-first and pullback visibility necessarily change 5.1.1 | Specific refusal ordering and disclosure changes may do so. Replacing an implementation while preserving its contract may not | Compare old and new replies, selected pages, counts and diagnostics, including unauthorized and partially visible queries |
| Reserved revision stamp | A constant field reconciles WR’s request with D68 without adding a record kind | A field still needs an actual meaning and consumer. D68 is not automatically lifted at release | Show the producer and checker that consume the stamp now, or keep the field specified until that use exists |

The marked Opus additions deserve these dispositions:

- **Section 3, witness counting: amend and keep.** Opus’s reason is that finite threshold checking is a useful restricted instance. I agree with the implementation, but the correspondence to Fine’s world-counting modality has not been supplied. Keep the counting atom, complete checkpoint binding and policy checks. A fixture with two roots at the same count, duplicate signers and a witness-policy transition decides whether the check is adequate. Honest quorum intersection remains conditional on the declared fault assumptions.

- **Section 3, modal interfaces: keep as a footnote.** Opus’s reason is that commands introduce required and permitted protocol behavior. My qualification is that ordinary forward simulation is not automatically modal refinement. The cited construction checks required specification transitions and permitted implementation transitions in different directions. A port needs that mapping before adopting the name. A POST implementation that never replies can satisfy some trace-safety properties while failing the required service contract. [Modal interface automata, §3](</Users/ember/paperbin/luttgen2013-modal-interface-automata.pdf>)

- **Section 3, truth maintenance: keep with a narrower claim.** Opus places reconsideration in dependency bookkeeping rather than a new modality. I agree. The required check is completeness of affected-support discovery, including negative dependencies, followed by explicit reassessment. A withdrawn support must invalidate its dependent current claim without erasing the historical claim or claiming an external repair occurred.

- **Section 4, staging under D68: keep the staging, amend the field argument.** The completed TRANSPORT note says runtime evolution is conditional on D68 being revisited, not merely on the first release having happened. A current interpretation manifest can have immediate consumers in simulator runs and checkpoint statements. That is a reason to implement that identity, distinct from reserving speculative migration fields.

These amendments let the note shrink: remove the unsupported modal-class rows, move unused theories to short footnotes, and let the generated contracts, record meanings and refuting examples carry the engineering argument.