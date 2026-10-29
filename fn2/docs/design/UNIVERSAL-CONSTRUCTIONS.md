# fn2 as universal constructions: the algebra behind the toolkit (2026-10-28; Opus researcher; present state)

Brief: `build/coordinator/briefs/UNIVERSAL-CONSTRUCTIONS-20261028.md`. Ember, verbatim: "we're trying to find the universal constructions and the various ways of decomposing and understanding the system, finding its colimits and pulling back to think about equalizers in the space of the causality flows that these systems purport ... fn2 i'm kinda imagining is gonna be the toolkit from which so many things flow, so many systems built around its primitives."

Read against: `EXECUTION-MODEL.md` (EXEC), `STORAGE-DESIGN.md` (STORAGE; decision 1's summary equation), `INBOX-DELIVERY.md` §4-5 (INBOX), `PLANES-AND-GAMES.md` §2 and §4 (PLANES), `PLANES-ADDENDUM-INTERWEAVING.md` (ADDENDUM), `CLIENTS-AND-DATA-MODELS.md` §2 (CLIENTS). Papers are cited by their filename in `~/paperbin/` (`.pdf` with a `.txt` beside it unless the name ends `.txt`); 39 were fetched for this document and are listed in the "Universal constructions" section of `~/paperbin/README-fn2-20261028.md`.

The rule this document keeps: **a construction is named only if it predicts something concrete for the engineering.** Where the category theory only renames what the documents already say, the section says so: it marks the item *(placement)* or cuts it. Every "predicts" line is a missing law, a primitive that should be two, two mechanisms that are one, or a statement that should change shape. The draft was attacked by Astra (§13; three fatal and fourteen material findings, all accepted), and this text is the corrected present state.

## Contents
0. The answer in one page
1. The journal: free monoids, traces, event structures, cuts
2. Folds and projections: monoid actions, observational equivalence, read strengths, DBSP, Σ ⊣ Δ ⊣ Π
3. Selection, joins and inboxes: span composition
4. Identity and content addressing: monos, semilattices, catamorphisms, Merkle clocks
5. Consistency, agreement and the planes: CALM, sheaves, semilattices, gradings
6. Obligations, protocols, leases and time domains
7. Lenses: folds are the get side
8. Ownership and the byte pool: a resource algebra
9. The algebra of fn2: eight interfaces over four irreducible ones
10. The three DSLs and the ten operations
11. The cost: where the constructions are too general
12. Five decisions for ember
13. Astra's round, folded in
14. Bibliography

---

## 0. The answer in one page

fn2 is described by **eight named interfaces** over **four irreducible ones**. Each is a familiar universal construction, and each comes with laws. Some of those laws are free. Others are proof obligations that the construction makes local and small. Astra's round (§13) separated the two, and this page reflects the separation.

The irreducible four:
- **Log**: a word in the free monoid on typed events, one per commit domain; positions are its prefixes. Appending is the only write. "One atomic mutation, one domain" is an architectural restriction: products of free monoids exist, and fn2 declines to use them.
- **Decide**: the serial command processor at the head of one domain, `(state at head, command) → (outcome, events)`. Every choice that is not a merge of validated facts happens here: accept versus conflict, claim, transfer, release. Where each of these choices sits is the question CALM and invariant confluence answer (`hellerstein-alvaro2019-keeping-calm.pdf`, `bailis2014-coordination-avoidance-database-systems.pdf`).
- **Fold**: a right action of the free monoid on a state set (an automaton). The summary equation is its action law and is free. *Discarding* history needs a proof that future observations are preserved.
- **Name**: a content commitment, a map assumed injective, computed as a catamorphism over a declared tree shape.

The four specialized interfaces are Folds (and, for one, Decide) whose contracts are worth naming once:
- **Binding**: a multivalue identity map `key ↦ set of validated values`, merged by union, conflicted when the set has two or more elements. Message-ID identity and signer equivocation are two instances.
- **Span**: a keyed relation (an index). Indexes compose by pullback-then-pushforward (`Σ∘Δ`, `spivak2010-functorial-data-migration.pdf`). Selection and materialization are two evaluation orders of one composite.
- **Frontier**: a monotone value in a join-semilattice (a position, a vector cut, a head-set). Waits, timers, coverage and cursor positions are threshold reads on frontiers (`kuper2014-freeze-after-writing-quasi-deterministic-lvars.pdf`).
- **Obligation**: a linear resource, created by a commit and either outstanding or discharged exactly once by an authorized evidence, waiver or expiry event. With an exclusive holder and a fencing incarnation it is a claim or a lease.

None of this replaces EXEC's operational contracts: bounded execution, reservation before work, adapter ownership of loaned bytes, and the persistent `uncertain` state with its prepare, fence, install and recovery protocol. The algebra describes what is computed; EXEC describes how it is computed under faults and bounds.

What the constructions contribute that the documents lack, after Astra's corrections. Each item is argued in its section, and items marked *(placement)* restate an existing requirement in a better place rather than predicting something new.
1. **A read contract with two strengths.** `exactly-at(p)` needs retained version state or a snapshot plus replay. `at-least(p)` is a threshold read on coverage. `cov ≥ p` gives only the second: a latest-only projection cannot answer exactly at `p < cov`. This defect is inherited from PLANES §2.2 (§2.4; Astra 4).
2. **`catch-up` replaces the general `select` fallback.** It is the projection's maintenance state at `cov` advanced over an available suffix, and it requires both to exist. INBOX §4.6 already does this for the inbox *(placement)* (§2.4).
3. **Summary adequacy has a local certificate.** Two equations per event kind (a coalgebra homomorphism for the declared observations) are a *sufficient* proof of a summary rule, and they turn STORAGE decision 1's simulation obligation into per-event-kind lemmas. The certificate is not necessary; a general rule needs a simulation (§2.2; Astra 2).
4. **The peer convergence statement has a definite form.** For equal sets of *validated* identity facts, the Binding is equal at every node. `conflicted(mid)` holds iff two or more contents are recorded. Local acceptance outcomes and article numbers are not part of what converges. A conflict refusal records its evidence, subject to an admission contract (§4.3; Astra 8).
5. **Message-ID conflict and signer equivocation are one Binding**, with distinct validation rules (§4.3).
6. **Durable dependencies that need later content inline it or name it durably.** An explicitly lossy `(epoch, seq)` reference stays legal and is typed as such (§5.6; Astra's amendment to decision 5).
7. **Mixed durable and transient delivery has a specifiable exact order on one node**, provided durable items sort as `(q, 0)`, transient items as `(p, s)` with `s > 0` drawn from a sequence of declared scope, and the delivery merge is required to respect that order across delayed notification, pagination and live gaps. This is an amendment to PLANES §2.3, not a free consequence (§5.3; Astra 10).
8. **Time-domain clocks must be monotone across anchors, and unreachable deadlines are explicit.** A pause delays only unreached deadlines. A converted deadline is provisional until it fires and is revalidated then (§6.4; Astra 11).
9. **Authority of a lease holder is defined at commit.** It lasts until committed expiry, revocation or supersession, and fencing rejects superseded holders. Time-dependent authorization is declared, not abolished (§6.3; Astra 12).
10. **Protocol states are shared declarations.** Parser, machine, client and checker read one finite-state protocol table for each served protocol. Commands carry preconditions and observable postconditions. The lens vocabulary is reserved for restricted update languages with proved lifting laws (§6.2, §7; Astra 13).

---

## 1. The journal: free monoids, traces, event structures, cuts

### 1.1 One domain: a word, its prefixes, and the coalgebra that observes it
**Construction.** A commit domain's journal is a finite word `j ∈ E*`, an element of the free monoid on the typed event alphabet `E`. A sealed batch is a word, and committing it is concatenation. A position is a prefix, and positions form the chain `(ℕ, ≤)`. Rutten's universal coalgebra (`rutten2000-universal-coalgebra-theory-of-systems.pdf`) supplies the observer's side: an observer that may see the journal grow forever sees an element of the final coalgebra of `X ↦ 1 + E × X`. Equality of observed behaviour is bisimilarity, and coinduction is its proof principle.

**Laws for free.** Append is associative with the empty batch as unit, and a position names one prefix forever. "One atomic mutation belongs to one commit domain" (STORAGE decision 1) is **not** an algebraic impossibility: products of free monoids exist, and a two-domain atomic append would be an element of one. It is an architectural restriction that fn2 adopts so that Decide stays serial per domain (Astra 1).

**What it predicts.** On its own, nothing the documents lack. The coalgebraic half earns its place in §2.2.

### 1.2 Independence: the total order over-specifies, and trace theory says by how much
**Construction.** Two transitions commute when neither affects the other's enabledness, effects or outputs. Given an independence relation `I ⊆ E × E`, the trace monoid `M(E, I) = E* / ~` (the free partially commutative monoid; `mazurkiewicz1995-introduction-to-trace-theory.pdf`) identifies words that differ only by swapping adjacent independent letters, and the journal is one linearization of a trace. Mazurkiewicz's projection lemma: a trace is determined by its projections onto the cliques of the dependence relation.

**What it predicts.**
1. **Conservative effect summaries for the transitions that fusion or partial-order reduction actually exploits.** EXEC §4's fusion obligation ("same scheduled transitions or a proved commutation of independent ones") can draw its independent pairs from declared *effect summaries* (rows read and written, plus shared quotas, allocator, scheduler and action-stream effects). Such a summary is a sound *over-approximation*: overlapping transitions may still commute, and disjoint rows may still share hidden state. Each exploited commutation therefore keeps an explicit lemma that preserves enabledness, outputs and the specified scheduler. The default summary is "the entire semantic state and its effects", which gives no reduction but is always safe. Precise summaries are added only where fusion or the simulator's partial-order reduction consumes them (Astra 15). The payoff when they are added is a bound on the simulator's state space. Its theoretical support is in `goubault2000-geometry-and-concurrency-users-guide.pdf`, which relates trace equivalence to the partial-order methods of Godefroid and Wolper.
2. **A k-way merge of per-stream indexes by commit position reconstructs a linearization *(placement)*.** By the projection lemma, per-stream indexes are projections of the trace. INBOX §4.4 relies on this without stating it, and commit position is the canonical linearization that lets the cursor be a scalar.
3. **If commit domains are ever split, the split follows dependence.** A domain must contain every dependence clique that an atomic mutation spans, so the effect summaries make "one atomic mutation, one domain" checkable rather than conventional.

### 1.3 Several domains and peers: event structures, configurations, cuts
**Construction.** Across domains and peers there is no total order, only causality. Winskel's prime event structures (`winskel1987-event-structures.pdf`) have a causal partial order and a conflict relation. A *configuration* is a conflict-free, down-closed set of events. Lamport's happened-before (`lamport1978-time-clocks-ordering-of-events.pdf`) is the causal order. Mattern (`mattern1989-virtual-time-global-states.pdf`, Theorem 2) shows that consistent cuts form a lattice and that vector time characterizes causality. Behavioural equivalence in presheaf models is a span of open maps (`joyal-nielsen-winskel1996-bisimulation-from-open-maps.pdf`; `cattani-stark-winskel1997-presheaf-models-pi-calculus.pdf`).

**Laws for free.** For per-domain chains with cross-references, a down-closed set is determined by its height on each chain. The lattice of consistent cuts therefore embeds in `ℕ^D`, which is why vector clocks are the free representation of a cut.

**What it predicts.**
1. **The multi-domain cursor is a cut, and it must be down-closed.** INBOX §4.8 reserves `(domain = 0, sequence)` for a later cursor version. That version is a vector of per-domain positions, and the law the documents do not state is that *a cursor proposal never includes an event of domain A that depends on a position of domain B that the cursor has not reached*. Concretely, an event that references another domain's position carries that position, and the multi-domain merge advances domain A past it only once its dependency is covered.
2. **Acceptance choices and evidence about them are different events (Astra 9).** Two contents offered under one Message-ID are *conflicting acceptance choices*: no configuration contains both acceptances. *Observations* that both were offered are compatible facts, and a monotone evidence set may contain both. §4.3's Binding is built from the observations, not from the acceptances. That distinction keeps the event-structure reading consistent.
3. **Peers exchange events and never merge journals.** Two different total orders over a common prefix have no pushout in the category of total orders. Each node keeps its own linearization, and what peers converge on is the set of validated facts (§4.3). Equality of fact sets is a *convergence* notion. It is weaker than open-map bisimulation, which also constrains future enabled behaviour. The open-maps reading is kept only as the reason journal equality is the wrong criterion (Astra 9).

### 1.4 The space of causality flows: directed topology
**Construction.** Fajstrup, Goubault and Raussen model a concurrent program as a directed space (`goubault2000-geometry-and-concurrency-users-guide.pdf`; `goubault2003-geometric-perspectives-concurrency-theory.pdf`). Executions are directed paths. Dihomotopic paths are equivalent schedules, and for PV programs these are exactly Mazurkiewicz traces. Deadlocks and unsafe regions are geometric features of the forbidden region (the states where two processes hold a resource the other needs).

**What it predicts.** Two things, both small. (a) Schedule equivalence in the refinement obligation (EXEC §4) is dihomotopy, which reduces to §1.2's traces. The geometry adds nothing the footprint does not already give. (b) EXEC §7a item 2 asks for "a resource acquisition and release protocol that excludes deadlock". The geometry says a forbidden-region complement has no deadlock when every machine acquires its resources in one global order, which is the classical condition. A machine DSL that declares admission bundles in a fixed resource order makes deadlock freedom a syntactic check; the trace-space computation is never needed. **Kept as the justification for a static acquisition-order check; the topology itself is cut.**

---

## 2. Folds and projections: monoid actions, observational equivalence, read strengths, DBSP, Σ ⊣ Δ ⊣ Π

### 2.1 A fold is a monoid action; the summary equation is its action law
**Construction.** A fold with state set `S`, initial state `s₀` and step `δ : S × E → S` extends uniquely to a right action of the free monoid, `S × E* → S`. This is the universal property of `E*`. Equivalently, it is the catamorphism over snoc-lists, the unique algebra homomorphism out of the initial algebra of `X ↦ 1 + X × E` (`meijer-fokkinga-paterson1991-bananas-lenses-envelopes-barbed-wire.pdf`).

**Laws for free.** `fold(s, u·v) = fold(fold(s, u), v)`, which is STORAGE decision 1's `State = Fold(Summary_k, Events_{k+1..n})` with `Summary_k = fold(s₀, E_{1..k})`. The fusion law (`h ∘ ⦇δ⦈ = ⦇δ'⦈` when `h` commutes with the steps) is the one-line proof that a derived or compressed state stays correct.

**What it predicts.** The summary equation is *never* the hard part. It holds for every deterministic fold, which is why stating it as a decision added nothing. The hard part is the next subsection.

### 2.2 Discarding history: preservation of future observations, with a local certificate
**Construction.** Let a fold name its observations `obs : S → O`: the answers it must keep giving, such as identity decisions, outcomes, cursor states and delivered items. Two states are observationally equivalent, `s ≈ s'`, iff `obs(fold(s, v)) = obs(fold(s', v))` for every future suffix `v`. This is the Myhill-Nerode congruence. `S/≈` is the coequalizer of the kernel pair of the behaviour map: the image of `S` in the final coalgebra of the Moore-machine functor `X ↦ O × X^E` (Rutten, minimal systems, `rutten2000-universal-coalgebra-theory-of-systems.pdf`).

**The law, stated correctly (Astra 2).** A summary rule `σ : S → Σ` is *adequate* iff it preserves all future observations. Being a coalgebra homomorphism, `obs_Σ ∘ σ = obs` and `σ(δ(s, e)) = δ_Σ(σ(s), e)` for every event kind, is a **sufficient certificate**, and it is local: two equations per event kind. It is not necessary. Astra's counterexample is a counter summarized as `(n mod 2, 0)`: the observation reads only the first component, so every future observation agrees, but the hidden second component breaks the step equation. Necessity holds only when the summary is observationally reduced. In general an adequate summary needs a simulation relation.

**What it predicts.** STORAGE decision 1 already requires that discarding history be proved "as an observation-preserving simulation against the retained contract's observations and future requests". The construction adds the **proof shape**, and the obligation itself is placement. For the summaries fn2 actually writes (identity octets with binding evidence, obligation evidence, latest-only folds), the homomorphism certificate is the default. Its teeth: a σ that drops the exact Message-ID octets fails the identity-decision equation on the suffix "re-offer the same Message-ID with different content". The observations are named by **reference to the existing contract observations**, and only for summaries that discard history. They are not a separately maintained list on every projection (Astra 18).

The Merkle log is an instance with a caveat (Astra 2). For the observation "root after any future appends", the minimal summary is the frontier of perfect subtrees, O(log n) hashes (`opentimestamps2026-docs-merkle-mountain-range.md`). Inclusion proofs for already-retained leaves are a *different* observation and need retained proof material, which is why STORAGE retains "a pageable frontier and proof material", both of them.

### 2.3 What a fold can absorb: capabilities, not an algebra class
**Construction.** DBSP (`budiu2023-dbsp-automatic-incremental-view-maintenance.pdf`) works over abelian groups (Z-sets: multisets with integer weights), where `Q^Δ = D ∘ Q ∘ I`. Linear operators are their own incremental version, the chain rule `(S₁ ∘ S₂)^Δ = S₁^Δ ∘ S₂^Δ` holds, and bilinear operators (joins) are incremental at the cost of an indexed copy of each side (DBSP Proposition 3.2, Theorem 3.4). Joins of a semilattice are idempotent and commutative (`kuper2014-freeze-after-writing-quasi-deterministic-lvars.pdf`; `meiklejohn-vanroy2015-lasp-coordination-free-programming.pdf`).

**What it does and does not predict (Astra 3).** An earlier draft classified every fold's state into one of three algebras and derived its maintenance mode from the class. That classification is withdrawn, for three reasons. An arbitrary automaton's state carries none of these structures. Semilattices are monoids, so the classes overlap. And legality of a maintenance mode depends on work, fan-out, dependencies, charging and atomicity, none of which follows from algebra: a bounded unique-key join can run in-transaction, and a linear map can still traverse unboundedly. **`mode` stays explicit**, checked against the resource bounds as PLANES §4.2 has it.

What survives is a small vocabulary of **capabilities a fold declares when it uses them**, each with its proof:
- **retraction**: the fold absorbs a withdrawal, either through an inverse (group-valued state such as counts, balances and keyed Z-set rows) or through retained candidates (top-k, latest-by-key). A fold over withdrawable sources that has neither cannot be maintained. fn's withdrawal reports (FNWD1) are negative-weight deltas exactly when the consuming fold declares an inverse.
- **merge**: the fold's state has a join and its updates are inflationary, so replicas may merge it without order. This is the capability peers need (§4.3, §5.4).
- **duplicate tolerance**: reapplying an event leaves the state unchanged, the property that makes replay after an `uncertain` resolution and duplicate peer delivery harmless.

DBSP remains the route for deriving incremental interpretations of relational queries when hand-written folds stop scaling. It is incrementalization machinery, not a scheduling classification.

### 2.4 Frontiers and reads: exactly-at versus at-least, and `catch-up`
**Construction (motivation, not an operational law; Astra 4).** Treat positions as the chain category `ℕ`, and a projection maintained through `cov` as a functor `P : [0, cov] → Set`. For `i : [0, cov] ↪ ℕ`, the left Kan extension evaluated at `p > cov` is `P(cov)` ("answer at `cov` and say so"). The right Kan extension there is a limit over an empty diagram, a singleton carrying no information. The action law (§2.1) gives the true value as `fold(P(cov), E_{cov+1..p})`. These calculations are correct for a Set-valued diagram. They motivate three read policies; they do not supply blocking semantics, progress, or the state the policies need.

**What it predicts.**
1. **An inherited defect: coverage is not history (Astra 4).** PLANES §2.2's read rule says "if the projection's `cov ≥ p`, it answers from the projection". For a latest-only projection that answers *at-least-as-fresh-as `p`*, not *exactly at `p`*. An exact answer at `p < cov` needs retained version state, or a snapshot plus replay. The read contract therefore has two strengths: **`exactly-at(p)`**, which needs version state or snapshot-plus-replay, has retention and authorization-version behaviour, and reports unavailable history as a gap; and **`at-least(p)`**, a threshold read on `cov`. Every read names which strength it asks for.
2. **`catch-up` replaces `select` as the general fallback.** PLANES §2.2's `select`, "recompute from the source streams", read literally for a catalog or a leaderboard, is a fold from history start. `catch-up` is the projection's **maintenance state** at `cov` advanced by a bounded, resumable interpreter over the suffix `(cov, p]`. It needs three things to exist: the maintenance state (a displayed maximum alone cannot absorb the deletion of its winner; the retained candidates can), a complete available suffix, and a local interpreter. An external projection may have none of these, and then the fallbacks are `wait` and `stale-ok` only. INBOX §4.6's rule is `catch-up` for the inbox *(placement)*.
3. **`wait` is a threshold read on the frontier** (§5.1's LVars reading). Its progress depends on the maintainer's progress, which is a liveness claim under the maintenance class's reserved share. It is not given by the read itself.

### 2.5 Projections as functorial data migration
**Construction.** A schema is a category `C` and an instance is a functor `C → Set`. A schema mapping `F : C → D` induces three migrations: `Δ_F` (reindexing, a pullback), its left adjoint `Σ_F` (union and quotient) and its right adjoint `Π_F` (join and universal quantification) (`spivak2010-functorial-data-migration.pdf`; with attributes and typed values, `schultz-spivak-vasilakopoulou-wisnesky2016-algebraic-databases.pdf`).

**What it predicts.** (a) **For the mappings it supports, the generator can emit a fold version migration** (STORAGE decision 1: "a new or changed fold may use an existing summary only through a valid bootstrap or migration rule"). Supported means renaming, reindexing, a projection onto fewer columns, or a union into a coarser table, with any value transformation supplied by the author and its semantic correspondence proved. A schema functor does not supply a string-splitting function, missing foreign-key values, or preservation of application observations (Astra 16). Interpretation changes still re-fold. (b) Selection versus materialization is not an adjunction, contrary to the brief's suggestion: the two are evaluation orders of one span composite (§3.1). The Σ/Π distinction is kept for §3.2, where it locates the decisions that need the order.

---

## 3. Selection, joins and inboxes: span composition

### 3.1 Every index is a span, and an inbox is a composite of spans
**Construction.** A keyed index is a span `A ← R → B`, where `R` is the set of stored rows. INBOX's structures are spans:
- a stream: `StreamId ← Entry → Event`, each entry carrying its commit position;
- `addr`: `Principal ← Addressing → Event`;
- a registration: `Consumer ← Edge → StreamId`, each edge carrying a start position and a policy.

Spans compose by pullback. The inbox of a consumer is the composite `Consumer ← Edge ×_{StreamId} Entry → Event`, which is `Σ_t ∘ Δ_s` in migration terms.

**Laws for free.** Composition is associative. It preserves disjoint unions, so the composite over a registration is the disjoint union of the per-edge composites. The fibre over an event is its reason set.

**What it predicts.**
1. **Selection, materialization, the per-edge hybrid and hubs are one construction** *(mostly placement: INBOX §§4.5-4.6 already specify per-edge caching with coverage)*. Selection evaluates the composite lazily. Materialization caches a summand of it. A hub caches a partial composite, which associativity permits. Twitter's celebrity hybrid and Feeding Frenzy's per-(producer, consumer) choice choose bracketings and summands. What the construction adds is the *reason* the raw decomposition is legal.
2. **The decomposition does not discharge the inbox contract (Astra 5).** The delivered inbox is not the raw composite. It also quotients duplicate events, unions their reasons, sorts by position, paginates, and proposes a cursor that is complete across every edge. Two individually correct edges can still produce a duplicate, omit a reason, or advance the cursor past an unread entry when combined. So per-edge equivalence is one lemma. Composition additionally needs the correctness of deduplication, the ordered merge, completeness cuts, policy intervals and authorization versions. **INBOX's differential whole-consumer check stays.** The tiny-profile "two edges, one switch" scenario remains the right smallest case.
3. **Authority recheck is a pullback** along "readable by principal at view-version v". It commutes with the disjoint union, so a materialized summand needs the same recheck. INBOX §4.2 says this in prose *(placement)*.

### 3.2 Universal quantification over a fibre: Π, and why such reads must name a version
**Construction.** `Π_F` computes "for all" over fibres: room members ↦ "every member has acknowledged p" (the meet of their ack frontiers); stored object ↦ "every retention requirement is discharged". `Σ` is monotone in its input. `Π` is not: adding an element to the fibre (a new member, a new obligation) can turn true into false.

**What it predicts.** Two laws the documents leave implicit. (a) **Every Π-shaped read names the version of the fibre it quantifies over.** "Seen by everyone" is relative to a membership version, and "releasable" is relative to the obligation set at a position. A Π answer without its fibre's version is unfalsifiable. (b) **Π-shaped decisions are made in the commit order.** STORAGE decision 3's release ("only when all applicable retention requirements and independent durable obligations permit it") is a Π over a fibre that commits can extend, so release must run in Decide at the domain's head. This is already true. The construction gives the general rule: Σ-shaped work (recording validated facts into a set, indexing, delivering) can be done anywhere and at any lag behind a frontier; Π-shaped decisions cannot (§5.1).

### 3.3 Competing consumers and claims: a partial function is not a semilattice
**Construction.** A claim assignment is a partial function `Entry ⇀ (Holder, Incarnation)`. Relations are closed under union; partial functions are not, because two claimants on one entry make a relation that is not a function. So claim state is not a join-semilattice. By CALM (§5.1), any implementation needs coordination: in fn2, the commit order of the queue's domain.

**What it predicts.** (a) A claim and the entry it claims belong to one commit domain, an instance of "one atomic mutation, one domain" that a cross-domain work queue would otherwise violate silently. (b) Kafka consumer groups (claims on partitions), SQS-style queues (claims on entries), MMO zone leases (claims on scopes) and helm's `work claim` (claims on dispatch rows) are **the same primitive at different grains**; PLANES §4.7 already observes this for leases. The "Lawvere theory of a queue" suggested by the brief predicts nothing beyond this (a FIFO's equational theory is non-commutative and fn2 never exposes dequeue as an operation). **Cut.**

---

## 4. Identity and content addressing: monos, semilattices, catamorphisms, Merkle clocks

### 4.1 Names are monos by assumption; two identities, because two quotients
**Construction.** A content name is a function `name : Bytes → Names` assumed injective (a mono) under a cryptographic assumption. A filter or short hash `h` is not a mono. Its kernel contains byte equality, so `h(x) ≠ h(y)` proves `x ≠ y` and `h(x) = h(y)` proves nothing. The physical page hash binds allocation context, so its kernel is "same bytes *and* same placement". Content identity must be invariant under relocation, so it factors through the quotient that forgets placement.

**What it predicts.** Nothing new; it confirms three of STORAGE's corrections in one line each. "A hash may reject, never decide" (§1) is the non-mono law. Content identity versus physical hashes (correction 10) are two maps with two different kernels, so they cannot be one field. Exact Message-ID octets are kept (decision 6) because a digest is not a mono onto Message-IDs. **Confirmation only.**

### 4.2 Merkle trees are catamorphisms over a declared shape
**Construction.** A tree hash is a catamorphism: a leaf algebra, a node algebra and a root finalization folded over a tree whose *shape is a function of the length*. In BLAKE3 the shape is the left-balanced binary tree over 1 KiB chunks (`oconnor2021-blake3-spec.pdf`). A range proof evaluates the same catamorphism on the covering subtrees and folds in the sibling values along the path to the root. The fusion law makes this sound.

**What it predicts.** (a) STORAGE correction 10 ("BLAKE3 range verification needs the reconstruction algorithm specified") is answered by specifying exactly three things: the shape function `shape(len)`, the two algebras, and the root flag. Partial final blocks and small objects are cases of `shape`, not extra rules. (b) PLANES §4.8's outboard tree *is the memo table of the catamorphism*: the stored intermediate values at chosen depths. The engine row per object holds the root, and verification granularity is the depth at which the memo is cut. A sequential hash (SHA-256 over the whole payload) has no such memo and cannot verify ranges. That is a reason, not a preference, for keeping tree hashes on payloads.

### 4.3 Identity as a Binding: validated evidence merged by union, and the peer convergence statement
**Construction.** A **Binding** is a multivalue map `B : Key → P_fin(ValidatedFact)`, ordered pointwise by inclusion and merged by union (a join; in a poset, joins are colimits). For Message-ID identity a fact is `(content identity, binding evidence)`, validated under the node's declared rules: signature, dependencies available, policy. The predicate `conflicted(mid) ⇔ |contents(mid)| ≥ 2` is defined on `B`. A node's local outcome for an offered `(mid, c)` is *Decide's* answer at its head: `stored`, `duplicate`, or `conflict` when some other content is already recorded. That is the case where `B(mid) = {c₁}` and `c ≠ c₁`, so the offer conflicts *before* the set reaches cardinality two (Astra 8). Mimram and Di Giusto (`mimram-digiusto2013-categorical-theory-of-patches.pdf`) show that a category of changes in which conflicting changes lack pushouts has a free completion under pushouts, where conflicts are objects that later merges compose with.

**Laws for free.** Union is associative, commutative and idempotent, so any delivery order and any duplication of *validated* facts converges.

**What it predicts.**
1. **The convergence statement, stated precisely (Astra 8).** *For any two nodes whose sets of validated identity facts are equal, `B` is equal and `conflicted` agrees.* What is assumed and stated separately: validation is deterministic in the fact and its declared dependencies, not in arrival order; and dissemination is eventual. What does not converge: first-arrival acceptance outcomes, local article numbers, and the choice of which content to serve. These are local Decide results. The teeth: a node that refuses a conflicting content *and records nothing* diverges from a peer that saw the two offers in the other order, and neither node ever learns of the conflict.
2. **A conflict refusal records evidence, under an admission contract.** STORAGE correction 5 lists "conflict state" as permanent identity metadata. The construction says that state is the set of conflicting content identities with their binding evidence, a portable fact peers forward. Recording it is a commit and needs a reservation: a per-Message-ID bound on retained conflicting identities, charged to the offering principal or peer, with a named refusal word when the bound is reached. It cannot become an unlimited permanent storage obligation imposed by any offer (Astra 8).
3. **Resolution never deletes.** A choice of which content to serve is a separate statement, and the served view is a fold over `B` plus resolution statements. Evidence stays monotone, and the choice lives in Decide on one node.
4. **Message-ID conflict and signer equivocation are one Binding.** fn's statement equivocation detection (`fn-sn-equivocatorp`, CLIENTS §2.2 item 4) is a Binding keyed by `(signer, previous-head)`. Both share the multivalue-map implementation, the union, the `conflicted` predicate and the convergence lemma. Their validation and key rules stay distinct.

### 4.4 Merkle clocks and vector clocks are two representations of one object
**Construction.** A consistent cut (§1.3) can be represented as a vector of per-domain heights (Mattern) or as the set of its maximal elements named by content hashes that commit to their causal past, a Merkle-DAG used as a logical clock (`sanjuan2020-merkle-crdts.pdf`).

**What it predicts.** The choice is an engineering trade, and the construction says exactly what is traded. A vector has size equal to the number of domains and compares in O(D), but needs a closed, enumerated set of domains. A head-set has size equal to the antichain width, admits an open population of writers, and compares by traversal. helm's per-signer previous-head chains (CLIENTS §2.1) and fabric records are head-sets with width one per signer. **Rule: inside a node with few commit domains, cursors are vectors (§1.3); across open peering and per-signer chains, references are head-sets.** Both satisfy the same down-closure law.

### 4.5 Provenance: sufficient dependency evidence per promised operation
**Construction.** A derived row is an arrow from its sources: `addr` and `inbox` values carry an event reference, and PLANES §4.5's `external-checkpoint` carries `(input-log range) → state digest`. Lineage composes.

**What it predicts, narrowed (Astra 16).** An earlier draft required every output row to carry the positions of all its sources. A balance may depend on millions of events, and an explicit source set would destroy the compaction the fold exists for. The law that survives: **each promised operation has sufficient dependency evidence.** That evidence may be an event reference (an inbox entry), a range (a checkpoint), a cut (a summary), keyed contributions or retained candidates (a retraction), or replay. Overview, `addr`, the inbox and external checkpoints already satisfy it *(placement)*.

---

## 5. Consistency, agreement and the planes: CALM, sheaves, semilattices, gradings

### 5.1 Merge, admission, retry and outcome are four properties; CALM speaks to the first
**Construction.** The CALM theorem (`hellerstein-alvaro2019-keeping-calm.pdf`): a problem has a consistent, coordination-free distributed implementation iff it is monotone. Bailis's invariant confluence (`bailis2014-coordination-avoidance-database-systems.pdf`) is the transactional form: operations can run without coordination iff every invariant is preserved when any two invariant-satisfying states are merged. LVars (`kuper2014-freeze-after-writing-quasi-deterministic-lvars.pdf`) give the discipline: joins as the only writes, threshold reads as the only deterministic reads, and `freeze` as the controlled escape.

**What it does and does not predict (Astra 6, 7).** An earlier draft concluded that monotone operations need no operation identity. That is false. Four properties of an operation are independent:
1. **merge**: is the state change a join of a validated fact?
2. **admission**: does it consume or reserve anything, or renew a lifetime?
3. **retry identity**: what makes two submissions "the same"?
4. **outcome evidence**: what durable answer is promised to the retrier?

Incrementing a counter is monotone but not retry-idempotent. A genuine join may still charge, allocate, renew or produce a response whose meaning changes on retry. Ack keeps its three outcomes (CLIENTS §1.1, INBOX §4.8):
- *accepted*: durable; equal retries are idempotent.
- *refused*: depends on lineage, registration epoch, principal, query and view versions, and the proposal's validity, none of which a max can check.
- *uncertain*: mutation is fenced until persistence resolves, and reapplying a max is not a resolution protocol.

Backfill progress lives under the proposal's identity. CALM concerns coordination-free computation of monotone results. It does not classify retry contracts, and it does not require a total commit order for everything else.

What survives, and is still worth having:
- **Where the commit order is required.** Choices that are not merges of validated facts: assigning local numbers, claims (§3.3), transfers under `balance ≥ 0` (not invariant-confluent), release and reclamation (Π, §3.2), and fence *allocation*. Fence *observation* is a max; allocating a new incarnation requires exclusive authority (Astra 6). These go through Decide, and peers cannot perform them independently.
- **What may be merged across peers without coordination.** Validated identity facts, conflict evidence, have-ranges and observed fences, as Bindings and Frontiers (§4.3).
- **The narrow op-id saving.** A pure join of a fixed authenticated fact may omit an *additional* generic op-id row when repeated application has the same promised observable effect under a stated retry contract. Ack does not need a generic op-id row, because it already has its proposal identity and durable cursor evidence. Ack still keeps its validation, its uncertainty recovery and its promised retry result. A later cursor proves coverage, not the original operation's outcome (Astra 7).
- **The deep reason behind "conflict as quarantine".** "One content per Message-ID" is a uniqueness invariant, the textbook non-invariant-confluent constraint (Bailis §5). fn replaces it with a monotone candidate set and a local Decide (§4.3), and that replacement makes identity exchange coordination-free. It is a general recipe that application uniqueness constraints (usernames, room aliases) can be offered.
- **Decide as its own interface.** The log orders; Decide chooses. Practitioners reach the same separation. In the "Event Sourcing is Hard" thread (HN 19072850), one comment reads: "I treated my commands (system inputs) as events, but ended up regretting it ... If I could do it again, I would have strictly separated the command and event ontologies, and adopted the concept of a command processor" (HN 19073810).

### 5.2 Sheaves: where local-to-global is real, and where it is decoration
**Construction.** A sheaf assigns data to the opens of a cover and requires that sections agreeing on overlaps glue uniquely. Contextuality is the existence of local sections with no global section (`abramsky-brandenburger2011-sheaf-theoretic-contextuality.pdf`). Robinson's consistency radius measures failure to glue (`robinson2016-sheaves-canonical-data-structure-sensor-integration.pdf`). Goguen models objects as sheaves over time (`goguen1992-sheaf-semantics-concurrent-interacting-objects.pdf`). Felber, Flores and Galeana characterize task solvability as the existence of global sections (`felber-flores-galeana2025-sheaf-theoretic-characterization-tasks-distributed.pdf`).

**What it predicts.** One thing: *no node can certify the global absence of a conflict from its local data.* An `ACCEPTED` or `DUPLICATE` answer is a statement about the node's own section of the Binding, and the outcome contract should say so. The rest is decoration and is **cut**. Witness checkpoints are an example: compatible hash-chain prefixes are a useful consistency check, but calling that a sheaf condition adds no witness authenticity, quorum or freshness guarantee, and STORAGE decision 4's concrete witness conditions stand as written (Astra 9). Robinson's metric radius, Goguen's sheaves over time (satisfied trivially by any journal) and the task-solvability frame predict nothing further for fn2.

### 5.3 The order of transient items on one node: specifiable exactly, not free
**Construction.** Schultz and Spivak's temporal type theory (`schultz-spivak2017-temporal-type-theory.pdf`; with `schultz-spivak-vasilakopoulou2016-dynamical-systems-and-sheaves.pdf`) takes behaviours as sheaves on the *interval domain*, whose points are intervals of possible times. A precise time is a degenerate interval.

**What it predicts, as an amendment (Astra 10).** PLANES §2.3 stamps a live item with "the installed commit position at its publication: a *happened-after* hint, not an order", while the ADDENDUM asks for "one stream, one order, both classes". On one node and within one epoch an exact order can be *specified*: durable item `q` sorts as `(q, 0)`, and a transient item published after install `p` sorts as `(p, s)` with `s > 0`. The interval reading suggests this. It does not follow from it, for two reasons. First, EXEC installs the root before incremental publication and notification, so a live publish can run between an install and the notification of that install's items. Second, PLANES's live sequences are per stream, so `(p, s)` can tie across streams. The amendment therefore has three parts:
1. `s` is drawn from a sequence whose scope is declared, node-wide or per stream. A node-wide sequence gives an exact multi-stream order; a per-stream sequence gives an order within each stream only, and says so.
2. The delivery merge is required to respect `(position, s)` despite delayed notifications, pagination and live gaps.
3. The simulator carries a scenario with a live publish between install and notification.

Across an `epoch-reset` or across nodes, the stamp is a genuine interval and stays a hint.

### 5.4 Semilattice data types: what fn2 must provide and what it need not
**Construction.** State-based CRDTs are join-semilattices with inflationary updates (`shapiro2011-comprehensive-study-crdts.pdf`). Monotone maps compose (Lasp). Delta-state CRDTs ship join-decompositions (`almeida2016-delta-state-replicated-data-types.pdf`). A general JSON CRDT shows the metadata cost (`kleppmann-beresford2017-conflict-free-replicated-json-datatype.pdf`).

**What it predicts.**
1. **A log of validated facts already serves as a delta stream** for fn2's own Bindings, have-ranges and observed frontiers: exchanging "the facts since your acknowledged cut" is δ-mutation. Nothing CRDT-specific is needed for them.
2. **Within one commit domain, collaborative editing can use server reconciliation instead of a CRDT**: optimistic local application, the server's order, and client rebase (`weidner2025-collaborative-text-editing-without-crdts-or-ot.txt`; its author in HN 44053560: "Storage is cheap, text is small, and you probably want a complete op log anyway"). This does not remove editing semantics or metadata (Astra 17). It needs unique *occurrence* identities, which content Names cannot provide since two identical characters share a Name, plus anchors that survive deletion (tombstones) and client-side reconciliation. fn2 supplies the order, Decide and the durable op log. The application supplies the element-identity scheme.
3. **Across domains, peers and offline clients, the application's fold declares the `merge` capability (§2.3).** fn2 stores and orders the opaque updates (helm's blind relay, CLIENTS §2.1) and can run the merge as a projection. A generic CRDT library is **deferred as a scope choice**: nothing in the mathematics forbids one, but no fn2 client has asked for one.

### 5.5 Consistency models: the lattice tells the API what to return
**Construction.** Viotti and Vukolić order non-transactional consistency models by strength (`viotti-vukolic2016-consistency-non-transactional-storage.pdf`).

**What it predicts.** fn2's surfaces sit at definite points:
- Decide is linearizable within a domain;
- `exactly-at(p)` is a snapshot at a prefix (§2.4);
- `at-least(p)` with `stale-ok` is bounded staleness measured in positions;
- a consumer has monotonic reads through a forward-only cut, and causal reads across domains once §1.3's down-closure law holds;
- live items are FIFO per epoch, within the scope of §5.3;
- peers converge on validated facts.

One API rule follows: **every outcome returns its position, and every read accepts a position with a strength.** Read-your-writes is then `at-least(position of my outcome)`, a threshold read that needs no session stickiness. That is still true after Astra's round; its precondition is §2.4's read contract.

### 5.6 Durability as a grading
**Construction.** Durability is a grade on publication, `transient < durable`, with the grade naming what survives a crash. Graded monads (`orchard-wadler-eades2020-unifying-graded-parameterised-monads.pdf`) index effects by an ordered monoid of grades.

**What it predicts.**
1. **Promotion that needs later content must carry it.** The ADDENDUM says "'placed' is a durable event whose payload *may* carry the trajectory's digest or the trajectory itself". If the durable record's meaning depends on the transient content later, it must inline that content or name it durably. A durable record may still hold an explicitly lossy `(epoch, seq)` reference (for example "reacted to live item (e, s)") provided its consumers read it as possibly unavailable, typed like any other gap (Astra's amendment to decision 5).
2. **Positions are grade-indexed types** (law L5, confirmed).
3. L1 as a reflective subcategory and L2 as a retraction rename the laws and predict nothing beyond them. **Cut.**

---

## 6. Obligations, protocols, leases and time domains

### 6.1 An obligation is a linear resource with an evidence formula
**Construction.** In linear logic a resource is used exactly once. `A ⊗ B` owes both; `A ⊕ B` owes one of two, the discharger choosing which. Wadler's propositions-as-sessions (`wadler2012-propositions-as-sessions.pdf`) reads such propositions as protocols.

**Laws for free.** Independent obligations on one object are separate resources in a `⊗`, so discharging one leaves the others standing. This is fn's "independent pins survive one another's release" (CLIENTS §2.2 item 6).

**What it predicts.**
1. **The generalized obligation kind has a definite shape:** `(creating event kind, holder, evidence formula, expiry (domain, value), on-expiry outcome)`. The evidence formula combines atomic predicates over committed events with `⊗` and `⊕`. Examples: `delivered(peer) ⊕ waived(operator)` for forwarding custody; `reply(dispatch-id) ⊕ cancelled(dispatch-id)` for helm's owed reply; `transfer(a→escrow) ⊗ transfer(escrow→b)` for escrow. With no `!`, no nested `⊸` and no quantifiers, a release check is decidable and bounded.
2. **The safety property, stated correctly (Astra 14):** *every created obligation is either outstanding or has exactly one authorized discharge.* It belongs to RECLAIM; no new checker is needed. Teeth: an obligation discharged by evidence and then also by an expiry that fires later in the same turn has two discharges. A late reply after a cancel finds nothing to discharge. **Eventual discharge is a separate liveness claim** under environmental assumptions: evidence becomes available, expiry is reachable. A finite trace ending with an outstanding obligation is legal.
3. **Retention pins, forwarding and BP custody, owed replies, escrow, claims and leases share one shape** *(partly placement: PLANES §4.7 already makes claims and leases obligations)*: one declaration, one safety property, one charging rule (EXEC rule 5) and one expiry service.

### 6.2 Protocols: shared state declarations now, session-type projection later
**Construction.** A multiparty session type (`honda-yoshida-carbone2008-multiparty-asynchronous-session-types.pdf`) is a global protocol. Projecting it gives each participant's local type, and well-formed projection gives safety and progress over asynchronous queues. Resource-aware session types charge for each step (`das2019-nomos-resource-aware-session-types-digital-contracts.pdf`).

**What it predicts (amended after Astra 18).** The consumer protocol E3 must specify (EXEC §7a item 4) is naturally a finite protocol table:

```
register(edges) → registered(epoch) | refused(word)
then repeatedly:
  poll(cut)            → items(…, next-cut, more?) | rebase-required | refused(word)
  wait(timeout)        → woken | timed-out
  ack(cut, proposal)   → acked | stale | uncertain(position)
  edit(edges)          → edited(query-version) | refused(word)
  cancel               → end
```

**Worth doing in 5.1.1:** one declared table of protocol states and legal request/reply transitions for each served protocol (NNTP, the consumer protocol, later peering), read by the parser, the machine, the client library and the WIRE/CONSUMER checkers, so that it is written once. **Deferred:** global multiparty projection machinery and a session type checker. **Corrected:** unknown branch labels are *not* automatically safe to ignore (Astra 18). The existing "ignorable by contract" rule for reason codes and gap causes holds because those labels were *declared* ignorable. A new reply branch that changes what the client must do is a new protocol version.

### 6.3 Leases and fencing: define authority at commit
**Construction.** A fencing token is a number the granting authority increments on each grant. The protected resource accepts a write iff its token is at least the highest it has seen (`kleppmann2016-how-to-do-distributed-locking-fencing.txt`: "you need to include a fencing token with every write request"). Highest-seen is a max-register; *allocating* the next token requires exclusive authority (Astra 6).

**What it predicts, narrowed (Astra 12).** An earlier draft said every safety property rests on the commit order and fencing. That is too broad: ownership, authorization and integrity have their own invariants. It is also too narrow about fencing. Highest-seen rejects an old holder only after the sink has learned the newer token, so if expiry itself ends authority, a write that arrives after expiry but before any replacement must also be refused. The law that survives: **each lease declares whether its authority ends at committed expiry, at revocation, or only at supersession, and Decide checks that authoritative state at commit.** Fencing guarantees that superseded holders cannot act. Time-dependent authorization is declared, never abolished. The simulator's clock-jump and pause faults exercise both.

### 6.4 Time domains: deadlines as first crossings
**Construction.** A time domain `D` is given by a map `τ_D : NodeTime → D`, piecewise between rate events anchored at commit positions (PLANES §4.6). A deadline `d` converts to node time as the first crossing `τ_D^♭(d) = min { t | τ_D(t) ≥ d }`. Where that minimum exists for every `d`, `τ_D^♭` is the lower adjoint of a Galois connection, and nested domains compose contravariantly: `(τ₂ ∘ τ₁)^♭ = τ₁^♭ ∘ τ₂^♭`.

**What it predicts, corrected (Astra 11).** A non-negative rate is not sufficient. `τ(t) = 0` is monotone and continuous, yet the deadline `1` has no finite preimage. And non-negative slopes still allow a backward jump at a new anchor. The laws:
1. `τ_D` is **monotone across anchors**: a rate event or re-anchoring that would move the domain clock backwards is refused by name;
2. an **unreachable deadline is represented explicitly**, never as a sentinel time;
3. a pause (rate 0) delays only *unreached* deadlines, while deadlines already reached fire immediately;
4. because future rate events are unknown, a converted deadline is **provisional**: it is recomputed on every relevant mapping change, including changes to ancestor domains, and revalidated at firing (PLANES already re-arms on rate events; revalidation at firing is the addition).

---

## 7. Lenses: folds are the get side

### 7.1 Folds are the get side; commands are not a lens by being deterministic
**Construction.** A lens is a pair `get : S → V`, `put : V × S → S` satisfying GetPut, PutGet and PutPut (`foster2007-combinators-bidirectional-tree-transformations-lenses.pdf`). Delta lenses make `get` a functor between categories of states and updates and `put` a lifting of view updates (`diskin-xiong-czarnecki2011-delta-based-bidirectional-transformations.pdf`). Lenses are algebras for a monad, and c-lenses are split opfibrations (`johnson-rosebrugh-wood2012-lenses-fibrations-universal-translations.pdf`). Delta lenses are coalgebras for a comonad (`clarke2021-delta-lenses-coalgebras-comonad.pdf`). Optics generalize them (`riley2018-categories-of-optics.pdf`).

Let `J` be journal prefixes with appends as morphisms, and `V` a projection's states. The fold is a functor `get : J → V`, which is **free** (§2.1).

**What it predicts, after Astra 13.** The put side is not free. A deterministic Decide can reject an update, choose an unauthorized change, or implement the wrong view change; determinism proves none of the lens laws. General view updates may have no legal lift. GetPut is also false as a rule for fn2: a command with no visible view change may still owe a durable outcome, an audit event or a binding record, so for a lens over journal prefixes that append is not the identity. And delta-lens composition concerns lifting composed updates; it has nothing to do with retry deduplication. What survives:
1. **Commands carry preconditions and observable postconditions.** Consequential commands get independent postconditions, checked by the simulator against the folded result. This is the useful content of "PutGet".
2. **The expected-prior-version binding is a precondition at a source** *(placement: STORAGE decision 1)*. When the head moves, Decide recomputes at the new head (rebase) or refuses by name. Server reconciliation (§5.4) is the same recomputation.
3. **A partial delta lens is claimed only for an explicitly restricted update language with proved lifting laws.** One candidate: field-level edits of a declared record schema, where the lift is "append the edit event", proved once. Nothing more general is claimed.

So the brief's question gets a split answer. "The log is the only authority, folds are views" is a lens law on the get side by construction. On the put side it is a contract of pre- and postconditions, and a lens only in restricted cases.

---

## 8. Ownership and the byte pool: a resource algebra

### 8.1 Pool ownership is a partial commutative monoid with an authoritative element
**Construction.** Iris's resource algebras (`jung2015-iris-monoids-invariants-orthogonal-basis.pdf`; `jung2018-iris-from-the-ground-up.pdf`) model ownership as a partial commutative monoid: disjoint pieces compose, and a state change is legal iff it is a **frame-preserving update**. The authoritative construction pairs a full element `●a` held by the owner of the truth with fragments `◯b` held by others, under the invariant that every fragment is included in `●a`. Fractional permissions split read access into shares.

The mapping is direct:
- the core holds `●(pool state)`;
- a receive or read loan is an exclusive fragment lent to the host;
- a send or write loan is a fractional fragment, and reuse waits until every fraction returns;
- the generation is the authoritative version, so a fragment from an older generation is rejected.

**What it predicts, narrowed (Astra 14).**
1. **OWN as frame preservation over the loan kinds that exist.** "Every transition is a frame-preserving update" is the checker's statement. A *generic* camera-declaration language is deferred until a new loan kind (a datagram receive, PLANES §4.3) shows the duplication it would remove.
2. **Linearity applies to ownership rights, not to every handle-shaped value.** Generation checks reject stale handles; they do not reject a duplicated *current*-generation ownership token. Some handles are legitimately shared references. The machine DSL therefore marks **ownership-token fields** (loans, leases, reservations) as linear and checks keep, transfer or release on every transition, which is "assert, never absorb" made mechanical. Plain references stay unmarked.
3. **The byte-fill theorem stays its own obligation.** Frame preservation shows a loan returned legally. It does not show that a completion exposes exactly the bytes that were written. EXEC §4's byte-fill correspondence remains necessary.
4. Obligations (§6.1) and object leases are fragments of the same kind of authority, and "a BODY acquires its storage lease before its success status" is "a promise is made only while holding a fragment" *(placement)*.

---

## 9. The algebra of fn2

### 9.1 Eight named interfaces over four irreducible ones
Astra's first attack (§13, item 1) holds: some of these are specializations of others. Frontier, Binding and Span are Folds with particular state algebras, and Obligation is a Fold whose transitions are guarded by Decide. The table keeps all eight because each has laws that users and checkers program against. The **irreducible** column marks the four that are not specializations.

| interface | irreducible? | construction | laws (section) | what it builds |
|---|---|---|---|---|
| **Log** (per commit domain; items graded `durable`/`transient`) | yes | free monoid `E*`; positions are prefixes; across domains, cuts in a lattice of down-closed sets | append associative with unit; prefix stability (§1.1); one atomic batch in one domain by architecture, not algebra (§1.1); multi-domain cursors are down-closed cuts (§1.3); durable dependencies on later content inline or name it, and lossy references are typed (§5.6) | every stream: rooms, match inputs, ledgers, queues, mixed VR streams |
| **Decide** | yes | the serial command processor at one domain's head | a function of (head state, command); preconditions and postconditions per command (§7.1); the binding is a precondition and a moved head means rebase or named refusal; locus of every choice that is not a merge of validated facts (§5.1); retry identity, admission and outcome evidence declared per operation, not inferred from monotonicity (§5.1) | accept/duplicate/conflict, transfers, claims, releases, fence allocation, promotion, server reconciliation |
| **Fold** | yes | right action of `E*` on a state set; minimal summary is the image in a final coalgebra | action law, i.e. the summary equation (§2.1); a summary is adequate iff it preserves future observations, certified locally by a homomorphism (§2.2); declared capabilities (retraction, merge, duplicate tolerance) when used (§2.3); `mode` explicit and bounded (§2.3) | balances, read-state, catalogs, character sheets, document state, overview, latest checkpoint per scope, time-domain clocks |
| **Name** | yes | content commitment, a mono by assumption, computed as a catamorphism over `shape(len)` | a hash refutes and never decides (§4.1); range proofs are sub-catamorphisms; the outboard tree is the catamorphism's memo (§4.2) | payloads, large objects, Merkle logs and checkpoints |
| **Binding** | no: a Fold with union | multivalue map `Key → P_fin(ValidatedFact)` | merge by union; `conflicted ⇔ ≥ 2`; convergence for equal validated fact sets (§4.3); conflict evidence recorded under an admission bound; resolution never deletes | Message-ID identity, signer equivocation, application uniqueness offered as candidates plus Decide |
| **Span** | no: a stored relation | span `A ← R → B`; composition `Σ∘Δ`; `Π` for universal reads | associative; distributes over disjoint unions, which legalizes per-summand evaluation while the inbox contract keeps its whole-consumer check (§3.1); a Π-read names its fibre's version and Π-decisions run in Decide (§3.2) | `addr`, membership, edges, inboxes, hubs, have-ranges |
| **Frontier** | no: a join-semilattice Fold | position (max), vector cut, head-set (Merkle clock); an LVar | threshold reads (`wait`, timers, `at-least(p)`); `exactly-at(p)` needs version state (§2.4); vectors inside a node, head-sets across open peering (§4.4) | cursors, coverage, wake, timers, read-your-writes |
| **Obligation** | no: a Fold guarded by Decide | linear resource with an `⊗`/`⊕` evidence formula; with holder and incarnation, a claim or lease | outstanding, or exactly one authorized discharge (safety); eventual discharge is liveness under assumptions (§6.1); lease authority defined at commit, fencing for supersession (§6.3); release is Π-shaped and runs in Decide | retention pins, custody, owed replies, escrow, claims, leases, object leases |

**Outside the algebra, and not replaced by it** (Astra's addition): EXEC's bounded execution (work caps, budgets, continuations); reservation before work and per-principal accounting; adapter ownership of loaned bytes (§8); and the persistent `uncertain` state with the commit machine's prepare, fence, install and recovery protocol. An abstract append is a successful commit; the commit machine is how fn2 earns the right to call it one.

### 9.2 Former mechanisms as compositions
| mechanism | composition |
|---|---|
| stream | Span `StreamId ← Entry → Event` over a Log |
| subscription, wait, wake | Span of edges plus a threshold read on each edge's stream Frontier; the wake is a hint because the threshold read is re-checked (INBOX's final frontier check) |
| inbox, `addr`, hub, per-edge policy | Span composite, with chosen summands cached as Folds with their own Frontiers, under INBOX's whole-consumer contract |
| claim, lease, consumer-group partition | Obligation with exclusive holder and incarnation, decided in the claimed entry's domain |
| timer, deadline in game time | threshold read on a time-domain Fold, through the first-crossing conversion (§6.4) |
| external checkpoint | Decide (predecessor and authority check) appending a Name (snapshot) and an input range, under a lease Obligation |
| promotion of transient to durable | Decide appending a durable event that inlines or names the content it depends on |
| signed record with a previous-head chain | Log event plus Name, with a Binding on `(signer, previous-head)` |
| pinned version | an `exactly-at(p)` read with a retention hold; an object lease is an Obligation fragment |

### 9.3 What the eight build
| target | composition | what it gets that hand-rolled versions usually lack |
|---|---|---|
| **helm's rooms** | rooms as Log streams; `addr` and membership Spans; seat cursors and waits as Frontiers; dispatch rows as Obligations (`reply ⊕ cancelled`) with Decide keyed by dispatch id; premises and fabric records as Names with a `(signer, previous-head)` Binding; presence as transient items | a mention in any room wakes the seat through one edge; joins "from now" without a rebase; owed replies with checked discharge; equivocation recorded as a fact |
| **Wild Earth's catalog** | tile packages as Names with outboard trees; the catalog as an after-commit Fold with retained candidates behind a Frontier; a region/species Span; have-ranges as a merge-capable Fold; work queues and tile ownership as claims and leases | range reads under leases; catalog reads with stated strength; peers converge on have-ranges and identities without coordination |
| **an RTS match stream** | a Log of input batches; the simulation's content identity as a Name; the result through Decide; the relay under a lease | replay and audit as consumers; a zombie relay's result refused `fenced` |
| **a VR room with interwoven durability** | one Log stream with both grades; Decide promotes "placed" with the trajectory inlined or named; Folds for "who is here" (transient) and "what was built" (durable) | one subscription; an exact mixed order on the node when §5.3's amendment is adopted; typed loss |
| **a collaborative document** | in one domain: a Log of operations addressed by application-assigned occurrence identities, Decide for order and binding (server reconciliation), a Fold for state; across domains: a merge-capable Fold the application declares | no CRDT metadata where a server order exists; the application keeps its element identities and tombstones either way |
| **a mailbox** | `addr` Span plus edges; the inbox as a Span composite; ack with its proposal identity and three outcomes; read-state as a retraction-capable Fold | delivery work proportional to delivered items; read-your-writes by position |
| **a work queue** | a queue Log; claims as Obligations with incarnations; Decide for claim, result and dead-letter | at most one authoritative holder; late results refused by name; nothing lost at expiry |
| **a ledger** | a journal Log; transfers via Decide (`balance ≥ 0` is not invariant-confluent); balances as a retraction-capable Fold; signed Merkle checkpoints as Names; escrow as `⊗` Obligations | exact retries via operation identity; a summary certified by per-event-kind equations; independently verifiable history |

---

## 10. The three DSLs and the ten operations

### 10.1 What the constructions imply for each DSL (sized by Astra's cost table, §11)
**Records and columns (`defcolumns`) are attributed C-sets.** A schema is a small category: tables are objects, foreign keys are morphisms, typed columns are attributes. One array per table and column is the struct-of-arrays representation (`patterson-lynch-fairbanks2021-categorical-data-structures-acsets.pdf`, from `schultz-spivak-vasilakopoulou-wisnesky2016-algebraic-databases.pdf`). This matches REVIEW-SINS's "fields addressed by name, never by position; a layout compiled into a codec". Implied now:
- a foreign key is declared as a morphism to a named table, with a generation-checked handle value, so referential integrity is a declared, checked property;
- a span is a two-foreign-key table, so `addr`, edges and stream entries are ordinary declarations.

Deferred: generated `Δ`/`Σ` migrations, until a fold version change needs one (§2.5).

**Machines (`defmachine`) are coalgebras with budgets.** A machine kind is a coalgebra for `X ↦ (Observation → X × Actions)` under a work cap. EXEC §5's correspondence between the stobj and ATC realizations is then a per-transition simulation, the same local proof shape as §2.2. Implied now:
- `linear` on ownership-token fields (loans, leases, reservations), with keep, transfer or release checked on every transition (§8.1);
- `acquires`, the admission bundle in the global resource order (§1.4);
- the machine's protocol states read from the shared protocol table (§6.2).

Deferred: precise per-transition `footprint`s, until fusion or the simulator's partial-order reduction consumes them. The default is the whole semantic state (§1.2).

**Command grammars are syntax plus protocol plus Decide.** Each command entry declares:
- the protocol states in which it is legal (from the shared table);
- its Decide function;
- its retry identity, admission and outcome evidence, written explicitly and never inferred from monotonicity (§5.1);
- its preconditions and observable postconditions, the postconditions independent for consequential commands and checked by the simulator (§7.1);
- its refusal words.

NNTP, the consumer protocol and later peering are protocol tables over one grammar DSL, so layer A's ownership of the forms extends to every protocol.

### 10.2 The ten operations a friend reaches for
1. **`append(stream, items, grade = durable)` → positions.** The batch is atomic in one domain, and positions are prefix-stable. Transient loss is typed, and the mixed order is as specified in §5.3. *Against Kafka:* durability per item on one stream, exact identity, and no second pub/sub system for the ephemeral half (Third Room's seam).
2. **`command(domain, op, op-id?, expect = version)` → outcome at a position.** Serial at the head. Retry identity and outcome evidence are declared per operation. A failed binding is a named refusal or a rebase. `uncertain` is resolved by position. *Against Postgres:* a transaction, an idempotency key and a durable outcome, built in rather than application-side.
3. **`put(bytes)` → name; `get(name, range, lease)`.** Idempotent and deduplicated. Ranges verify against the name. A held lease prevents loss through reclamation. *Against Redis and Postgres:* content-addressed, range-verifiable large values with leases.
4. **`project(declaration)` → projection id.** Sources, key schema, interpretation, explicit mode, coverage, the capabilities used, and observations by reference where history is discarded. Contract: for every maintenance schedule, `at-least(p)` reads equal the interpretation folded over the sources at or below the answer's position. *Against Postgres:* a materialized view that is incremental and has a published frontier. *Against Kafka Streams:* the same, without a second cluster.
5. **`read(target, at = p, strength = exactly | at-least, fallback = wait | stale-ok | catch-up)` → value at a position.** The answer states its position and strength. `exactly` needs version state, or reports a gap. `catch-up` needs maintenance state and an available suffix. *Against Redis and Postgres replicas:* read-your-writes and monotonic reads by passing back a position.
6. **`seek(stream, after = cut, limit)` → entries, next cut, `more`.** Entries come in position order, complete through the returned cut. Gaps appear only for declared retention or bootstrap. *Against Matrix /sync:* no composite tokens, no `limited` gaps, and cost proportional to the entries delivered.
7. **`subscribe(edges)`; `wait(timeout)` → woken or timed out.** Edge changes are log events. A lost wake costs latency, never an item. *Against Redis pub/sub and Postgres LISTEN/NOTIFY:* the wake carries no data, and the next read is a threshold read.
8. **`ack(cut, proposal)` → accepted | refused | uncertain(position).** Forward-only. Validated against lineage, registration epoch, principal and versions. Retries use the proposal identity. The cut must be down-closed. *Against Kafka:* offsets that do not expire under a quiet consumer (KAFKA-4682), and one cut across many streams.
9. **`claim(entry | scope, expiry)` → incarnation; results carry it.** At most one authoritative holder. Authority ends as declared (§6.3). A superseded incarnation is refused `fenced`. Expiry re-offers the entry with an attempt count and a dead-letter rule. *Against Redis Streams' XCLAIM and SQS:* fencing, and an authority defined at commit.
10. **`oblige(kind, subject, evidence, expiry)`.** Outstanding, or discharged exactly once by authorized evidence, waiver or expiry. Charged to its creator. *None of the four systems has this.* Owed replies, custody, escrow and retention are one checkable primitive.

### 10.3 Against the systems a friend already knows
| | Kafka | Postgres | Matrix | Redis | fn2 |
|---|---|---|---|---|---|
| ordered history | per partition; retention by time | WAL, internal | per-room DAG | Streams, in memory | per commit domain, durable, with a signed Merkle checkpoint |
| exact retry of a command | idempotent producer and transactions inside Kafka; no stored application outcome | application idempotency keys | transaction ids per device | none | declared retry identity and durable outcome per command |
| derived views | Kafka Streams (separate) | materialized views, manual refresh | server-side, not declarable | none | declared projections with frontiers and two read strengths |
| multi-stream cursor | per-partition offsets | none | composite sync tokens | per-stream IDs | one down-closed cut over many streams |
| wake without loss | poll | LISTEN/NOTIFY, lost across restarts | long-poll /sync | pub/sub, at most once | edges plus threshold reads; a lost wake costs latency only |
| exclusive work with fencing | group rebalancing | `FOR UPDATE SKIP LOCKED`, no fencing token | none | XCLAIM, no fencing | claims with incarnations and declared authority |
| evidence-gated obligations | none | none | none | none | Obligation |
| transient and durable in one stream | no | no | separate ephemeral events | separate pub/sub | per-item grade in one stream |
| cross-node convergence | replication of one log | logical replication | state resolution | replication | validated facts merged by union, conflicts recorded |

---

## 11. The cost: where the constructions are too general, and what the engineering chooses

Categorical designs usually fail by implementing the general construction instead of the instance the system needs. When CQL, the one shipped categorical database, reached HN (30075577, 2022), the best response it drew was the question of why not just relational algebra. The first table names the instance fn2 uses; the second is Astra's sizing of the declared fields for the 5.1.1 slice, adopted whole.

| construction | too general because | fn2 uses | not built |
|---|---|---|---|
| event structures, presheaf models, open maps | arbitrary causality and conflict; bisimulation over presheaves | one domain in 5.1.1 with scalar positions; vector cuts only once a second domain exists | event-structure merging; open-map checking |
| antichain frontiers (Naiad, differential dataflow) | multidimensional progress tracking | one order per domain | timestamp-lattice progress tracking |
| observational quotient | the minimal summary is not computable in general | author-declared summaries, certified by per-event-kind equations where they hold, by a simulation otherwise | quotient computation |
| DBSP | Z-set weights, recursion, indexed join state | capabilities declared when used; hand-written folds | a general incremental engine in the core |
| functorial migration | arbitrary schema functors; Π can blow up instances | supported mappings with supplied value transformations, when a migration is needed | CQL as a user language |
| sheaves | general sites and cohomology | one sentence in the outcome contract (§5.2) | everything else |
| session types | checkers, higher-order sessions, projection algorithms | shared protocol tables | MPST projection; a type checker |
| linear logic | exponentials, nested implication | `⊗`/`⊕` over atomic evidence predicates | proof search |
| resource algebras | higher-order ghost state | OWN as frame preservation over existing loan kinds | a camera-declaration language |
| graded monads | arbitrary grade monoids | two grades | more classes |
| directed topology | trace spaces | a global acquisition order | geometric analysis |
| CRDT libraries | each type is a policy with its own metadata | a merge capability on folds; server reconciliation | a shipped library (deferred, a scope choice) |

**The declared fields, sized for 5.1.1 (Astra, item 18, adopted):**

| field | worth doing now | cut or defer |
|---|---|---|
| `observes` | references to existing contract observations, for summaries that discard history | a separately maintained observation list on every projection |
| `linear` | lifecycle checks on ownership tokens for pool loans and resources | blanket linearity of handles; a generic camera-declaration language |
| `session` | shared finite protocol states and legal request/reply transitions | global multiparty projection; treating unknown branch labels as safe to ignore |
| `footprint` | conservative effects where a current check needs them | precise per-transition declarations before fusion or partial-order reduction uses them |
| `algebra` | optional proved merge and retraction capabilities, when exercised | a mandatory three-way enum; derived mode |
| `lineage` | existing event references and checkpoint ranges | source sets on every aggregate row |
| `view effect` | independent postconditions for consequential commands | a generic lens-law field; a universal "no-op commits nothing" rule |

Handwritten bounded folds and the existing projection declaration stay. DBSP generation, categorical migrations and general session projection wait until an implemented consumer shows the duplication they would remove. A default does not establish correctness: a `monoid` default in particular proves nothing, so defaults are chosen to be safe and slow (whole-state footprints, mode explicit) and never claimed as evidence.

---

## 12. Five decisions for ember

Each is the draft's decision amended by Astra's verdict (§13), with a recommendation.

1. **Vocabulary.** Use eight named interfaces as fn2's provisional semantic vocabulary: Log, Decide, Fold and Name, which are irreducible, and Binding, Span, Frontier and Obligation, which are specializations with named contracts. Document every mechanism as a composition of them (§9.2). Keep EXEC's operational contracts (bounds, reservation, loan ownership, persistent uncertainty) beside them as a separate layer. Make no minimality claim and no "admit an eighth only with laws" rule. *Recommended yes*: it gives friends one map of the system and gives the documents a shared vocabulary, at the cost of rewriting nothing.
2. **The read contract.** Every read names a strength: `exactly-at(p)` (needs version state, or a snapshot plus replay, and reports unavailable history as a gap) or `at-least(p)` (a threshold read on coverage). The fallbacks are `wait`, `stale-ok` and `catch-up`, where `catch-up` requires maintenance state and an available suffix. Every outcome returns its position, so read-your-writes is `at-least(my position)`. Projection `mode` stays explicit and bounded. Summaries that discard history name their observations by reference to the existing contract observations and are certified per event kind where the homomorphism equations hold. *Recommended yes*: it fixes the inherited `cov ≥ p` defect in PLANES §2.2 before the projection plane is built on it.
3. **Identity as a Binding, and four properties per operation.** Validated identity evidence is merged by union. A conflict refusal records its evidence under a per-Message-ID admission bound with a named refusal word. Message-ID conflicts and signer equivocation share one Binding with distinct validation. Peer convergence is stated for equal validated fact sets, with dissemination assumed separately. Every operation declares merge, admission, retry identity and outcome evidence separately. Ack keeps its three outcomes and uses its proposal identity rather than a generic op-id row. *Recommended yes*: it gives peering the convergence statement CLIENTS lists as missing, and it removes a divergence bug (silent conflict refusal) before it can ship.
4. **Protocols and commands.** Keep one table of protocol states and transitions for each served protocol (NNTP, consumer, later peering), shared by parser, machine, client library and checkers. Every command declares its legal states, its Decide, the four properties above, and its preconditions and observable postconditions, which the simulator checks for consequential commands. Defer session-type projection and lens laws; claim a partial delta lens only for a restricted, proved update language. *Recommended yes, scoped*: it writes each protocol once, and leaves the type-theoretic machinery for later.
5. **The planes and time.** Durable records whose meaning needs later content inline it or name it durably; lossy `(epoch, seq)` references stay legal and are typed. Mixed delivery order is specified as durable `(q, 0)` and transient `(p, s > 0)` with a declared sequence scope, and tested by a scenario that publishes between install and notification. Each lease declares when its authority ends, checked at commit, with fencing against supersession. Time-domain clocks are monotone across anchors, unreachable deadlines are explicit, a pause delays only unreached deadlines, and converted deadlines are revalidated at firing. A generic CRDT library is deferred as a scope choice. *Recommended yes*: each item is a sentence in an existing brief plus one simulator scenario, and each closes a defect that would otherwise ship.

---

## 13. Astra's round, folded in

One round, `codex exec -m gpt-6-astra --sandbox read-only` on the first draft. The prompt is `fn2/universal-astra.prompt`, the answer is `fn2/universal-astra.md` (Astra's words) and the log is `fn2/universal-astra.log`. Astra's verdict, verbatim: "**Do not adopt §12 as written.** The useful result is a vocabulary of reusable contracts. The claimed minimal basis and several 'laws for free' do not follow. The largest engineering mistake is turning sufficient proof techniques into mandatory declarations and operational policies."

| # | Astra's attack | severity | disposition | where |
|---|---|---|---|---|
| 1 | seven is not a floor; Frontier, Span and Obligation are specialized Folds; Name bundles commitment with binding; EXEC's operational contracts are missing; products of free monoids exist | material | accepted: eight interfaces over four irreducible; Binding split from Name; operational layer named; one-domain restated as architecture | §0, §1.1, §9.1 |
| 2 | the homomorphism is sufficient, not necessary (the `(n mod 2, 0)` counterexample); the Merkle frontier does not give inclusion proofs | material | accepted | §2.2 |
| 3 | an algebra class neither classifies states nor derives mode | material | accepted: classification withdrawn; capabilities declared when used; mode explicit | §2.3 |
| 4 | the Kan calculation is right but operationally empty; `catch-up` needs maintenance state; `cov ≥ p` does not give exactly-at-`p` | material | accepted, including the inherited PLANES defect; the two read strengths adopted | §2.4, §5.5, decision 2 |
| 5 | coproduct preservation does not discharge dedup, merge, cursor completeness | material | accepted: whole-consumer differential check stays | §3.1 |
| 6 | CALM does not determine op-id requirements; counters; fence allocation needs exclusive authority | **fatal** | accepted: four properties per operation | §5.1 |
| 7 | ack is not a max under its three outcomes | **fatal** | accepted: ack keeps its outcomes and proposal identity | §5.1, §10.2 |
| 8 | convergence is underspecified; the outcome formula mismatches; conflict evidence needs admission | material | accepted: validated facts, the `conflicted` predicate, an admission bound | §4.3 |
| 9 | Binding contradicts event-structure conflict; fact equality is not open-map bisimulation; the witness "sheaf condition" adds nothing | material | accepted: choices versus observations; open maps kept only as motivation; sheaf condition cut | §1.3, §5.2 |
| 10 | exact local order is not free: install precedes notification, and per-stream sequences tie | material | accepted as an amendment with a declared sequence scope and a scenario | §5.3 |
| 11 | adjoint existence conditions are wrong (`τ = 0`); anchors can jump back; pauses; provisional deadlines | material | accepted | §6.4 |
| 12 | fencing does not supply every safety property; expiry-ended authority needs a commit-time check | material | accepted | §6.3 |
| 13 | Decide is not a lens by being deterministic; GetPut fails for commands that owe outcomes; PutPut is not retry dedup | **fatal** | accepted: pre/postconditions; partial delta lens only for a restricted, proved update language | §7.1 |
| 14 | linearity proves neither eventual discharge nor byte-fill; generation checks do not stop duplicated current tokens | material | accepted: safety and liveness split; linearity on ownership tokens only; byte-fill stays | §6.1, §8.1 |
| 15 | footprints are sufficient approximations, and the safe default is the whole semantic state | material | accepted | §1.2, §10.1 |
| 16 | universal lineage and automatic migration overpromise | material | accepted | §2.5, §4.5 |
| 17 | several predictions restate existing requirements; Weidner's rebase needs occurrence IDs and tombstones | minor | accepted: such items marked *(placement)*; element identities belong to the application | §0, §5.4 |
| 18 | declared fields cost more than "one field" | material | accepted whole: Astra's field table | §11 |

**Astra's four additions, all adopted:**
- the read-contract distinction (§2.4, decision 2);
- the peer-evidence contract (§4.3, decision 3);
- the persistent uncertainty model kept beside the algebra (§9.1);
- executable counterexamples for each adopted law, listed below as simulator scenarios.

**Simulator scenarios that refute each adopted law if it is false** (tiny profile; added to the existing scenario list, run by the existing checkers):
1. two inbox edges that overlap on one event, with one edge materialized behind its `cov` and a page boundary on the overlap (CONSUMER: no duplicate, no lost reason, no cursor past an unread entry);
2. an ack whose commit is `uncertain`, retried after recovery with the same proposal and with a later cut (CONSUMER: the original outcome is reported, and a later cut does not stand in for it);
3. a summary with a hidden component that is observationally irrelevant, and one that is relevant (HISTORY: the first passes by simulation and the second is caught by the identity-decision suffix);
4. a live publish between an install and its notification, on two streams (CONSUMER: order as declared by the sequence scope);
5. a paused and then re-anchored time domain with one deadline reached before the pause and one after (TRACE: the reached deadline fires, the unreached one waits, and a backward re-anchor is refused);
6. two nodes receiving conflicting contents for one Message-ID in opposite orders (IDENTITY: equal Bindings, `conflicted` at both, and the admission bound refusing a third conflicting content by name).

**Where this note and Astra still differ.** Nowhere on substance. One difference of emphasis remains. Astra calls the eight "provisional interfaces"; this note keeps them as the *user-facing vocabulary*, the names a friend from Kafka or Postgres learns first, while agreeing that they are not a minimal basis. The four irreducibles and the merge/Decide boundary (which choices need the commit order) are the parts of the algebra that survived the attack intact.

---

## 14. Bibliography

All sources are in `~/paperbin/` under the filenames cited inline. The 39 fetched for this note are annotated, with what each predicts for fn2, in the "Universal constructions" section of `~/paperbin/README-fn2-20261028.md`. Reused from earlier passes: `budiu2023-dbsp-automatic-incremental-view-maintenance.pdf`, `almeida2016-delta-state-replicated-data-types.pdf`, `shapiro2011-comprehensive-study-crdts.pdf`, `jung2018-iris-from-the-ground-up.pdf`, `das2019-nomos-resource-aware-session-types-digital-contracts.pdf`, `oconnor2021-blake3-spec.pdf`, `opentimestamps2026-docs-merkle-mountain-range.md`. Practitioner threads, via Scry over `hackernews.items`: 19072850 ("Event Sourcing is Hard"; comment 19073810 quoted in §5.1), 44053560 ("Collaborative Text Editing Without CRDTs or OT"; comment 44057497 quoted in §5.4), 30075577 (CQL). The gaps (Malcolm 2009, Kuper-Newton 2013, Katsumata 2014, Gray-Cheriton 1989, the Fajstrup et al. book) and their stand-ins are listed in that README section.
