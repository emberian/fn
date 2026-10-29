# fn2's squares and their generators: a coherence theorem for the frame (2026-10-28; Opus researcher with Astra as co-author; present state)

Brief: `build/coordinator/briefs/COHERENCE-20261028.md`. Ember, verbatim: "is transport across versions the only thing it'd buy us? or is that just the foundation for much more general and powerful system? ... i feel like coherence conditions or something else maybe could be useful."

The coordinator's answer, which this note tests: transport is the least interesting instance of one proof shape fn2 relies on everywhere, a relation `R` between two representations of one meaning that every transition preserves. If every correctness claim is a commuting square, a finite generating set of squares is what the simulator checks exhaustively and the proofs later prove, and a coherence theorem for the frame says the generators suffice. The bugs then live in the diagrams that do not follow from the generators.

Read against: `MODAL-KERNEL.md` (MK; the six judgment families, §2's laws by number, §8's open items), `UNIVERSAL-CONSTRUCTIONS.md` (UC; §2.2's per-event-kind certificate, §9, §13), `TRANSPORT.md` (TR; §0, §3-5, §9's results of Experiments A and B), `EXECUTION-MODEL.md` (EXEC; §4's refinement obligation), `EXECUTION-MODEL-ROUND2-ASTRA.md` (R2; §A, §C.4, §F), `INBOX-DELIVERY.md` §4.6 (INBOX), `PLANES-ADDENDUM-INTERWEAVING.md` (ADDENDUM), `STORAGE-DESIGN.md` §4 decision 1 (STORAGE), and the simulator on `origin/fn2/main` at `957b018c1`: `fn2/sim/check-trace.lisp`, `fn2/sim/check.lisp`, `fn2/books/reference.lisp`, with `fn2/books/machines.lisp`, `machines-a.lisp`, `vocab.lisp`, `profile.lisp` and `fn2/tests/sim-layer-a*.l*` for counts. Papers are cited by filename in `~/paperbin/` (a `.pdf` with its `.txt` beside it); the ones fetched for this note are in the "Coherence" section of `~/paperbin/README-fn2-20261028.md`.

**The discipline this note keeps** is MK's: a construction is named only if it predicts something concrete (a check that can fail, a field, a refusal word, a declaration), and a linkage to a theory counts only when the morphism is written down and something is checked across it.

## Contents
1. The inventory of squares
2. The generating set
3. The coherence conjecture for fn2's frame (co-written with Astra)
4. The diagrams that do not follow (co-written with Astra)
5. What this changes in the engineering
6. The verdict, and five decisions for ember (co-written with Astra)
7. The Astra sessions, and where the two authors differ
8. Bibliography

---

## Notation

A **square** is `(A, B, R, T, obs, κ)`: two representations `A` and `B` of one meaning, each a state set with transitions; a relation `R ⊆ A × B`; a set `T` of transition labels, each interpreted on both sides as `t_A` and `t_B` (where `t_B` may be a word of `B`-transitions, so the square may stutter); declared observations `obs_A`, `obs_B`; and a declared loss `κ`, an identification relation on observations (MK D4), the identity when nothing is lost. The square **commutes for `t`** when

```text
R(a, b)  ⇒  R(t_A a, t_B b)                       (step)
R(a, b)  ⇒  obs_A(a) ≡_κ obs_B(b)                 (edge)
init_A R init_B                                    (base)
```

A **diamond** is a square with `A = B` whose two routes are `t;u` and `u;t` from one state, and whose relation is an equivalence `≈` on states. A **2-cell** is a claimed equality between two routes of squares with the same ends (TR Experiment D). A square is **thin** when its content is a proposition (two observations are equal, or a relation holds) and **data-carrying** when the route chooses something (a position map `ρ`, a converted cut, a kernel, an event identification) that a second route could choose differently.

Seven kinds of relation occur. Every row below has one:
- **E**: equality, or the graph of a function (`R(a, b) ⇔ b = f(a)`);
- **S**: forward simulation, one direction, with stuttering allowed on one side;
- **B**: bisimulation up to a declared relation (all-future observational congruence, UC §2.2);
- **L**: lens laws on a restricted update language (UC §7.1);
- **Q**: a lossy map with its kernel declared as an identification relation (MK §5.1);
- **T**: trace equivalence: equality of declared observations across schedules that differ by swaps of declared-independent steps (Mazurkiewicz, UC §1.2);
- **X**: containment of an environment: one side's behaviours are a subset of the other's allowed behaviours. An X row is an assumption about the world, not a square of the frame.

---

## 1. The inventory of squares

Every "two representations of one meaning" relation fn2 relies on. The brief named eight (Q1, Q4, Q5, Q6, Q2, Q12, Q9, Q10 below); the documents and the simulator supply seventeen more. "Today" means `957b018c1`: `check.lisp` names eleven checkers; OWN is implemented, TRACE and WORK are implemented through their own entry points (`fn2-check-trace-turn`, `check-work.lisp`) and refuse a bare call, and the other eight return `:not-yet`. The owed theorems are `defthm-owed` statements with evaluated teeth, none proved (RELEASE-PLAN §4 counts twenty-one).

| # | name | the two sides | the relation `R` | transitions that must preserve it | checked / proved / assumed today | kind |
|---|---|---|---|---|---|---|
| Q1 | **refinement** | the fused, host-called `fn2-turn` on `fn2-core`; the one-transition-at-a-time `fn2-ref-turn` on `fn2-ref-core` with list FIFOs and a literal calendar | `fn2-representation-relation`: no `fn2-ref-scheduler-difference` (literal calendar, cursor, per-principal FIFOs, intrusive links, service flags) and no `fn2-ref-core-difference` | every turn under every environment observation order; per turn, `(status obs visits actions)` equal and the budget inequality | TRACE, in lockstep per turn (`fn2-check-trace-turn` imports the adapter boundary, runs both, compares); owed `fn2-turn-refinement` with teeth `fn2-reference-teeth`; no fusion yet, so `fn2-turn` is the reference loop over concrete transitions | S (with `σ` existential, EXEC §4); today E per turn |
| Q2 | **stobj vs ATC flat form** | the ACL2 stobj realization; the flat integer-array dispatcher (EXEC §5, R2 §A.3) | a representation function from flat arrays to stobj fields | every machine transition | assumed: `defmachine`'s `*fn2-machine-obligations*` lists `flat-representation` and `flat-transition` as `:owed`; no flat form exists | E |
| Q3 | **logical view vs served columns** | the abstract interface (maps, sequences, octet lists; EXEC rule 1); the struct-of-arrays columns and pool | an abstraction function (`defabsstobj` correspondence) | every exported operation | assumed; TR Experiment B states the logical row's correspondence to served columns as a separate, unexamined obligation | E |
| Q4 | **fold vs summary** | a fold over retained history; the summary that replaces `Events_{≤k}` (STORAGE decision 1, MK S1') | a relation closed under each event kind's step (TR §3.1(i)), stronger than the observation | every event kind, and every future suffix | **proved on a toy**: TR Experiment A (`fc-rel-fold`, `rs-summary-adequate`); HISTORY scenario 3 owed (HISTORY is `:not-yet`) | B (certified by a per-event-kind S square in both directions) |
| Q5 | **materialized vs select-only** | a consumer's inbox read through the policy table and the materializer's fold below `cov`; the select-only reference (INBOX §4.6) | equality of the consumer's observations: items, order, reasons, gaps, cursor proposals, ack outcomes | every policy assignment, every materializer schedule, every poll, wake, ack and edge change | owed: CONSUMER differential (`:not-yet`), the two-edge one-switch tiny scenario (UC §13 scenario 1) | T (over materializer schedules) |
| Q6 | **simulator vs native host** | the core under the simulated host (`fn2/sim/sim*.lisp`, `storage.lisp`, `network.lisp`); the same core under the native adapters | native behaviours ⊆ the simulator's fault profile (26 fault classes today) | every primitive: accept, receive, send, read, write, fence, cancel, close, clock | assumed: A-PERSISTENCE-FENCE, A-INTEGRITY-EVIDENCE; M7's filesystem experiments, published; the natives as the classical gate | X |
| Q7 | **turn boundaries** | one reference run over a word `σ₁σ₂`; two turns, over `σ₁` then `σ₂` | equal semantic observations, packing allowed to differ | any split of observations across harvest and turn boundaries | scenario 20 (dispatcher differential: "vary harvest/turn boundaries under corresponding schedules"), owed | T |
| Q8 | **replay** | a recorded run (profile, seed, observation order, fault choices, revision); its replay | equality of the disk fingerprint and observations | every recorded step | **checked**: `fn2-sim-replay-control` (`sim-replay-controls.lisp`; fingerprints are regression evidence, not collision-free) | E |
| Q9 | **a world at v3 vs v4** | `T₃` room state; `T₄` with thread annotations (MK §4.4) | `π(s₄) = s₃`, with `π(step₄(s₄,e₄)) = Fold₃(π(s₄), h(e₄))` | every admitted event, with each new kind's old meaning `h` declared | specified, not built: D68 (TR decision 1) | S (ext grade) |
| Q10 | **route 2-cells** | two migration routes with the same ends, `m₂ ∘ m₁` and `m₃` (MK R5) | equal observations on every future suffix, and equal position maps and converted cuts | every suffix | specified: TR Experiment D, deferred until two real routes exist | 2-cell over S squares |
| Q11 | **transport** | the domain at node `n` under `r`, incarnation `i`; at `n'` under `r'`, `i+1` (MK R9, A-LOC) | the certificate of Q9 (identity for a pure move) plus the recorded position map `ρ` | every read in the preserved interface: `@p φ ⇔ @ρ(p) σ_m φ` | specified; succession (fencing) is a second, independent obligation, not a square | E (pure move), S (revision) |
| Q12 | **two peers** | two nodes' identity Bindings (UC §4.3, MK B1) | equal validated fact sets ⇒ equal Bindings and equal `conflicted` | delivery of validated facts in any order, with duplication | owed: IDENTITY scenario 6 (`:not-yet`) | T (the diamonds hold algebraically: union is a join) |
| Q13 | **a port's view** | the room model `M_room`; the NNTP reduct `j*M_room` (MK §4.2) | `V = j*`; the kernel `κ_j(M,N) ⇔ V(M) ≅ V(N)` | every room transition (read view); every translated command (a command port) | owed: WIRE (`:not-yet`); the article-number uniqueness obligation | Q (read), S (commands) |
| Q14 | **retry vs original** | the first decision of operation `op` at `p₀`; any later retry of `op` (MK S1'') | `[retry(op)] out = @p₀ out`; a contradictory reuse refused `op-reused` | every intervening commit, recovery and summary | owed: CONSUMER scenario 2 (UC §13), HISTORY | E |
| Q15 | **commit protocol vs atomic append** | the commit machine (`collect → seal → … → notify`, with `uncertain`); an abstract append (UC §9.1) | accepted outcomes have the durable batch; refused ones contribute nothing; uncertain ones stay fenced | every commit-machine transition and death cut | owed: HISTORY, RECOVERY (both `:not-yet`); scenarios 13-16 | S (into a nondeterministic specification) |
| Q16 | **recovered vs crash-free** | the state recovery selects after a death cut; the states of crash-free runs on durable prefixes (MK D1, E8) | the recovered state is one of the allowed recovery states for the evidence held | every submitted-action prefix and death cut (EXEC §4 "crash composition") | `recover-stub.lisp`, `sim-recovery.lisp`, `fn2-sim-recovery-controls`; RECOVERY `:not-yet` | S (into a set) |
| Q17 | **mixed durable/transient order** | the delivered sequence of one stream on one node; the declared order, durable `(q, 0)`, transient `(p, s > 0)` (UC §5.3, ADDENDUM item 2) | equality of the delivered order with the declared one | install, publish, notify, page, overrun, epoch change | owed: UC §13 scenario 4 | E (a declared linearization) |
| Q18 | **catch-up vs fold from start** | `fold(P(cov), E_{cov+1..p})`; `fold(s₀, E_{1..p})` (UC §2.4) | equality | every suffix | free: the action law (MK S1) | E |
| Q19 | **fork prefix** | parent `d` at `q ≤ p₀`; child `d'` at `q` (MK §1.3 item 3) | `@(d',q) e ↔ @(d,q) e` for event and outcome atoms; nothing about the present | none after the fork: the prefix is shared by identification | free on the prefix; disposition O7 is a separate total check (HISTORY fork scenario, owed) | E (on the prefix only) |
| Q20 | **ownership shadow** | the pool and ops tables; the OWN checker's independent shadow `fn2-own` | every slot's ownership state, loans and generations agree with the shadow's | every issue, harvest, read, write and release | **checked**: OWN (`fn2-check-own`, run after every step of `fn2-scenario-rounds`) | E |
| Q21 | **client oracle** | the echo machine's bytes on a capability; the test-side client record (expected remaining echo, never read from the pool) | byte equality per connection, with drops attributed to a named cause | every send, receive and close | **checked**: `echo-scenario.lisp`, 1,000-seed runs plus the live run with zero unattributed drops | E (per connection) |
| Q22 | **wired composite vs components** | the simulator's composite of listener, echo and allocator; the relational composite of their per-component behaviours (TR Experiment E) | equality of behaviour sets on the common timeline up to `L` | every component event | specified for after layer D; a two-component version omitting the allocator must fail | T |
| Q23 | **representation change of a table** | v1 logical row; v2 with the position split into epoch and seq (TR Experiment B) | `defiso` maps, restricted to the image | every user function and theorem in the propagated range | **proved on a toy**: `propagate-iso`, 15 generated events; the lossy v3 is refused at `:beta-of-alpha` | E (an isomorphism onto its image) |
| Q24 | **time-domain conversion** | a deadline in domain `D`; its first crossing in node time (UC §6.4) | `τ_D^♭`, a Galois connection where it exists; nested domains compose `(τ₂∘τ₁)^♭ = τ₁^♭∘τ₂^♭` | every rate event, anchor and pause | owed: UC §13 scenario 5; revalidation at firing | S (provisional, revalidated) |
| Q25 | **field-edit lens** | a record view; its journal of `(:set field value)` events (TR Experiment C) | `fl-get`, with PutGet, view-level GetPut and PutPut over total records | every put | specified, waiting for an editing consumer | L |

Three things the table shows before any theory.
1. **Eighteen of the twenty-five rows are E, S, B, L or Q squares about a single transition at a time** (Q1-Q4, Q8-Q9, Q11, Q13-Q16, Q18-Q21, Q23-Q25). Their content is one implication per transition kind. Q17 is a declared linearization (§4.1). Four rows are T rows (Q5, Q7, Q12, Q22) whose content is about *orders* of transitions. One is a 2-cell (Q10). One is an X row (Q6), and it is the only row no generator can discharge.
2. **The rows already checked are all E rows checked in lockstep** (Q1 per turn, Q8, Q20, Q21). No T row is checked yet, and the simulator explores orders by seeded sampling (`fn2-scenario-runs` iterates 10,000 seeds on the tiny profile and 1,000 on the near-limit one, accumulating a 14-bit action mask and a 26-bit fault-choice mask as coverage evidence). The orders are where the next bugs are, and they are the rows nobody checks.
3. **Q1 is the square every other row lives inside, but it is not the only evidence.** (Astra's qualification: TRACE compares the dispatcher with a reference that shares the machine handlers, so a bug in a shared handler passes TRACE; Q20, Q21 and the semantic contracts stay independent evidence.) The reference semantics is deterministic given the observation order (EXEC rule 4: wall time never selects a machine; `fn2-ref-transition` takes the posted completions in order, then the literal calendar). So the only nondeterminism in fn2 at one node is the **environment's**: which completion the adapter posts next, which fault it injects, where a death cut falls, how the client fragments its bytes. At several nodes it is also the order in which facts arrive. Every T row is therefore an equivalence between environment schedules, never between two reference schedules of one environment.

---

## 2. The generating set

### 2.1 Three families and a base

The proposal is three families of local squares, each stated per transition kind or per pair of kinds, plus base squares. "Local" means each generator mentions one state and one or two transitions.

- **G0, base squares.** `init_A R init_B` for each square, and, for a square entered mid-run, `R(s, convert(s))` at the state where it is entered (TR §3.1(i)'s converter, MK §4.4's `convert`, a transport's installed state). A converter is a base square, not a step square, and it fails independently (MK decision 2: a conservative theory can have a faulty converter).
- **G1, simulation squares, one per transition kind per representation pair.** For each kind `t`: `R(a,b) ⇒ R(t_A a, t_B b)` (with `t_B` a declared word when the square stutters) and the edge `R ⇒ obs ≡_κ obs`. The per-event-kind summary equations (UC §2.2) are G1 with `A` the history fold and `B` the summary; the reference-vs-fused squares are G1 with `A` the concrete transition and `B` its reference word; the migration step equation (MK §4.4) is G1 with `B` the old interpretation and `t_B = h(e)`. They are one family; UC and TR found the same shape three times.
- **G1q, quotient squares**, the special case of G1 in which `R` is the graph of a lossy map `q` with kernel `κ_q`. Its step condition is that `κ_q` is a **congruence** for every transition in the map's scope: `κ_q(a,b) ⇒ κ_q(t a, t b)`. It is kept as a named variant because its failure has its own shape: a kernel that identifies two states now and distinguishes them after a later step. That is exactly how TR's windowed lossy version "violated its own migration law" (TR §7 item 14; Astra's witness, window 2, `hwm = 0`, reads `{3}`, then `(:read 1) (:read 2)`). The port's loss (Q13), a lossy migration's kernel and every variant of the declared-loss envelope that identifies states (MK D4's `kernel` variant) are G1q.
- **G2, independence diamonds, one per declared-independent pair of kinds.** For kinds `t`, `u` declared independent under a condition `ind(s, t, u)`: if both are enabled at `s` then each stays enabled after the other, and `u_A(t_A s) ≈ t_A(u_A s)`, where `≈` is a declared state relation that is itself step-closed (a G1 square of `A` with itself) and whose edge is the observation class in force. The independence is declared through effect footprints (UC §1.2: rows read and written, shared quotas, allocator, scheduler and action-stream effects), whose safe default is "everything", which declares no pair independent. Peers' fact deliveries (Q12), materializer steps against consumer steps (Q5), environment completions for different principals (Q7) and any reordering fusion (R2 §C.4) are G2.

The smallest set: G0 ∪ G1 ∪ G2, with G1q inside G1. Nothing else is needed for the derivations of §2.2, and §2.3 shows what nothing in the set can derive.

### 2.2 The derived squares, with their derivations

Each derivation uses one of three pasting rules, which §3 states as the coherence conjecture. **Vertical pasting** composes G1 squares along a word of transitions: by induction on the word, a square for every generator is a square for every run. It is the universal property of the free monoid, and TR Experiment A proved it once as `fc-rel-fold` for an arbitrary relation. **Horizontal pasting** composes G2 diamonds: by the Mazurkiewicz construction, the equivalence generated by swapping adjacent independent steps is trace equivalence, so a property invariant under each swap is invariant under all of them. **Mixed pasting** composes a G1 square with a G2 diamond: it needs `R ; ≈_B ⊆ ≈_A ; R`, that is, the representation relation respects the independence relations of the two sides. It is not free, and it is not the only condition that is not free (§2.5, §3.3).

| derived square | from | derivation | follows? |
|---|---|---|---|
| Q1 over many turns | G1 per concrete transition kind; G0 at `fn2-core-init` | vertical pasting along the observation word; the per-turn statement is the pasted square for one turn's word | **yes**, for order-preserving fusion (R2 §C.4's first form: consecutive runs of one kind). Reordering fusion additionally needs G2 for each reordered pair, then mixed pasting |
| Q4 summary adequacy | G1 per event kind (`rs-same-reads-of-read`, `-of-catchup`); G0 | vertical pasting: exactly TR Experiment A's `rs-summary-adequate` by `:functional-instance fc-rel-fold` | **yes**, proved on the toy; the converter `rs-summarize-related` is its separate G0 |
| Q9 v3 vs v4 | G1 per event (`π(step₄(s,e)) = Fold₃(π s, h e)`); G0 `convert(s) = (s, empty)` | vertical pasting (MK §4.4: "together with initialization, this establishes agreement of old observations after every admitted suffix") | **yes**, for the old observations; new observations need their own justification (TR §3.2(ii)) |
| Q10 route 2-cells, for observations | G1 for each migration of each route | each route's pasted square relates the target to the source with equality on the preserved observation; two equalities to one source agree | **yes, for every observation preserved by every migration on both routes**. The square is thin there: a 2-cell between two equalities is unique. **No** for the data a route chooses (position maps `ρ`, converted cuts, the loss each route reports) and for an observation preserved by one route only: those are data-carrying 2-cells and need Experiment D's check |
| Q11 transport, semantics | G0 (the installed state is related) and G1 (identity morphism, or Q9's) | vertical pasting from the installed state | **yes** for semantic preservation. **No** for succession: fencing at the commit authority and protected sinks is not a square (MK R9 keeps it a second obligation) |
| Q12 peers | G2: `deliver(f)` and `deliver(g)` commute (union is commutative and idempotent); G1: validation is a function of the fact and its declared dependencies, not of arrival | horizontal pasting over delivery orders; dependencies arriving late are absorbed by the pending set | **yes**, given the validation G1 and an explicit idempotence route equation for duplicated deliveries (`f` against `ff`, which no swap derives; §2.5). The teeth are UC §4.3's: a node that refuses a conflicting content and records nothing breaks the G2 diamond for the two offers, and the derivation correctly fails |
| Q13 port read view | G1q: snapshot factorization of every retained observation through `κ_j`; future congruence only where the port promises future behaviour (§2.5) | vertical pasting through the reduct | **yes**. Composition of ports needs no new generator: `κ_(j∘k)(M,N) ⇔ κ_k(j*M, j*N)` is a pullback, strictly associative as a relation (MK §5.1's `(x, y) ↦ x ↦ x mod 2`) |
| Q13 port with commands | G1 per translated command (command simulation, outcome map) | vertical pasting | **yes**, for safety over finite traces. A required reply's eventual arrival is liveness and is not a square (MK §5.1) |
| Q5 materialized vs select-only | G1 per materializer step (fold entry vs the stream entries it covers); G1 for the **poll** itself (merge, dedupe, reason union, cursor proposal), select-only vs mixed source; G2 materializer steps against polls, acks and edge changes | mixed pasting over every materializer schedule | **yes, once the poll is covered**, either as its own generator or by a proved generic merge theorem (Astra: "if and only if" was too strong). Per-edge squares alone do not cover it: two correct edges can still produce a duplicate, a lost reason or a cursor past an unread entry (UC §3.1 item 2). Generators belong to transitions of the composite machine, never to components (§2.5) |
| Q22 wiring | G1 per component event; G2 for component events declared independent | mixed pasting | **not established.** The allocator as a component is necessary: without it listener and echo events are not independent (both touch the free list and counts), and TR Experiment E's two-component tooth is that false diamond. It is not sufficient (Astra): the scheduler, operation correlation, initialization and every other shared effect must also be components, and per-component S certificates give containment of behaviour sets, not equality |
| Q14 retry | G1 for the retry transition of each command kind: a recorded outcome at `p₀` and a retry give the recorded outcome; G1 for every summary step, keeping outcome evidence in the summary's observations (STORAGE decision 1) | vertical pasting from `p₀` | **yes**, while the commit is resolved. **No** across an unresolved `uncertain` commit: §4 item 4 |
| Q15, Q16 commit and recovery | G1 per commit-machine phase into the abstract append; a crash square per (phase, fault class) relating the recovered state to an allowed one | vertical pasting along the phases; crashes during recovery compose because `→_C` is declared as a closure (MK §1.1) | **partly**: the crash squares form a finite family (eleven commit phases by the fault profile; R2 §E.2 and scenario 13), and pasting is sound because the closure is transitive. What the evidence establishes (`intact / torn tail / damaged / unknown`) rests on A-INTEGRITY-EVIDENCE and A-INDEPENDENT-FRONTIER: X, not derived |
| Q7 turn boundaries | G1 for the concrete turn as a word of reference transitions; the reference loop is a fold | vertical pasting | **yes only for the same induced word.** Splitting a fixed word between turns is the action law. Moving a harvest boundary can change the word itself, because `fn2-ref-transition` takes posted observations before calendar visits: `post(a); run; post(b); run` and `post(a); post(b); run` can queue machines differently and change an admission (Astra's witness, §4.6). A G1 correspondence between the induced words is owed |
| Q18 catch-up | the action law | free | **yes**, and it needs the maintenance state at `cov` and the suffix (UC §2.4) |
| Q19 fork prefix | identification | free | **yes** on the prefix; the disposition of the present is §4 item 5 |
| Q2, Q3, Q23 representation changes | G1 per operation, with `R` a function | vertical pasting; Experiment B's `propagate-iso` is the mechanized form | **yes**, within the image (Experiment B's `:beta-image` refusal is a false G0) |
| Q20, Q21 checkers' oracles | G1 per step against an independent model | vertical pasting | **yes**; they are already run per step |
| Q24 time conversion | G1 per rate event, with revalidation at firing | vertical pasting of provisional conversions | **yes**, provided the conversion is revalidated when it fires (UC §6.4 law 4); a backward re-anchor is refused, so no square needs to commute across it |
| Q25 field-edit lens | G1 per put on the restricted language | vertical pasting | **yes**, at the view level; GetPut fails at the journal level exactly for outcome-owing puts (TR Experiment C), which the observation class must say |
| Q6 simulator vs native | none | an X row is an assumption about the device and the network | **no**, by kind |
| Q17 mixed order | none, as the documents stand | §4 item 1 | **no** |

### 2.3 What no generator derives, and why that is the useful part

Four kinds of statement are outside the closure of G0 ∪ G1 ∪ G2 under the three pastings, whatever generators are added:
1. **X rows** (Q6, and the evidence assumptions inside Q16): the environment is not a representation of fn2's meaning.
2. **Liveness.** Squares relate finite prefixes. Eventual discharge of an obligation, eventual reply, the service bound under continuous eligibility (MK E5(b)) are FAIR and WORK properties under a declared bounded-completion environment (R2 §F.2), not pastings.
3. **Data-carrying 2-cells**: position maps, converted cuts, event identifications across a diamond, and the loss a route reports. Pasting proves equalities of observations; it does not choose these, and two routes can choose them differently.
4. **Interactions whose diamond is false in every observation class anyone would accept**: the five of §4.

The same closure also *predicts* UC §13's two inherited defects. Item 4 (coverage is not history): a latest-only projection is a G1q square whose kernel identifies every historical version below `cov`, so `exactly-at(p < cov)` is an observation outside its image and no pasting reaches it; `at-least(p)` and `catch-up` are inside it. Item 10 (the exact local order is not free): install, live publish and notify are three transitions whose diamonds are false on the delivered order, so Q17 cannot be derived and has to be declared. Both were found by Astra by reading; the frame finds them by asking which squares are generated.

### 2.4 The count: schemata first, instances measured

*Rewritten after Astra's session 1, which replaced the draft's per-kind pair arithmetic with a count of schemata and instances; the numbers below are the agreed ones.*

A generator in §2.1 is a **schema** (one per transition kind, or per pair of kinds with a condition). What the simulator checks is an **instance**: a schema at a reachable state with concrete occurrences. The two counts must not be confused, and neither is a coverage claim until the declarations exist.

Layer A at `957b018c1`, counted from the declarations:
- **dispatch cases (G1 schemata for Q1)**: 22 continuation states (listener 2, echo 6, scribe 14 in `machines-a.lisp`), 9 routed observations (listener 2, echo 4, scribe 3 `:observes` entries), 1 unrouted observation, clock and signal (2), 4 service visits, 1 empty-principal visit: **39**, with harvesting counted inside the observation cases. Some cases share an implementation and one case can hold several semantically distinct branches, so 39 is neither a theorem count nor a primitive-action count (Astra). Q20 and Q21 have their own schemata, partitioned by their own boundaries (the OWN shadow's observed operations, the client oracle's per-connection bytes), not a copy of Q1's 39 (Astra, session 2); Q2 and Q3 add schemata of their own once a flat form and an abstract interface exist.
- **G2 candidate pairs**: the environment's choices are 12 completion kinds (`vocab.lisp`'s `fn2-event` enum) and 26 fault classes. At the coarse kind-pair level, allowing equal kinds, that is `38·39/2 = 741` candidate pairs. This is pessimistic for those 38 choices only; it excludes posting and execution boundaries, clock and signal interactions, parameters and reachability. Most candidates are illegal or dependent and must be *classified*, never silently counted as passing (Astra).
- **The independence condition is not "different machines"**, and §2's first draft was wrong to suggest it. Astra's code-traced witness: one occupied echo row with an outstanding Close, and a listener with an outstanding Accept, both in principal 0's FIFO. Posting `AcceptResult; CloseResult` queues the listener first, and `fn2-listener-admit` finds no free echo row and closes the new connection; posting `CloseResult; AcceptResult` queues the echo first, `fn2-connection-release` frees the row, and the listener admits the new capability. Two completions, two visits, a client-visible difference. The two machines share the allocator (the free head and the active and connection counts read at `machines-a-run.lisp` lines 82-98). So a footprint must name the allocator, and "different principal" is at best a candidate condition to be checked, because harvesting writes one posted FIFO and later allocation can retain order effects.
- **G0**: one per square, about 6 in layer A.

**The work report the generator mode prints** is Astra's:

```text
G1 instances = Σ over reachable states s, over relation contracts R,
                 of the enabled covered transition instances at s
G2 instances = Σ over reachable states s
                 of the declared-independent enabled occurrence pairs at s
```

with separate counts of base checks, non-vacuous declaration witnesses, dynamic triple checks, declared route equations and rejected independence candidates.

Layer D, sized from R2 §B's catalogue as **schemata only**: twelve machine kinds with about 95 states, about 25 event kinds and about 10 command kinds; about 50 summary-step schemata (identity, obligation evidence and read-state folds, about 8 event kinds each, two equations per kind); about 15 G1q schemata for the NNTP read port; about 10 G1 and 50 G2 schemata for the inbox poll and materializer; about 300 environment pair candidates and about 55 command-pair candidates. **About 620 schemata, about 1,000 pessimistically.** That figure is provisional sizing and must not become a coverage claim before the declarations exist (Astra).

One prediction follows already, sharpened by Astra. **Two POSTs to the same group exchange their article numbers**, because numbers are assigned in commit order. NNTP replies carry article numbers, so Q1 and WIRE, which preserve reply bytes, must treat the two POSTs as dependent; Q12, which observes validated facts, may forget local numbering and treat them as independent. There is no single observation class that both preserves connection byte streams and excludes article numbers. Every square therefore names the contract it preserves, and an independence declaration is relative to that contract. A G2 declared under the wrong contract fails at the first state where both POSTs are enabled.

### 2.5 The set as amended by Astra (session 1, adopted)

Astra kept the four names and made their roles exact. Adopted:
- **G0**: entry, conversion and invariant establishment.
- **G1**: matched transitions *of the composite machine*, including outputs, refusals, invariant preservation and the named observation edge. "Generators belong to transitions of the composite semantic machine, including its synchronization and shared-resource protocols. Component certificates discharge composite cases only through an explicit composition rule" (Astra). The allocator, the scheduler, admission, the inbox merge, retry resolution and fork disposition are such transitions. The poll lesson of Q5 and the allocator lesson of Q22 are one lesson.
- **G1q**: a declaration and checker variant of G1, not a separate mathematical primitive, which splits **snapshot factorization** (every retained observation factors through the kernel, including authorization and refusal results) from **future congruence** (the kernel is preserved by future transitions), and requires the second only where the square promises future behaviour. A read-only port view need not be a congruence under every room command (§4.2).
- **G2**: legal swaps of transition *occurrences*, with enabledness, effects, scheduler consequences, the residual occurrence map and the selected observation contract.
- **Compatibility obligations**: future closure of `≈`, mixed pasting, label correspondence, and cube or residual consistency where it is claimed (§3.2).
- **Declared route equations**: the data-carrying 2-cells (Q10) and equations that are not permutations, such as Q12's duplicate absorption (`f` against `ff`), which no length-preserving swap derives.
- **Crash coverage**: crash obligations stay G1 instances mathematically, but get their own generated coverage table, indexed by submitted-action prefix, persistence state, fault choice, evidence and recovery transition. "Eleven phases times fault classes" does not enumerate the physical cuts inside a phase, and the closure of `→_C` only composes crash steps already matched.

The Opus draft's claim that mixed pasting is "the one condition that is not free" is withdrawn: future closure, valid enabledness, label correspondence, dynamic consistency and adequacy of the observation contract are also not free (§3.3).

---

## 3. The coherence conjecture for fn2's frame

*Co-written. The text from §3.1 to §3.4 is Astra's (session 1, `fn2/coherence-astra-1.md`), adopted with filenames and two citations repaired; §3.0 and §3.5 are the Opus author's. The largest change Astra made to the brief's framing is to split the claim in two: soundness of generated diagrams, which is an induction once the hypotheses hold, and completeness of the generators, which is the real conjecture and is not established by a finite list of kinds.*

### 3.0 The conjecture in one paragraph (Opus)

Fix an implementation revision, a profile, a fault profile and an initial state satisfying the invariant. **Schedules** are finite legal executions of the composite core and its modelled environment, labelled by transition *occurrences*, quotiented by the equivalence generated by legal adjacent swaps that G2 certifies. **Observations** are those of one named contract, and the properties checked over them are prefix-closed safety properties invariant under the certified swaps: a connection's ordered reply bytes, a domain's journal, operation outcomes, ownership violations. Global interleavings, timing, turn counts and packing are outside the T quotient (not outside every fn2 contract: WORK and FAIR observe turn counts), and local article numbers are outside it only for a contract that forgets them, such as Q12's validated facts (Astra, session 2). Under the hypotheses H0, H1, H≈, HI, HM, HQ and H2 of §3.2, **every diagram generated from G0, G1, G1q and G2 preserves that contract's observations** (a theorem schema, by induction). **The coherence conjecture proper** is that, for a declared contract, every pair of routes the documents call interchangeable is connected by such a diagram plus the declared data-carrying route equations. It is not claimed globally; it is to be established first for one fragment (§3.2).


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

### 3.4 The theories that predict something (Astra)

**Mac Lane: structural coherence, not arbitrary program equivalence.** Associate each typed interface with an object, each certified component with an arrow, and composition of independent interfaces with tensor. The interpretation is:

```text
F : free monoidal syntax of declared components → semantic components
```

`F` maps reassociation and unit insertion to the actual interface rearrangements. The pentagon and triangle, with naturality, ensure that structural rebracketing has one meaning. Strictification permits list-shaped interfaces and strictly associative syntax, provided the semantic interpretation carries the corresponding coherence.

Most fn2 squares are thin. Once a proposition `Obs(route₁) = Obs(route₂)` is proved, there is no further operational distinction between its proofs in the proposed ACL2 interface. Mac Lane does not remove the obligation to prove that proposition. The substantial case is a structural transformation that carries a position map, cut conversion or occurrence bijection. Those maps can disagree and must be compared.

**Prediction:** normalize structural wiring, and compare the carried maps where route data is used. The analogy to migration routes otherwise remains a footnote. Sources: `maclane1963-natural-associativity-commutativity.pdf`; `selinger2009-survey-graphical-languages-monoidal-categories.pdf`, especially the structural coherence discussion and Theorem 3.12. 

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

**Prediction:** `:up-to` names a closure with a compatibility theorem, never an unrestricted comparison callback. References: Damien Pous and Davide Sangiorgi, *Enhancements of the Bisimulation Proof Method*, in *Advanced Topics in Bisimulation and Coinduction*, 2012 (not fetched; a gap); their historical account, `pous-sangiorgi2019-bisimulation-and-coinduction-enhancements-historical-perspective.pdf`, which states it: "a monotone function f is compatible with b if f ◦ b ⊆ b ◦ f". `abstract-account-up-to-techniques-inductive-behavioural2024-2412.07351.pdf` supplies related generalizations.

**Winskel and Nielsen: occurrence identity across a diamond.** Starting with the transition system, identify opposite edges representing the same occurrence across certified squares:

```text
(s --t--> s_t) ∼ (s_u --t/u--> s_ut).
```

Events are equivalence classes of such parallel transitions in the appropriate unfolding. A morphism `(f,h)` maps states and transition labels while preserving transitions and independence. A G1 label-to-word interpretation needs an expansion before it becomes this kind of morphism; it is not automatically one.

Check uniqueness and consistency of residual occurrences, completion of the required diamonds, and preservation of independence under event identification. Then a run maps to a configuration, and a cursor maps to a down-closed set of events. Conflicting admission choices and compatible observations of those choices remain different kinds of event.

**Prediction:** event correspondence belongs in a dynamic G2 certificate; multi-domain cuts must remain down-closed across that correspondence. Sources: `winskel1987-event-structures.pdf`; `winskel-nielsen1995-models-for-concurrency.pdf` (transition systems with independence; the `.txt` is OCR).

**Goubault: a geometric realization of the same checked swaps.** Construct a directed complex `K` with invariant states as vertices, transition instances as edges and certified G2 squares as faces. The realization sends a schedule `σ` to a directed path `|σ|`; a G2 swap becomes a deformation across its face.

For the corresponding discrete PV progress models, combinatorial dihomotopy is generated by these adjacent swaps. This is the precise trace-equivalence connection. A blanket identification of arbitrary continuous dihomotopy with fn2 schedule equivalence would require an additional representation theorem.

**Prediction:** a shared-resource obstruction means there is no certified face across which to move the schedule. The useful artifact is the failed diamond or resource-acquisition condition. Computing topology adds no immediate checker beyond that. Sources: `goubault2000-geometry-and-concurrency-users-guide.pdf`; `goubault2003-geometric-perspectives-concurrency-theory.pdf`, §§3 and 5. The geometric language is currently a footnote to G2, not another implementation requirement.

**Games: coherence must survive interaction.** Map environment completions and faults to Opponent moves, and core decisions and actions to Proponent moves. Map a complete legal interaction to a play in the asynchronous graph; map each permitted rescheduling to a permutation tile.

What must be checked is that the core's permitted plays and the environment contract remain closed under the claimed tiles, with consistent residuals and the cube property where a partial-order interpretation is claimed. Determinism under one input order does not establish that closure.

**Prediction:** an environment-side independence declaration must say which responsive core behavior it preserves. Otherwise “different client” is an unsound independence test. Melliès and Mimram make the cube requirement explicit in *Asynchronous Games: Innocence without Alternation*, CONCUR 2007 (`mellies-mimram2007-asynchronous-games-innocence-without-alternation.pdf`: "The cube property expresses a fundamental causality principle in the diagrammatic language of" asynchronous transition systems). The broader innocent-strategy machinery is a footnote unless fn2 uses its additional conditions; `mellies2006-asynchronous-games-2-true-concurrency-innocence.pdf` is background.

**Symmetric monoidal coherence and string-diagram rewriting: useful for generated wiring.** Let `Σwire` contain typed component operations. Interpret:

```text
J : FreeSMC(Σwire) → Rel
```

with interfaces mapped to behavior spaces, boxes to relations, composition to composition over shared boundary records, and tensor to independent interfaces. Allocator and scheduler interactions must be explicit boundary records. Two components sharing an undeclared allocator are not independent tensor factors.

Structural symmetry and reassociation can then be normalized without changing meaning. A semantic rewrite still needs `J(lhs) = J(rhs)`. The Bonchi, Gadducci, Kissinger, Sobociński and Zanasi results explain why arbitrary graph rewriting is not automatically sound for string diagrams: the interfaces and, for general symmetric monoidal theories, convexity restrictions matter.

**Prediction:** a wiring optimizer retains typed boundaries and checks each nonstructural rewrite; it does not copy or discard ownership wires without a declared operation. Sources: `selinger2009-survey-graphical-languages-monoidal-categories.pdf`; `bonchi-gadducci-kissinger-sobocinski-zanasi2022-string-diagram-rewrite-theory-I.pdf` and `…-II.pdf`. Until fn2 has such an optimizer, this is a design constraint for Q22, not a reason to build a diagram library.

**Squier and Newman: closer to the ambitious completeness claim.** Suppose route expressions have a terminating rewrite system. Map each expression to its semantic route, and each rewrite to a certified route equation. Newman's lemma makes local confluence sufficient for confluence under termination. Squier's theorem goes further: for a convergent presentation, resolutions of critical branchings generate a homotopy basis; a finite convergent string presentation has finitely many such branchings. Guiraud and Malbos, *Polygraphs of Finite Derivation Type* (`guiraud-malbos2018-polygraphs-of-finite-derivation-type.pdf`), and their *Coherence in Monoidal Track Categories* (`guiraud-malbos2012-coherence-monoidal-track-categories.pdf`).

**Prediction:** if fn2 builds a route normalizer, enumerate overlaps between its rewrite rules, compare their carried maps, and provide a decreasing measure. This is closer than Mac Lane to “all intended route equalities follow from a finite basis.” fn2 has not supplied that presentation.

Even sorting independent actions is not automatically convergent. Let `a < b < c`, with `a I b`, `b I c`, but `a` dependent on `c`. Orient independent descending pairs toward ascending order:

```text
cba → bca
cba → cab.
```

Both results are irreducible under those rules. A normalizer needs a better representation or additional rules and critical-branching resolutions. The server itself is not a terminating rewrite system merely because each turn has a budget.

**Partial-order reduction and movers: the nearest engineering applications.** For POR, map a full execution to its dependence order and choose representative linearizations. Soundness requires valid dependence and a search rule that retains representatives of the required behaviors. G2 validates swaps; it does not itself implement persistent sets, DPOR backtracking or source sets.

The immediate prediction is a separation between **checking independence declarations** and **using them to prune exploration**. Start with the former. Flanagan and Godefroid dynamically discover backtracking points; Abdulla and coauthors' source sets and wakeup trees improve which representatives are explored. Sources: `godefroid1995-thesis-partial-order-methods-verification-concurrent-systems.pdf`; `flanagan-godefroid2005-dynamic-partial-order-reduction.pdf`; `abdulla-aronis-jonsson-sagonas2014-optimal-dynamic-partial-order-reduction.pdf`; Abdulla et al., *Source Sets*, JACM 2017 (not fetched).

For Lipton reduction, map a concrete segment consisting of right movers, a central action and left movers to an abstract atomic action. Check the directional commutations, gates, invariants and permitted observation boundaries. This directly predicts a certificate for reordering fusion. It does not authorize hiding a submitted action from a crash between submissions.

Sources: `lipton1975-reduction-method-proving-properties-parallel-programs.pdf`; `kragl-qadeer2018-layered-concurrent-programs.pdf`. Civl's layered refinement is particularly close to fn2's desired generated implementation and local correspondence obligations.

Finally, a bounded search must preserve its bound under reduction. Swapping adjacent steps preserves word length; changing turn packing, preemption counts or expansion lengths may not. Coons, Musuvathi and McKinley's *Bounded Partial-Order Reduction* gives an explicit warning: simply combining a bound with ordinary DPOR can omit behaviors within that bound. (`coons-musuvathi-mckinley2013-bounded-partial-order-reduction.pdf`).

### 3.5 Opus additions: the three sources closest to the claim, and the summary

**The coordinator's sentence is a theorem in rewriting, with a name.** Guiraud and Malbos state the shape exactly: the method reduces "the infinite requirement 'every diagram commutes' to a finite requirement 'if a specified finite set of diagrams commute then every diagram commutes'", and they call such a set a **coherence basis**; for a convergent presentation, "the confluence diagrams of critical branchings form a coherence" basis (`guiraud-malbos2012-coherence-monoidal-track-categories.pdf`). Mac Lane's own definition is the thin case: "coherence requires that any two formally different iterates between the same pair of functors be equal", and his Theorem 3.1 is that the pentagon "is commutative for every quadruple" suffices (`maclane1963-natural-associativity-commutativity.pdf`, OCR). What fn2 lacks, and what Astra's `cba` example shows it lacks, is the convergent presentation of its routes. Until there is one, "a finite generating set" means a finite set of *schemata* whose pasting is sound, not a basis whose completeness is proved.

**Horizontal pasting is proved, with checkable hypotheses, for static independence.** Godefroid's "valid dependency relation" requires that independent transitions neither enable nor disable each other and that, enabled together, they reach a unique common state (Definition 3.1); his Theorem 3.10 is then exactly horizontal pasting: "If `s ⇒^{w₁} s₁` and `s ⇒^{w₂} s₂` in AG, and if `[w₁] = [w₂]`, then `s₁ = s₂`" (`godefroid1995-thesis-partial-order-methods-verification-concurrent-systems.pdf`). His Definition 3.15 is the footprint form (disjoint active processes, pairwise independent operations on shared objects). HI is Definition 3.1 checked as a diamond; the generator mode of §5 checks it at reachable states. DPOR (`flanagan-godefroid2005-dynamic-partial-order-reduction.pdf`) computes backtracking points from conflicts observed under a dependence model with sound backtracking rules; it does not learn universal independence from the absence of observed conflicts (Astra, session 2), so a footprint table stays declared and checked.

**Commutativity enumerated from a specification is an engineering practice already.** Clements et al.'s rule, "Whenever interface operations commute, they can be implemented in a way that scales", comes with COMMUTER, which "generates test cases for an arbitrary implementation based on a model of that implementation's interface" from the commutativity of interface operations (`clements2013-scalable-commutativity-rule.pdf`). That is G2 at the interface level, the level of POST, TAKETHIS, ack and edit in layer D, and it is stronger than an endpoint diamond: its SIM commutativity includes response validity and indistinguishability under future operations, with a prefix condition (Astra, session 2), which is H≈ stated for interfaces. It also says something fn2 can use beyond checking: an operation pair that commutes in the specification is one fn2 *can* implement without ordering them, which is where a multi-domain split (UC §1.2 item 3) would come from; the rule does not parallelize anything by itself.

**What sampling guarantees, for comparison.** Burckhardt et al.'s PCT guarantees at least `1/(n k^(d−1))` detection probability per run for its own scheduler and its stated model of `n` threads, `k` steps and bug depth `d` (`burckhardt2010-pct-randomized-scheduler.pdf`). That is a lower bound for PCT, and fn2's seeded scheduler inherits no such bound; nor does exchanging two completions establish depth two (Astra, session 2, correcting the Opus draft). A local diamond check guarantees neither reaching the enabling state nor a detection probability. What it does guarantee is that, at every state it reaches where both occurrences are enabled, both orders are compared. Whether that matters on layer A's code is the measurement of §6.

| relation to fn2 | the morphism written down | what is checked across it | verdict |
|---|---|---|---|
| Mac Lane, strictification | free monoidal syntax of declared components to semantic components (Astra) | that carried data (position maps, cuts, occurrence bijections) agrees along routes | **predicts** only at data-carrying 2-cells; thin squares make it a footnote elsewhere |
| Mazurkiewicz trace monoid | `q_I : Σ* → M(Σ, I)`, observations factor through it | each `tu = ut` respected by the action, enabledness included | **predicts**: the declaration shape of G2 (condition, contract, diamond) |
| Godefroid validity, POR, DPOR | dependence order and representative linearizations | Definition 3.1 as a diamond; Theorem 3.10 as the pasting | **predicts**: horizontal pasting proved once; check declarations before pruning with them |
| Lipton movers, CIVL | right movers, central action, left movers to one atomic action | directional commutations at fused segments | **predicts**: the certificate for reordering fusion (R2 §C.4) |
| Pous-Sangiorgi up-to | the progression `b` over the two folds' coalgebra | `f ∘ b ⊆ b ∘ f` for any `:up-to` closure | **predicts**: `:up-to` names a closure with a compatibility theorem, never a callback |
| Winskel-Nielsen, event structures | occurrence identification across certified squares | residual uniqueness, diamond completion, independence preserved | **predicts** where occurrence identity is used (multi-domain cuts); otherwise footnote |
| Melliès-Mimram games | environment moves as Opponent, core as Proponent, swaps as tiles | the core's plays closed under the claimed tiles; the cube property where a partial order is claimed | **predicts**: environment-side independence must say which responsive behaviour it preserves |
| Squier, Guiraud-Malbos | route expressions with a terminating rewrite system | critical branchings resolved, carried maps compared | **predicts** only once fn2 has a route normalizer; the closest form of completeness |
| symmetric monoidal coherence, string-diagram rewriting | `J : FreeSMC(Σwire) → Rel` | nonstructural rewrites checked, structural ones normalized | **design constraint** for Q22; no library |
| Goubault, directed topology | a directed complex with G2 squares as faces | nothing beyond the failed diamond | **footnote** |
| COMMUTER, PCT | interface specification to test cases; schedules to bug depth | SIM-commutativity test cases (future indistinguishability included); PCT's floor for its own scheduler only | **predicts** the layer-D G2 workload; PCT is context for §6, not a bound fn2 inherits |

---

## 4. The diagrams that do not follow

*Co-written. §4.1 to §4.6 are Astra's (session 1), adopted; the summary table in §4.7 and the decisions it names are the Opus author's, checked against Astra's verdicts.*


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

### 4.7 Summary: missing generator or decision (Opus, from Astra's verdicts)

| # | the two routes | smallest witness | verdict | what it costs |
|---|---|---|---|---|
| 4.1 | install; publish live; notify, against install; notify; publish live | one durable item, one transient item, arrival-order delivery gives `L, D` against `D, L` | **non-coherent on arrival order; a decision** (UC §5.3's order `(q,0)`, `(p,s>0)`), which then **creates a missing G1** for the composite delivery transition (delivered prefix = prefix of the declared merge) | reader frontier state, catch-up or waiting; a node-wide sequence for a multi-stream order, or a per-stream claim |
| 4.2 | lossy map then suffix, against suffix then lossy map; route through a dropped field | window 2, `hwm = 0`, reads `{3}`, then `read 1; read 2`; rows `(7,100,5)` and `(7,100,6)` with token 5 | **missing generator**: G1q's future congruence (the window) and snapshot factorization for every retained observation including refusals (the generation) | retain the information, or declare the region unavailable, or narrow the contract; never "declare a kernel" |
| 4.3 | read at least `p`; adopt, against adopt; read at least `p` | the value equal, the returned interpretation `r` against `r'` | **non-coherent as commands; a decision** already made: reads name position and interpretation, and the order is the journal's; plus **one G1** (the migration certificate) for declared preserved queries at corresponding snapshots | pinned interpretations and cuts, retained history for exact queries, MK R3's crossing rule |
| 4.4 | resolve; retry, against retry while unresolved; resolve | one operation, one lost barrier completion, one retry; and the ack whose later cut stands in for nothing | **dependent; missing G1s** (unresolved retries never execute fresh; resolved retries return the record; contradictory reuse is `op-reused`; summaries and recovery keep the evidence) and **a decision** that `uncertain` stays observable and distinct from refusal | retained bindings and resolution evidence, fenced work, reserved resources; the evidence-retirement rule of STORAGE decision 1 |
| 4.5 | fork with the obligation to the child; discharge in the parent, against the reverse | one outstanding external-effect obligation and one valid receipt | **dependent; missing G1s** for the composite `fork` and `promote` (total disposition, per-kind authority contract, conserving split, no held effect emitted, promote re-decides) and **a decision**: separate historical disposition at `c` from transfer of live authority in the parent's commit order (Astra's proposal), or keep all external authority in the parent and make the child observational until promotion (the cheaper alternative) | snapshot and disposition evidence, live authority tracked separately, refusable transfers and promotions |
| 4.6 | harvest boundary moved; compaction against a historical read; cancel-not-found against target release; `f` against `ff` | the listener/reclamation witness; a latest-only fold at `cov = 2`; one borrowed buffer; one duplicated fact | **missing generators**: a G1 correspondence of induced words (Q7); compaction's G1 preserving unexpired retained contracts; the ownership G1 consuming actual release evidence; an idempotence route equation for Q12 | boundary conditions on turn splitting; retained version state; retained target operations; a scoped idempotence claim |

Of the five diagrams the brief named, one (4.2) is a missing generator and nothing more. The other four (4.1, 4.3, 4.4, 4.5) fail their equation for the exhibited implementations or the full response contract; each needs a declared order or a declared narrower contract, exactly as the mixed durable/transient amendment does, and the declaration then yields new G1 obligations the generator mode can check. "Non-coherent" in the table means that, and no more: a corrected merge can make a narrower publish/notify square valid (Astra, session 2). The four further diagrams of 4.6 are all missing generators. That is the useful outcome of the frame: **a non-coherent interaction becomes a decision plus generators, never an unexamined assumption.**

---

## 5. What this changes in the engineering

*Co-written. The Opus author drafted this section; Astra's session 2 (`fn2/coherence-astra-2.md`) replaced most of §5.1, §5.3 and §5.4 and the opening of §5.2, and the replacements are adopted. What Astra changed, in one line each: the existing runs are pool scenarios plus an echo workload, not 11,000 dispatcher traces; the mode separates checking local obligations from reaching states, and never prunes in its first experiment; the missing facility is a whole exploration checkpoint, and replaying prefixes avoids building one first; the comparison must be a named contract, never "the columns that differ"; the estimate is 12 engineer-days pessimistically, not four; `defsquare` is a registry with templates, and the Opus author's single form is one of two positions; the owed count is 22, not 21, and most of them do not change shape; T7 and T9 are durability and identity, not crash refinement and summaries.*

### 5.1 The simulator: a generator mode beside the sampling mode

**What runs today (Astra).** At `957b018c1`, the acceptance driver (`sim-layer-a-a4-driver.lsp`) runs 10,000 tiny-profile and 1,000 near-limit **pool scenarios**, whose rounds issue operations directly and run OWN after every step. These are not 11,000 dispatcher traces. The same driver separately runs the scribe scenario and an echo workload from seed `20261028`, targeting 1,000 completed or attributed-dropped connections, then a 200-connection bounded-completion run; the echo workload runs TRACE per turn. Coverage figures must name the workload, the checked contract and the execution boundary. The 14-bit action mask and 26-bit fault mask measure which kinds occurred, not which schedules or diamonds were exercised.

**The mode (Astra's design, adopted).** `fn2-sim-run-generators` separates two activities, enumerating local obligations at reached states and systematically reaching states; neither needs partial-order reduction at first.
1. **G1 checks.** Compare `fn2-transition` with `fn2-ref-transition` at corresponding boundaries, keeping the reference's independent queues and calendar and importing adapter effects only at the real boundary. The driver aligns remaining budgets, return values, accumulated work and turn initialization and termination explicitly (the two loops accumulate work differently, so two transition calls do not replace one turn call). The per-turn comparison stays, as a composition check.
2. **G2 checks.** At each reached state, every applicable declared-independent pair of concrete *occurrences*: both legal routes, with emitted effects and the residual occurrence correspondence, compared by the declared endpoint relation and the observation histories. A short matched continuation can refute future closure (H≈); passing it does not establish H≈. An occurrence includes its operation, generation, result cell, payload and fault choice: reusing a seed after a swap can attach the next random fault or payload to a different operation, so corresponding continuations must preserve identities or report the correspondence illegal.
3. **Reachability.** First replay recorded prefixes and exhaust the finite choices at selected boundaries; then bounded prefix enumeration over an explicitly listed input domain. "Exhaustive" means all declared instances at those states, or all prefixes within that domain and horizon, and nothing more.
4. **Evidence.** Reached, exercised, rejected, unexercised and unimplemented cases are reported separately, in the spirit of `check.lisp` ("missing evidence and unimplemented checks are never passing results"). Every declaration has a non-vacuous positive fixture and a negative control; the first negative control is the listener/reclamation pair of §2.4 declared independent, which must fail.
5. **No pruning in the first experiment.** Passing diamond checks does not authorize removing schedules. Later pruning needs a sound dependence model and a reduction that keeps its bound, since combining a bound with ordinary DPOR "misses parts of the state space reachable" within it (`coons-musuvathi-mckinley2013-bounded-partial-order-reduction.pdf`).

**What exists, and what does not.** Much of the copying exists: `fn2/books/reference-state.lisp` generates, from the column registry, congruent child stobjs (`fn2-ref-core` is `:congruent-to fn2-core`), per-child `-REF-COPY` and `-REF-DIFF`, and `fn2-ref-copy-core`. What is missing is a complete, independently restorable **exploration checkpoint** (Astra): `fn2-core-children` registers the core's children, not the simulator; `fn2-sim` has nested network and storage stobjs, PRNG state, clocks, pending flights and fault state; `fn2-own` has its own arrays; and the scenario carries client records, reference queues and counters as ordinary arguments. `defcolumns` records enough layout to generate much of a checkpoint, but recursive nested stobjs, array lengths and non-numeric fields need handling, and unsupported kinds must fail generation; copy, restore and branch-isolation controls are required. For the first experiment, **replaying a prefix into freshly initialized states** avoids making checkpoint generation a prerequisite. The semantic difference is a separate obligation: generated field traversal gives exact comparison and diagnostics, but it cannot infer an observation contract or a future-closed equivalence. Today's reference comparison deliberately omits the reference's unused intrusive scheduler and compares only relevant pool bytes; those exclusions do not carry over to two concrete executions, which must account for both schedulers, pending operations, live bytes, client-visible outputs, ownership evidence and environment state, with any renaming of allocated identifiers as an explicit correspondence.

**The cost (pessimistic, Astra's).** **12 engineer-days** for the scoped layer-A experiment of §6 (replay, finite boundary choices, transition-level comparison, independent oracles, mutation measurements). Four to five days (the Opus estimate) buys a paired-replay demonstrator, not this mode. General recursive checkpoints and state deduplication are a separate **eight-day pessimistic extension** for the current layer-A layouts, undertaken only if replay cost warrants it.

**The counts.** The 741 coarse candidate pairs of §2.4 cover only the 12 completion kinds and 26 fault classes, before occurrence parameters, legality and reachability: they are not 741 independence laws. The work is at least `2(2 + k)` branch transitions per pair check for `k`-step continuations, before replay, copying, reference execution and comparison; under the restricted assumption of 28 pairs at each of 960,000 states and `k = 8`, that is about **538 million branch transitions for the pair checks alone** (Astra's correction of the Opus figure, which counted one route). Neither number is an upper bound on the experiment: 960,000 pool rounds are not 960,000 dispatcher states, and eight operation rows with two result cells each do not bound every completion, fault, clock and submission choice by 28. The experiment publishes actual branch lengths, replay work, comparison work and memory, never as a gate.

**What sampling keeps (Astra).** Sampling, deterministic scenarios and bounded systematic exploration stay for both independent and dependent interactions. Bugs are often in dependent orders, and systematic search explores those too. Local diamond checking asks whether a claimed interchange is valid; schedule exploration asks whether an execution violates a contract. They are different questions, not a division of behaviours between two modes. The orders of §4 (a publish between install and notify, a retry against an unresolved commit, a death cut inside a phase) are explored by schedules, with their declared orders as the contracts.

### 5.2 The DSL: one registry, templates for each shape

**The question is whether a declaration form is a second specification (Astra).** A form is useful if it connects an existing contract to its implementations, generates concrete obligations, and gives a checker or proof generator enough to consume them. It is a second specification if authors must restate the machine's transition catalogue, observations and admissibility rules in it. So the form references the existing machine, event or operation registry and an existing named contract; authors supply only the additional mathematics (the relation, the invariant, the matching transition or word, admissibility, any observation or occurrence correspondence); and generation checks coverage against the authoritative registry. G2 declarations additionally need a legal-choice enumerator, a residual correspondence and an endpoint relation; a function name in `:observes` supplies none of these.

Astra's minimal envelope (proposed syntax, not an existing macro; templates add required fields):

```lisp
(defsquare name
  :contract       existing-contract
  :sides          (implementation-a implementation-b)
  :template       :simulation              ; or :diamond, :quotient, :iso
  :cases-from     existing-transition-registry
  :correspondence existing-matching-definition
  :check          executable-check-adapter
  :teeth          (positive-witness negative-witness)
  :composition    applicable-library-theorem)
```

**What each instance emits (Astra).** Concrete `defthm-owed` formulas, or references to existing ones, with named executable teeth (the generator cannot manufacture meaningful witnesses from a relation name, and `fn2-assert-owed-teeth` runs named zero-argument functions without establishing that they exercise each generated case); executable case records with applicability conditions and a real checker entry point (a quantified ACL2 relation need not be executable); and composition or transformation events only where a library theorem's premises are supplied. `:checked` names the revision, profile, input domain, horizon and exercised instances, and is never interchangeable with `:proved`. TRACE needs a new entry point for this mode, and HISTORY, CONSUMER, WIRE, IDENTITY and RECOVERY are placeholders at the pinned revision, so "no new checker" is false as an implementation claim.

| instance | what a real consumer can use (Astra) |
|---|---|
| machine preservation (`defmachine :obligations`) | an invariant-preservation template over declared arms; `frame` additionally compares pre- and post-state, and `output-correspondence` needs a specified output meaning; neither follows from equality on the invariant's diagonal. `flat-representation` and `flat-transition` are a `:simulation` (or `:iso`) template between the stobj and the flat form (Q2); `budget-progress` is not a square |
| Q1 refinement | matching concrete and independent-reference transitions, initialization, output and work correspondence, then a turn-composition theorem; TRACE consumes the executable cases |
| Q4 summary | event-step preservation, converter correctness and observation agreement, instantiated into relational fold induction (`fc-rel-fold`) |
| Q5 materialization | a composite consumer relation including poll, deduplication, reasons, cursors and acks; schedule diamonds are additional obligations where actually valid |
| Q13 read port | snapshot factorization of the retained observations; future congruence only for a promised future interface; command translation adds simulation obligations |
| Q23 representation change | domain and image conditions, inverse laws and base-function correspondences consumed by `defiso` and `propagate-iso`; more than a base check |

**What Experiments A and B become.** A is the first convincing instance of the composition template: its reusable contract is 58 code lines, and the instance still writes the event lemmas, the converter theorem and the observation work (`rs-obs-count-agree`), which functional instantiation does not remove. B is an instance of the transformation template: **its measured toy cost stays 72 hand-written lines for 71 generated**, with 15 generated events, because registration does not write base correspondence theorems; `propagate-iso` consumes the isomorphism and the base correspondences, and `fc-rel-fold` is not its composition engine. Neither establishes correspondence to fn2's served columns. A form saves registration and enumeration, not proofs.

**Two positions on the form (decision 2 of §6).** *Opus:* one public form now, because shared registration and enumeration remove work repeated in six places, and a single form is what makes the generator mode's table complete by construction. *Astra:* a common registry with specialized templates first, because the single form as drafted omitted substantive premises and proposed consumers that do not exist yet. *What decides:* two real instances (the summary of Q4 and the refinement of Q1), counting hand-written semantic declarations, generated obligations and checker adapters, including the machinery needed to make both work. A single public form is welcome if it lowers that total without concealing an obligation.

### 5.3 The owed list: local obligations plus reusable composition lemmas

*Replaced by Astra's text, adopted; the Opus draft's claim that the keystones become "a finite local list plus one theorem" is withdrawn as stated.*

The engineering objective is reusable composition lemmas plus explicit local obligations. The three pasting shapes of §2.2 are a useful organization, not a demonstrated proof API for E, S, B, L, Q and T. `fc-rel-fold` handles its relational fold contract; simulations with matching words, emitted effects, crashes or nondeterministic targets need extensions and instantiation obligations; horizontal and mixed composition need the hypotheses of §3.2. Godefroid's Theorem 3.10 states horizontal pasting for a valid static dependency relation, but its ACL2 cost over fn2's transition system is not established by citing it.

**The count is 22, not 21.** RELEASE-PLAN §4 lists 21; the pinned code has 22 `defthm-owed` instances: five pool, four vocabulary, ten core (nine issue-refusal instances, entropy included, plus `fn2-core-harvest-byte-fill`), two executor-side (`fn2-turn-bounds` and `fn2-turn-refinement`) and one scheduler (`fn2-sched-starvation`). They are not all local invariants (Astra): `no-reuse` and `generation` relate before and after; the stale and refusal properties specify preservation and returned decisions; `result-reservation` covers enqueue, acknowledgment and posting; `harvest-byte-fill` starts from a trace of actual adapter writes. Calling them squares does not reduce their proof work.

**What changes shape.** `fn2-turn-refinement` (T2a) is the clearest candidate: per-transition G1 squares, but with initialization, boundary compatibility, termination and status, and work accounting beside them; at this revision `fn2-turn` calls `fn2-concrete-turn` while `fn2-ref-turn` implements list scheduling independently, so their correspondence is no longer equality by definition. T8 (`fn2-reply-trace-fragmentation-invariant`: for equal logical input, fragmentation preserves the reply trace) is a T square over fragmentation boundaries in exactly the sense of Q7, and is the second keystone the frame gives a shape. T3's bounds and T4's visitation stay explicit: counters, monitors and compositional cost arguments help prove them; observational equality does not. T7 (`fn2-acknowledged-survives`) and T9 (`fn2-exact-identity`) are durability and identity contracts; summary adequacy (Q4) supports them only through explicit client obligations. **So the reduction is real for T2a and T8, and nil for the rest of the present list.**

### 5.4 What it does not buy (Astra's list, adopted, with one Opus line)

- **The actual environment.** Nondeterminism does not prevent simulation proofs; they establish containment in a nondeterministic specification. What stays outside is the claim that real disks, networks and adapters satisfy the modelled assumptions (Q6). Native experiments give evidence, not containment.
- **Foreign implementations.** A command port needs a foreign-side model and an outcome correspondence. Finite safety refines across that boundary; eventual replies need progress assumptions.
- **Crash coverage for free.** The cut space is submitted-action prefixes × persistence states × faults × evidence × recovery transitions, not phases × fault classes. The closure of `→_C` composes matched recovery steps; it does not match missing cuts.
- **Runtime parallelism from declarations alone.** Shared scheduler and allocator effects constrain independence. Disjoint footprints are sufficient in suitable models, not necessary (shared operations may commute), and a conflict-free implementation still has to be built.
- **Progress and resource bounds from equality.** Bounded visitation can be checked as finite safety and costs can compose by explicit accounting; neither follows because two routes return equal values. Wall-time performance stays measured and published.
- **Independent semantics from shared handlers.** TRACE can miss a bug shared by both executors; OWN, the client oracle and the semantic contracts keep independent work.
- **Completeness or unbounded correctness from bounded checks.** The mode refutes declarations and exposes omitted cases; it neither proves them nor establishes a complete coherence basis.
- **Automatic speedup.** Local branching may find bugs sooner, or spend most of its time replaying and comparing. The experiment decides.
- **(Opus) One executor's internal concurrency.** Inside one node the scheduler is part of the semantics (EXEC rule 4), so few pairs of internal transitions are independent; G2's payoff is at the environment boundary (completion, fault and fragmentation orders), across domains and across peers. Order-preserving fusion (R2 §C.4's first form) needs no G2 at all.

---

## 6. The verdict, and five decisions for ember

*Co-written. The verdict sentence is the two authors' merge of Astra's ("Coherence is a useful foundation for a more powerful way to build, check and change fn2; a universal higher-categorical frame for fn2 remains an intellectual exercise") and the Opus draft's ("a foundation for how fn2 is checked and declared, not for what fn2 does at runtime"); the experiment, its mutation set, its interpretation and the decision table are Astra's (session 2), adopted, with the Opus positions recorded where they differ.*

**The verdict: it is a foundation, not an exercise, for how fn2 is built, checked and changed (every substitution and every reordering stated once as a local square that a checker or a proof consumes); the higher-categorical frame around it (Mac Lane coherence, a complete coherence basis, a universal theory of routes) is an exercise, except where a route carries data.**

The reasons, in ember's terms.
1. **Transport is the least interesting instance, and the coordinator was right about that.** The same square, `R` preserved by every step with observations agreeing, is what makes a summary replace history (Q4), a generated representation inherit its clients' theorems (Q23), a fused executor replace the reference (Q1), a materialized inbox stand in for selection (Q5), a port forget what it forgets (Q13), and a fragmented input give the same replies (T8). Twenty-five rows of §1, one shape, seven kinds of relation. That is broader and more useful than moving a world between versions, which D68 has priced at zero before the first release anyway.
2. **What it buys is accountability for substitutions and reorderings**, not new behaviour. An author states the relationship once; generated cases expose its omissions; a real checker or transformation consumes it. Experiment A showed reusable composition on a toy. Experiment B showed transport working and, at toy scale, saving no hand-written work (72 lines for 71). The frame has not yet shown a benefit on fn2's own code, and the experiment below is how it would.
3. **It already found things on paper.** It predicts UC §13's two inherited defects (coverage is not history; the mixed order is not free) as "not in the closure" (§2.3). It refuted the draft's own independence condition with a code-traced layer-A witness (§2.4). It turned five named problem interactions into one missing generator and four declared orders, each with new checkable obligations (§4.7). It found that one observation class cannot serve both WIRE and peer convergence, because article numbers are in reply bytes (§2.4). None of these needed category theory; all of them needed the question "which squares are generated, and under which contract".
4. **The higher-categorical part is thin almost everywhere.** fn2's squares are propositions (observations equal, relations hold), so Mac Lane's problem, that two pastings of 2-cells might differ, does not arise for them. It arises only where a route chooses data: position maps, converted cuts, occurrence identities, reported losses, and equations that are not permutations (duplicate absorption). Those want canonical data and a route-equation check (Experiment D's harness), not a library. A complete coherence basis would need a convergent presentation of fn2's routes, which fn2 does not have, and Astra's `cba` example shows that even sorting independent actions is not convergent without more rules (§3.4).

**Two positions on "not runtime".** *Opus:* this is a foundation for checking and declaration, not for runtime behaviour, which describes the immediate deliverable. *Astra:* "not runtime" is too permanent, because certificates can later authorize implementation choices, such as replacing history by a summary or fusing a reference segment. *What decides:* a real implementation generator or optimizer consuming a certificate while preserving a user-facing contract. Until then the note claims better checking, not a more capable runtime.

### 6.1 The first thing to build, and the measurement that decides it (Astra's design)

Build a **replay-based driver** that exhausts applicable local cases and bounded choice windows in layer A, on the real pool, echo and scribe workloads. It keeps the concrete scheduler, enumerates legal environment choices and submission or harvest boundaries, and never permutes internal continuations arbitrarily. The first finite domain: distinct small client payloads, full and short transfers, delayed completions, reset, early and late borrow release, stale and duplicate results, and selected descriptor-handoff deaths, every admitted value and boundary recorded in the experiment's manifest. The broad random workload stays as a separate baseline; the restricted experiment is not called exhaustive over all 26 fault classes. Exploration from initialization and from replayable prefixes that reach crowded or nearly retired states are reported separately: a supplied deep prefix tests a local claim but is no evidence that search found that state.

**The mutation set, frozen before timed runs.** Each admitted mutant needs a legal witness on which the original passes and the mutant violates a named contract; compile errors and unreachable mutants are reported separately. These are proposed mutations to qualify, not bugs claimed already executed.

| mutation | concrete change | distinguishing contract |
|---|---|---|
| premature listener/reclamation reuse | publish an echo row onto the free chain in `fn2-echo-observe-close` instead of in a successful `fn2-connection-release`, before outstanding borrows drain | close, release and a new accept expose a row to reuse while the old incarnation still owns work; allocator partition and incarnation ownership, then the client continuation |
| head insertion | `fn2-sched-make-runnable` inserts at the principal FIFO's head, links kept valid; `fn2-ref-enqueue` unchanged | two wakes give a different runnable order; TRACE fails, and the listener/reclamation fixture gives an admission consequence |
| lost early borrow release | in `fn2-harvest-one`, suppress `fn2-pool-release-out` for `borrow-released` when the terminal cell is not yet harvested | early release leaves a borrow retained after both cells are consumed; ownership and release accounting, then reset or reclamation |
| premature operation recycling | remove the leading terminal-not-harvested case from `fn2-op-harvest-phase` | an early release marks the operation done before its terminal result; OWN and the late completion expose a recycled identity or lost evidence |
| wrong short-send accumulation | in `fn2-echo-observe-send`, `off = count` instead of `off = old-off + count` | repeated short sends repeat bytes or never complete; the independent client byte oracle catches it even though concrete and reference handlers agree |
| incomplete independence footprint | a declaration covering listener admission and echo reclamation that omits the allocator, kept as checker input | the original legal race refutes the declaration; counted as a declaration defect, not a runtime defect |

The unmodified listener/reclamation race is a **negative independence control**, not a server bug: admission may legitimately depend on whether reclamation ran first. Early and late release are legal protocol alternatives, not automatically a co-enabled pair. Both modes get the same independent monitors; where OWN does not cover the machine free chain, an allocator-consistency monitor is added and given to both, so systematic exploration is never credited for an oracle withheld from sampling.

**What counts as found.** A saved, replayable legal execution that violates a named contract, with the first failing boundary identified; a failed diamond additionally records the common prefix, both routes, the occurrence correspondence and the first distinguishing observation. A raw field difference is not a semantic finding; a timeout is a censored measurement, not a counterexample; duplicates count once per mutant; seeded mutations and defects found in unmodified code are reported separately.

**Three configurations, so the result is attributable:** (1) the existing random driver with today's oracle cadence; (2) random choice through the new explicit-choice interface with the transition checks and shared monitors; (3) exhaustive local cases and bounded prefix enumeration through the same interface and checks. Comparing (2) with (3) separates a search improvement from better instrumentation; an optional random-prefix-plus-diamond configuration isolates the local checker's contribution. One designated box (a lane box under `swarm-build`, never hbox, never a timing measurement on `/tank`), one runtime image, one profile and input domain; precommitted seeds, enumeration orders and workload order; 20 campaign seeds or orderings per mutant, ten minutes of wall time per campaign; every trial, detection fraction, median, tail and censored run published; execution order rotated. Time to first detection includes replay, checkpointing, comparison and garbage collection; core, reference, adapter and replayed-prefix transitions are counted separately and in total, both branches counted; distinguishing trace length is reported apart from search effort; detection curves compared at common wall-time and transition budgets.

**How to read the result.**
- **Same bugs found faster**: configuration (3) finds the same qualified defect set at lower detection cost, in wall time, in transitions, or both, and says which.
- **New bugs found within the budget**: (3) finds a qualified defect that (2) misses under the precommitted budget. That is a bounded result, not a claim that sampling cannot find it; a defect in unmodified code is a separate and stronger result.
- **No demonstrated difference**: detection sets and costs show no useful improvement, or only the instrumentation change of (2) helps. Then **the generator mode is an exercise for layer A's workload**, and the note says so; the useful controls and diagnostics stay, and nothing is inferred about summary composition or representation transport, which stand on their own proofs.

**Size: 12 engineer-days, pessimistically** (three for explicit choices and replay, three for transition correspondence and semantic comparison, three for controls and mutation qualification, three for bounded enumeration, measurement and fixes), plus several machine-days for the campaigns. It excludes generic recursive checkpoints, partial-order reduction and a universal declaration form. The Opus draft's four to five days buys only a paired-replay demonstrator (§5.1).

### 6.2 Five decisions for ember

| # | decision | recommendation | cost, complexity, and what it forecloses |
|---|---|---|---|
| 1 | Build the measurement first? | **Yes**: the replay-based layer-A experiment of §6.1, before any declaration form or proof library | **12 engineer-days pessimistically**, plus machine time; adds a test driver and an explicit-choice interface; forecloses claiming a payoff before measuring one |
| 2 | Adopt one universal declaration form now? | **Astra:** one registry with separate simulation and diamond templates first. **Opus:** one public form now. Decided by two real instances (§5.2) | **four additional days pessimistically** for the two templates and two real consumers (Q4's summary, Q1's refinement); some explicit adapters remain; forecloses forcing lenses, isomorphism transforms and progress into an inadequate common record |
| 3 | Which equality does the checker use? | keep exact Q1 correspondence distinct from each semantic G2 contract; include histories and future-relevant state; every square names the contract it preserves (WIRE's reply bytes and Q12's validated facts are different contracts) | **two days, inside decision 1's budget**, for the initial contracts and controls; forecloses one permissive comparator that silently discards inconvenient effects |
| 4 | Prune schedules once bounded diamond checks pass? | **No**, until a sound dependence model and a bound-preserving reduction exist | **zero days now; 12 days pessimistically** for a later, narrowly scoped reduction prototype, excluding any general completeness proof; forecloses an immediate coverage claim resting on tested footprints |
| 5 | Invest next in a runtime consumer, or in categorical completeness? | one real consumer, preferably summary replacement (Q4, which STORAGE already owes) or order-preserving fusion (Q1), before any route-normalization framework; keep D68 | **ten days pessimistically** for one scoped integration experiment once its consumer exists, excluding the consumer's own construction; forecloses a general migration framework and a global coherence claim for the present release |

Decision 2 is the one open disagreement between the authors. Both agree on the deciding measurement and on decisions 1, 3, 4 and 5.

---

## 7. The Astra sessions, and where the two authors differ

Two sessions of `codex exec -m gpt-6-astra -s read-only -C ~/dev/fn`, each detached with a PID file. **Session 1** (prompt `fn2/coherence-astra-1.prompt`, answer `fn2/coherence-astra-1.md`, log `fn2/coherence-astra-1.log`) received §1-2, co-wrote §3 and §4, proposed the amended generating set of §2.5, rewrote the count of §2.4 as schemata and instances, and supplied the layer-A false diamond. It located four papers that were then fetched (`mellies-mimram2007-…`, `pous-sangiorgi2019-…`, `guiraud-malbos2018-…`, `coons-musuvathi-mckinley2013-…`). **Session 2** (`fn2/coherence-astra-2.prompt`, `.md`, `.log`) received §1-5, replaced most of §5, co-wrote §6 (the verdict's first half, the experiment, the mutation set and the decision table) and checked the note's adoption of session 1. Neither session hit a capacity or authentication error; session 2's log shows MCP transport errors from a local server that codex could not reach, which did not affect the answer. Astra's words are in those files; the note quotes or adopts them where marked.

| issue | Opus position, and its reason | Astra position, and its reason | state |
|---|---|---|---|
| what the coherence claim is | the generators suffice: a finite generating set plus a coherence theorem | two claims: soundness of generated diagrams (an induction, once the hypotheses hold) and completeness of the generators (the real conjecture, unproved, to be established per fragment) | **converged** on Astra's (§3.0, §3.2) |
| the non-free conditions | mixed pasting is the one condition that is not free | future closure, valid enabledness, label correspondence, dynamic consistency and adequacy of the observation contract are also not free | **converged** on Astra's (§2.5, §3.3) |
| independence condition in layer A | completions for different owners, or different principals, commute | "different machines" is refuted by the listener/reclamation witness; owner separation is a candidate condition to check, never a certificate, because the posted FIFO, allocator, quotas and services are shared | **converged** on Astra's (§2.4) |
| counts | about 125 generators for layer A by kind-pair arithmetic | count schemata, then measured instances; 741 coarse candidate pairs to classify, not laws; Q20 and Q21 have their own schemata | **converged** on Astra's (§2.4) |
| one observation class | exclude article numbers, so POSTs commute | impossible for reply bytes; contracts differ by claim | **converged** on Astra's (§2.4, decision 3) |
| Q1 as the containing square | every row lives inside Q1 | containment is not a correctness claim: shared handlers mean TRACE can pass a semantic bug; the short-send mutation discriminates | **converged** on Astra's, Q1 kept as the frame of the T rows only (§1 point 3) |
| Q5 | follows if and only if the poll is a generator | the whole consumer contract must be established; a generic merge theorem could discharge it; neither decomposition is necessary | **converged** on Astra's (§2.2) |
| Q7 | follows from the action law | only for the same induced word; moving harvest boundaries changes the word | **converged** on Astra's (§2.2, §4.6) |
| Q22 | follows once the allocator is a component | necessary, not sufficient; containment, not equality | **converged** on Astra's (§2.2) |
| G1q | a separate family | a declaration and checker variant, with snapshot factorization split from future congruence | **converged** on Astra's (§2.5) |
| crash squares | a finite family, phases × fault classes | a separate coverage table indexed by action prefix, persistence state, fault, evidence and recovery transition | **converged** on Astra's (§2.5, §5.4) |
| §4 verdicts | four interactions are "genuinely non-coherent" | they fail the equation for the exhibited implementations or the full response contract; a narrower square can be valid | **converged** on Astra's wording (§4.7) |
| PCT and COMMUTER | sampling finds a depth-2 bug with probability about `1/(nk)` at best | PCT's bound is a lower bound for PCT's scheduler only; fn2 inherits none; COMMUTER's SIM commutativity includes future indistinguishability | **converged** on Astra's (§3.5) |
| the cost of the first build | four to five days | 12 engineer-days pessimistically for the scoped experiment; four to five buys a demonstrator | **converged** on Astra's, the pessimistic number quoted (§5.1, §6.1) |
| owed list | the keystones become a finite local list plus one theorem; only T2a changes shape | 22 obligations, mostly not local invariants; T2a changes shape with initialization, boundaries and work beside it; T7 and T9 are durability and identity | **converged** on Astra's, with the Opus addition that T8 is a T square (§5.3) |
| **runtime** | a foundation for checking and declaration, not for runtime behaviour | "not runtime" is too permanent; certificates can later authorize implementation choices | **open**: decided by a real generator or optimizer consuming a certificate while preserving a user-facing contract (§6) |
| **one form or templates** | one public `defsquare` now, so the generator table is complete by construction | a registry with specialized templates first; the single form omitted premises and proposed absent consumers | **open**: decided by two real instances, counting declarations, obligations and adapters (§5.2, decision 2) |

What the collaboration changed, measured: §2 lost its independence condition, its count method and two derivations (Q7, Q22) and gained §2.5; §3 and §4 are Astra's apart from §3.0, §3.5 and §4.7; §5 is mostly Astra's replacement; §6's experiment and decisions are Astra's, the verdict is merged, and two disagreements stay open. The cost estimate for the first build rose from four days to twelve.

---

## 8. Bibliography

All sources are in `~/paperbin/` under the filenames cited inline. The 22 fetched for this note are annotated, with what each gives fn2, in the "Coherence" section of `~/paperbin/README-fn2-20261028.md`, with the gaps (Pous-Sangiorgi's 2011 chapter, Pous 2016, the Book of Traces as a whole, Diekert-Métivier, Kelly 1964, Joyal-Street, Squier-Otto-Kobayashi, Thomson-Donaldson-Betts, Abdulla et al.'s Source Sets) and their stand-ins. Two (Mac Lane 1963, Winskel-Nielsen 1995) are scans whose `.txt` is a local OCR. Reused from earlier passes: `mazurkiewicz1995-introduction-to-trace-theory.pdf`, `winskel1987-event-structures.pdf`, `goubault2000-geometry-and-concurrency-users-guide.pdf`, `goubault2003-geometric-perspectives-concurrency-theory.pdf`, `joyal-nielsen-winskel1996-bisimulation-from-open-maps.pdf`, `abstract-account-up-to-techniques-inductive-behavioural2024-2412.07351.pdf`, `kozen1997-kleene-algebra-with-tests.pdf`, `rutten2000-universal-coalgebra-theory-of-systems.pdf`. Practitioner threads, via Scry over `hackernews.items` (searched 2026-10-28): only link posts for the scalable commutativity rule (8552893) and DPOR-based checkers (21250657 on Loom and CDSChecker, 42279691 on McMini); none is quoted.
