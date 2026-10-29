# fn2's kernel as a multi-modal logic, and its worlds as theories (2026-10-28; Opus researcher with Astra as co-author; present state)

Brief: `build/coordinator/briefs/MODAL-KERNEL-20261028.md`, amended by the coordinator the same day with two rulings from ember: Astra is a co-author rather than a red team, and the note must guard against conceptual linkages multiplying. Ember, verbatim: "I notice this is starting to sound like (modal) logics and theories. Which is good. because that's the right direction." And, on the amendment: "we are, after all, trying to craft something usable (by us / for our own purposes..) and good."

Read against: `WIDEST-ROLE.md` (WR), `UNIVERSAL-CONSTRUCTIONS.md` §0, §9, §11, §13 (UC), `PLANES-AND-GAMES.md` §2 (PLANES), `PLANES-ADDENDUM-INTERWEAVING.md` (ADDENDUM), `REALMS-FROM-DREGG.md` (REALMS), `EXECUTION-MODEL.md` (EXEC), `STORAGE-DESIGN.md` (STORAGE), `TRANSPORT.md` §0-4 (the copy on disk stops inside Experiment E), the twelve drafts in `fn2/widest/`, and nanodregg's `CHARTER.md` laws. Papers are cited by filename in `~/paperbin/` (a `.pdf` with its `.txt` beside it). The ones fetched for this note are listed in the "Modal kernel" section of `~/paperbin/README-fn2-20261028.md`.

**The discipline this note keeps.** It follows UC's rule that a construction is named only if it predicts something concrete. The amendment adds three rules, and they bind every section:
1. **The base theory is UC §9's eight interfaces at one node and one revision** (the 5.1.1 fragment). Call it **B**. Every modality is an extension of B, and each extension is either shown **conservative** over B, or the note says exactly what it changes and flags that as a decision. Conservative here means that it proves nothing new about a single-node, single-revision world: every model of B expands to a model of the extension with the new sorts set to trivial values.
2. **A linkage counts only when the morphism is written down and something is checked across it.** Otherwise it is a footnote.
3. **Where two of WR's additions are one construction, they are merged and the merge is stated.** The test for every modality is the one the brief sets: it must correspond to a **checker**, a **refusal word**, or a **record kind**. A modality that has none of the three is cut as decoration.

The result is six judgment families, not the eighteen or so that the brief's prose and WR's nine-plus-sixteen invite. Four of WR's additions (Revision, Equiv, Port, Wire) share one mapping mechanism and a fifth (Transport) is a Decide that uses it; Witness, Receipt, Claim, Grant and the domain lease share one evidence infrastructure; Meter's reservations and custody share the obligations' accounting.

## Contents
0. The answer in one page
1. The frame
2. The axioms
3. The existing logics whose metatheory we would otherwise reinvent (co-written with Astra)
4. Worlds as theories (co-written with Astra)
5. What this changes in the engineering
6. The cost table
7. Five decisions for ember
8. The Astra sessions, and where the two authors differ
9. Bibliography

---

## 0. The answer in one page

**The claim, made precise.** fn2's kernel is the base theory B (UC §9's eight interfaces, at one node and one revision) extended by six families of modal judgments over a frame of worlds `(domain, position, revision, incarnation, node)`. Each family's optional interfaces admit a model expansion that preserves every old interpretation, so they prove nothing new about a 5.1.1 world (§2.8). What can change 5.1.1 is a change to an old admission, disclosure, release, availability or wire observation; the first such change on the table is the authorization checker, and fixtures decide exactly what it changes (decision 3). The worlds themselves are theories: a world's revision is a presentation, a port, a migration and a wiring are mappings between presentations, the composition of worlds is a pushout, and transport is a fenced Decide that moves a model along a mapping.

**The six, each with what makes it real** (logic | checker | refusal word | record kind):

| modality | logic | checker | refusal word | record kind |
|---|---|---|---|---|
| **M1 position** (`as-of`, `at-least`, cuts, interval time, supported reads) | hybrid past-time temporal logic over a discrete chain per domain and a lattice of cuts; nominals for positions; contextual reads | CONSUMER, HISTORY, TRACE | `gap`, `projection-behind`, `version-unavailable`, `supports-moved`, `anchor-backward` | `cut` |
| **M2 revision** (`under r`) | a translation judgment: an institution's satisfaction condition along graded mappings (`≡`, `ext`, `lossy κ`, `none`), connected to actual states by a certificate relation; no modal box is claimed | HISTORY (grades, 2-cells), WIRE (ports), TRANSPORT scenarios | `revision-moved`, `revision-orphans-obligation`, `refused-lossy`, `stream-owner-conflict` | `revision`, `migration`, `port`, `wire` |
| **M3 says with evidence** (`signed by`, `authorized by`, `witnessed by k of G`) | constructive authorization logic (lax `says` for derived affirmations, signed leaves as their own constructor, scoped speaks-for with hand-off), counting of witnesses on one bound statement, typed evidence constructors; checking only | the evidence checker in Decide; TRACE, IDENTITY, RECOVERY | `proof-format`, `unauthorized(reason)`, `authorization-context-stale`, `fenced`, `rolled-back`, `conflicted` | `grant`, authorization context, `claim`, `cosignature`, `receipt` |
| **M4 obligation** (`owes`) | a linear lifecycle (one terminal transition) with typed evidence (reusable receipts, consumable allocations) and declared contrary-to-duty continuations; not a deontic modality | HISTORY, RECLAIM, ACCOUNT | `evidence-insufficient`, `already-discharged`, `disposition-incomplete`, `budget-exhausted` | `obligation`, `discharge`, `waiver`, `hold` |
| **M5 command** (occasions, `in fork`) | deterministic dynamic logic for pure Decide (`[α]φ ↔ ⟨α⟩φ`), with persistence as a second subject; fork as a world-creating program when admitted | TRACE, WORK | Decide's words, `op-reused` | outcome (with producer interpretation and authorization context), `fork`, `promote` |
| **M6 durability** (`durable`, `transient`) | a two-point grade over the crash relation, with one typed declared-loss envelope | RECOVERY, CONSUMER | `gap(live-overrun)`, `gap(epoch-reset)` | `declared-loss` |

**What merged.** WR's Revision, Equiv, Port and Wire are one specification-and-mapping mechanism; Transport is a Decide that uses it; Witness, Receipt, Claim, Grant and the domain lease share one authenticated-evidence infrastructure ("says with evidence"), with distinct judgments; Incarnation is nominal uniqueness plus a lease; Meter's reservations share the obligations' resource accounting (its scheduling share stays a FAIR property); the counterfactual is a fork; every kind of declared loss is one envelope with typed variants. **What was cut**: an epistemic `K_i` (Halpern and Moses make common knowledge unattainable, and nothing fn2 checks needs it), SDL's `O` (obligations have no closure under consequence, which is why Chisholm's paradox does not arise), Lewis counterfactuals (a fork is constructed, not the closest world), and Halpern-Shoham interval operators (undecidable; two endpoint comparisons suffice).

**What the modal reading buys that the algebra did not** (each a check that can fail, a field or a word):
1. observation permanence becomes a theorem of the frame, whose three axioms are fencing, revision events and shared history (§1.3), so the TRACE and HISTORY properties that make it true are named;
2. the read contract returns `(q, r, v)` with coverage, and reads carry their supports and are refused with the moved supports named (P4, P8);
3. the outcome gains an authorization-context record (policy interpretation, proof, supports, time observations, issuer-indexed revocation cuts), without which a follower can reach another verdict, and admission separately checks that the context is acceptable now (§2.9, §5.2);
4. a port is a reduct whose forgotten distinctions are its declared loss, and a wiring is refused `stream-owner-conflict` before it runs (§4.2, §4.3);
5. conservativity is stated as model expansion and kept apart from migration certificates, which need a relation, a converter and retained-contract obligations; an `ext` migration's theory change must be conservative, which is necessary and not sufficient (§4.4, decision 2);
6. three interactions are settled: the obligation kind's evidence contract selects what discharges it, so the brief's "discharged only by evidence witnessed at k" is false as a universal law; events and outcomes keep their producer interpretation across a revision, while fold observations agree across one only through a certificate relation and coverage transfers only at the converted cut; authorization checking is monotone in a fixed context while context selection is not (§2.9).

**What it must not become.** A catalogue of logics, a modal theorem prover in the node, or a vocabulary with nothing behind it. No completeness theorem transfers without its translation; no signature establishes the truth of its payload; no colimit establishes consistency; no resource equation establishes progress; no observational equivalence supplies a fence (Astra, session 1).

---

## Notation (fixed for the whole note)

A **world** is `w = (d, p, r, i, n)`: commit domain `d`, position `p` in `d`'s journal, revision `r`, incarnation `i` of `d`'s writer, and hosting node `n`. **L_B** is the language of B: event atoms (`e@p`, "event `e` is at position `p`"), fold observations `obs_f(x)`, Binding facts, frontier values, and obligation states. Formulas are built from L_B atoms with the operators below and nothing else. Sorts never mix (PLANES L5): positions, live sequences, ticks, time-domain readings and revisions are five types.

| operator | read as | modality |
|---|---|---|
| `@p φ`, `@c φ` | φ holds exactly at position `p`; at cut `c` (a vector of positions). `p` and `c` are nominals | M1 position |
| `⟨≥p⟩ v` | the read is answered at an installed position `q ≥ p` chosen by the node, returns `(q, r, v)`, and is complete at `q` (UC's `at-least(p)`). It is not an existential search over past positions (Astra, §8) | M1 |
| `φ S ψ`, `G φ` | φ since ψ; φ at every later position | M1 |
| `@^r φ` | φ holds under revision `r` | M2 revision |
| `m : r →_g r'`, `σ_m φ` | a migration of grade `g ∈ {≡, ext, lossy κ, none}`, and its translation of formulas | M2 |
| `K says φ`, `t : K says φ` | `K` affirms φ (a derived affirmation inside an authorization proof); evidence term `t` checks it. A *signed* statement is a distinct constructor, written `signed(K, φ)`; `says` and "signed by" are not synonyms | M3 says |
| `K ⇒_s L` | `K` speaks for `L` within scope `s` | M3 |
| `G^k` | the threshold principal "any `k` of the set `G`" | M3 |
| `Owes(o)`, `Dis(o, t)` | obligation `o` is outstanding; `o` is discharged by evidence term `t` | M4 obligation |
| `o ▷ o'` | contrary-to-duty continuation: if `o` expires undischarged, `o'` is created | M4 |
| `[α] φ` | after command `α` is decided, φ holds | M5 command |
| `□_D φ`, `gap(cause)` | φ survives every crash and recovery; a typed record of what did not | M6 durability |

`▷` is written here for what Governatori and Rotolo write `⊗` (`governatori-rotolo2006-logic-of-violations-gentzen-contrary-to-duty.pdf`), because UC already uses `⊗` for joint evidence ("both are required"), and the two must not be confused.

---

## 1. The frame

### 1.1 Worlds and the six accessibility relations

WR §2 gives the coordinates. Each one carries one relation, and each relation has the properties the engineering gives it, not the properties a textbook logic would like it to have.

| relation | on | refl. | trans. | symm. | other | modal logic of its box | source of the property |
|---|---|---|---|---|---|---|---|
| **`≤_d`** later position in one domain | `Pos` within one `d` and one lineage | yes | yes | no | linear, discrete, with a least element (genesis); antisymmetric | `G` is S4.3 over a discrete linear order, which with `S` is past-time LTL over finite and growing traces | the free monoid's prefix order (UC §1.1): append is the only write |
| **`⊑`** cut inclusion | cuts: down-closed sets of `(domain, position)` | yes | yes | no | a distributive lattice (meet and join are intersection and union of down-closed sets) | S4 over a lattice; `@c` for a cut is a nominal | Mattern's consistent cuts (`mattern1989-virtual-time-global-states.pdf`); UC §1.3 |
| **fork-of**, and its closure **ancestry** | domains | fork-of: no (direct); ancestry: yes | fork-of: no; ancestry: yes | no | a forest; a child forked at `p` shares the event occurrences and historical snapshots `≤ p` with its parent, and nothing of its present | none of its own: it identifies historical snapshots (§1.3) | WR §2 Log → World ("fork by reference") |
| **`→_m`** migration | revisions | yes (identity) | yes (composition) | only for grade `≡` | a category; its `≡` arrows form a groupoid, and `ext`/`lossy` arrows are one-way | none: it carries translations (R4), not a box | TRANSPORT §3.1's four grades; rollback needs a valid backward migration (R6) |
| **`i → i+1`** incarnation succession, and its reflexive-transitive closure | incarnations of one `d` | the closure only | the closure only | no | linear; at most one incarnation is authoritative at any position, and fencing must be *enforced* at the commit authority and protected sinks, not merely recorded | it carries no box; it makes historical positions nominals (§1.3) | fencing (UC §6.3); WR Incarnation |
| **`→_C`** crash and recover, declared as the permitted crash-and-recovery closure | semantic states | yes, by declaration of the closure | yes, by declaration (a crash during recovery composes) | no | branching: recovery may land in several successor states, classified `intact / torn tail / damaged / unknown` | S4; `□_D` is its box | EXEC rule 8; STORAGE §1 |

There is no relation on nodes. A world's node is **not** part of what any fact means: an event at `(d, p)` is the same fact at every node that holds it, and moving `d` changes where it is decided, not what was decided. This is an axiom (A-LOC, §2.1). It is what makes transport a theory isomorphism plus a fence (§4.5) rather than a new kind of world.

Two relations on principals are also part of the frame. They are not coordinates of a world: they sit between the parties that author events.

| relation | on | refl. | trans. | symm. | other | logic |
|---|---|---|---|---|---|---|
| **`⇒_s`** speaks for, within scope `s` | principals | yes | yes, and scopes meet along a chain: `K ⇒_s L ∧ L ⇒_t M → K ⇒_{s ∧ t} M` | no | only narrows: a delegated scope is at most the delegator's | the speaks-for preorder of ABLP (`abadi-burrows-lampson-plotkin1993-calculus-access-control-distributed-systems.pdf`), with Garg and Pfenning's constructive, lax `says` (`garg-pfenning2006-non-interference-constructive-authorization-logic.pdf`) |
| **witnesses** `W(w, o)`: `w` co-signs checkpoints of origin `o` | principals × origins | **no**: a self-witness is not independent (A-INDEPENDENT-FRONTIER) | **no**: `a` witnessing `b` and `b` witnessing `c` gives `a` nothing about `c` | **no** | a finite, declared, versioned set per origin, with a quorum rule | a *graded* (counting) modality: `G^k says φ` holds when at least `k` successors in `W` assert φ (Fine's "in so many possible worlds"; the paper itself is a gap, §9) |

The brief asked whether `witnessed by k` is an epistemic modality "nearer common knowledge than belief". It is neither, and §2.4 states why: it is a `says` by a threshold principal, checkable from signatures, and common knowledge is the one thing fn2 can never claim (`halpern-moses1990-knowledge-common-knowledge-distributed-environment.pdf`).

### 1.2 Where the frame is a lattice, and where it is a groupoid

- **Lattices.** Positions within one domain form a chain. Cuts across domains form a distributive lattice. Frontiers are monotone maps into these lattices (UC §9.1, LVars). Every `wait`, timer and coverage check is a threshold predicate `F ≥ p` on one of them, and the lattice is what makes *that predicate* monotone: once true, true at every later position (UC's LVar freeze). The value an `at-least(p)` read returns is not monotone: a balance above ten at one position may fall below ten later. Only the coverage predicate that licenses the read is (Astra, §8 item 3).
- **A groupoid of mappings, not a box.** Revisions related by `≡`-grade migrations form a groupoid: every arrow has an inverse up to equality of declared observations, and two parallel routes must agree (TRANSPORT Experiment D's 2-cells). What that gives is coherent *translations* between interpretation-indexed languages (R4, R5). It does not by itself make `@^r` a modal box with S5 laws, and this note claims none (Astra, §8).
- **A category that is not a groupoid.** `ext` and `lossy` arrows are one-way, and `none` is the absence of an arrow. Across those arrows truth transports in one direction only, and only for the observations the arrow preserves (§2.3). This is why a rollback along a lossy migration is refused by name (`refused-lossy`, TRANSPORT Experiment D).
- **A tree.** Domains and forks form a forest. A fork is a *new* world-line that shares a prefix by identification, not by copying.

### 1.3 Nominals, and what makes a position name exactly one world

Hybrid logic (`blackburn2000-hybrid-logic-manifesto.pdf`) adds **nominals**, formulas true at exactly one world, and the satisfaction operator `@`. fn2's positions and cuts are meant to be nominals: `@p φ` is UC's `exactly-at(p)`. A position names one world only if three things hold. Each is an engineering property, not a logical one:
1. **one writer per `(d, i)`**, and an incarnation step fences every earlier one (UC §6.3; WR Incarnation);
2. **the revision in force at `p` is determined by the journal** (TRANSPORT §3.1: "every revision is a committed event"), so `(d, p)` fixes `r`;
3. **fork-of shares history, not the present**: for a child `d'` forked from `d` at `p₀`, the event occurrences and historical snapshots at `q ≤ p₀` are one and the same (`@(d', q) e ↔ @(d, q) e` for every event and outcome atom `e`), while parent and child keep distinct current authority, incarnation and obligation dispositions (O7). A position therefore names one *historical snapshot*; it does not identify the two whole worlds (Astra, §8 item 2: a formula about the current owner or the held effects would otherwise distinguish worlds the frame declared identical).

When all three hold, the hybrid-logic fact that **satisfaction statements are rigid** (`@p φ` is true at every world if it is true at any) applies, and it *is* WR's law of observation permanence ("an observation stamped `(r, p)` is never re-interpreted"). Hybrid rigidity holds inside one model. fn2's history is a model that *grows* (each append extends it) and may be *recovered* or *migrated*, so permanence also needs the named snapshot and its interpretation to be preserved by append, recovery and migration (Astra, §8 item 2). With that added, observation permanence is a **theorem of the frame**, and the axioms are where the work is: fencing (1), the revision event (2), and prefix sharing (3). A zombie incarnation that writes at `p` after a successor took over would make `p` name two worlds, which is exactly why its writes are recorded as equivocation and grafted only as observations (physical-and-offplanet §4 step 5).

### 1.4 Which operators have a modal class (K, T, S4, KD), and which are judgments of another kind

| modality | normal (K)? | T (`□φ → φ`)? | 4? | 5? | D? | classification |
|---|---|---|---|---|---|---|
| M1 `G` over `≤_d` | yes | yes | yes | no | yes | S4.3, discrete; with `S`, past-time LTL |
| M1 `@p`, `@c` | yes | n/a (nominal) | n/a | n/a | n/a | hybrid `H(@)`, which has the same complexity as the underlying logic, unlike the `↓` binder, which fn2 does not need (§3) |
| M2 `@^r` | not a box | — | — | — | — | **a translation judgment, not a modal operator over the revision groupoid**: `@^r φ` evaluates an interpretation-indexed sentence, and R4 relates translations. No S5 or S4 classification is claimed (Astra, sessions 1 and 2; the Opus author's earlier S5 reading is withdrawn, §8) |
| M3 `K says` | yes (`K says (φ→ψ) → K says φ → K says ψ`) | **no** (`K says φ` does not give φ) | yes, as the lax monad's join | no | no | a **lax modality** (CL, Garg-Pfenning): `φ → K says φ` and `K says K says φ → K says φ`. Not T, which is the whole point of authorization logic |
| M3 `G^k says` | **no**: `G^k says φ ∧ G^k says ψ` does not give `G^k says (φ∧ψ)`, because different `k`-subsets may have signed each | no | no | no | no | a graded (counting) modality, not normal; fn2 uses it only on *one* statement, a checkpoint claim, so the failure of closure under conjunction never bites |
| M4 `Owes` | **no** | no | no | no | no | **not a deontic modality at all**: an obligation is a linear resource with an evidence formula, so there is no necessitation and no closure under consequence (§2.5) |
| M5 `[α]` | yes | no | no | no | for total commands, `[α]φ ↔ ⟨α⟩φ` | deterministic propositional dynamic logic: every Decide is total and deterministic, so its box and diamond coincide (§2.6) |
| M6 `□_D` | yes | yes | yes | no | yes | S4 over the crash relation, used as a 2-point grade (`durable ⊐ transient`) |

Two of these are the most useful lines in the table, because they are where a reader expecting textbook logic will be wrong:
- **`says` is not T**, and `Owes` is **not KD**. Standard deontic logic (SDL) is KD, and its paradoxes (Ross: `O p → O(p ∨ q)`; Chisholm's contrary-to-duty set) come from K's closure under consequence. fn2 obligations have no such closure: an obligation whose evidence formula is `p` is not discharged by `p ∨ q`. That is why fn2 inherits none of the paradoxes, and it is a reason never to describe obligations with SDL's `O`.
- **Transport is syntactically restricted.** R4's translation preserves only formulas stated through the declared interface (`init`, `step`, `obs`), which is TRANSPORT §1.1's structure-identity rule. A formula that mentions a representation accessor is not in the translated language. This is checkable: a theorem's statement either uses only declared observations or it does not.

---

## 2. The axioms

Each law is written once, in the notation, with its **status**:
- **Ax**: an axiom, definitional; the engineering makes it true by construction, and a checker refutes an implementation that breaks it;
- **Th**: a theorem of the frame, true once the axioms hold;
- **Ob**: an obligation discharged per instance (per fold, per migration, per port), by proof or by a refuting simulator scenario;
- **As**: an empirical assumption about the platform or the world, which no proof inside fn2 discharges.

The last column says whether the law is in B already, or which modality extends B with it and whether the extension is conservative (§2.8 gives the expansion that proves it).

### 2.1 The base: PLANES' six laws, EXEC's meaning rules, STORAGE's decisions

| # | law | formula | status | checker | in B? |
|---|---|---|---|---|---|
| L1 | authority flows down (PLANES) | every *authoritative premise* of a Decide (a fact it relies on about state, identity, evidence or another domain) is `□_D`; foreign premises enter as `t : K says φ` with `□_D` of the *receipt*, never of φ. The incoming command and a volatile reservation are inputs, not premises, and need not be durable (Astra, §8 item 5) | Ax | TRACE (a committed outcome whose authoritative premise was transient) | B, with M3's form for foreign premises |
| L2 | every upper state is reconstructible plus declared loss | for a projection `f` with sources `S` and coverage `cov`: `@p obs_f = Fold_f(S ≤ p)` for `p ≤ cov`, otherwise `gap(projection-behind)` or `gap(declared-loss κ)` | Th for internal projections (the action law, UC §2.1); As for external executors, which only sign | HISTORY; CONSUMER | B |
| L3 | output gating | an output correspondence property, not a dynamic-logic formula (`[α]⊤` is valid even when `α` refuses): `emitted(α, durable-assertion(x, φ)) → established-durable-evidence(φ)` (Astra, §8 item 5) | Ax | RECOVERY; WIRE | B |
| L4 | loss is typed | for a non-durable item `x`: `¬□_D x → ◇ gap(cause)` with `cause ∈ {live-overrun, epoch-reset, unavailable, …}`, and no silent hole | Ax | CONSUMER (live-class oracle) | B |
| L5 | positions never mix | sort discipline: no accessibility relation crosses sorts; a mapping between sorts is itself an event (a checkpoint records the tick and the positions it covers) | Ax (typing) | the DSLs' type checks | B |
| L6 | time is declared | every deadline names a time domain `τ`; no relation in the frame is wall time, so no `[α]` is selected by it | Ax | TRACE (schedule independence of wall time) | B |
| E1 | one executor, one semantic state (EXEC 1) | worlds of one node at one instant form one state; transitions are the only change | Ax | all | B |
| E4 | the scheduler is part of the semantics (EXEC 4) | `[α]` is a function of `(state, observation order, schedule)`; two runs with equal inputs give equal outcomes | Ax | TRACE, FAIR | B |
| E5 | isolation (EXEC 5) | two laws, not one: (a) **stock**: a reservation is a hold `Owes(h)` with an allocation identity and a quantity `q` in a resource unit, `Σ holds ≤ capacity` per principal, and one reservation is never spent twice; (b) **service**: a continuously eligible principal is visited within `L` visits, which follows from the calendar and eligibility rules (EXEC 4), not from any conservation equation (Astra, §8 item 7) | Ax (a), Th of the scheduler (b) | ACCOUNT (a), FAIR (b) | B, with (a) restated through M4 (flagged, §2.8) |
| E8 | durability with uncertainty (EXEC 8) | `uncertain(α)` is the commit protocol's classification when the recovery evidence establishes neither durable acceptance nor definitive non-acceptance; Decide itself stays deterministic. Read modally, it concerns the histories compatible with the evidence held, not necessarily several crash successors of the actual physical state. Recovery resolves it only by evidence, and `uncertain` never reads as `refused` | Ax (definition of the outcome) | RECOVERY (lose a barrier completion after the batch may have persisted, then retry after recovery) | B |
| A-PF | A-PERSISTENCE-FENCE | a completed barrier makes what it covers `□_D` | As (the device) | M7 filesystem experiments, published | B |
| A-IE | A-INTEGRITY-EVIDENCE | damage is detectable by the declared evidence | As | RECOVERY under fault profiles | B |
| A-IF | A-INDEPENDENT-FRONTIER | rollback below `n` is detectable only if acceptable independent evidence of `n` survives (a witness cosignature is the usual form, not the only one; an untrusted `says` is none) | As (that the evidence is independent and survives) | RECOVERY with a `rolled-back (witnessed)` scenario | M3, conservative (§2.8) |
| S1 | summary equation (STORAGE 1) | `State = Fold(Summary_k, Events_{k+1..n})` | Th (the action law) | HISTORY | B |
| S1' | discarding history | `Summary_k` may replace `Events_{≤k}` only if, for every retained-contract observation `o` and every suffix `s`, `obs_o(Fold(Summary_k, s)) = obs_o(Fold(Events_{≤k}, s))` | Ob (per summary rule; UC §2.2's per-event-kind certificate is sufficient) | HISTORY scenario 3 | B |
| S1'' | retry returns the original outcome | for operation identity `op` decided at `p₀`: `[retry(op)] out = @p₀ out`, and a contradictory reuse is refused (`op-reused`) | Ax | CONSUMER scenario 2 | B |
| S6 | exact identity is permanent | `bound(mid, x) → G bound(mid, x)`: once bound, bound at every later position, after any reclamation of the body | Ax | IDENTITY | B |
| B1 | Binding merges by union, `conflicted ⇔ ≥ 2` (UC §4.3) | for equal validated fact sets `F`: Binding at every node is `∪F` | Th | IDENTITY scenario 6 | B |
| A-LOC | location independence | `@(d,p) φ` has the same truth at every node holding `(d, p)`; a node is where `d` is decided, never part of what `d` means | Ax | TRANSPORT (old reads equal translated new reads) | B (one node: vacuous) |

### 2.2 M1: position, cut and time (hybrid past-time logic)

| # | law | formula | status | checker | extension |
|---|---|---|---|---|---|
| P1 | append is the only write | `e@p → G e@p` (an event, once at `p`, is at `p` at every later position) | Ax | HISTORY | B |
| P2 | nominal uniqueness | for each `(d, p)` there is one historical snapshot: one authoritative writer per `(d, i)`, and `i' > i` is fenced at the commit authority and at protected sinks (§1.3) | Ax | TRACE: no two incarnations commit at one position | M1 + incarnation, conservative |
| P3 | observation permanence | `@p φ → G @p φ` and `@p φ → @q @p φ` for every `q`, for event and outcome atoms and for observations under their stamped revision | Th (rigidity of satisfaction statements, given P1, P2, R1, plus preservation of the named snapshot by append, recovery and migration) | HISTORY | B |
| P4 | two read strengths (UC decision 2) | `exactly-at(p) ≝ @p`; `at-least(p)` returns `(q, r, v)` with `q ≥ p`, the interpretation complete at `q` (`cov(f@r) ≥ q`; a latest-only materializer answers at its own covered state, so a head at 100 with coverage 80 answers at 80 for a request at 70, never "at 100") and `v = obs_{f@r}(q)`; `@p obs_f` needs retained version state at `p` | Ax | CONSUMER (a read after a debit, with an older qualifying snapshot retained, must return the current value) | B |
| P5 | frontiers are monotone | for a frontier `F`: `F ≥ p → G (F ≥ p)` | Ax | CONSUMER; FAIR | B |
| P6 | wake is a hint | a wake makes a consumer *eligible* to re-check; delivery requires the re-check at the installed state, available resources and scheduling, and never follows from the wake alone | Ax | CONSUMER (INBOX's final frontier check) | B |
| P7 | a multi-domain cursor is a cut | `c` is down-closed: `(d, p) ∈ c ∧ (d', p') ≺ (d, p) → (d', p') ∈ c`, where `≺` is the cross-domain dependency recorded by receipts | Ax | CONSUMER; TRANSPORT ("no cut regressed") | M1 cuts, conservative (one domain: a cut is a position) |
| P8 | reads name their supports (REALMS item 4, nanodregg holes) | a read result is `@c [Ψ] v`: a value valid in the context `Ψ` of the supports it read (including the version of a searched fibre when it found nothing), at cut `c`. Reuse at `c' ⊒ c` is licensed when `@c' Ψ = @c Ψ` (sufficient), or through a checked contextual substitution from `Ψ` into the new context; otherwise the read is refused `supports-moved(Ψ')` listing what moved | Ax | CONSUMER | M1, conservative (contextual modal types, §3) |
| P9 | interval time with two firing senses | a time-domain reading is an interval `[t⁻, t⁺]` in domain `τ`; for a deadline `δ`: `certainly(δ) ≝ t⁻ ≥ δ`, `possibly(δ) ≝ t⁺ ≥ δ`; every obligation and grant declares which sense releases it, and custody releases only on `certainly` | Ax | TRACE scenario 5 (re-anchor), plus a release-sense scenario | M1, conservative (a point clock is an interval of width 0, where the two senses coincide) |
| P10 | time domains are monotone across anchors | `t⁻` never decreases along `≤_d`; a backward re-anchor is refused (`anchor-backward`); a pause delays only unreached deadlines | Ax (UC §6.4) | TRACE scenario 5 | B |

Halpern and Shoham's interval logic is *not* adopted as a logic (it is undecidable in general, and the decidable fragments are small: `marcinkowski-michaliszyn2010-last-paper-halpern-shoham-interval-logic.pdf`). fn2 needs only P9's two atomic comparisons, which are Allen relations between an interval and a point, decided by two integer comparisons.

### 2.3 M2: revision, migration and transport (an institution's satisfaction condition)

| # | law | formula | status | checker | extension |
|---|---|---|---|---|---|
| R1 | a revision is a committed event | `adopt(r → r')@p` determines `rev(q) = r'` for `q ≥ p` until the next adopt; `rev` is a Fold over revision events | Ax | HISTORY | M2, conservative (one revision: `rev` is constant) |
| R2 | history is never re-decided | for every event and outcome atom `a`: `@^r @p a ↔ @^{r'} @p a` | Ax | HISTORY (no replay re-decides; STORAGE decision 1) | M2, conservative |
| R3 | world age, and the Decide crossing rule | an activation started at `p` under `r` finishes under `r`, except Decide: a Decide revision activates only when no command of the revised set holds a continuation in the domain, or the crossing command is revalidated under `r'` before commit (TRANSPORT §3.2(iv)) | Ax | TRACE; TRANSPORT §3.2(vii)'s gating scenario | M2, conservative |
| R4 | the satisfaction condition along a migration, connected to actual states | sentences: for `m : r →_g r'` and φ over the observations `g` preserves, `M' ⊨ σ_m φ ⇔ m*M' ⊨ φ`. States: a certificate relation `R_m` with `R_m(s, s') ⇒ obs_{f@r}(s, q) = obs_{f'@r'}(s', ρ(q))`, extended over corresponding admitted suffixes by step preservation. For `≡` both directions; for `ext` the old observations; for `lossy` the observations constant on the identification classes of the kernel relation and with a compatible target interpretation; for `none` nothing | Ob (TRANSPORT §3.1's per-event-kind certificate) | HISTORY (grade claims); Experiment D (2-cells) | M2, conservative |
| R5 | coherence of routes | for parallel routes `m₂ ∘ m₁` and `m₃` declared equal: `σ_{m₂} σ_{m₁} φ ↔ σ_{m₃} φ` at every suffix | Ob | HISTORY (Experiment D, future-suffix comparison) | M2 |
| R6 | rollback needs a valid backward migration | `rollback(r' → r)` is admitted iff a backward migration valid for the current state, the events still admitted and the outstanding contracts exists; an `≡` path is sufficient, not necessary (TRANSPORT §3.2, its Astra 4); otherwise `refused-lossy` | Ax | Experiment D | M2 |
| R7 | dependencies are derived | a changed dependency manifest of an interpretation changes the composed interpretation's identity and triggers its compatibility checks; it need not change a Decide's command semantics. Dependencies are derived through the access boundary, never hand-written read lists (TRANSPORT §3.1(v)) | Ax | HISTORY | M2 |
| R8 | compatibility of a Decide revision | the revision states a named compatibility relation per obligation kind, preserving authorized discharge, fencing, retry outcomes and retained promises; mere expressibility of `ev(o)` under `r'` is not enough (replacing "authorized receipt" with `true` is expressible). Checked when the revision is *built*, over the finite declared kinds; at commit a bounded check refuses `revision-orphans-obligation` for any outstanding kind lacking a relation (TRANSPORT §3.2(iv)) | Ax | HISTORY | M2 |
| R9 | transport is a mapping plus succession | `transport(d; n → n', r → r', i → i+1)` carries the semantic state and retained contracts along a certified mapping (R4), establishes authoritative succession (the source fenced at its commit authority and protected sinks, the destination installed through its persistence protocol before success is published), records the position map `p₀ ↦ p₀'` as an event (L5), carries every outstanding obligation (M4) and maps every registered cut (P7). Semantic preservation and succession are two independently checked obligations | Ax (as a Decide) | TRANSPORT scenarios (WR §4's gate), with death cuts before and after each fence, persistence and installation boundary | M2 + M3 + M4, conservative (no transport events in B) |

R4 is the one law that makes M2 a modality worth having. Everything else in the "revision" column of WR (Equiv, Transport, Port, Wire, and the revision stamp on events) is either R4 at a particular grade, or an application of it to a particular morphism. §4 shows which of them share one mapping mechanism and merges them.

Under ember's D68 (TRANSPORT decision 1), every revision before the first release is a wipe and rebuild, so M2 is *specified* now and built after the release; R1-R9 are the specification. That is exactly M2's trivial expansion (one revision), which is why it is conservative.

### 2.4 M3: says with evidence (authorization, witness, receipt, claim)

| # | law | formula | status | checker | extension |
|---|---|---|---|---|---|
| A1 | unit and join (lax), for derived affirmations only | inside a proof: `φ → K says φ`; `K says K says φ → K says φ`; `K says (φ → ψ) → K says φ → K says ψ`. Signed leaves are a separate constructor: the unit never manufactures a signature, and an unsigned tautology presented as a checkpoint fails the evidence check (Astra, §8 item 4) | Ax (the logic) | the proof checker | M3 |
| A2 | speaks for, within scope, only narrowing | `(K ⇒_s L) ∧ (K says φ) ∧ φ ∈ s → L says φ`; `K ⇒_s L ∧ L ⇒_t M → K ⇒_{s∧t} M` | Ax | proof checker; attenuation property in TRACE | M3 |
| A3 | a grant is a signed delegation plus a hand-off | `grant(g) = t_g : I says (H ⇒_{scope(g)} I)` with expiry `@[u₁,u₂]` in a named time domain and a revocation handle; it takes effect through ABLP's hand-off rule `(I says (H ⇒_s I)) → (H ⇒_s I)`, which the policy grants only to issuers it names: a signed statement alone confers nothing | Ax | proof checker (negative cases: expired delegation, scope-widening child grant) | M3 |
| A4 | validity at head is validity at a recorded cut | a chain `π` is valid for `α` at `p` iff every link is unexpired under P9's declared sense at `p` and unrevoked at the cut `c(α)` of each issuer's revocation domain that `α`'s outcome records | Ax | TRACE (replaying the outcome with the recorded `c(α)` gives the same verdict) | M3, **not conservative** (§2.8) |
| A5 | a checkpoint claim is a signed bound statement; a receipt is a constructor | `t_sig : D says stmt(o) = (history, incarnation, cut, count, root, policy)`; a **receipt** is `receipt(checkpoint-evidence, inclusion-proof, bound-statement)`, checked against the statement's history, incarnation, cut, root and policy bindings (not an application of a signature to a proof) | Ax | IDENTITY; RECOVERY | B has the signed claim; the receipt constructor is M3, conservative |
| A6 | witnessed | `witnessed_k(stmt)`: `k` distinct accepted witness principals cosign the **same bound checkpoint statement** (history, incarnation, count, root) under a named witness-policy version; counting signatures on `count ≥ n` alone would omit root and lineage compatibility | Ax | RECOVERY (fixture: two roots at one count, duplicate signers, a policy transition) | M3, conservative |
| A7 | equivocation is a Binding conflict | `K says ψ₁ ∧ K says ψ₂ ∧ incompatible(ψ₁, ψ₂) → conflicted(K, key)`: double-spend, split view and a zombie body are three instances | Th (from B1) | IDENTITY | B, generalized |
| A8 | freshness | a candidate authoritative head or recovery state below accepted independent frontier evidence is refused (`rolled-back`); an explicitly historical read, or an old inclusion receipt below that frontier, stays legal | Ax | RECOVERY scenario: hold a checkpoint at 100, read a valid receipt at 60, attempt recovery at 60: only the recovery is stale | M3 |
| A9 | visibility is the pullback along the grant | a read by `K` returns `@c obs` restricted to `scope(K)`; never a filter applied to an unrestricted answer | Ax | CONSUMER (a disclosure oracle) | M3, **not conservative** where 5.1.1 reads are unscoped (§2.8) |

**Why not an epistemic modality.** `K_i φ` ("node `i` knows φ") is the logic of Halpern and Moses, and its main result for fn2 is negative: under unreliable communication, common knowledge of anything that was not common knowledge at the start is unattainable, and only weaker variants (eventual, timestamped, ε-common knowledge) are achievable. fn2 needs none of them. What it needs is A8: whoever has *seen* a witnessed claim refuses a rollback below it. That is a property of a held justification, stated with M3, and checked by RECOVERY. A modality `K_i` would correspond to no checker, refusal word or record kind, so it is cut. Justification logic (`artemov2008-logic-of-justification.pdf`) is the right reading of what remains: `t : φ` with application `s · t` and sum `s + t` is exactly how a receipt (A5) and an evidence formula (§2.5) are built, and fn2 only ever *checks* terms; it never searches for them.

### 2.5 M4: the obligation resource (deontic, without the deontic paradoxes)

| # | law | formula | status | checker | extension |
|---|---|---|---|---|---|
| O1 | outstanding or one terminal transition (UC §6.1) | every created obligation is outstanding or has exactly one authorized terminal transition allowed by its kind (`discharged`, `cancelled`, `waived`, `expired`); never two. This is safety only: eventual discharge is a separate liveness claim under stated assumptions | Ax | HISTORY | B |
| O2 | discharge is a checked evidence term at head | `[discharge(o, t)] Dis(o, t)` only if `t : ev(o)` checks at the head position, and the discharger is admitted by `o`'s declaration (M3) | Ax | HISTORY; TRACE | B, with M3's form |
| O3 | evidence formulas | `ev ::= atom | ev ⊗ ev | ev ⊕ ev | k-of-n(ev…) | q ≥ amount`; atoms are local events, authenticated statements, receipts (A5) and witnessed statements (A6). Checked as `Γ ; Δ ⊢ t : ev(o) ⊣ Δ'`: `Γ` holds reusable facts and receipts, `Δ` the consumable allocations, and joint evidence consumes disjoint allocations where the contract demands it | Ax | the evidence checker | B extended (k-of-n, quantity) conservatively |
| O4 | no closure under consequence | there is no rule from `ev(o) = φ` and `φ → ψ` to anything about `ψ`; obligations are records | Ax (the absence of a rule) | none needed | B |
| O5 | contrary-to-duty continuation | `o ▷ o'`: `expired(o) ∧ ¬Dis(o) → created(o')` in the same batch; a discharge may also create a continuation (`Dis(o) → created(o'')`, custody's next leg) | Ax | HISTORY | M4, conservative (no continuation declared: nothing created) |
| O6 | two parties, separately transferable | `o = ⟨obligor, obligee, …⟩`; assigning the obligee needs the obligee's grant; delegating the obligor needs the obligee's | Ax | HISTORY | M4, conservative (obligee := the node) |
| O7 | disposition at a fork is total | `fork(c)` is refused `disposition-incomplete` unless every `o` with `@c Owes(o)` is assigned to exactly one of `parent`, `child`, `refuse`, `split(ev₁, ev₂)` | Ax (a Π-read, UC §3.2) | HISTORY with the fork scenario of os-substrate §4 step 6 | M5 + M4 |
| O8 | effects in a fork are held | in a fork world, an external-effect obligation has no adapter able to discharge it; `promote` re-issues it on the parent under the parent's Decide | Ax | CONSUMER; RECOVERY | M5 + M4, conservative |
| O9 | quantities conserve; receipts are reusable unless consumed | for a unit `u`: `issued_u − burned_u = Σ balances_u + Σ holds_u` at every position. Linearity applies to consumable authority and to quantities, which carry allocation identities so one receipt cannot fund two transfers; an immutable receipt may justify any number of observations unless a contract explicitly consumes it (Astra, §8 item 7) | Ob (per event kind, UC §2.2's certificate) | ACCOUNT | M4 (economy) and E5(a) (Meter): one law |

**Chisholm, read in fn2.** The contrary-to-duty set (you ought to help; if you help you ought to tell; if you don't help you ought not tell; you don't help) is paradoxical in SDL because `O` is closed under consequence and detached by modus ponens. In fn2 (where an expiry counts as a violation only when the obligation's declaration says so), "help" is `o₁` with `ev = helped`, "tell" is `o₂ = o₁ ▷ ¬tell` on expiry and `Dis(o₁) → created(tell-owed)` on discharge. Nothing is derived: each obligation is created by a commit and discharged by a checked term, so the four sentences are four records and two continuations, and they are consistent. The brief's remark that "the Chisholm paradox is exactly an obligation whose discharge creates the next" is right in spirit and should be sharpened: in fn2 the *expiry* creates the contrary-to-duty obligation and the *discharge* creates the follow-on, and both are declared continuations, never inferences.

**The brief's interaction "an obligation is discharged only by evidence that is witnessed at k" is false as a universal law.** Local evidence, an event in the obligation's own domain, is the authority by L1 and needs no witness. The Opus draft first corrected it to "witnessed evidence exactly when the evidence is foreign"; Astra (session 2) showed that is too rigid in both directions: a signed foreign receipt from a trusted peer can suffice, and a local claim can require a quorum. The adopted law: **the obligation kind's evidence contract selects the evidence**, and `witnessed_k` is one atom it may require (§2.9). One evidence engine must express both a kind that accepts a trusted peer receipt and a kind that requires a quorum.

### 2.6 M5: command (occasion-typed dynamic logic)

| # | law | formula | status | checker | extension |
|---|---|---|---|---|---|
| C1 | pure Decide is total and deterministic; persistence reports the rest | for each command `α`, Decide returns `accepted(events)` or `refused(word)` deterministically (`[α]φ ↔ ⟨α⟩φ`); the commit protocol then reports established acceptance, definitive non-acceptance, or `uncertain` (E8) | Ax | TRACE; WORK (the bound) | B |
| C2 | preconditions in order (WR §2) | `Pre(α) = auth(α) ∧ reserve(α) ∧ receipts(α) ∧ pred_occ(α)`, evaluated in that order; the refusal word is the first failing conjunct's | Ax | TRACE (a refusal word determined by the first failing precondition) | M3 + M4, **not conservative** through `auth` (§2.8) |
| C3 | one atomic mutation per domain | `[α]` touches one domain's journal; cross-domain agreement is a sequence of `[α_d]` linked by receipts and holds | Ax (architecture, UC §1.1) | TRACE | B |
| C4 | the occasion is part of the command | `α ∈ Cmd_occ` for `occ ∈ {birth, adopt, write, relaw, invoke, import, fork, promote, transport}`; each occasion has its own `pred_occ` | Ax | the grammar DSL | M5, conservative (B's commands are all `write`) |
| C5 | an installed law is amended only by its own rule | `[relaw(k, π')]` is admitted only if `Decide_k`'s current program accepts the relaw | Ax | HISTORY | M5 + M2, conservative |
| C6 | a fork is a program that creates a world, when admitted | `accepted(fork(c, r', policy)) → ∃d'. fork-of(d', d, c) ∧ …`; a refused fork creates no child. A counterfactual "had we run `r'`" is `⟨fork(c, r'); replay(cmds)⟩ φ` | Ax | HISTORY; the behavioural-diff fold (versioned-world §4) | M5, conservative |
| C7 | fork isolation | no world reachable from a fork reaches its parent except through `[promote(cmds)]`, which re-decides each command on the parent and refuses by name where its binding moved | Ax | HISTORY; CONSUMER | M5 |

A counterfactual in Lewis's sense picks the *closest* world in which the antecedent holds. fn2 never needs similarity: the counterfactual world is *constructed* by C6 (same recorded commands, another revision, effects held), so "held in a fork" is a dynamic modality over a deterministic replay program, not a counterfactual conditional. The brief's "counterfactual" is merged into M5.

### 2.7 M6: durability grade and declared loss

| # | law | formula | status | checker | extension |
|---|---|---|---|---|---|
| D1 | the grade | each item carries `g ∈ {durable, transient}`; `durable ⇒ □_D` under the declared fault profile and retained contract (not a promise to keep every payload forever, nor to reconstruct acknowledged data from damage the profile excludes); `transient` promises nothing across `→_C`, which is declared as the permitted crash-and-recovery closure | Ax | RECOVERY; CONSUMER | B (UC's two grades, per item since ADDENDUM) |
| D2 | grades propagate by dependency | a durable record that depends on content `x` either inlines or names `x` durably, or carries the typed lossy reference `(epoch, seq)`, whose grade is `transient` | Ax (UC decision 5) | CONSUMER | B |
| D3 | promotion is an ordinary commit | `established(commit(y, refs(x₁…x_n))) → □_D y`, with `x_i` inlined or named; a commit request alone establishes nothing | Ax (ADDENDUM item 3) | CONSUMER scenario 4 | B |
| D4 | declared loss is one envelope with typed variants | `declared-loss(source, variant)` where `variant ∈ {kernel(identified states), unavailable(interval), estimate(method, uncertainty), omitted-fields(list)}`: a projection or port kernel, an unavailable historical range, a covariance under a named estimator, a dropped field. One read field and one record kind, but each variant keeps its own composition rule, and composing two losses keeps both, never a scalar (Astra, §8 item 8) | Ax | CONSUMER; HISTORY | M6, conservative (B has no declared loss beyond gaps) |

The merge in D4 is of the *envelope*, not of the meanings: the dual of the durability grade (what a crash may lose), the kernel of a morphism (what a translation identifies), a covariance (what an estimator does not know) and an omitted field are recorded by one record kind and reported in one read field, each as its own typed variant with its own composition rule. Physical-and-offplanet's covariance, the commons' `declared-loss`, PLANES L2 and L4, and TRANSPORT's lossy kernel are four producers of one record kind, never of one value.

### 2.8 Conservativity over B, extension by extension

*Co-written. The Opus draft gave a table that ended "everything is conservative except two clauses of M3". Astra's session 2 replaced it with the table below, which the Opus author adopts: it states expansions, not convenient deployments, and it withdraws the claim that those two clauses are the only possible non-conservative changes.*

The proof shape is model expansion: given any model of B (one node, one revision, one incarnation, no witnesses, no forks), give the new sorts inactive values, guard the new laws by activation, and check that every old operation keeps its interpretation. A local witness that an extension is consistent proves consistency, not conservativity.


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

The Opus draft's conclusion that exactly two clauses of M3 were the only possible non-conservative changes is withdrawn. The defensible conclusion is that the corrected optional interfaces admit the stated expansions, while changes to old admission, disclosure, release, availability or wire observations must be assessed explicitly.

What this means for ember: the optional interfaces of the six families admit the stated expansions. The changes that do touch 5.1.1 are changes to old admission, disclosure, release, availability or wire observations, wherever they occur; the authorization checker of decision 3 is the first such change, and it is a decision only to the extent that its refusal order and disclosure differ from 5.1.1's, which fixtures decide (old and new replies, pages, counts and diagnostics compared).

### 2.9 The three interactions the brief asked about

*Co-written. The text below is Astra's replacement (session 2) of the Opus draft, adopted. The Opus draft's three predictions survive in it: revocation makes context selection non-monotone while checking stays monotone; the outcome records the context it used; Decide checks and does not search. Two Opus claims were withdrawn: that witnessed evidence is required exactly for foreign evidence (the trust contract selects the evidence, §8), and the commutation formula `[adopt] ⟨≥p⟩ φ ↛ ⟨≥p⟩ [adopt] φ`, which treated a read operation as a modal operator.*


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

**Decide checks; the client proves (Opus, kept with Astra's widening).** NAL's guards and PCFS's procaps put proof search outside the reference monitor and proof checking inside it (`schneider-walsh-sirer2011-nexus-authorization-logic-nal.pdf`: "P is authorized if and only if a proof checker trusted by the guard establishes that the proof…"). For fn2 this is compatible with EXEC rule 3; so is Astra's alternative of cached static proofs with residual checks at admission, and bounded local evaluation of ground caveats. What is excluded is unbounded search in the node.

## 3. The existing logics whose metatheory we would otherwise reinvent

*Co-written. The table and the paragraph per logic are Astra’s (session 1, `fn2/modal-astra-1.md`), edited only for notation, filenames and law numbers that changed when §2 absorbed Astra’s corrections; the Opus additions are the three paragraphs marked at the end. Where the two authors differ, §8 records both positions.*


The useful inheritance is a collection of small calculi and proof routes. It is not a completeness theorem for their combination. Each imported result retains its hypotheses, and each translation into fn2 needs its own preservation argument.

The table distinguishes an available mathematical result from a checker fn2 has actually implemented. The law numbers identify the corresponding fn2 obligations, not claims that the papers already prove fn2 correct.

| Logic or theory | What is available | Adoption cost and corresponding laws | Verdict |
|---|---|---|---|
| ABLP, *A Calculus for Access Control in Distributed Systems*, **TOPLAS 1993** | A calculus of principals, `says`, delegation and `speaks-for`; soundness and completeness results for specified fragments | Translate scoped authority and justify credential introduction. Signatures, expiry and revocation remain separate. A2-A4 | **Adopt scoped speaks-for**, not the entire principal algebra |
| Garg-Pfenning constructive authorization; PCFS | Constructive proof rules, cut elimination and authorization non-interference results; PCFS has a correctness theorem for conditional proof verification | Define the accepted proof grammar, trusted premises, state conditions and revocation cuts. A1-A4, C2 | **Adopt bounded proof checking**; use the metatheory as a proof route |
| DKAL | An executable authorization language over a substrate; polynomial basic-query evaluation when nesting depth and rule-variable count are bounded | Its substrate and communication semantics exceed a grant-chain checker. A2-A4 | **Footnote** unless distributed policy evaluation becomes an implemented requirement |
| NAL/Nexus | Principal-indexed reasoning, restricted delegation and mechanically checkable authorization derivations | A richer policy language and explicit treatment of changing facts and guards. A2, A4, C2 | **Use as proof route** for scoped delegation and admission guards |
| SecPAL; Li-Mitchell Datalog with constraints | Sound, complete, terminating evaluation for SecPAL’s safe fragment; tractable constraint families for structured resources | Safety restrictions, constrained rule shapes and a specified constraint solver. A2-A4, A9 | **Adopt a decidable caveat fragment** |
| Dynamic logic, Hoare logic and Kleene algebra with tests | Relational program semantics, compositional pre/postcondition rules; KAT equational reasoning is PSPACE-complete | Bind program atoms to actual transitions, including refusal outputs. C1-C5, L3 | **Adopt the pre/postcondition fragment**; use KAT offline |
| Separation logic | Local reasoning through separating conjunction and the frame rule | Establish ownership composition, footprints and the frame side conditions. C3; EXEC §4’s frame and ownership obligations | **Use as proof route** for OWN and concrete refinement |
| Governatori-Rotolo contrary-to-duty logic | An ordered reparation connective and a Gentzen calculus | Its full metatheory is not supplied by the cited paper; deadline, violation and discharge semantics still need definitions. O1, O2, O5 | **Adopt finite declared continuation chains** |
| Artemov justification logic | Explicit evidence terms and operations on evidence | Distinguish derivation, authenticated assertion and consumable authority. A5, A6, O2, O3 | **Adopt typed evidence constructors**, not a general justification prover |
| Halpern-Moses common knowledge | A semantics of distributed knowledge and impossibility results under stated communication assumptions | Local evidence does not establish common knowledge. A6, A8 | **Footnote**; cut a separate knowledge modality |
| Past-time LTL; Halpern-Shoham interval logic | Efficient monitors for propositional past-time formulas; interval relations with sharply varying decidability | A trace monitor checks one execution; cuts need causal semantics; clock uncertainty is not interval-modal satisfiability. P1, P5-P7, P9 | **Adopt past-time monitors and endpoint comparisons**; cut general HS |
| Blackburn hybrid logic | Named states, satisfaction operators and a standard translation into first-order logic | Specify exactly what a name denotes; rigidity inside a model does not establish persistence between models. P2-P4 | **Adopt typed `@`**, without binders or a general satisfiability service |
| Bounded linear logic; graded effects and coeffects | Resource-sensitive typing; compositional grades and sound models of effect/coeffect interaction | Choose concrete units, grade operations and cost semantics. Polynomial time is insufficient for EXEC’s per-run bound. E5, O9 | **Adopt concrete cost grades**; use the larger theories as proof routes |
| Contextual modal type theory; Hazel lineage | Explicit contexts, contextual substitution and typed hole closures | Extract complete supports, including negative dependencies, and check substitutions between contexts. P8, R7 | **Adopt contextual read certificates** |
| HoTT univalence | Transport along equivalences for appropriately structured types | Establish the actual equivalence and its observed structure. R4, R5 | **Use the proof route already scoped in TRANSPORT** |
| Goguen-Burstall institutions, 1992 | Sentence translation, model reducts and the satisfaction condition; theory composition under stated hypotheses | Fix a specification language and prove translations admissible. R4, R5 | **Adopt the theory-morphism discipline** |
| Specware/Kestrel | Mechanical specification colimits, morphism obligations and refinement constructions | Supply presentations, mappings and proofs; general consistency is not decided. R4, R5, C2, C3 | **Adopt the construction pattern**; evaluate the tool on the room example |
| ACL2 `encapsulate`, functional instantiation, `defattach`; APT | Witnessed abstract interfaces, theorem reuse under checked substitutions, executable attachments and proof-generating transformations | Encode sorts by predicates, discharge constraints and guards, and connect the concrete served function. R4, R5, S1′; EXEC §4 | **Adopt as the implementation proof route** |

**ABLP.** Interpret `K ⇒_s L` as the family of implications `(K says φ) → (L says φ)` for `φ ∈ s`. Composition checks directly: if `φ ∈ s ∧ t`, apply the first delegation and then the second, obtaining A2 at scope `s ∧ t`. The paper separates authentication, “who made a statement,” from authorization, “who is trusted?” A signed A3 statement still needs a hand-off or policy rule that authorizes the delegation; a signature alone does not remove the surrounding `I says`. The journal citation is TOPLAS 15(4), 1993, not JACM. [ABLP] (`abadi-burrows-lampson-plotkin1993-calculus-access-control-distributed-systems.pdf`)

**Constructive authorization and PCFS.** Translate fn2’s evidence derivation into a judgment `Γ_(r,p,c) ⊢ K says permitted(α)`, with revision, position and revocation cut fixed in the context. Rule checking establishes authorization relative to that context; admission separately checks that the context is the one required now. Garg-Pfenning supply a “cut elimination theorem and the subformula property.” PCFS’s Theorem V.1 connects checked proofs and residual time/state conditions to valid authorization. It does not make revocation automatic: the paper states, “The current implementation of PCFS does not support revocation.” fn2 must supply A4’s cut discipline and a separately charged proof checker. [Constructive authorization] (`garg-pfenning2006-non-interference-constructive-authorization-logic.pdf`), [PCFS] (`garg-pfenning2010-proof-carrying-file-system.pdf`)

**DKAL.** The nearest translation is `p knows t ↦ p holds an admitted fact t`, with fn2’s typed records supplying the substrate. This is not `t is true`, nor does it identify DKAL’s communication rules with fn2 receipts. The 2008 paper bounds its basic-query algorithm by a polynomial in `ℓ^(δ+w)`, where `δ` is assertion nesting and `w` the maximum variable count: “when δ and w are bounded, the runtime is polynomial.” That is a conditional algorithmic result, not a constant-cost admission check. No additional fn2 mechanism follows from adopting the rest of DKAL here. [DKAL] (`gurevich-neeman2008-dkal-distributed-knowledge-authorization-language.pdf`)

**NAL/Nexus.** Map a guard’s authorization goal to C2’s `auth(α)` and its credentials to the admitted assertions at `c(α)`. Restricted speaks-for maps to A2; checking one restricted delegation verifies that authority outside its predicate is not imported. NAL explicitly allows the guard to “check a NAL derivation rather than generating its own.” Its warning about changing facts matters equally: a proof about a lock, membership or revocation state needs an admitted current-state premise. NAL is a useful proof route, but does not require a second policy engine alongside the chosen constructive fragment. [NAL] (`schneider-walsh-sirer2011-nexus-authorization-logic-nal.pdf`)

**SecPAL and constraint Datalog.** Translate a grant edge into a delegation clause and each caveat into a predicate on the requested action and pinned context. Construct attenuation as `scope_child(x) = scope_parent(x) ∧ caveat(x)`; inclusion then follows by conjunction elimination, without asking a solver to discover arbitrary implication. SecPAL gives “polynomial data complexity” for safe policies with fixed rules and queries and polynomial ground-constraint evaluation. Li-Mitchell’s stronger program-size result fixes a bound on rule size and uses specified tractable domains, including hierarchical and range domains. Adopt those finite, typed caveats first; adding arbitrary integer arithmetic invalidates the inherited bound. [SecPAL §§7-8] (`becker-fournet-gordon2010-secpal-decentralized-authorization-language.pdf`), [Li-Mitchell §§2-3] (`li-mitchell2003-datalog-constraints-trust-management.pdf`)

**Dynamic logic, Hoare logic and KAT.** Interpret a command atom as its reference transition relation and translate `{P} α {Q}` to `P → [α]Q`; in KAT the corresponding partial-correctness assertion is `P · α · ¬Q = 0`. Sequential composition checks by relational composition. Kozen reports that the equational theory is “actually PSPACE-complete.” This licenses offline reasoning about the command skeleton, not unbounded reasoning in Decide. C2’s first-failure behavior requires explicit refusal-producing branches: commuting Boolean tests may preserve acceptance while changing the refusal word. Termination and per-run cost remain separate obligations. [Kozen §4.3] (`kozen1997-kleene-algebra-with-tests.pdf`)

**Separation logic.** Interpret `P * Q` through UC §8’s partial ownership composition, not through a partition of the entire semantic state. The frame check is concrete: a transition owning `P` must preserve a compatible fragment `R`, giving `{P * R} α {Q * R}` under the variable and ownership side conditions. Reynolds describes the frame rule as enabling “local reasoning” about the heap. fn2’s outstanding I/O loans belong in the ownership interpretation; a generation number does not make two duplicated current tokens disjoint. This proof route serves OWN and EXEC §4 without adding a user-facing modality. [Reynolds] (`reynolds2002-separation-logic-shared-mutable-data.pdf`)

**Contrary-to-duty.** Compile the restricted chain `o ▷ o'` into an obligation transition: a committed violation of `o` records that violation and creates `o'` atomically. Check O5 by evaluating that transition, including retry and crash recovery; do not claim an interpretation of the entire Gentzen calculus. Governatori-Rotolo describe how “the violation of B1 can be repaired by B2,” but list proving soundness and completeness as future work. Expiry is a violation only when the obligation declaration says so. A successful discharge creating the next custody leg is a different continuation. The Prakken-Sergot comparison remains a gap in the gathered local packet; no result from it is imported here. [Governatori-Rotolo §§2, 6] (`governatori-rotolo2006-logic-of-violations-gentzen-contrary-to-duty.pdf`)

**Justification logic.** Map evidence constructors into checked judgments: signature verification yields an authenticated assertion; `receipt(t_sig,t_incl)` yields inclusion under the named checkpoint; `pair(t₁,t₂)` checks joint evidence; a tagged injection checks an alternative. Artemov’s application principle is `s:(F → G) → (t:F → (s·t):G)`. Thus A5’s dot notation requires an actual checked implication from the checkpoint statement and inclusion proof to the receipt claim. There is no rule from `t : K says φ` to `φ`. Nor does the classical evidence operation `+` make a custody token duplicable. [Artemov §§2-3] (`artemov2008-logic-of-justification.pdf`)

**Common knowledge.** The proposed translation `witnessed_k(φ) ↦ common-knowledge(φ)` fails. Deliver a valid quorum certificate to one node while delaying all messages to another: the first holds the certificate, but the second need not know that it exists. Halpern-Moses distinguish this from knowledge strong enough for “absolutely simultaneous coordination,” and explain assumptions under which common knowledge is unattainable or useful in an abstraction. fn2 needs the local rule A8 and a versioned quorum policy, not an unconditional assertion that common knowledge is impossible in every system. [Halpern-Moses §§8-10] (`halpern-moses1990-knowledge-common-knowledge-distributed-environment.pdf`)

**Temporal and interval logic.** Map one domain’s committed prefixes to trace indices. For `z = φ S ψ`, the monitor recurrence is `z_j = ψ_j ∨ (φ_j ∧ z_(j−1))`, with the initial case declared. This gives linear work in trace length for a fixed propositional formula, or `O(N·|φ|)` with formula size explicit; atomic query costs are additional. Havelund-Roșu describe memory “constant, also depending on the size of the formula.” Cuts are causally closed configurations, not arbitrary interleavings. P9 needs only `t⁻ ≥ δ` and `t⁺ ≥ δ`; it imports no HS satisfiability procedure. The gathered file is Marcinkowski and Michaliszyn’s *The Last Paper on the Halpern-Shoham Interval Temporal Logic*, including undecidability over discrete structures (first saved under a wrong author name; renamed). [Past-time monitoring] (`havelund-rosu2002-synthesizing-monitors-safety-properties.pdf`), [gathered interval paper] (`marcinkowski-michaliszyn2010-last-paper-halpern-shoham-interval-logic.pdf`)

**Hybrid logic.** Translate `@a φ` to evaluation of `φ` at the semantic snapshot named by `a`; Blackburn’s standard translation replaces the current-state variable by the variable denoting `a`. His defining condition is that nominals are “true at exactly one point in any model.” This checks P3 inside a fixed interpretation. To obtain fn2’s persistence claim, additionally prove that append, recovery and migration preserve the named snapshot and its interpretation. A domain position does not name the whole multi-domain machine state, and a node’s inability to retrieve a snapshot is not falsity at that snapshot. [Blackburn §3] (`blackburn2000-hybrid-logic-manifesto.pdf`)

**Grades, effects and coeffects.** Map a bounded run to a cost grade `q`, for example a vector of bytes visited, structural steps and action descriptors; sequential upper bounds compose by addition. Map required reservations to preconditions on the resource context, and check that actual consumption stays within the declared grade. Gaboardi et al. distinguish effects that change a context from coeffects that “make demands on the context.” Bounded linear logic supplies a route to polynomial resource guarantees, but a polynomial computation can still monopolize fn2’s executor. Stock conservation, peak occupancy, accumulated work and scheduling share require distinct interpretations; none follows merely from writing quantities as obligation fields. [Gaboardi et al.] (`gaboardi-katsumata-orchard2016-combining-effects-coeffects-grading.pdf`), [bounded linear logic] (not fetched; a gap, §9)

**Contextual modal types.** Interpret `@c [Ψ] v` as a result accompanied by a derivation whose free assumptions are the pinned support judgments in `Ψ`. Reuse at `c'` supplies a checked substitution from those assumptions into the new context. Identical supports provide the identity substitution; a proved equivalence can provide another. This is the substitution mechanism of Nanevski-Pfenning-Pientka, specialized to read dependencies. Hazel uses contextual modal types as “a logical basis for hole closures,” not as a database invalidation theorem. fn2 must extract supports itself, including the version of a searched fibre when the result depended on finding nothing. [CMTT §2] (`nanevski2008-contextual-modal-type-theory.pdf`), [Hazelnut Live] (`omar2019-hazelnut-live-live-functional-programming-typed-holes.pdf`)

**Univalence.** The applicable mapping and its limits are already in TRANSPORT §§1.1 and 3.1: relate admissible representations through `init`, `step` and declared observations, then transport statements expressed through that interface. The useful check is the commuting step/observation diagram, not the presence of HoTT vocabulary. No univalence axiom enters ACL2, and observational equivalence does not become literal equality of representations. [TRANSPORT] (`fn2/TRANSPORT.md`)

**Institutions.** Write `m:T→T'`, sentence translation `σ_m`, and model reduct `m*`. The law is `M' ⊨ σ_m φ ⇔ m*M' ⊨ φ`. Goguen-Burstall summarize it as “Truth is invariant under change of notation.” Section 4 checks it on the room port. R4 additionally needs a certificate relating the actual old model to the reduct of the actual new model; the institutional law alone does not certify a migration. [Goguen-Burstall §§1-2] (`goguen-burstall1992-institutions-abstract-model-theory.pdf`)

**Specware and especs.** Srinivas-Jüllig require that a specification morphism translate “axioms … to theorems.” Smith’s colimit construction identifies mapped symbols and collects translated axioms. The especs line adds behavior: guarded transitions and simulation must accompany structural mappings. The first especs file gathered is a three-author manuscript including Matthias Anlauff (saved as `anlauff-pavlovic-smith2002-composition-refinement-evolving-specifications.pdf`); the 2001 reference is *Composition and Refinement of Behavioral Specifications*. The later *Guarded Transitions* paper makes the relevant distinction explicit. Section 4 uses structural colimits for wiring and simulation for execution; it does not equate the two. [Srinivas-Jüllig] (`srinivas-juellig1995-specware-formal-support-composing-software.pdf`), [Smith] (`smith2006-composition-by-colimit-formal-software-development.pdf`), [guarded transitions] (`pavlovic-smith2003-guarded-transitions-evolving-specifications.pdf`)

**ACL2 and APT.** Map an abstract operation to a constrained function, its laws to exported theorems, and a realization to a functional substitution whose constraints are proved. `encapsulate` supplies local witnesses; functional instantiation transports theorems to the realization. `defattach` supplies execution, not a new logical equality: Kaufmann-Moore explicitly say “attachments are not invoked during proofs.” APT’s `isodata` and `propagate-iso` generate transformed functions and relationship proofs after their applicability conditions are discharged. Section 4.6 gives the room instance. [ACL2 encapsulate] (ACL2 documentation, ENCAPSULATE), [defattach] (`kaufmann-moore2011-how-can-i-do-that-acl2-defattach.pdf`), [APT] (`coglio2020-acl2-apt-isomorphic-data-type-transformations.pdf`)

**(Opus addition, amended by Astra) Counting for `witnessed by k`.** `G^k says φ` is *analogous* to Fine's graded modality ("in at least `k` accessible worlds") over the witness relation, but the correspondence has not been supplied and is not claimed (Astra, session 2). What fn2 checks is `k` distinct accepted witness principals cosigning the same bound checkpoint statement under a named witness-policy version (A6), with STORAGE decision 4's quorum-intersection requirement, which holds only under the declared fault assumptions. That is a finite check, bit-blastable for fixed `k` and set size. Verdict: **adopt the counting atom**, not graded modal logic. The fixture that decides adequacy: two roots at the same count, duplicate signers, and a witness-policy transition.

**(Opus addition) Modal transition systems, for ports with commands.** Larsen and Thomsen's may/must transitions and Lüttgen and Vogler's modal interface automata (`luttgen2013-modal-interface-automata.pdf`, already here) are the refinement theory of interfaces whose transitions are required (must) or permitted (may). A `defport` with commands is such an interface: a reply branch the foreign protocol requires is a must, an extension it tolerates is a may. Astra's §4.2 command simulation is the check; modal refinement is the name for it. Verdict: **footnote**, until a port with commands (`POST` through the room's NNTP view) is declared and its refinement checked; thorough refinement is EXPTIME-complete in general, so only the per-transition simulation would ever be checked.

**(Opus addition) Belief revision and truth maintenance, for `reconsider`.** AGM (`alchourron1985-logic-of-theory-change.pdf`) revises a belief set; fn2 never decides truth (agent-fleet §5, commons §5, Astra and Sol §5), so it has no belief set to revise. What `reconsider` needs is a justification-based truth maintenance system's bookkeeping (`elkan1990-rational-reconstruction-nonmonotonic-tms.pdf`; de Kleer's ATMS is cited by the Astra vantage draft): which derived claims lose support when a support is withdrawn. That is M3 claims with justifications plus B's Span, traversed as a paged, resumable fold. Verdict: **no new modality**; the record kinds are the Sol draft's (`correction`, `impact-job`, `reassessment`, `repair-receipt`).

## 4. Worlds as theories

*Co-written. The presentations, the morphisms, the counterexample of §4.3 and the conservativity argument of §4.4 are Astra’s (session 1); the framing paragraph, the merge statement at the end of §4.6 and the cross-references to §2 are the Opus author’s, reconciled with Astra’s.*


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

**(Astra, session 2) A qualification on the expansion.** Keep the old logical state sort and its interpretation, and introduce `State₄` as an *additional* representation with projection `π`. Replacing the old sort's carrier by `State₃ × ThreadAnnotations` is not literally an expansion preserving every old interpretation. The step equation proves behavioural preservation; the separate expanded presentation establishes conservativity. These are two obligations, and decision 2 keeps them apart.

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

Specware can construct the room and stream presentations, calculate the pushout’s symbol identifications, collect its axioms and expose morphism proof obligations. For `j`, an obligation is the translated article-number uniqueness law. For `m`, it is preservation of the old room interface. Its refinement machinery can organize the corresponding implementation development. The 4.2 manual names “colimits, extraction of proof obligations” and external theorem proving among its operations. It does not provide a general procedure deciding whether the resulting colimit has a model. [Specware 4.2, §3.1] (`kestrel2004-specware-4.2-user-manual.pdf`)

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

**(Opus) Where this sits against the rulings.** TRANSPORT decision 1 keeps ember's D68 through the first release: before it, every revision is a wipe and rebuild, and no revision record kind is added before its producer (D46). So §4.4 and §4.5 are specified now and built after the first release; the room presentation (§4.1), the port reduct (§4.2) and the wiring check (§4.3) do not depend on revisions and can be exercised as soon as their producers exist. WR decision 2 asks for a revision stamp in the envelope now; under D68 that stamp is constant, which is the trivial expansion of §2.8, so the two rulings are compatible if the stamp is a reserved field and not a record kind.

---

## 5. What this changes in the engineering

*Co-written. The Opus author drafted this section; Astra's session 2 replaced it, and the replacement is adopted with the Opus additions marked at the end. What Astra changed, in one line each: a port's kernel is an identification relation on models, not a set of missing sentences, and kernels compose by pullback, not union (the `(x, y) ↦ x ↦ x mod 2` example); the authorization checker starts with ground typed caveats, and a Datalog evaluator is added only when it removes real duplication; authorization and obligation evidence share machinery but keep two judgments, one with consumable allocations; the simulator's work is monitoring, bounded exploration and paired comparison, three different tasks; EXEC §4's refinement is a relational link presentation, which simplifies to a theory morphism only when a functional abstraction is proved; contracts are generated where a proof or checker consumes them, not on every machine.*

The declaration fields below are proposed fields, not claims about implemented macros. They extend the existing generators. They do not introduce a second specification beside the executable declarations.

The useful construction is a **contract with a checked interpretation**. A machine supplies transitions, a port interprets observations and commands, and a representation certificate relates executions. They share declarations and proof infrastructure while retaining different obligations.

### 5.1 Declarations and records

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

### 5.2 Authorization in Decide

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

A useful optimization is **checked static evidence plus residual conditions**. Cache the checked derivation under its policy, proof and credential identities; recheck its changing state, time and revocation conditions at admission. PCFS’s conditional verification theorem supports this division of work. Its implementation did not supply fn2’s revocation protocol. [PCFS, §V] (`garg-pfenning2010-proof-carrying-file-system.pdf`)

Authorization and obligation evidence should share codecs, authenticated leaves, support tracking and bounded traversal. They need distinct checking judgments:

```text
Γ ⊢ t : K says permitted(α)

Γ ; Δ ⊢ t : ev(o) ⊣ Δ'
```

`Γ` contains reusable facts and receipts. `Δ` contains consumable allocations or authority. Joint evidence requires disjoint consumed allocations where the obligation contract demands consumption. Reusing an immutable receipt for two historical observations remains legal.

This is one implementation substrate with typed entry points. Calling both inputs “proof terms” does not justify erasing their different resource rules.

### 5.3 What the simulator checks

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

### 5.4 The proof route

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

### 5.5 Words and answers people use

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

**(Opus addition) Two words never used.** "Knows" does not appear anywhere a friend reads: there is no epistemic modality (§2.4). "Obliged" does not appear either: it reads as SDL's `O`, which fn2 obligations deliberately are not (§1.4, §2.5); the word is `owes`. Of the ten operations a friend reaches for (UC §10.2), every read gains `as-of` / `at-least` and `under`; every accepted write returns its position and producer interpretation; `fork`, `transport`, `witness` and `grant` are the four new verbs.

---

## 6. The cost table

*Co-written: the Opus table, amended row by row by Astra's session 2 (each amendment adopted), with two rows Astra added. The "too general" column names the machinery declined, not a blanket claim about a research area.* The constraint that binds the table: **no general theorem prover in the node, and no undecidable fragment on a served path.**

| construction | machinery declined | fn2 uses | not built |
|---|---|---|---|
| hybrid temporal logic with past | binders, satisfiability services, unbounded verification | typed historical references (`@p`, `@c`) and fixed propositional past-time monitors; runtime monitoring, finite exploration and unbounded proof are three different costs | binders; a satisfiability service; future-time model checking in the node |
| Halpern-Shoham interval logic | interval-modal satisfiability (undecidable over discrete orders, `marcinkowski-michaliszyn2010-last-paper-halpern-shoham-interval-logic.pdf`) | two endpoint comparisons under a declared time interpretation (P9) | interval modal operators |
| institutions, Specware | an institution-independent framework; general colimit consistency | one presentation language (the DSLs'), typed mappings with certificate variants, checked instances; owner compatibility as *one* wiring check | a Specware toolchain; an institution library; consistency of arbitrary colimits |
| HoTT, univalence | univalence as an axiom; cubical computation; literal theory isomorphism from observational equivalence | interface-based theorem transport with supplied coherence obligations (TRANSPORT) | everything else |
| ABLP, Garg-Pfenning, NAL, DKAL | a general principal algebra; a distributed policy engine; proof search | an explicitly specified scoped-credential proof grammar with its soundness translation (§5.2), checked bounded and resumably | proof search in the node; DKAL's communication semantics |
| SecPAL, Datalog with constraints | rule evaluation over unbounded constraint domains | ground typed caveats and charged indexed predicates first (§5.2); a restricted rule evaluator only when it removes real duplication | a general constraint solver; the assumption that polynomial data complexity is an EXEC quantum bound |
| dynamic logic, KAT, Hoare, separation logic | PDL with iteration; program equivalence on a served path | pure Decide as a deterministic command contract; persistence with environmental choices as a second subject; contracts, simulation and frame proofs offline | a program logic or KAT procedure in the node |
| deontic logic | SDL's closure under consequence; defeasible priorities | obligation lifecycle with declaration-selected terminal transitions and continuations; at-most-once termination as safety, eventual discharge separately | an `O` operator; norm-conflict resolution |
| justification logic | the full justification algebra; internalization | typed constructors for authenticated statements, inclusion, conjunction, alternatives and thresholds, with reusable and consumable premises distinguished | term search |
| graded modalities, bounded linear logic, coeffects | arbitrary grade algebras; a graded type system | five distinct quantities kept apart: persistence grade, stock quantities, peak occupancy, accumulated work, service guarantees; a two-point durability grade is not a cost algebra | a graded type system over the DSLs |
| contextual modal type theory | first-class contextual types | support certificates and checked reuse, including negative dependencies and authorization context (P8) | contextual types in the DSLs |
| ACL2 relational refinement (Astra) | self-certifying generators | constrained interfaces, functional instantiation, concrete correspondence and converter correctness; obligations per realization | — |
| finite exploration and paired simulation (Astra) | unbounded claims from bounded runs | tiny-profile schedule and death-cut exploration; related-execution comparison; each result reports its bounds | — |
| epistemic logic | footnote only | nothing; local certificates do not establish common knowledge, under Halpern and Moses's stated assumptions | any `K_i` |

Counterfactual logic and belief revision have no row: forks and promotion are command execution (M5), and dependency invalidation and reassessment are supported reads and folds (M1, M3); no AGM operator is proposed.

**The risk that a modal vocabulary becomes decoration, and the test.** The failure mode is the one UC §11 names for category theory: the vocabulary multiplies, each word gets a section and a slogan, and nothing in the code can fail because of it. The test stays **checker, or refusal word, or record kind**, and Astra's session 2 sharpened it: each family must name a *concrete subject* and a *counterexample* that refutes it; a name in a table is not enough. And for each retained row, the evidence is recorded as a tested implementation, a recorded obligation or a proved theorem (TRANSPORT §3.1(ii), not a new evidence system).

| family | concrete subject that earns its place | checker | refusal or result word | record | counterexample that refutes it | scope correction (Astra) |
|---|---|---|---|---|---|---|
| M1 | read result, cut validation, time-domain transition, support reuse | CONSUMER, HISTORY, TRACE | `gap`, `projection-behind`, `version-unavailable`, `supports-moved`, `anchor-backward` | read certificate; cut where a deployment retains one | a read after a debit that returns an older qualifying snapshot | a cut need not be a standalone durable record in every deployment; `gap` is a result constructor, not necessarily a refusal |
| M2 | mapping certificate, interpreted observation, migration or wiring check | HISTORY, WIRE, TRANSPORT scenarios | `revision-moved`, `revision-orphans-obligation`, `refused-lossy`, `stream-owner-conflict` | migration, port, wiring declarations | a migration agreeing through the explored horizon and diverging later | declarations and proof artifacts are not automatically journal record kinds |
| M3 | credential, policy derivation, checkpoint, receipt | the evidence checker in Decide; TRACE, IDENTITY, RECOVERY | `proof-format`, `unauthorized(signature | issuer | scope | expired | revoked)`, `authorization-context-stale`, `fenced`, `rolled-back`, `conflicted` | grant, authorization context, claim, cosignature, receipt | an unsigned tautology as a checkpoint; a scope-widening child grant; two roots at one count | authentication, authorization and witnessed coverage remain distinct judgments |
| M4 | obligation transition and consumed allocation identities | HISTORY, RECLAIM (release), ACCOUNT (quantities) | `evidence-insufficient`, `already-discharged`, `disposition-incomplete`, `budget-exhausted` | obligation, discharge, waiver, hold | one allocation spent twice (must fail); one receipt reused for two reads (must pass) | FAIR remains separate from conservation |
| M5 | command contract, stable outcome, allowed execution | TRACE, WORK | Decide's words, `op-reused` | outcome with interpretation and authorization context; fork, promote | a refused fork that creates a child | pure decision and persistence protocol have distinct semantics |
| M6 | publication grade, dependency contract, typed loss report | RECOVERY, CONSUMER | `gap(live-overrun)`, `gap(epoch-reset)` | declared-loss envelope | a durable record depending on an uninlined transient item | durability is scoped by the fault profile and the retained contract |

Cut, as decoration: an epistemic `K_i`, SDL's `O`, Lewis counterfactuals, interval-modal operators. Merged without advertising a calculus: witness checking into M3. Incarnation merged into P2 and a lease grant, with Astra's correction that fencing also needs enforcement at the commit authority and protected sinks: recording a grant with an epoch does not establish that an old writer has stopped.

---

## 7. Five decisions for ember

*Co-written. The Opus draft proposed five; Astra's session 2 amended four and replaced decision 2. The texts below are the agreed wording, with the recommendation; where the authors still differ on a decision, §8 gives both positions.*

1. **Adopt six judgment families over the base theory B, with typed merges.** Use M1-M6 (position, revision, says with evidence, obligation, command, durability) to organize contracts over B. Revision, Equiv, Port and Wire share presentation-and-mapping infrastructure with distinct certificate variants. Transport combines a mapping with transfer, fencing and persistence. Credentials, claims, receipts and witness certificates share authenticated-evidence infrastructure. Obligation and reservation lifecycles share resource accounting where their contracts agree; scheduling share stays a separate FAIR property. Cut: any epistemic `K_i`, SDL's `O`, Lewis counterfactuals, interval-modal operators. *Recommended yes*: it covers the twelve drafts' demands that §2 could state as laws with fewer named things than WR's nine plus sixteen, and every family has a concrete subject, a checker, a word and a refuting counterexample (§6). It claims no modal class (S4, S5) that has not been proved for the actual operator.

2. **Separate conservative language growth from behaviour-preserving change.** A claimed conservative extension supplies an expansion of every B model that preserves the old interpretations (§2.8). A change to an old observation or command contract is stated explicitly as a decision. A migration supplies admissible states, event correspondence, a relational certificate, an executable converter and retained-contract obligations; its grade summarizes that evidence. Neither behavioural equivalence nor an `ext` label alone proves a model-conservative extension, and a conservative theory can still have a faulty converter (§4.4). *Recommended yes*: it is the discipline ember's amendment asked for, applied to the kernel's growth and to the worlds' evolution, with the two tests kept apart because they fail independently.

3. **Adopt bounded authorization checking with explicit context and disclosure.** Add the scoped-credential checker with the consumer protocol's authentication and capability path (EXEC §7a item 4, already owed). Freeze its proof grammar, primitive caveats (ground and typed first), cost accounting and context-validity rules; derive dependencies through the access boundary; retain or name the evidence required to explain an outcome (the authorization-context record of §5.2); define semantic refusal order and public diagnostics explicitly; scope query evaluation and its observable metadata according to the authorization contract. AUTHINFO need not issue a portable signed root grant: it can establish a local authenticated premise. Whether a reply changes is decided by fixtures that compare old and new replies, pages, counts and diagnostics, including unauthorized and partially visible queries. *Recommended yes, scoped*: it is the one family whose adoption may change 5.1.1 observations, and the fixtures say exactly which.

4. **Obligation lifecycle is linear; evidence use is typed.** Every created obligation is outstanding or has exactly one authorized terminal transition allowed by its kind. Discharge checks the declared evidence and authority at the applicable admission boundary. Immutable receipts are reusable unless the contract consumes a separately identified allocation. Expiry creates a contrary-to-duty continuation only when the declaration makes expiry a violation. Witness requirements are declared per evidence contract. Operator waiver remains limited to unsatisfiable obligations, as STORAGE requires. No `O` operator, no closure under consequence. *Recommended yes*: it is UC §6.1 and the economy draft's mechanism, stated so that SDL's paradoxes cannot enter through a careless "obliged", and it corrects the brief's "discharged only by evidence witnessed at k".

5. **Build contracts with their consumers; retain D68 until it is explicitly revisited.** Generate contracts and correspondence obligations from the existing DSLs where a current proof or checker consumes them; begin with the existing summary contract and one real port (the room's NNTP read view, §4.2). Use ACL2 for offline proofs (encapsulate, functional instantiation, relational refinement) and bounded typed checking in the node; no Specware toolchain, no institution library, no prover in the node. Keep TRANSPORT's schedule: representation certificates now; runtime revision, migration and shutdown machinery only when D68 is revisited and producers exist; a reserved field is not exempt from having a producer, a meaning and a consumer. Expose the read, evidence and persistence vocabulary of §5.5 (`as-of`, `at-least`, `under`, `signed by`, `authorized by`, `witnessed by k of G`, `owes`, `in fork`, `durable`/`transient`; never "knows", never "obliged") without requiring users to learn the modal classification. *Recommended yes*.

---

## 8. The Astra sessions, and where the two authors differ

Two sessions of `codex exec -m gpt-6-astra -s read-only -C ~/dev/fn`, each detached with a PID file. **Session 1** (prompt `fn2/modal-astra-1.prompt`, answer `fn2/modal-astra-1.md`, log `fn2/modal-astra-1.log`) received §1-2 and co-wrote §3 and §4, with eight proposals against §1-2. **Session 2** (`fn2/modal-astra-2.prompt`, `.md`, `.log`) received the whole draft, replaced §5, §2.8 and §2.9, amended §6 and four decisions, replaced decision 2, and checked every law against the engineering documents. Neither session hit a capacity or authentication error. Astra's words are in those files; the note quotes or adopts them where marked.

Per ember's ruling, disagreements are recorded as two positions with reasons, not verdicts. Most converged; the table says on what, and the two still open say what would decide them.

| issue | Opus position, and its reason | Astra position, and its reason | state |
|---|---|---|---|
| modal classes | named frame classes (S4.3, S5, KD) expose reusable laws, and ember asked for the modal reading | the table mixed satisfaction operators, temporal operators, translations, evidence judgments and resource predicates; `@^r` is a translation, not an S5 box | **converged** on six judgment families; modal classes kept only where the operator's semantics validates them (M1's `G`, M5's `[α]`, M6's `□_D`); M2's S5 withdrawn (§1.2, §1.4) |
| fork and nominals | identify parent and child worlds on the shared prefix, so positions are nominals | identify event occurrences and historical snapshots only; present authority and dispositions differ | **converged** on Astra's (§1.3, P2) |
| `at-least` | `⟨≥p⟩φ` as a modal diamond; threshold reads become permanently true | a read operation returning `(q, r, v)` complete at `q`; only the coverage predicate is monotone | **converged** on Astra's (notation, P4, P6) |
| `says` | lax `says` with unit, read as assertion | signed leaves and derived affirmations are different constructors; a grant needs a hand-off rule | **converged** on Astra's (A1, A3, A5; `signed by` ≠ `says` in §5.5) |
| L1, L3, E8, C1 | modal formulas for output gating and uncertainty | `[α]⊤` is valid even when `α` refuses; uncertainty is the commit protocol's evidence classification, not Decide's | **converged** on Astra's (L3 as output correspondence; C1 and E8 split) |
| revision rules | world age; rollback only along `≡`; obligations expressible under the new revision | TRANSPORT's completed rules: Decide crossing, a valid backward migration, compatibility relations preserving authorized discharge | **converged** on TRANSPORT's (R3, R6, R7, R8) |
| linearity and Meter | one linear-resource reading for evidence, obligations and Meter | linear for consumable authority and quantities only; receipts reusable; FAIR is the scheduler's, not conservation's | **converged** on Astra's (E5 split, O3, O9) |
| declared loss | one record for crash loss, migration kernels, port loss and covariance | one envelope with typed variants and their own composition rules | **converged** on Astra's (D4) |
| port kernel | missing foreign sentences; bridge loss is the union of kernels | an identification relation on models; composition pulls the later kernel back through the earlier reduct | **converged** on Astra's; the `(x, y) ↦ x ↦ x mod 2` example refutes union (§5.1) |
| caveat language | one stratified Datalog for grants, selections and evidence formulas | ground typed caveats first; an evaluator only when it removes real duplication; polynomial data complexity is not a quantum bound | **converged** on Astra's (§5.2, decision 3) |
| conservativity and grades | one discipline: an `ext` migration *is* a conservative extension | model expansion, actual-state conversion and future-behaviour preservation are three obligations; a conservative target can have a faulty converter | **converged** on Astra's (decision 2); the Opus point survives as "conservativity is necessary for `ext`, not sufficient" |
| witnessed evidence | witnessed evidence exactly when the evidence is foreign | the obligation's trust contract selects; a signed peer receipt can suffice; a local claim can require a quorum | **converged** on Astra's (§2.5, §2.9) |
| freshness | refuse every presentation below a held witnessed count | refuse authoritative rollback only; historical reads and old receipts stay legal | **converged** on Astra's (A8) |
| authorization and 5.1.1 | grants-first and pullback visibility necessarily change 5.1.1 | they may; replacing an implementation while preserving its contract need not; fixtures decide | **converged** on Astra's (§2.8, decision 3) |
| generated contracts | every `defmachine` emits an encapsulate-shaped presentation | generate where a proof or checker consumes it; execution machines have observation, action and continuation semantics beyond event folds | **converged** on Astra's (decision 5); the deciding test Astra names (apply the generator to a parser or the commit machine and show useful obligations without a duplicate specification) is the first use |
| **proof placement** | client search plus Decide's linear check is the placement EXEC rule 3 forces | cached static proofs with residual checks at admission, and bounded local evaluation of ground caveats, are also compatible; "linear" needs primitive-cost assumptions | **open on the default, agreed on the bound**: no unbounded search in the node. Decided by Astra's measurement: full checking versus residual checking under a changed revocation, cold pages and large supported proofs |
| **the revision stamp now** | a constant reserved stamp reconciles WR decision 2 (envelope fields now) with D68 (no revision record kind before its producer), as M2's trivial expansion | a field still needs a meaning and a consumer; D68 is not lifted by the release alone; an interpretation-manifest Name has consumers *now* (simulator runs, the checkpoint claim's fold/schema field) and is the thing worth implementing | **open**, and it is a tension between two existing rulings (WR decision 2 and TRANSPORT decision 1), not between the authors only. Decided by naming the producer and checker that consume the stamp now; until then the field stays specified. The Opus author recommends taking TRANSPORT decision 3's manifest Name as that consumer |

Astra's dispositions of the marked Opus additions: the counting atom for `witnessed by k` is kept, with the Fine correspondence withdrawn as unsupplied (§3); modal interfaces stay a footnote, because forward simulation is not automatically modal refinement and a `POST` that never replies can pass trace-safety checks; truth maintenance is kept with the narrower claim that reconsideration needs completeness of affected-support discovery, negative dependencies included; the D68 staging is kept with the field argument amended (the second open row above).

What the collaboration changed, measured: §1 lost its S5 claim and gained three frame repairs (closures, ancestry, `→_C` as a declared closure); §2 had 29 of its laws restated, two of the brief's interactions withdrawn (the universal witnessed-evidence law and the revision/at-least commutation formula), and its conservativity conclusion weakened from "exactly two non-conservative clauses" to "assess every change to an old observation"; §3 and §4 are mostly Astra's; §5 is Astra's with Opus additions; decisions 1, 3, 4 and 5 are amended and decision 2 replaced.

---

## 9. Bibliography

All sources are in `~/paperbin/` under the filenames cited inline. The 25 fetched for this note are annotated in the "Modal kernel" section of `~/paperbin/README-fn2-20261028.md`, with the gaps (Prakken-Sergot, Chisholm, Anderson, Hvitved, Girard-Scedrov-Scott, Fine, Lichtenstein-Pnueli-Zuck, Kaufmann-Moore 2001, Abadi 2003, and three books) and their stand-ins. Reused from earlier passes: `artemov2008-logic-of-justification.pdf`, `nanevski2008-contextual-modal-type-theory.pdf`, `murase2023-cmtt-polymorphic-contexts.pdf`, `omar2019-hazelnut-live-live-functional-programming-typed-holes.pdf`, `luttgen2013-modal-interface-automata.pdf`, `alchourron1985-logic-of-theory-change.pdf`, `elkan1990-rational-reconstruction-nonmonotonic-tms.pdf`, `hott2013-homotopy-type-theory-univalent-foundations-book.pdf`, `orchard-wadler-eades2020-unifying-graded-parameterised-monads.pdf`, `coglio2020-acl2-apt-isomorphic-data-type-transformations.pdf`, `kaufmann-moore2013-abstract-stobjs-isa-modeling.pdf`, `mattern1989-virtual-time-global-states.pdf`, and the UNIVERSAL-CONSTRUCTIONS and TRANSPORT sets. nanodregg's laws are cited from `~/dev/nanodregg/CHARTER.md`. Scry found no practitioner thread on authorization logic, Zanzibar, macaroons, UCAN or modal logic worth quoting (`hackernews.items`, searched 2026-10-28); none is cited.
