**Do not adopt §12 as written.** The useful result is a vocabulary of reusable contracts. The claimed minimal basis and several “laws for free” do not follow. The largest engineering mistake is turning sufficient proof techniques into mandatory declarations and operational policies.

1. **Material — Seven is not a demonstrated floor (§9.1).**

   > “Nothing in the list is a composite of the others.”

   A Frontier is a max/join Fold; a Span’s indexed relation can be a Fold; an Obligation is a Fold of creation/discharge events whose transitions are guarded by Decide. Name bundles two different things: content commitment and a mutable binding relation.

   **Correction:** “These are seven useful interfaces, not irreducible primitives.” Keep commitment separate from identity binding; treat indexes and obligations as specialized state machines. The list also does not account for bounded execution, resource reservation, adapter ownership or ambiguous persistence. Those are essential contracts in EXEC, not consequences of free-monoid laws. In particular, products of free monoids exist; “one atomic mutation, one domain” is an architectural restriction, not an algebraic impossibility.

2. **Material — Summary homomorphism is sufficient, not necessary (§2.2).**

   > “A summary rule … is adequate **iff it is a coalgebra homomorphism**.”

   Counterexample: summarize counter `n` as `(n mod 2, 0)`. The summary transition flips both bits; the observation reads only the first. Every future observation agrees, but `σ∘δ ≠ δΣ∘σ` because the hidden bit differs.

   **Correction:** Adequacy is preservation of future observations. The displayed equations are a convenient sufficient certificate; necessity requires additional restrictions, such as an observationally reduced target. General implementations may need a simulation relation.

   Also, an O(log n) Merkle frontier supports future roots, **not arbitrary inclusion proofs for retained leaves** without additional proof material. STORAGE explicitly retains both frontier and proof material.

3. **Material — State algebra does not classify implementations or determine mode (§2.3).**

   > “A fold’s state algebra is one of three classes.”

   An arbitrary automaton’s state need not carry any of these structures. Semilattices are monoids; `max` appears in both supposedly distinct rows. Abelian-group addition commutes; ordering requirements arise from admission predicates and observations, not inverses.

   > “In-transaction is legal exactly for linear interpretations…”

   A bounded unique-key join can run in-transaction; a nonlinear maximum update can take constant work. Conversely, linearity does not bound input traversal, allocation or I/O. External placement is plainly not derivable from algebra.

   **Correction:** Keep mode explicit. Check work, fan-out, dependencies, charging and atomicity. Declare independently proved capabilities—merge, retraction, duplicate tolerance—when used. [DBSP](https://www.vldb.org/pvldb/vol16/p1601-budiu.pdf) supplies incrementalization machinery, not this scheduling classification.

4. **Material — The Kan calculation is defensible; the operational interpretation is not (§2.4).**

   > “The only way to obtain an informative value is to defer … **wait**.”

   Given an actual Set-valued diagram, the stated terminal-object calculations work. But projection values are elements, not automatically the diagram’s objects. An empty limit supplies a singleton; it supplies neither blocking semantics nor eventual progress.

   **Correction:** Describe these as operational read policies. `catch-up` requires a retained **maintenance state**, a complete available suffix and a bounded resumable interpreter. A displayed maximum alone cannot absorb deletion of its winner; an external projection may have no local interpreter.

   There is also an inherited defect to fix: **`cov ≥ p` does not make a latest-only state answer exactly at `p`.** That requires retained version state or snapshot plus replay. Coverage and historical availability are different predicates.

5. **Material — Coproduct preservation does not discharge the inbox contract (§3.1).**

   > “The CONSUMER checker can therefore test one edge at a time and the property composes.”

   Raw span composition distributes over disjoint unions. The delivered inbox additionally quotients duplicate events, unions reasons, sorts, paginates and proposes a globally complete cursor. Two individually correct edges can produce a duplicate, omit a reason or advance past an unread entry when combined.

   **Correction:** Per-edge equivalence is one lemma. Composition additionally needs correctness of deduplication, ordered merge, completeness cuts, policy intervals and authorization versions. Keep INBOX’s differential whole-consumer check. Coproduct preservation explains decomposition; it does not replace these obligations.

6. **Fatal — CALM does not determine operation-identity requirements (§5.1).**

   > “Monotone operations need no operation identity.”

   Monotonicity, idempotence, commutativity and stable retry outcomes are different properties. Incrementing a natural-number counter is monotone but not retry-idempotent. Even a genuine join may incur charges, allocate a subscription, renew a lifetime or produce a response whose meaning changes on retry.

   **Correction:** A pure join of a fixed authenticated fact can omit an *additional* operation ID when repeated application has the same promised observable effect. That says nothing by itself about durable outcomes or admission.

   [CALM](https://arxiv.org/abs/1901.01930) concerns coordination-free computation of monotone results; it neither requires a total commit order for every other operation nor classifies retry contracts. Fence **observation** is max; fence **allocation** still requires exclusive authority.

7. **Fatal — Ack is not merely max under the existing three-outcome contract (§5.1).**

   > “For the left-hand column … the identity and the outcome table buy nothing.”

   CLIENTS §1.1 and INBOX §4.8 retain accepted/refused/uncertain:

   - **Accepted:** advancement is durable; equal retries are idempotent.
   - **Refused:** lineage, registration epoch, principal, query/view versions and proposal validity matter. Max alone cannot enforce these checks.
   - **Uncertain:** mutation is fenced until persistence is resolved. Reapplying max is not a resolution protocol.

   Backfill progress also lives under the proposal’s identity; the scalar cut is not the entire mutation.

   **Correction:** Ack may use its existing proposal identity and durable cursor evidence instead of a new generic op-ID row. Preserve validation, uncertainty recovery and the promised retry result. A later cursor proves coverage, not necessarily the original operation’s outcome.

8. **Material — Identity union is sound, but the advertised convergence theorem is underspecified (§4.3).**

   > “For any two nodes that have received the same set of signed sources … `B` is equal…”

   This follows only if both derive the same validated facts independently of arrival order. Signatures alone do not settle dependency availability, authorization policy or admission. First-arrival acceptance outcomes and local article numbers need not converge.

   The outcome formula also does not match the theorem: a new offer `c₂` conflicts with existing `B(mid)={c₁}` **before** the set has cardinality two.

   **Correction:** Define validated evidence facts, their union, and the separate predicate `conflicted(mid) ⇔ |contents(mid)|≥2`. Prove convergence for equal validated fact sets; state eventual dissemination assumptions separately. Share the multivalue-map implementation with signer equivocation, but retain distinct validation/key rules.

   Recording conflict evidence is useful, but “the identity fact may not [be refused]” needs an admission/reservation contract. It cannot silently impose unlimited permanent storage on every conflicting offer.

9. **Material — Event-structure conflict contradicts the proposed evidence representation (§§1.3, 5.2).**

   > “The Message-ID conflict *is* the conflict relation of the event structure.”

   A configuration cannot contain conflicting events. The proposed `B` deliberately contains evidence of **both** conflicting contents. These cannot simultaneously be the same events under the same conflict relation.

   **Correction:** Distinguish incompatible acceptance choices from compatible observations of those choices. The evidence set can grow monotonically.

   Likewise, equality of fact sets is not open-map bisimulation: future enabled behavior matters. Compatible hash-chain prefixes are a useful check, but calling them a sheaf condition adds no witness authenticity, quorum or freshness guarantee. Keep STORAGE’s concrete witness conditions.

10. **Material — An exact local order is available, but delivery does not obtain it for free (§5.3).**

    > “The cost is nothing; the documents only had to say it.”

    EXEC installs the complete root before incremental publication and notification. A live publish can run between those steps. Existing live sequences are per-stream, so `(p, live-seq)` can also tie across streams.

    **Correction:** Define durable item `q` as `(q,0)` and transient items after install `p` as `(p,s)` with positive, appropriately scoped publication sequence. Then require the delivery merge to respect that order despite delayed notifications, pagination and live gaps. A multi-stream exact publication order needs a node-wide sequence or a weaker explicitly scoped contract.

    This is a reasonable amendment, not a consequence of interval-domain semantics.

11. **Material — The deadline adjoint has missing existence and clock-history conditions (§6.4).**

    > “The adjoint exists iff `τ_D` is monotone and right-continuous, which means every rate is non-negative.”

    `τ(t)=0` is monotone and continuous, but deadline `1` has no finite preimage. Non-negative segment rates also permit backward jumps at new anchors. Right-continuity is not interchangeable with non-negative slope.

    **Correction:** For a specified ordered time domain, require monotonicity across anchors and an attained first crossing for reachable deadlines. Represent unreachable deadlines explicitly. A paused clock delays only **unreached** deadlines; already reached ones fire immediately.

    Unknown future rate events make today’s converted deadline provisional. Recompute on relevant mapping changes, including ancestors, and revalidate at firing. PLANES already requires re-arming on rate events.

12. **Material — Fencing does not supply every safety property (§6.3).**

    > “Every safety property of fn2 rests on the commit order and fencing…”

    Ownership, authorization and integrity also require their own invariants. More narrowly, highest-seen fencing rejects an old writer only after the sink learns the newer token. If expiry itself ends authority, a write after expiry but before replacement must also be rejected.

    **Correction:** Define whether authority lasts until committed expiry, revocation or supersession. Check that authoritative state at commit. Fencing prevents superseded holders from acting; it does not eliminate declared time-dependent authorization.

13. **Fatal — Decide is not a delta lens by being deterministic (§7).**

    > “The view-update problem never arises in fn2, by design.”

    A function can reject an update, choose an unauthorized source change or implement the wrong view change. Determinism proves none of the lens laws. General view updates may have no legal lift.

    > “The identity edit appends nothing…”

    A command with no visible view change may still owe a durable outcome, audit event or binding record. For a strict lens over journal prefixes, that append is not the identity.

    **Correction:** Use command preconditions and postconditions. Claim a partial delta lens only for an explicitly restricted update language with proved lifting laws. Delta-lens composition concerns lifting **composed updates**, not retry deduplication; see [Clarke’s definition](https://bryceclarke.github.io/papers/delta-lenses-as-coalgebra-for-a-comonad.pdf).

14. **Material — Linearity proves neither eventual discharge nor correctness of borrowed bytes (§§6.1, 8).**

    > “Every obligation instance is consumed exactly once along every trace.”

    A finite trace ending with an outstanding obligation refutes this immediately; an infinite trace awaiting unavailable evidence can also be valid.

    **Correction:** Every created obligation remains outstanding or has exactly one authorized discharge. Eventual discharge is a separate liveness claim with environmental assumptions.

    Similarly, generation checks reject stale handles, not duplicated current-generation ownership tokens. Some handles are shared references. Mark ownership rights, not all handle-shaped values, as linear. Frame preservation also does not prove that a completion exposes exactly the bytes actually written; EXEC’s byte-fill correspondence remains necessary.

15. **Material — Footprints are sufficient approximations, not an exact independence oracle (§1.2).**

    > “Fusion is legal exactly on independent pairs…”

    Overlapping operations can commute; disjoint application rows can still share quotas, allocator state, scheduler state or an observable action stream. Reordering transitions must preserve enabledness, outputs and the specified scheduler, not merely final row values.

    **Correction:** Use sound conservative effect summaries, with an explicit commutation lemma for each exploited case. “Whole machine table” is not a safe default when transitions access shared state; default to the entire semantic state and effects. Add precise footprints when fusion or partial-order reduction actually consumes them.

16. **Material — Universal provenance and automatic migration overpromise (§§2.5, 4.5).**

    > “Every projection’s output row carries the positions of its sources.”

    A balance may depend on millions of events. An explicit source-position set destroys the intended compaction. Retractions can instead use keyed contributions, retained candidates or replay.

    > “The generator can emit both the migration and its correctness for free.”

    A schema functor does not supply a string-splitting function, missing foreign-key values or preservation of application observations.

    **Correction:** Require sufficient dependency evidence for each promised operation, possibly a cut, range or separate index. Generate migrations only for supported mappings with supplied value transformations and semantic correspondence proofs.

17. **Minor — Several advertised predictions are already requirements; one removes too much (§0).**

    > “What the constructions predict that the documents have not said…”

    STORAGE §4.1 already requires retained observations and future requests; INBOX §§4.5–4.6 already specify per-edge caching, coverage and equivalence; PLANES §§4.5–4.7 already specify checkpoint lineage, fencing, re-arming and claims as obligations. New notation or declaration placement is useful, but should be called that.

    > “With operations addressed by element identity … the rebase is trivial.”

    The cited [Weidner text](/Users/ember/paperbin/weidner2025-collaborative-text-editing-without-crdts-or-ot.txt:73) requires unique occurrence IDs, deleted anchors/tombstones and client reconciliation. Content Names cannot distinguish two identical characters. **Correction:** Defer a generic CRDT library; do not claim the log eliminates collaborative-editing semantics or metadata.

18. **Material — “One field” conceals a checker, representation and maintenance commitment (§11).**

    > “Each replaces a hand-written mechanism or a hand-argued proof…”

    That replacement is mostly unestablished. For the actual 5.1.1 slice:

    | Field | Worth doing now | Cut or defer |
    |---|---|---|
    | `observes` | References to existing contract observations for summaries that discard history | A separately maintained observation list on every projection |
    | `linear` | Ownership-token lifecycle checks for pool loans and resources | Blanket linearity of handles; a generic camera declaration language |
    | `session` | Shared finite protocol states and legal request/reply transitions | Global multiparty projection machinery. Unknown branch labels are not automatically safe to ignore |
    | `footprint` | Conservative effects where a current check needs them | Precise per-transition declarations before fusion/POR |
    | `algebra` | Optional proved join/retraction capabilities when exercised | Mandatory three-way enum; derived mode |
    | `lineage` | Existing event references and checkpoint ranges | Source sets attached to every aggregate row |
    | `view effect` | Independent postconditions for consequential commands | Generic lens-law field and universal no-op/no-commit rule |

    Keep the existing projection declaration and handwritten bounded folds. Defer DBSP generation, categorical migrations and general session projection until an implemented consumer demonstrates the duplication they remove. A `monoid` default does not establish correctness.

**Verdicts on §12’s five decisions**

| Decision | Verdict | Replacement wording |
|---|---|---|
| **1. Seven primitives** | **Amend** | “Use these seven names as provisional interfaces. Document their compositions and independent contracts; make no minimality claim or seven-or-eighth admission rule.” |
| **2. Projection fields and catch-up** | **Amend** | “Name retained observations and sufficient maintenance state. Keep mode explicit, checked against resource bounds. Offer catch-up when state and suffix are available; distinguish exact historical reads from reads at least as fresh as a position. Add provenance only where required.” Drop the algebra enum and derived-mode requirement. |
| **3. Monotonicity split** | **Amend** | “Separate merge algebra, admission, retry identity and outcome evidence. Pure joins may omit additional op-IDs only under a stated retry contract. Preserve ack’s three outcomes. Merge validated identity evidence by union; keep local acceptance and serving policy separate.” |
| **4. Global protocols and lenses** | **Amend** | “Share protocol state/transition declarations between parser, machine, client and checker for the served protocols. Declare command preconditions and observable postconditions.” Defer global projection; drop mandatory monotonicity classification and lens laws. |
| **5. Four plane/time laws; no CRDT library** | **Amend** | “Durable dependencies requiring later content must inline or durably name it; explicitly lossy epoch references remain legal. Specify and test mixed delivery order. Define expiry and fencing authority precisely. Require monotone clock mappings and explicit unreachable deadlines.” Defer a generic CRDT library as a scope choice, not a mathematical consequence. |

**Four additions the note needs**

- **A read-contract distinction:** `exactly-at(p)` versus `at-least(p)`, with retention, authorization-version and unavailable-history behavior.
- **A peer-evidence contract:** validation dependencies, admission, durable evidence storage and dissemination assumptions behind convergence.
- **A persistent uncertainty model:** retain EXEC’s prepare/fence/install/recovery states alongside the abstract Log; algebraic append cannot replace them.
- **Executable counterexamples for each adopted law:** overlapping inbox edges, ambiguous ack, summary with hidden state, live publication between install and notification, and a paused or re-anchored clock. These should constrain the abstractions before new declaration machinery does.