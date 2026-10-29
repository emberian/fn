**Do not adopt §6 as written.** The useful core is a version-specific simulation certificate and an explicit activation boundary. The note repeatedly turns sufficient proof techniques into mandatory machinery—the mistake UC §13 rejected.

1. **Fatal — The extension obligations do not establish the claimed preservation.**

   > “every theorem about the old observations”

   Coherence is required only on **old** event kinds. A new event may change the old component even though old `δ₁` ignores it. All listed obligations can hold while an old invariant fails.

   **Correction:** require `φ(δ₂(s,e)) = δ₁(φ(s),e)` for every admitted event, with old semantics explicitly defined for new events, plus initialization and invariant preservation. Alternatively restrict the transported theorem to old-alphabet traces.

   Likewise, `φ ∘ ℓ = id` says nothing about historical accuracy of new fields. If v2 adds an event counter, lifting its value to zero preserves the old state but loses the prefix count. Hazel retains hole closures and their environments; an ignored event leaves no such residual computation.

2. **Material — “Equivalence” conflates behavioral equivalence, representation isomorphism, and an executable migration.**

   > “a relation `R ⊆ S₁ × S₂`, total and surjective”

   A total relation preserving observations and steps can establish behavioral equivalence without being an invertible representation map. It also supplies no executable, bounded converter. These are different obligations.

   **Correction:** state the admissible states, event correspondence, initial relation, step preservation and observations; separately supply the actual converter and its correctness. “Up to observational equivalence” is sound if this means UC’s **all-future** congruence and the up-to argument is justified. Present-answer equality alone is insufficient. The four labels are fn2’s proposed cases, not a demonstrated restriction of Trocq’s lattice.

3. **Fatal — Coverage is inherited at the converted state’s cut, not automatically at the revision position.**

   > “The last three inherit coverage at the revision position”

   If revision position is `r` and the old materializer is at `c < r`, conversion earns coverage at `c`. §3.2(i) correctly says this; §6 contradicts it. Extension additionally needs separate coverage for its new observations.

   **Correction:** “A migration transports the certified observations at the source state’s actual cut; subsequent processing advances coverage.” It creates neither historical snapshots nor previously unavailable `exactly-at` answers.

   The lossy equations are a sufficient certificate when properly scoped. Its “kernel” must describe an identification relation, however, not merely list missing fields. A history-compressing summary that preserves every retained observation is **not observationally lossy** merely because its representation forgets history.

4. **Material — Rollback and path independence do not follow from homotopical patch theory.**

   > “Rollback is legal only along equivalences.”

   The extension row already permits rollback by `φ`. A narrowing can also be reversible on the currently reachable subset; retained complementary data can make an otherwise lossy conversion reversible.

   **Correction:** rollback needs a backward migration valid for the current state, admitted future events and outstanding contracts. A global equivalence is sufficient, not necessary.

   > “Two migration routes between the same versions must agree”

   Only routes declared interchangeable must agree; parallel paths need not be equal. HoTT does not prove arbitrary migration diamonds: defining the interpreter requires supplying the images of the declared path laws. Functoriality then preserves them. [Homotopical Patch Theory, §5](https://www.cs.cmu.edu/~rwh/papers/htpt/paper.pdf).

5. **Material — A record revision is an alphabet map only for a restricted semantic-event change.**

   > “The semantic obligation is then one statement per (fold, record kind) pair”

   For a context-free, one-event-to-one-event conversion, the appropriate equation is:

   `σ(δ₁(s,e)) = δ₂(σ(s),u(e))`.

   Together with initialization, observations and domain invariants, that proves the fold correspondence. It does not establish framing, decoder bounds, authentication of original bytes, or physical recovery effects. On `fn2/b-durability`, `format.lisp` explicitly includes maintenance records **without semantic event numbers**, allocation records and physical references.

   Per-field relations also need whole-record constraints; lengths, references and identity bindings are not independent fields. A partial narrowing cannot be admitted safely without evidence that all required old records remain interpretable.

   > “v1 records stay v1 on disk forever”

   Semantic history is append-only; physical placements are reclaimable under STORAGE. Preserve required meanings and evidence, not every old encoding forever.

6. **Fatal — The revision-vector Fold cannot identify a pinned activation’s producer revision.**

   > “No new per-batch or per-outcome field is needed.”

   Start a Decide under r17, install r18, then let the pinned r17 Decide commit. The revision Fold at its outcome position says r18. Static read sets do not recover its start revision.

   **Correction:** either prohibit old-revision decisions from committing across activation, revalidate them, or retain a durable binding from the outcome to its actual producer revision. That binding may reuse existing records; it need not be a new field on every outcome.

   > “A consumer then reads ‘evidence about r18’ as `at-least(position of the r18 revision)`”

   This may return r19—or an r17-produced outcome after the boundary. Position and interpretation identity are separate coordinates. Specify both. Historical reads can also explicitly request a selected projection version; “the version active then” is one policy, not the only well-defined semantics.

7. **Fatal — The Π-check neither preserves obligations nor has a bounded implementation.**

   > “every obligation kind outstanding in the domain has its evidence formula expressible under the new Decide”

   Expressibility is much weaker than preserving discharge rules. Replacing “authorized receipt for this object” with `true` remains expressible. Preserving a kind’s vocabulary also says nothing about its existing instances, evidence bindings or available discharge operations.

   **Correction:** check a named compatibility relation preserving authorized discharge, fencing, retry outcomes and retained promises. Waivers remain separately authorized; STORAGE §4.3 limits operator waiver to unsatisfiable obligations.

   Quantifying over all outstanding instances at commit cannot become an unbounded scan. Use a proved conservative summary, or resumable validation whose result is bound to a version and revalidated at activation. “Π-shaped” supplies none of that engineering.

8. **Material — Read dependencies are useful; automatic semantic revision is too strong.**

   > “A fold revision whose fold appears in some Decide’s read set is a revision of that Decide too”

   An observationally equivalent representation change need not change Decide’s semantics. Conversely, an incomplete manually written list misses dependencies through helpers, configuration or authorization state.

   **Correction:** conservative dependencies trigger compatibility checking. Derive or enforce them through the actual access boundary; change the composed interpretation identity when its dependency identity changes, without pretending every such change alters command behavior.

   Similarly, “reads through observations” does not authorize downstream migration. A lossy source may remove precisely the observation that reader needs. Each consumer must discharge its own compatibility obligation.

9. **Fatal — Hashing the declaration does not make interpretation immutable.**

   > “it costs a hash in the declaration macro”

   `machines-a.lisp` declarations call helpers such as `fn2-connection-reply`. Change that helper without changing the declaration and this proposed Name stays constant. The same problem applies to fold functions, constants and macro expansion.

   **Correction:** name a canonical manifest binding the relevant transitive definitions, dependencies and interpretation semantics. Unison references definitions by hash; it does not leave dependency symbols mutable underneath an unchanged hash. [Unison’s design](https://www.unison-lang.org/docs/the-big-idea/).

   This is more than a few macro lines. The current checkpoint field is also `(fold-schema (:id schema))`, not a content digest; adopting the proposal requires an encoding or registry decision.

10. **Fatal — Equal output digests do not justify early cutoff across revisions.**

    > “a projection rebuilt after a revision may stop early when its output digest at a checkpoint equals the old version’s”

    Two counters can both output zero at a checkpoint while the old step adds one and the new step adds two. Even equal current outputs under the same step can conceal different maintenance state.

    **Correction:** reuse requires the same computation and dependencies, or a certificate that the retained states have identical required future behavior. `(version Name, source cut)` keys results; it does not establish that certificate. Cut this “free” optimization.

11. **Material — Experiment A is a valid restricted lemma, not the proposed general Fold contract.**

    > “each event’s effect on an observation is a function `g` of the event, the query and the old observation only”

    This makes each query independently sufficient for its future answers. It works for Boolean read membership. Many folds require cross-query state; a distinct-read count cannot decide whether another `read n` increments it from the count alone.

    **Correction:** keep A explicitly as a pointwise example; use an invariant-preserving relation for the general contract. Its coverage theorem establishes future membership agreement, not storage-level historical availability.

    There is also a literal ACL2 defect: `(member n reads)` returns a list tail, not Boolean `t`. As written, the equality against `rs-g` fails after an ordinary read. Booleanize membership and state the valid-state/query hypotheses or explicit totalization.

12. **Material — Experiment B understates its inputs and misidentifies its negative result.**

    > “the generated … theorems … exist … without hand-written proofs”

    `propagate-iso` consumes supplied translated interface functions **and correspondence theorems**, then propagates through their users. The omitted `...` contains substantive work. That is explicit in [the installed documentation](/Users/ember/tools/acl2-fn/acl2-8.7/books/kestrel/apt/propagate-iso-doc.lisp:60).

    Restricting `epoch < 2²⁸` correctly gives the u60 image. The unrestricted witness should concretely show either failure of the backward image obligation or inverse law, according to the chosen conversion—not merely failure to prove `defiso`.

    Dropping generation should be tested against **stale-incarnation rejection**, not a row-predicate conjunct. Two generations collapse to one row but accept different tokens. Finally, a logical-row experiment proves nothing about the served column implementation until connected by correspondence. Keep B as a tooling experiment; defer its DSL variant.

13. **Material — Experiment C’s unconditional PutPut theorem is false.**

    > `(equal (fl-get (fl-put v2 (fl-put v1 j))) (fl-get (fl-put v2 j)))`

    Take empty `j`, `v1 = {x:1}`, and `v2 = {}`. With no deletion, the left side retains `x`; the right side is empty.

    **Correction:** require a fixed complete field domain, suitable domain-inclusion hypotheses on both puts, or formulate partial edits with their actual composition law. Canonical alist representation is also needed for literal `equal`, rather than map equality.

    Base `fl-getput` **does** hold over the journal because `diff` is empty. Only the outcome-appending variant breaks it. Thus the concluding blanket claim that journal GetPut is false contradicts the experiment itself. These examples do not yet license `defrecord-edit`.

14. **Fatal — Experiment D’s lossy example fails its own migration law; its delayed-divergence tooth is misplaced.**

    > “v4 is a windowed representation that keeps reads only within `W` of `hwm`”

    Let `W=2`, `hwm=0`, and the old read set contain `3`. Migration drops `3`. Append `read 1; read 2`: the old compacted state reaches `hwm=3`; v4 reaches only `2`. The discarded information becomes relevant as the window moves.

    **Correction:** use a fixed discarded domain or a contract with explicit unavailable answers; otherwise this is reinterpretation, not the claimed homomorphic loss.

    > “It satisfies the 2-cell at the split point … and fails after a suffix”

    For A’s pointwise membership dynamics, agreement on every membership query implies agreement after every suffix. Ignoring catchup produces an immediate discrepancy. To test delayed divergence, add hidden state affecting a later event. Also exercise `m34` against its claimed equation; the proposed 2-cells do not.

15. **Material — Experiment E lacks the composition semantics needed for its equality.**

    > “Only the first composes behaviours compositionally.”

    Variable-sharing systems also have compositional theories. Even Myers’s general behavior construction is lax; recovering all composite behaviors requires additional conditions. See [§5.3.3](/Users/ember/paperbin/myers2023-categorical-systems-theory-book-draft.txt:23433).

    > “Adding `fn2-machines-free-head` … must make the check pass.”

    Declaring a variable does not supply its transition protocol. E needs a common timeline, scheduler constraints, resource ownership and initialization, completion correlations, stuttering and a consistent global trace bound. Independently bounded component traces cannot simply be joined after erasing those constraints.

    The actual `fn2-listener-admit` also reads active count, capacity and pool state, reserves a pool slot, and writes the echo row. It is not the stated capability-only wire. Model an explicit allocator/resource component or a justified shared-state composition. One added field cannot guarantee equality.

16. **Material — The state-spill prohibition is neither necessary nor sufficient.**

    > “no other kind stores a field value of this kind”

    Copying immutable data is harmless; holding an untracked representation-dependent reference is the problem. A generation-checked handle prevents stale-slot reuse, not interpretation under the wrong layout.

    **Correction:** prohibit untracked representation-dependent aliases and specify handle invalidation across restart. Do not prohibit all copied values. Nor can “drain” mean waiting indefinitely for long-lived connections, parked consumers and maintenance rows to finish; define restart/cancellation behavior preserving borrows and uncertain commits.

17. **Material — Owed statements and failed proofs are repeatedly promoted into stronger evidence.**

    > “obligations discharged, either as theorems … or as an owed statement … plus a simulator scenario that refutes it if false”

    `defthm-owed` creates no theorem. A bounded scenario cannot refute every false unbounded law, and `must-fail` can succeed because automation failed on a true statement.

    **Correction:** retain fn2’s current distinction: tested implementation, recorded obligation, proved theorem. Every negative experiment needs an evaluated witness satisfying the relevant domain assumptions and falsifying the equation. Do not call provisional coverage transport “discharged” or claim the bounded check guarantees detection.

18. **Material — The cost table repeats the CQL failure in smaller units.**

    > “The grades are four constants, the 2-cell check is a test file, the compositional check is a scenario”

    Their costs are converter retention, dependency identity, activation ordering, historical interpretation, recovery, compatibility checking and resource accounting. File count is irrelevant.

    For 5.1.1:

    - **Keep:** explicit interpretation identity and coverage; one concrete migration certificate when an actual retained summary must change; conservative dependencies where a current check uses them.
    - **Defer:** mandatory four-grade declarations, `on-source-revision`, generated per-field upcasters, version graphs and route search, generic Π validation, machine revision Names and spill analysis.
    - **Cut:** unconditional early cutoff and mandatory equivalence-only rollback.
    - **Experiments:** A is a useful small example; B is a bounded tooling probe. C needs an actual editing consumer; D needs two real supported routes; E needs an intended compositional reduction.

    “Formats will change before release” does not establish a compatibility obligation—especially under D68. Reserving a record tag is cheap; implementing its lifecycle is not. Summary simulation, original retry outcomes, no replayed effects, abstract-view correspondence, external-executor fencing and versioned projections mostly restate STORAGE, EXEC and PLANES. Mark those as placement. The concrete additions are proof shapes and specific counterexamples.

**Verdicts on §6**

| Decision | Verdict | Replacement wording |
|---|---|---|
| 1. Revision events and pinning | **Amend** | “Record supported semantic activation changes at a definite durable boundary. Bind each result to its actual interpretation; drain/revalidate crossing work or retain its producer binding. Reads identify both interpretation and position. Machine updates restart under an explicit shutdown contract.” |
| 2. Migration grades | **Amend** | “A concrete migration declares its preserved observations, domains and simulation obligation. Transfer only their coverage at the converted cut. Labels summarize evidence; they do not authorize transport. Add upcasters and backward migrations when required by supported history.” |
| 3. Content Names | **Amend** | “Name a canonical interpretation manifest including its semantic dependencies. An unchanged declaration hash alone is not interpretation identity.” |
| 4. Decide dependencies and Π-check | **Amend** | “Use conservative, enforced dependencies to identify compatibility obligations. Activation preserves existing promises through a bounded, version-bound check; equivalent dependency changes need not change command semantics.” |
| 5. Five experiments | **Amend** | “Run corrected A and a narrowly scoped B. Defer C, D and E until their consumers, alternative routes or intended exploration reduction exist. No experiment presently validates the proposed revision lifecycle or complete content-name construction.” |

**Missing additions**

1. **One revision crash scenario:** two prepared batches, an old activation, revision installation, retry and recovery at every persistence/install cut. Check actual producer revision and original outcome.
2. **A retention contract for interpretation artifacts:** declarations, converters, decoders and summaries remain available for precisely the historical answers and retries still promised.
3. **An explicit compatibility boundary:** define supported old formats and behavior on unknown required versions, including decoding the revision record itself.
4. **A real cost measurement:** compare one handwritten conversion against the generated alternative, including proof adaptation, rebuild work, retained bytes and recovery complexity. That decides whether a reusable construction pays.