Yes—and I would make this a central part of fn’s construction, not an assortment of increasingly elaborate crash scripts.

**My recommendation is a shared, model-based resilience framework with four interchangeable execution modes: fast deterministic simulation, native fault-controlled execution, block-level crash replay, and interoperability against independent implementations.** The shared parts should be the workload language, correctness model, failure corpus, and minimizer. The execution backends should remain distinct because they establish different things.

The critical deliverable is not “we ran a million crashes.” It is:

> **Here is the smallest execution that violates this particular commitment, under this precisely stated failure model, reproduced on this executable.**

## 1. Build on the existing machinery—but give it one common language

At the reviewed revision, fn already has native cut tables and process-kill campaigns, a source-level correspondence check between native persistence operations and modeled programs, a block-write replay campaign, and real INN interoperability labs. These are useful foundations, not things to throw away. 

There is also an important naming distinction: `tools/run_simulator.py` currently runs fixed ACL2 scenarios. That is useful executable model evidence, but it is not yet a general deterministic exploration engine controlling a whole node’s environment. 

I would connect the existing pieces through a versioned **scenario intermediate representation**:

```text
Scenario
  = contract profile
  + initial-state recipe
  + actors and operations
  + environment/fault schedule
  + healing phase
  + assertions and required witnesses
```

Then the architecture becomes:

```text
                   generators and corpus
                            |
                      scenario format
                            |
          +-----------------+------------------+
          |                 |                  |
    deterministic      native processes    block replay
       execution       + controlled I/O    + filesystem recovery
          |                 |                  |
          +-----------------+------------------+
                            |
                   independent observations
                            |
                history / resource / protocol
                         checkers
                            |
                   minimize and reproduce
```

Independent implementations get adapters into the same workload language, but not necessarily the same physical fault schedule.

This is the architectural lesson I would borrow from FoundationDB and TigerBeetle: run real implementation code inside a controllable environment, preserve reproducibility, and reuse workloads across simulated and real execution. Their simulators are tightly integrated with their systems; they are precedents, not libraries that can simply be attached to fn. :chatgpt-content-reference{index="2"}

### What the scenario must express

Not just `POST`, `READ`, and `KILL`.

It needs operations such as: acquire a reader snapshot; begin a post; deliver another chunk; complete a disk operation without delivering its completion; disconnect a client; change an authorized policy; acquire or discharge a particular obligation; begin compaction; deliver a delayed page; replay old carried media; and restart during recovery.

Use **symbolic operation, article, obligation, and generation identities**. A fault should attach to something like:

```text
operation post-A
boundary durable-publication-before-client-observation
action lose-response
```

—not “sleep 37 milliseconds and kill the process,” and not solely “fail the seventeenth syscall.”

Timed kills remain valuable native tests. They are simply a different execution mode, with weaker replay guarantees.

**Hypothesis’s rule-based state machines are my first choice for constructing and shrinking these scenarios in the existing Python test infrastructure.** They support sequences of operations, reuse of generated values through bundles, and invariants checked throughout execution. They can drive native processes; fn itself does not need to become Python. :chatgpt-content-reference{index="3"}

## 2. The most important new component is the history checker

The checker should not merely ask whether every returned article is individually plausible.

It should ask:

> **Does one legal execution of the contract explain all the observations together?**

This matters enormously after lost acknowledgements and crashes.

Suppose an atomic post creates memberships in two groups. A checker that independently allows “old or new” for each membership can accept a fractured outcome: one membership survived and the other did not. Each observation passes locally, but no legal atomic acceptance explains both.

The existing power-loss campaign’s documented oracle checks acknowledged articles against their reference bytes and permits certain alternatives for unacknowledged or reclaimed articles. Those are useful checks; I would strengthen their composition with a whole-history consistency requirement rather than treating each permitted alternative independently. 

### Model uncertainty as a set of possible histories

Conceptually, maintain:

\[
\mathcal B_t
=
\{\text{contract states consistent with observations through time }t\}.
\]

A lost reply may leave both “committed” and “not committed” possibilities. A subsequent read, retry, receipt, or restart should narrow those possibilities. A correctness violation occurs when:

\[
\mathcal B_t=\varnothing.
\]

This is much stronger than treating `uncertain` as a third permanent outcome that excuses subsequent inconsistency.

For tractability, start with small histories, bounded concurrency, memoized abstract states, and explicit reconciliation points. A checker that runs out of resources reports **inconclusive**, never “valid.”

### Keep three histories separate

The framework should record:

**Client observations:** invocation, received response, disconnect, timeout, returned bytes, and snapshot identity where exposed.

**Internal diagnostic events:** admissions, chosen records, publication boundaries, generation switches, and effect identities.

**Environment facts:** which write completed, which bytes were persisted in the selected crash image, which packet or completion was withheld.

Only the first should establish what the client was promised. Internal events help diagnose a failure; a log line saying “durable” is not evidence that the client received an acknowledgement or that the disk satisfied a barrier.

The observation journal must survive independently of the faulted store. Otherwise, losing the evidence of an acknowledged operation can make losing the operation itself appear acceptable.

### Do not impose the wrong consistency model

Jepsen is useful both as a framework and as a methodology: generate concurrent histories against actual processes while a separately scheduled “nemesis” introduces faults, then check the history against the intended model. :chatgpt-content-reference{index="5"}

But fn’s disconnected network is not necessarily one globally linearizable database.

I would check local acceptance and publication against their local contract; pinned readers against their snapshot semantics; replication against the appropriate delivery and evidence rules; and custody transfer against the precise undertaking being discharged.

**Porcupine is worth using for genuinely linearizable subinterfaces**, since it takes an executable sequential specification and a concurrent history. It is not a ready-made checker for all of fn’s uncertainty, crash, snapshot, and disconnected-delivery semantics. Those need to be modeled explicitly. :chatgpt-content-reference{index="6"}

### Include productivity, not just safety

Every fault campaign should have a **healing phase**:

```text
stop introducing faults
restore the required contacts
allow outstanding primitive operations to finish
provide the declared resources
run recovery and reconciliation
probe useful operations
```

Then assert that the relevant work finishes within the contract’s declared bound—or within an explicitly experimental budget while that bound is being developed.

A server that permanently fences itself after every disturbance must not receive the same verdict as one that recovers correctly.

Require positive witnesses too: some posts accepted, some retries reconciled, some reads completed during competing work, some reclaim operations actually freed eligible content. Otherwise, a regression that refuses everything can make an entire safety campaign greener.

## 3. Make the fault model an executable object

The framework should have **two explicitly separated fault classes**.

### Contract-admissible failures

These preserve the environmental assumptions under which fn promises correctness: process death, allowed write loss before durability, short I/O, reported errors, lost replies, temporary disconnection, and permitted scheduling delays.

A violation here is a counterexample to the promised behavior, subject to checking the harness and oracle.

### Assumption-challenging failures

These deliberately challenge those premises: a device losing acknowledged durable writes, substitution of a different valid record, rollback of an entire store image, misdirected reads, or a trusted peer lying about retention.

These tests ask a different question:

> Which violations are detected, how are they contained, and what evidence remains?

Some violations cannot be detected without an independent trusted commitment. For example, arbitrary rollback of all local state cannot always be distinguished from a genuinely older state using that same local state alone.

Do not mix these classes into a single “crash test pass rate.” Also do not discard the second class as irrelevant: it is how you discover assumptions that are unnecessarily broad or insufficiently defended.

### Separate an effect from observing its completion

This should be a central abstraction:

```text
issued → performed → persisted → completion observed
```

Not every effect has all four stages, but storage publication does have distinctions of this kind.

Explore both:

* The operation happened, but its completion was lost.
* The completion reported failure, although some or all permitted writes reached storage.

That prevents a common harness mistake: implementing an injected failed `fsync` as “none of the preceding writes happened.”

The deterministic backend should separately control clock observations, randomness, read/write outcomes, effect completion delivery, socket fragments, connection events, and worker scheduling.

A fixed PRNG seed alone does not provide determinism if native thread scheduling, foreign-library behavior, clocks, or iteration order still influence execution. **Advertise determinism at the boundary you actually control.**

### Add a small set of high-value schedule points

For fn, I would begin with:

| Schedule point | Adversarial interleaving |
|---|---|
| Publication durable, client response pending | Lose the reply, restart, retry the original identity |
| Page read outstanding | Cancel reader, retire old generation, then deliver the read |
| Reclaim candidate selected | Acquire a new independent hold before destructive action |
| New checkpoint prepared | Crash before installation, during installation, and during cleanup |
| Recovery has performed a repair write | Crash again before recovery completes |
| Receipt observed | Duplicate it, reorder it with policy changes, or lose its durable completion |

These should be first-class generated scenarios, not six isolated hand-written scripts.

## 4. Extend the block-replay rig instead of starting another one

`tools/power_loss.py` already does considerably more than killing a process: it records block writes with `dm-log-writes`, handles flush/FUA information, constructs selected crash images, runs filesystem recovery, and checks the reopened service. It also verifies that full replay matches the captured device image. That last check is important harness validation. 

I would extend this in four directions.

### A. Give persistence schedules an explicit semantics

Record the ordering constraints that a selected storage profile requires. Generate alternative persisted-write sets and orderings only within those constraints.

The distinction between ordinary write completion, preflush, and FUA matters. Linux’s `dm-log-writes` documentation explicitly describes its handling of completed writes around flushes and the separate treatment of FUA. Its log is not simply a chronological list of “durable now” events. :chatgpt-content-reference{index="8"}

For writes that overlap, reordering and omission require particular care. Randomly selecting sectors without respecting the chosen model can create either impossible counterexamples or an unrealistically forgiving device.

### B. Crash during recovery

For each interesting crash image:

1. Start the real recovery path.
2. Record the writes it makes.
3. Cut that recovery at selected boundaries.
4. Recover again.
5. Check the original commitments and the interrupted operation.

A system can survive every crash in normal operation and still fail when recovery itself is interrupted.

The bounded black-box crash-testing work behind CrashMonkey/Ace is a useful methodological precedent: small, systematically explored workloads can find failures that broad random workloads miss. I would borrow that exploration strategy, not assume its historical implementation is a turnkey fit for fn’s current platform. :chatgpt-content-reference{index="9"}

### C. Add reported errors and long-lived degradation

Use `dm-flakey` and `dm-delay` on disposable test devices to exercise failed reads/writes, delays, corruption, and—in a separately classified adversarial profile—silently dropped writes. These mechanisms are documented Linux device-mapper facilities. :chatgpt-content-reference{index="10"}

The useful scenario is not merely “disk unavailable for thirty seconds.” It is:

> Disk stops making progress while readers retain old generations, a batch owns completion credits, another client disconnects, and maintenance is waiting for space.

That tests whether the resource and recovery arguments compose.

### D. Keep evidence before any recovery changes the image

Preserve the pre-recovery image, the exact persisted-write selection, filesystem and mount configuration, executable identity, and observer history.

Normal filesystem journal replay is part of the recovery experiment. An unrecorded repair step that changes the image before the service is checked is not.

Run this machinery only against dedicated disposable images or VMs, not the live nodes or their stores.

And retain the distinction between **a crash image generated under a block model** and **actual physical power interruption on a named device**. The first explores systematically; the second tests whether the platform behaves like the model.

## 5. Fuzz several different spaces, not just input bytes

I would use four coordinated fuzzing modes, all producing the same replayable scenario format.

### Stateful protocol fuzzing

Start with valid conversations that reach interesting states: authenticated posting, group selection, article retrieval, transfer, TLS transitions, compression, and reconnect/retry.

Then mutate both commands and their history.

For NNTP, good cases include splitting delimiters across reads, coalescing multiple commands, disconnecting during multiline input, transitioning into TLS with buffered bytes, changing groups before numbered lookup, and retrying a completed transfer after losing its final response.

**boofuzz is useful for structured wire mutation and process/network monitoring. AFLNet’s state-feedback approach is also relevant:** it mutates message sequences and uses response codes as well as coverage to guide exploration. Neither supplies fn’s semantic history oracle. :chatgpt-content-reference{index="11"}

Preserve transport semantics in the ordinary network-fault profile. Packet reordering in TCP does not authorize the harness to reorder application bytes arbitrarily. Malformed application streams belong in a separate input-adversary profile.

### Structure-aware storage fuzzing

Random damage will often stop at the first checksum. That is useful, but insufficient.

Generate storage cases with valid outer structure and a deliberately wrong inner relationship:

* A valid page from another generation.
* A valid entry paired with the wrong expected commitment.
* Individually valid records whose sequence or identity bindings conflict.
* A checkpoint and suffix that are each valid but do not belong together.
* A tombstone or receipt referring to the wrong retained obligation.

Use both checksum-preserving mutations, which reach deeper semantic checks, and checksum-breaking mutations, which exercise integrity handling.

Similarly, signed fixtures need an explicit choice: preserve the signature and expect rejection after source mutation, or resign with a test key to exercise the post-verification semantic path. Do not silently bypass authentication and call that a production-path test.

### Semantic coverage-guided fuzzing

Code coverage alone will miss many of the interesting distinctions.

A useful feedback signature could contain:

```text
publication phase
certainty of client outcome
pending effect classes
reader-generation relation
active-hold count class
resource headroom band
policy/evidence version relation
recovery attempt number
```

Count abstract situations, not fresh IDs. Otherwise every new Message-ID appears to be a novel state.

Reward reaching combinations such as:

```text
uncertain post + checkpoint installed + restart + duplicate retry
```

or:

```text
old reader pinned + reclaim eligible + low memory + delayed page
```

**LibAFL is the stronger long-term substrate if you need custom structured inputs, feedback, scheduling, and distributed corpus search.** It explicitly supports replacing its input and instrumentation components, including AST-like inputs and binary instrumentation backends. I would start with Hypothesis and introduce LibAFL where execution throughput or search control justifies it—not rewrite the whole testing system to adopt it. :chatgpt-content-reference{index="12"}

For SBCL, verify that any coverage technique actually observes fn’s executed code. Coverage of a Python driver or C wrapper is not coverage of the Lisp core.

### Resource-adversarial fuzzing

Search for inputs and schedules that maximize:

\[
\frac{\text{work}}{\text{input bytes}},\qquad
\frac{\text{peak retained memory}}{\text{charged memory}},\qquad
\text{resources still owned after healing}.
\]

Examples include many long shared-prefix identifiers, alternating compressed readers, many independent holds on one article, abandoned uploads, repeatedly refreshed snapshots, and maintenance under tight funded headroom.

Use deterministic work counters where available; measure native time and memory separately. A noisy wall-time outlier is not the same evidence as an operation exceeding its counted-work contract.

## 6. Use a differential matrix, not one “reference implementation”

Different comparisons expose different mistakes:

| Comparison | Primary purpose | Important restriction |
|---|---|---|
| ACL2 reference execution ↔ shipped extracted execution | Translation, attachment, primitive and state-update discrepancies | Agreement can preserve a shared specification bug |
| Incremental/indexed path ↔ simple full reconstruction | Representation and maintained-view correctness | The oracle must not reuse the same index or cached answer |
| fn ↔ INN | NNTP interoperability and shared protocol semantics | INN does not define fn’s stronger retention/durability contract |
| fn through different BP implementations | Bundle and convergence-layer interoperability | Compare only supported profiles; transport success is not application processing |

### Expand the existing INN lab into generated behavioral differentials

fn already has a lab that exercises native fn against real INN, including both feed directions, duplicates, loops, and cuts. Extend that adapter rather than creating a competing integration harness. 

Compare semantic observations for controlled workloads: Message-ID lookup, group membership, overview information, command-state transitions, multiline framing, and duplicate/conflict behavior.

But be extremely conservative about normalization.

Locally assigned article numbers and transport-added fields can legitimately differ. Map them using explicit rules. Do not normalize away response classes, wrong identities, missing memberships, or authored-byte changes merely to make transcripts match. The NNTP RFC and the selected supported profile should adjudicate a discrepancy, not majority vote among implementations. :chatgpt-content-reference{index="14"}

An independent implementation accepting malformed input does not automatically mean fn should accept it.

### Add a genuinely independent BP peer

Keep the existing dtn7-based labs. For a second implementation, **µD3TN is worth evaluating for the overlapping BPv7 and convergence-layer profile**; it provides a separate DTN stack and application-agent interface. Confirm the exact supported intersection before defining comparisons.  :chatgpt-content-reference{index="16"}

The high-value tests are intermittent contacts, lost application receipts, duplicate delivery after restart, old-media reintroduction, and rejection of unsupported or unauthorized contexts.

Do not infer that a bundle delivery acknowledgement establishes a durable fn obligation, much less that a consuming application processed it.

### Metamorphic tests should continue into the future

These are particularly valuable for the representation changes discussed earlier.

Compare a scenario with transformed variants:

```text
different input chunking
different permitted batch boundaries
warm cache versus cold cache
incremental views versus full reconstruction
checkpoint/reopen inserted
physical compaction inserted
duplicate idempotent delivery inserted
```

Under the transformation’s stated preconditions, the promised semantic observations should agree.

For compaction, do not stop at comparing current reads. Generate **future continuations**—retries, new holds, releases, reimports, policy changes—and compare those too.

That is a practical test approximation to the future-observation equivalence I recommended for the proofs.

Chunking equivalence also needs correct preconditions: do not change elapsed time, resource availability, or timeout behavior and then demand identical results.

## 7. Search systematically, then shrink causally

I would combine three search strategies.

### Bounded exhaustive exploration around small worlds

Use tiny but expressive configurations: a few articles, two independent holds, two generations, several clients, and resource budgets that force reuse and refusal paths.

Enumerate single faults around all registered relevant boundaries. Then enumerate selected two-fault combinations, especially failures involving recovery.

Do not equate “small world” with “small input bytes.” Keep boundary-sized payloads, long identifiers, and large declared lengths represented in the corpus.

Use partial-order reduction only when operations are actually independent. Different articles may still share a log batch, allocator, global budget, or checkpoint. Disjoint Message-IDs do not prove commutativity.

### Coverage-guided long histories

Long runs find lifetime and accumulation failures: descriptor leakage, forgotten credits, stale-generation references, and counters that drift only after repeated cycles.

Alternate destructive stress with useful work and healing. A campaign that never reaches recovery completion mostly tests whether failure can prevent progress—which is unsurprising.

### Lineage-driven fault selection

This is the sophisticated extension I find most promising for fn.

Lineage-driven fault injection works backward from a successful outcome, identifies dependencies supporting it, and chooses failures that might remove that support. It then executes those failures to discover whether another successful path exists. The original MOLLY work combines provenance with satisfiability-based search; its guarantees depend on its bounded model, and its original model does not provide a ready-made crash-recovery engine for fn. :chatgpt-content-reference{index="17"}

For fn, the raw material is unusually good: operation identities, durable events, obligations, receipts, and publication dependencies.

Consider:

```text
sender released obligation
    because receiver receipt was accepted
    because receiver accepted undertaking
    because required content was durably retained
```

The test engine can ask which lost messages, crashes, delayed completions, or stale views could make the sender reach release without the required surviving support.

I would initially implement a modest version: record these dependency edges, prioritize faults along them, and search small combinations. Treat it as a heuristic until the completeness conditions of the dependency model are established.

This also complements the proposed incremental-view layer: provenance can explain both **why a view contains a fact** and **which failures or missing updates would challenge it**.

### Shrinking must preserve causality

A useful minimizer reduces more than bytes:

```text
actors → operations → faults → interleavings → payload → resource limits
```

But it must preserve prerequisites. Removing the original post while retaining its receipt produces an invalid test, not a smaller explanation. Removing a generation switch while keeping the “stale” page can erase the bug’s cause.

Use symbolic identities and dependency-aware shrinking. Keep separate randomness streams for workload generation and fault scheduling so removing an unrelated action does not completely scramble the environment.

For native races without exact schedule control, retain the smallest observed trace and label the replay limitation. Do not silently discard an intermittent failure as “flaky.”

## 8. Antithesis is the packaged option I would seriously evaluate

For testing the complete native stack—including dependencies, scheduling, networking, and actual process behavior—**Antithesis is a strong candidate**. Its documented model is deterministic, fault-filled execution with correctness assertions and exploration of alternative timelines. :chatgpt-content-reference{index="18"}

There is also a practical path for Common Lisp integration: its fallback SDK accepts assertion and lifecycle messages through a JSONL file, so a language-native Lisp SDK is not required to begin expressing properties. :chatgpt-content-reference{index="19"}

However, I would make an evaluation prove three things rather than assume them:

**The intended faults actually occur.** Packaging two services in one fault domain can prevent testing failures between them.

**The storage behavior matches the declared campaign.** Antithesis documents configurable restart/durability behavior; do not assume that a container kill is the exact persistence model fn needs.

**The desired scheduling and coverage feedback reaches SBCL code.** Its thread-pausing feature requires instrumentation, and its documented clock skips affect nodes together. Those capabilities are not interchangeable with arbitrary per-node clock faults or verified Lisp-level coverage. :chatgpt-content-reference{index="20"}

My division of responsibility would be:

> Own the scenarios, contracts, checkers, and replay artifacts. Use Antithesis as an additional whole-system exploration backend.

That avoids both building your own hypervisor and making the warranty evidence dependent on an opaque vendor-specific workload.

## 9. Make failures feed back into the proof argument

Every minimized failure should end with a classification:

| Finding | Consequence |
|---|---|
| Execution differs from the proved function | Repair extraction, attachment, host correspondence, or runtime integration |
| Execution matches the model but violates the public promise | Strengthen the specification or the theorem |
| The failure violates a declared environmental assumption | Improve detection/containment or reconsider the supported platform |
| The checker rejected a legal behavior | Repair the oracle, preserving the counterexample as a checker regression |
| The intended fault never occurred or evidence was lost | Harness failure or incomplete coverage—not a product pass |

Also test the testers.

Deliberately suppress a workload, make every post refuse, disable a fault hook, corrupt a checker result, truncate a history, omit a required witness, and kill a test stage. The framework must distinguish these from a successful resilience run.

For regression, retain the **scenario and observations**, not just the seed. Include the executable and dependency identities, initial-state recipe or snapshot, exact fault decisions, persisted-write selection when applicable, oracle version, and the minimized failure explanation.

### The implementation order I would choose

First, extract a shared scenario format and independent history checker into the existing campaign infrastructure. Adapt the current native cut, INN, and block-replay runners to it.

Second, add Hypothesis-generated stateful workloads and dependency-aware shrinking. Establish strong useful-work and healing assertions before increasing test volume.

Third, make I/O completion delivery and selected scheduling boundaries deterministic. Build a small exhaustive suite around uncertainty, independent holds, generation changes, and repeated recovery.

Fourth, add semantic coverage and structure-aware storage mutation. Then evaluate LibAFL and Antithesis against the same corpus and assertions.

A useful initial run policy would be short deterministic regressions on affected changes, broader generated exploration on scheduled runs, and complete required cut/profile coverage on release candidates. Set explicit execution budgets, but report budget-exhausted exploration as incomplete rather than manufacturing a pass.

**The measure of success is that the framework produces explanations the engineers and proof agents can act on: “after this publication, this observation was lost, this generation was reclaimed, and this later answer can no longer be explained by any legal history.”** That makes testing an active guide to the assurance architecture—not merely a final attempt to shake bugs out of it.

Yes. **The strongest version of fn is a machine for making, preserving, and discharging commitments—not merely an NNTP server whose implementation functions have associated theorems.** I would organize the assurance argument around those commitments, and make the implementation and proof architecture serve them.

I reviewed the pinned `dev` revision `33bb1ada701e535e6cf77eaa07264867d20e73b7`, including storage/recovery proofs, the payload representations and native realizers, reclamation, resource accounting, and the documented extraction boundary. This was source-level review, not an independent recertification or live-node experiment. The specific findings below distinguish code facts from proposed counterexamples and architectural recommendations. 

My central concern is **not that the project lacks meaningful proofs**. For example, `store-node-resolution.lisp` already contains initialized mixed-trace preservation, exact live-versus-replay correspondence, and preservation of acknowledged records through mixed traces. Those are substantial ingredients. The concern is whether the argument assembled from those ingredients rules out the failures that matter to someone relying on the system. 

## 1. Make the warranty reject useless-but-“safe” implementations

Two examples illustrate the distinction.

### A success-implies-durability theorem does not establish a working posting service

`fn-own-240-follows-consumed-completion` connects a successful served outcome to an enabled, consumed completion, the submitted identity and payload, and a record in durable history. That is useful. But its success characterization is itself expressed using the response produced by `fn-served-post-outcome` with `:durable`. A public contract ultimately needs a separately established connection to the actual externally observed protocol response. 

More importantly, **a machine that always answers “uncertain” can satisfy an implication saying that any success it emits was earned**.

The source records an especially instructive earlier regression: comparing a payload handle directly against staged octets made every served POST finish report `:fault` until the comparison was routed through the arena. That is exactly the sort of failure a warranty must exclude, even though a no-false-success theorem alone need not exclude it. 

I would pair every important safety theorem with a productive counterpart:

> A valid, authorized, funded request, under the specified successful primitive completions, reaches its specified successful outcome within a bounded amount of core work.

“Valid,” “authorized,” and “funded” must be defined by the contract, not merely by whatever the implementation’s current admission predicate happens to accept.

Likewise, uncertainty needs a justification theorem:

> An uncertain result corresponds to a named unresolved effect or observation loss; it is not an unrestricted escape hatch for an implementation that cannot finish its work.

This does not require pretending that disks always respond or networks are reliable. It requires specifying what happens **when the stated environmental conditions do hold**.

### A theorem about constructing a decision is not a theorem about performing it

`fn-lgr-decide-checkpoints-the-rewrite` is a particularly clear example. Its statement establishes that when `fn-lgr-decide` returns `:reclaim`, one element of the returned list equals `fn-rclp-events` under the selected context. Its proof unfolds the decision constructor. It does not itself quantify over checkpoint writes, installation, a crash, reopening, or subsequent observations. 

That theorem should stay. It is a useful wiring lemma. But **“checkpoints” in the theorem’s name must not substitute for a theorem about checkpoint execution**.

The eventual public argument should look more like:

\[
\forall \tau\in\operatorname{Executions}(B,P,E),\quad
A(E,\tau)\Longrightarrow
\operatorname{Observe}(\tau)\in\operatorname{AllowedTraces}(P),
\]

where \(B\) is the actual executable artifact, \(P\) the supported profile, and \(A\) the explicit environmental assumptions.

That safety statement should be accompanied by conditional progress and resource statements. Otherwise, an implementation that refuses everything remains an admissible refinement.

**What I would change:** choose a small set of public commitments, give them independent observable semantics, and make the existing proof tower discharge those commitments. Do not make theorem coverage itself the product contract.

---

## 2. A concrete boundary defect: the extent reader checks self-consistency, not the expected identity

This is the most immediately actionable code finding.

In `host/native/extent.lisp`:

```lisp
(defun fnn-extent-entry (file eoff elen trailer)
  (declare (ignore trailer))
  ...)
```

The function reads the entry and the trailer located after it. `fnn-extent-entry-ok` then passes **that newly read trailer** to the ACL2 check. The expected trailer supplied by the extent descriptor is ignored. Cache hits are keyed by `file` and `eoff`, without checking the supplied `elen` or expected trailer. 

The logical buffer checker faithfully establishes:

\[
\operatorname{digest}(\text{read prefix})=\text{trailer supplied to the checker}.
\]

That is exactly what its theorem says. It does not establish that the supplied trailer is the one the accepted extent was supposed to have. 

### The counterexample to test

Construct two different, equal-sized, individually valid entries:

\[
(E_0,T_0),\qquad(E_1,T_1),
\quad T_i=\operatorname{digest}(E_i).
\]

An extent expects \(E_0,T_0\). On a cold read, the storage observation supplies \(E_1,T_1\).

The current local check accepts the self-consistent pair \(E_1,T_1\). No hash collision is needed.

I have **not** demonstrated a remotely reachable exploit or shown that this substitution is permitted by the current narrowly stated crash model. Under a perfect immutable-file and correct-offset premise, the substitution is excluded. But it exposes exactly how much correctness the premise is carrying—and the expected trailer is already available to make the boundary stronger.

The failure specification says a read not matching the entry’s recorded trailer is refused. The native function does not establish that comparison against the descriptor’s expected trailer. 

### The repair should be more than adding one comparison

Require that the read content matches the **expected** commitment, and that the payload slice lies within the authenticated entry. Cache lookup must preserve the same statement: either include the relevant descriptor fields in its identity or validate that a hit agrees with them.

The identity should distinguish durable file incarnation from transient operating-system descriptor identity. A numeric file handle whose meaning is process-local is not, by itself, an adequate identity for a cross-restart argument.

The test family should include a wrong expected trailer, a different valid same-sized entry, a wrong offset, a stale cache entry, and an entry from another store or generation. These are stronger boundary tests than random byte damage because every substituted object can remain perfectly well formed.

**The general lesson:** proving that a checker checks its argument correctly does not prove that the host supplied the right argument.

---

## 3. Stop hiding fallible I/O inside total logical value access

The durable-extent abstraction exposes functions such as:

```lisp
(fn-durable-realize-octets file eoff elen poff plen trailer)
```

and constrains their result to equal the durable octets. The compressed realizer is similarly constrained to equal decoding those durable octets. The native implementations instead may perform I/O, block, allocate, consult caches, acquire locks, and raise a storage fault.  

This is a legitimate *partial-correctness abstraction*: whenever the native operation successfully returns, its value is assumed to agree. But it is an awkward foundation for a warranty concerning responsiveness, bounded allocation, cancellation, recovery, and isolation from other clients.

**A function that looks like a pure array access should not secretly contain an unbounded disk wait.**

I would separate the denotation from the execution protocol.

The logical denotation can remain:

\[
\operatorname{Payload}(h)=\text{the immutable byte sequence named by }h.
\]

The executable interface should look conceptually like:

```text
read_step(lease, cursor, work_budget, resident_pages)
    -> Bytes(chunk, next_cursor)
     | NeedPage(request_identity)
     | Done
     | Fault(reason)
```

Then prove the pieces that actually compose:

* Successful chunks concatenate to the denoted payload, without omission or duplication.
* Yielding and resuming is observationally equivalent to uninterrupted execution.
* A page completion belongs to the exact outstanding request and storage generation.
* Cancellation and failure preserve the required state, ownership, and accounting invariants.
* Each step has a bound on work and allocation, including its helpers.

This makes the ownership of a late completion explicit. A client timeout must not free a buffer or descriptor still owned by an outstanding I/O operation. Conversely, abandoning a client must not leave an immortal reader pin.

The existing native reader holds the extent mutex while fetching and checking a cache miss, and the single-octet realizer acquires that mutex for each access. Moving I/O out of the owner’s critical path is therefore not merely a scheduler improvement; it needs an interface that makes waiting and ownership visible to the proof. 

For methodological precedent, the useful aspect of FSCQ and Perennial is not “switch to Coq.” It is treating crash behavior and concurrent storage effects as part of the program specification and composition rules, rather than burying them inside a value oracle. Perennial’s work includes a concurrent mail server with a no-lost-delivered-messages argument—a particularly relevant neighboring problem. :chatgpt-content-reference{index="33"}

---

## 4. The representation work needs a stronger rule than “smaller and provably equivalent”

There is real progress in the representation architecture: the generic arena, byte-array implementation, paged implementation, and correspondence obligations already provide a way to change execution without rewriting every consumer proof. I would preserve that mechanism.  

But representation equivalence should include an **access and ownership contract**, not just value equality.

### Whole articles as bignums are an architectural compromise, not an obvious destination

`packed-submission.lisp` packs an article’s octet list into one natural number when it is enqueued, then reconstructs the list when the committer takes it. The implementation uses divide-and-conquer packing; the corresponding digit reader also uses divide and conquer. This is not the naïve quadratic construction one might initially suspect.  

Nevertheless, this is still:

```text
bytes → lists → whole-body integer → lists → later representation
```

The packer repeatedly traverses list portions and operates on wide integers. Under the conventional list/limb cost model, the divide-and-conquer structure incurs \(O(n\log n)\) work rather than giving you a zero-copy queue transition. That is an algorithmic assessment, not a timing measurement.

I would compare this against:

> A submission owns an immutable byte-buffer lease; enqueue and dequeue transfer the lease, not the article’s representation.

The logical view of the lease can still be an octet list. The queue does not need to execute that list.

Bounded packed blocks may remain a reasonable choice for some parts of the wire machine. The objection is not “bignums are inherently wrong.” It is **using a whole-body conversion to cross an ownership boundary that should require only transferring a handle**.

There is also an assurance subtlety: the packer’s unconditional round trip preserves non-octet inputs through a `:raw` fallback. That is convenient for totality, but it is not an unconditional footprint theorem. A proof that the charged length equals `len` does not bound the memory occupied by an arbitrary raw Lisp object. The reachable production domain must rule those cases out before accounting relies on that length. 

### Compressed bytes should not become a list-valued random-access cache

The compressed extent cache retains one decoded payload as a list, and `fn-arena$x-get` retrieves byte \(i\) through `fn-oct-nth` on that returned value. The cache is a single “last decoded payload,” shared across accesses.  

Two access patterns deserve explicit regression tests:

**Sequential byte reads:** ordinary repeated indexing into a list produces quadratic traversal. Trace the actual served consumer to establish whether this cost is realized, rather than inferring performance from the abstract `get` API.

**Alternating readers:** switching between two compressed articles can defeat a one-entry decompression cache. An interface that is cheap for one reader can repeatedly decode under a different interleaving.

The executable contract should promise something concrete: a decoded byte array with bounded indexed access, or a forward chunk cursor with bounded amortized work. Its cache should be budgeted in bytes, including decompressed size and dictionary ownership—not just number of entries.

### Stop repairing each whole-store traversal independently

The resource contract identifies repeated replays during reconfiguration, per-POST pin scans, store-linear status generation, worst-case linear hash buckets, and several other history-sized operations on served paths. Those are not all the same bug, but they suggest a recurring construction pattern: derive a useful answer by walking a large semantic representation, then add a specialized optimization when it becomes painful. 

I would impose operation-level complexity contracts:

| Operation | Intended executable contract |
|---|---|
| Message-ID lookup | Bounded-key trie/radix lookup or balanced-tree lookup; distinguish expected hash performance from deterministic worst case |
| Group/range enumeration | Seek plus work proportional to returned entries, not the numeric span or entire archive |
| Acquire/release a hold | Update the affected obligation and object, not scan every pin |
| Status/health counters | Read maintained aggregates |
| Reconfiguration | Recompute only affected projections, or perform a versioned bounded rebuild |
| Body transfer | Chunked work proportional to transferred bytes, with explicit leases |

A deep invariant check should not silently reintroduce the traversal that an index eliminated. Prove that ordinary transitions maintain the relation; reserve full reconstruction/checking for a separately budgeted validation operation.

---

## 5. The resource warranty must connect accounting to execution

The heap books do more than handwave: they define state, history, transient, buffer, and collector terms and prove inequalities between them. But the model explicitly incorporates measured representation constants and assumptions about copying and collector behavior. The arithmetic theorem does not independently establish those runtime facts.  

The missing distinction is:

\[
\underbrace{\operatorname{Charge}(s)\le B}_{\text{accounting invariant}}
\qquad\text{versus}\qquad
\underbrace{\operatorname{ActualFootprint}(c)\le
\operatorname{Charge}(s)+R}_{\text{representation/runtime bridge}}.
\]

You need both.

Otherwise, **you risk proving the accounting spreadsheet rather than the allocator**.

This remains true after credit admission is fully connected. A perfectly preserved credit ledger can undercharge an allocation, omit a retained alias, fail to include an old snapshot, or assume garbage is reclaimable sooner than the runtime actually reclaims it.

I would split the guarantee into three explicit layers.

**Logical resource conservation.** Every operation, cache entry, outstanding I/O, and retained version has an owner and a charge. Transfers conserve charge. Admission funds the entire remaining obligation, including completion and cleanup—not merely its next allocation.

**Concrete representation cost.** Constructors and transitions establish bounds on objects created, bytes copied, retained roots, temporary coexistence, and release. Resizing must charge the old and new arrays while both exist. Compaction must charge the old generation until its last reader and outstanding read are gone.

**Runtime envelope.** Collector overhead, foreign-library allocation, thread stacks, kernel resources, and page-cache behavior have their own scoped assumptions or measurements. Those should not disappear into a miscellaneous margin that every subsystem presumes someone else owns.

The same distinction applies to time. The scheduler theorem that a control request waits at most three quanta does not establish a latency bound unless every intervening quantum has a bounded cost. The repository explicitly distinguishes quantum counts from quantum duration. 

A useful cost model should count something operational: bytes scanned, array cells touched, tree nodes visited, decoded output, and pending work. Treating “call a function” as one step while that function hashes a megabyte or scans the store defeats the purpose.

Also separate **resource containment** from **resource sufficiency**. An operating-system memory cap can establish that fn cannot consume unlimited memory. Killing the process at that cap does not establish that funded, admitted operations complete without exhaustion. Those are different warranties.

---

## 6. Make the event history the semantic backbone—not merely the input to replay

The existing mixed-trace and replay theorems are a good base. But “live execution equals replay” can still mean that the same semantic mistake is reproduced faithfully. The next layer should say what histories mean and which transformations preserve that meaning. 

### Prove that acknowledgements identify commitments

A successful acceptance should establish a durable identity binding:

\[
\operatorname{Accepted}(op)
\Rightarrow
\operatorname{Recorded}
(op,\;subject,\;principal,\;policyContext,\;undertakings).
\]

Here `subject` must name the exact accepted authored object or explicitly specified projection—not ambiguously conflate source bytes, mutable transport headers, and stored rendering.

Then subsequent traces should preserve the acceptance fact and its identity, while payload availability is governed by the outstanding retention obligations. This avoids both overclaiming “success means bytes forever” and underclaiming “success means some internal completion existed.”

A refusal should establish its exact semantic footprint. The repository already recognizes that a refused POST can consume an allocator identity without accepting the article. Keep that distinction in the public model; do not force an inaccurate universal “refusal changes nothing” story. 

### Prove authorization provenance, not just reproducible verdicts

For every authority-sensitive transition, the history should recover why it was authorized:

> This principal, under this policy version and evidence context, was authorized to cause this particular transition.

Replaying under today’s policy must not retroactively invent authorization for yesterday’s decision. Conversely, preserving historical authorization should not automatically confer current authority after revocation.

I would keep three concepts sharply separate in the semantic schema:

**Observed evidence** says what statement or object arrived.

**An authorized decision** says what local transition the node accepted on that evidence.

**An obligation** says what must remain true until a specified discharge occurs.

A signature verification result belongs to the first category unless an authorization rule connects it to the second. An observation of a receipt is not automatically the third category’s discharge.

### Preserve knowledge through uncertainty and reclamation

The system should distinguish:

```text
not accepted
accepted and retained
accepted and legitimately reclaimed
outcome unresolved
history unavailable
```

Current absence of a payload must not collapse these into “not accepted.”

This is especially important for retries after lost acknowledgements. The persistent evidence needed to reconcile the original operation identity has a different lifetime from its body bytes.

### Make reclamation a semantic transition plus a representation transformation

`store-reclaim-pack.lisp` rewrites reclaimable article records into tombstoned records while preserving identity, numbering, obligation-related fields, and other event kinds. It proves useful field, shape, and idempotence properties. 

But the strongest required theorem is not “the rewrite is well formed” or even “the rewrite is idempotent.”

It is a **future-observation equivalence**:

\[
\forall E,\quad
\operatorname{Observe}(\operatorname{Continue}(S,E))
=
\operatorname{Observe}(\operatorname{Continue}(C(S),E)),
\]

where \(C\) is physical compaction/reclamation **after the corresponding logical release**, and `Continue` includes refusals, retries, queries, and future authority changes.

This formulation catches mistakes that current-state equality misses:

* Reclaiming an identity record can permit a conflicting retry to be accepted later.
* Dropping one dependency can make a later receipt incorrectly discharge an obligation.
* Reconstructing under a new policy can change whether an old decision appears authorized.
* A summary can preserve today’s query answers but fail to preserve tomorrow’s enabled transitions.

If reclamation is itself supposed to change the logical answer, represent that change explicitly first; then prove that physically removing bytes implements it. Do not describe an observable change as mere storage optimization.

This does **not** require retaining every historical byte forever. The resource contract correctly notes that reclaim presently frees content bytes without freeing transaction count. An indefinitely useful bounded store will need an explicit history-lifetime policy or a proved summary—not just increasingly efficient packing of an ever-growing identity history. 

A Merkle root can authenticate retained evidence, but it does not answer an unavailable historical query, establish non-equivocation by itself, or prove that omitted facts were safely forgotten. The summary must be sufficient for the observations and future decisions the warranty promises.

---

## 7. Yes: a verified incremental-view layer is a strong architectural direction

I think your differential-dataflow suggestion points at something more important than a performance technique.

**Much of fn’s mutable state could be specified as materialized views of committed facts, with proved incremental maintenance.**

The relevant ideas are differential collections, incremental view maintenance, and explicit treatment of retractions. Differential dataflow supplies a framework for maintaining changing computations, including iterative ones; DBSP develops a general algebraic approach to incrementalization across richer query languages. Neither requires that fn adopt a distributed dataflow runtime wholesale. :chatgpt-content-reference{index="49"}

### Start with a small relational vocabulary

For example:

```text
Article(article_id, source_commitment, metadata)
Membership(group, number, article_id)
Obligation(obligation_id, article_id, kind, release_rule)
Discharge(obligation_id, evidence_id, decision_context)
Evidence(evidence_id, subject, issuer, context)
ConsumerPosition(consumer, history_id, position)
```

Then specify views such as visible memberships, active obligations, protected dependency closure, replication candidates, resource totals, and status counts.

For each view \(Q\), maintain a concrete representation \(V\) with:

\[
\operatorname{decode}(V)=Q(F),
\]

where \(F\) is the committed fact state.

For an accepted transaction producing \(\Delta F\), prove:

\[
\operatorname{decode}
\bigl(\operatorname{Update}_Q(V,\Delta F)\bigr)
=
Q(F+\Delta F).
\]

That one theorem shape can replace a recurring pattern of whole-store recomputation followed by a separately developed fast path.

### The algebra gives you small reusable proof obligations

For a join, for example:

\[
\Delta(L\Join R)
=
(\Delta L\Join R)
+
(L\Join\Delta R)
+
(\Delta L\Join\Delta R).
\]

The cross-term is not optional when both sides change in one transaction. Alternatively, a sequential update scheme must account for it exactly once.

Prove a small library of map, filter, keyed aggregation, join, and selected retraction rules. Instantiate it for specific views rather than independently rebuilding each maintenance argument.

Keep the reference query functions simple and executable. They are valuable test oracles even when the production path never runs them on a large store.

### Retention is a particularly good first application

An article can have multiple independent reasons to remain protected. Therefore:

\[
\operatorname{Required}(a)
=
\exists o.\;
\operatorname{ActiveObligation}(o,a).
\]

Do not maintain this as a boolean that “release” clears. Maintain obligation identity and the contributions supporting the result. Duplicate receipt delivery must not subtract twice; releasing one obligation must not erase another.

Physical reclamation additionally requires the absence of transient readers, staged operations, and old-generation references. Those are different kinds of ownership from durable retention undertakings, even if both contribute to a final reclaimability decision.

For dependency closure, be careful with cycles. Naïve reference counts are not equivalent to reachability from protected roots on cyclic graphs. Either prove that the dependency structure is acyclic or use an appropriate reachability-maintenance argument.

### Do not let differential retractions perform irreversible actions directly

This is the most important restriction.

A transient materialized view can briefly report “no active holders” while updates are being processed. That must never directly cause file deletion.

Use a transaction-controlled path:

```text
committed facts
    → maintained candidate view
    → decision bound to a complete committed version
    → durable release/reclaim decision
    → physical work
```

If a new hold arrives between candidate generation and action, the final decision must revalidate the relevant version or participate in the same serialized transaction.

Likewise, a retracted view row does not mean an external action has been undone. A transmission that happened, an acknowledgement emitted, or a file unlinked requires its own event/effect semantics.

### Give the views explicit completeness and version identities

For ordinary local projections, start with a single committed sequence number. Introduce partially ordered timestamps only where the computation actually needs them—for example, nested fixed-point maintenance.

A view should be associated with a token identifying the store history, committed position, and relevant schema/policy interpretation. “Computed through this version” needs a precise meaning: all its required inputs through that version have been incorporated.

A lagging view cannot silently authorize a current destructive decision. An older snapshot may be entirely correct for a reader that explicitly holds that snapshot.

### Incremental does not mean bounded by the size of the input delta

One changed group policy can affect every article in that group. One changed root can alter a large dependency closure. The work bound must include affected output and fanout.

The target is:

> Pay for the affected region, expose the remaining work as a cursor, and fund the retained intermediate state.

It is not:

> Every event becomes constant-time because it is represented as a delta.

Also, maintained arrangements and historical versions consume memory. Compaction of those structures must respect the oldest live reader or computation that still needs them. Otherwise, the dataflow layer merely relocates the same lifetime bugs.

**My recommendation:** build a small verified incremental-view substrate inside the existing architecture. Start with status aggregates and active-retention contributions. Those offer both immediate performance value and a clear test of whether the abstraction actually reduces proof duplication.

---

## 8. Strengthen the trust argument without turning it into more paperwork

### A local witness proves consistency, not adequacy

The assumption books correctly use constrained functions with local witnesses. But those witnesses demonstrate that the constraints are satisfiable. They do not demonstrate that the deployment implements them, nor that the constraints express the desired physical property. The source itself acknowledges that merely declaring an assumption does not make a theorem depend on it. 

For each public commitment, I would want one traversable dependency path:

```text
observable contract
→ semantic theorem
→ maintained representation relation
→ actual executable entry
→ effect/adapter correspondence
→ physical or cryptographic premise
```

The question is not “how many assumptions?” It is:

> Does an assumption quietly contain the behavior that the software was supposed to establish?

“Reads return the correct bytes” is a reasonable bottom-level premise in some models. But once fn has its own cache, offsets, descriptors, checksums, decoding, and asynchronous requests, much of *which bytes were requested and returned* is fn’s responsibility, not the disk’s.

### Do not optimize for syntactically impressive theorems

The repository’s theorem-shape detector explicitly acknowledges that it cannot determine whether a theorem is about the right subject and that absence of a flag is not evidence of strength. That is the correct limitation. 

I would go further: a strong end-to-end theorem **should often become a short corollary** once the abstraction boundaries are right. A long proof is not more warrantable than a one-line application of a strong interface theorem.

Keep the lints as diagnostics. Do not let avoiding “definition restated” or “instance corollary” become an optimization target for the agents. Judge the contract stated, the premises discharged, and the behaviors excluded.

### Correct the quantitative assumption language

The failure specification describes a \(2^{-128}\) collision figure “per chosen pair” for a 256-bit digest and calls it a birthday bound. That conflates different quantities. 

Under an ideal 256-bit-hash model, two independent random inputs collide with probability \(2^{-256}\); among \(q\) sampled inputs, birthday collision probability is approximately \(q(q-1)/2^{257}\) in the small-probability regime; generic collision search reaches constant success probability at roughly \(2^{128}\) work.

None of those figures automatically describes the probability that a particular torn-write process produces a validating frame. State the actual threat/fault model and its required cryptographic property. Do not substitute a security-strength number for a failure-probability argument.

### Extraction needs semantic validation, not only matching outputs

The specification already describes per-build stateful differential testing for the extracted SBCL product, including outcomes, files, subsequent reads, interruption, and failures. That is the right direction. 

The next strengthening is independence. If both sides share the same incorrect response formatter or replay interpretation, agreement can preserve the same error.

I would add a deliberately small contract interpreter and observer that do not share the production codec/replay pipeline. Compare client-visible histories and recovery outcomes against that model, not just one executable against another.

For the extractor itself, concentrate validation on its actual semantic hazards: attachment resolution, guard domains, `mbe` branch selection, integer behavior, stobj updates, aliasing, exceptions, and foreign-call boundaries. A smaller independently checked translation subset is more valuable than a larger number of ordinary successful transcripts.

### Test the guarantee by trying to preserve proofs while breaking the promise

Use semantic mutations such as:

* Always return uncertainty instead of completing a valid POST.
* Substitute a different self-consistent extent.
* Apply a receipt twice or release the wrong obligation.
* Serve an index from a different committed prefix.
* Omit one retraction from a maintained view.
* Forget an operation identity during reclamation, then retry it.

Freeze the public contract while applying these mutations. Ask which guarantee rejects each mutant.

A surviving mutant is not automatically proof of a defect—the mutant might preserve the contract—but it forces the useful question. A `must-fail` proof attempt by itself is weaker evidence than an explicit reachable violating execution: prover failure can reflect difficulty rather than falsity.

---

## 9. The development unit I would use next: one complete warranted lifecycle

I would not ask the agents merely to “close all the assurance gaps.” That invites another expansion of local obligations.

I would give them one cross-cutting lifecycle:

> Accept a post; lose its acknowledgement; restart; reconcile the original operation; read through the indexed view; establish two independent holds; discharge one; run compaction; discharge the other; reclaim the payload; retry the original operation again.

For every prefix—including cuts during compaction and delayed I/O completion—establish the observable outcome, retained evidence, ownership state, and resource charge.

The work can be split into a few concrete packages:

| Package | Deliverable that would materially improve the warranty |
|---|---|
| **Extent identity and reads** | Expected-commitment binding, cold/cache-hit substitution tests, and an explicit fallible/resumable read protocol |
| **Contract-level theorems** | Success soundness **and** productive behavior under successful primitives, with a separately specified external observer |
| **History and reclamation** | Operation reconciliation and future-observation preservation across release, compaction, and payload removal |
| **Incremental views** | One reusable delta-maintenance abstraction, demonstrated on aggregates and independent retention contributions |
| **Resource correspondence** | A bridge from the funded ledger to concrete allocations, retained generations, and outstanding effects |
| **Independent validation** | A small contract interpreter plus mutation and stateful differential tests against the actual shipped artifact |

The crucial acceptance criterion is not that each package has its own theorem. It is that the lifecycle composes without requiring someone to say, between two proved layers, **“and obviously the host does the corresponding thing.”**

**My overall recommendation is to keep the formal core and representation-refinement approach, but change the organizing center. Make commitments, histories, owned resources, and observable traces primary. Make the data structures maintained representations of that semantics. Make physical effects explicit.**

Then the warranty becomes a statement someone can actually rely on:

> Under these stated conditions, this artifact makes these commitments, preserves them through these failures, refuses only within this specified envelope, and cannot silently convert uncertainty, missing evidence, or storage transformation into a false answer.

That is a much stronger destination than “the theorems cover the functions the server calls.”