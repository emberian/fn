## 1. Misstatements and weakened requirements

The execution model is agreed. These sentences need correction:

**§2, BODY accounting**

> “A 16 MiB BODY is 256 output quanta across many turns; a TAKETHIS window is several record lifecycles at once; `XOVER 1-1000000000` is a cursor over an indexed, pinned selection.”

Replace with:

> “A 16 MiB BODY requires at least 256 payload quanta at 64 KiB, or 4,096 at the initial 4 KiB execution quantum, plus framing and partial-I/O work; a TAKETHIS window contains independent record lifecycles; XOVER traverses an indexed, pinned selection.”

Round 1’s calculation was conditional on **64 KiB**, not the subsequently chosen execution quantum.

**§2, CPU ceiling**

> “CPU is the ceiling only near 67k POSTs/s (ENVELOPE §1).”

Replace with:

> “The envelope projects a CPU ceiling near 67k POSTs/s under its assumed per-POST cost; the composed implementation must establish its actual ceiling.”

This is arithmetic, not an established capacity.

**§3.8, durability**

> “Barriers per backend: finish all dependency writes, then the backend's durability barrier covering them; FUA on the final sector alone is never sufficient (preflush vs FUA).”

Replace with:

> “The baseline completes all dependency and batch/log writes before a covering durability barrier; an alternative completes preceding writes before a sealing write with the specified preflush-plus-FUA contract, or establishes every dependency’s durability separately.”

The omitted **batch/log writes** matter. “Never sufficient” also overstates the objection: final-sector FUA can suffice when all preceding dependencies are already durable.

Add the publication requirement explicitly:

> “One bounded transition installs the complete committed root/frontier; replies and wake fan-out proceed incrementally afterward and do not gate visibility.”

That was a central round-2 decision, not merely an implementation detail hidden behind `publish`.

**§4, assurance scope**

> “The five robustness claims: no-crash and bounded-work are core theorems; isolation is a trace property of repeated transitions plus scheduler fairness; durable acceptance and exact identity are core-plus-environment under the named assumptions (round 1 §3).”

Replace with:

> “Core theorems establish guard safety for arbitrary client octets, modeled work and memory bounds, typed failures, reply semantics, and exact identity decisions; protected-resource isolation is a trace property, service guarantees additionally require fairness and available dependencies, and whole-process safety and end-to-end durability/identity require the relevant adapter, runtime, and environment contracts.”

Round 1 explicitly retained memory, typed-failure, and reply obligations. Fairness is needed for service guarantees, not every isolation property.

Finally, §1’s semantic-boundary list should explicitly retain **the built-in web interface and authentication/authorization policy**, both inside my round-1 boundary.

## 2. New decisions I disagree with

**Freezing all three DSLs before protocol use.**

> “The three DSLs (records/columns; machines with state enums, fields, accounts, continuations and budgets; command grammars) are designed in the bytes-and-store layers and stabilized before the protocol layer uses them.”

I argued for shared declarations generating the realizations and correspondence obligations. I did **not** argue for stabilizing a command-grammar DSL before exercising a protocol.

Better:

> “Develop the shared declarations bottom-up, exercising them through the first composed protocol slice before stabilizing their interfaces.”

The byte and store layers cannot establish that a grammar abstraction handles fragmented commands, article framing, discard, and STARTTLS correctly. Designing the whole boundary first is sound; freezing its generator before its first real consumer is premature.

The other substantive new disagreements—startup indexing, filesystem selection, and the durable-state recommendation—are addressed below.

## 3. Section 6 rulings and section 7 recommendations

**§6.1 — Message-ID index: disagree.**

The ruling says:

> “Ruling: start with rebuild-at-open (simplest, measured cheap at 1M) and treat the pageable index as the first storage-layer optimization once the replay overlay's growth is measured; the rebuild stays as the repair path either way.”

“Measured cheap” is false: ENVELOPE §1.6 labels the estimate **[D]**, and §2.8 explicitly lists that measurement as unperformed.

Better ruling:

> “The first served storage design uses a persistent pageable identity index with bounded replay state and explicit backpressure when maintenance falls behind; full rebuild remains a bounded-memory repair path.”

The objection is architectural, not a disputed constant. Rebuilding a resident hash table couples retained identity history to RAM; making startup incremental only bounds each step, not total recovery work. Measuring one million entries cannot settle either issue. This also resolves §6.1’s contradiction with rule 9.

**§6.2 — Bounds classification: agree; change the measurement sequencing.**

Adopt all four categories and round 2 §G’s corrections. Run the five measurements before freezing the capacities they inform; they need not all precede byte-pool, simulator, or machine construction. Access to a rented PLP device should not gate independent work.

**§6.3 — Threads: agree, with one qualification.**

Foreign work whose supported worst-case cost fits the quantum may run inline. Otherwise use bounded workers with reserved capacity. One semantic executor remains the rule.

**§7.1 — One preallocated data file: agree.**

Specify capacity, full-store behavior, initialization persistence, and protected maintenance space. Direct I/O is a backend qualification choice; it does not supply durability by itself.

**§7.2 — Refuse CoW filesystems: disagree with the categorical rule.**

Better recommendation:

> “Support named, qualified backend configurations according to their persistence, failure, alignment, and resource contracts; reject unsupported configurations, rather than filesystem categories.”

The core names logical file offsets, not physical filesystem blocks. Physical relocation alone therefore does not establish incompatibility. Conversely, “page-cache backend” or “zvol” alone establishes none of the required guarantees. An operator override must name the weaker supported profile; it cannot waive a missing correctness premise. I am not declaring any particular ZFS configuration qualified.

**§7.3 — Article size: agree.**

One MiB is an admission default, not a representation ceiling. The composition-test profile must explicitly admit the 16 MiB BODY fixture.

**§7.4 — Unit of state: agree only after narrowing the wording.**

Better recommendation:

> “Use immutable committed records as the authoritative history; persist derived indexes, roots, consumer progress, identity bindings, and other required state through that history’s checkpoint/recovery contract. Defer a general client-facing mutable-key API from the first slice.”

“Only durable unit” otherwise confuses logical authority with physical representation. “Until a client needs them” is also misleading: CLIENTS §2.2 and §5 already identify keyed-state needs. Deferral can be a deliberate slice boundary, but cannot stand as the answer to those needs.

## 4. What the first-slice builder still needs

These are missing implementation contracts, including gaps in my rounds:

- **A concrete storage format and root-selection algorithm.** Specify record/page encodings, integrity coverage, incarnation and predecessor fields, root installation/selection, and allocator recovery. In particular, define how two prepared batches construct successive roots without losing each other’s updates. Four superblock copies and an atomic in-memory root assignment do not answer this.

- **A resource acquisition and release protocol that excludes deadlock.** The tables enumerate resources but do not establish acquisition order or complete admission bundles. Define protected credits for cancellation, close, fence, and recovery; demonstrate that accepted work can reach its release transitions under saturation. Define how notification debt transfers out of a committed batch so two slow recipients cannot occupy both batch slots indefinitely.

- **The executable host/core ABI.** Specify how an adapter acknowledges consuming an outbox prefix, how the core distinguishes queued from submitted operations, and exactly when initialized bytes become core-readable. Include partial submission and process-death cuts at that handoff. Event names and queue capacities alone do not define this interface.

- **The remote consumer protocol and authentication path.** Give actual wait/poll/ack frames, cursor and query-version encodings, retry/outcome semantics, and login/capability establishment. STARTTLS admission alone does not implement the authenticated consumer used by the acceptance scenarios. Add wire fixtures that the independent checker can consume.

- **One unambiguous implementation baseline.** State which round-2 tables are normative, which values are provisional profiles, and that this decision supersedes contradictory envelope/orientation instructions. Otherwise tomorrow’s builder is simultaneously told to page identities and rebuild a resident table, and to test a 16 MiB article under a 1 MiB default.