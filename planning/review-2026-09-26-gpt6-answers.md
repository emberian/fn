# gpt-6's answers to the deputy's seven questions, 2026-09-26 (forwarded by ember)

Answers `planning/for-gpt6-2026-09-26.md`, reviewed from `145ed138` (the
candidate b6759850's closure) through `4fb6dfc0` (rep-wave-d-3's merge).
The deputy's actions on it are in `build/coordinator/WAVE-STATE.md`: the
three qualification reframings sent to qual-b6759850 (§4); lane
rollback-history for the misstep in §7; lane rep-wave-d-4 (Fable) for the
representation wave's shape in §1 (this answers PKT-293 with refinements:
ember confirms or overrules); the exit-code and CONFLICT decisions of §5
queued as lane outcome-algebra for the coordinator's word (PKT-295,
PKT-246); the second convergence's ranks in §4 as the next cut's definition;
the proposed AGENTS.md rule at the end for ember and the coordinator.

---

Yes—and **the repository moved far enough during this review to change the answer to the biggest question**.

I started from `145ed138`, which records the fresh full closure for candidate **`b6759850`**. Then I followed the representation continuation through **`4fb6dfc07847637ba6c5d521585dd694d3d85cd6`**, including `rep-wave-d-3`. The candidate's recorded certification and the later representation work are separate evidence coordinates; I have not rebuilt or independently rerun their native campaigns.

**The demonstrated checkpoint-reader failure is now repaired in that continuation.** The same 670 MB checkpoint that exhausted the old reader's heap now reopens in **132.3 seconds at a 19.3 GB peak**, according to the matched native record. The retained state still contains two list copies of each payload after checkpoint recovery, but "implement the buffer decoder" is no longer the next assignment. Its integration and qualification are.

My central recommendation is:

> **Converge on a system whose admitted data remains operable throughout its lifetime—not merely encodable at ingress. Use the representation work to make that lifetime affordable, and use independently operated nodes and real consumers to determine whether the resulting system is useful.**

Below are direct answers to the seven questions, including what I would reject and its cost.

---

## 1. Representation: approve the shared transition, but preserve the logical model

**Recommendation: adopt the payload-opaque transition and two representation views. Do not implement it as a global replacement of the old payload predicate with `natp`.**

The revised investigation is important: the record and acceptance state share the payload today, and the transition itself performs byte-dependent interpretation. Changing only the record field would neither remove all retained lists nor leave `fn-sn-finish` executable. Likewise, a wire codec cannot remain injective over arbitrary arena handles when different handles may denote identical bytes. The D-2 record identifies these problems accurately.

### "Parametric" is the right idea; it needs a precise meaning

The undesirable twin is **a second implementation of semantic decisions that must evolve alongside the first**. It is not every pair of logical and executable functions. Abstract stobjs explicitly support different logical and executable operations connected by correspondence, preservation, and guard obligations; avoiding those pairs would defeat the mechanism.

I would structure this as:

- A **logical/wire record**, preserving the existing octet-list semantics and codec domain.
- A **retained record**, containing a payload reference and byte-derived metadata.
- A **shared semantic transition** that operates on the metadata and transports the payload reference without depending on its concrete representation.
- A small set of byte-observing boundaries: intern, compare, encode, render, recover, and reclaim.

Sharing tuple accessors is fine. Sharing a predicate whose meaning silently changes from "contains octets" to "contains an integer" is not.

The central relation should connect a concrete owner and arena to the old logical owner. Schematically, under that relation and corresponding input events:

alpha(S_c', A') = S_l', and [[E_c]]_{A', pin} = E_l.

The first equation connects states. The second connects **effects**, including the bytes eventually written. Chunked execution may require trace refinement rather than equality of one effect list.

This is stronger and more useful than "the new record materializes correctly": it establishes that the **actual transition and its outputs** still mean the same thing.

### Split cached facts into two classes

**Byte-derived facts** can be computed once from immutable bytes: header/body boundaries, body line count, parsed control target, source digest, and representation classification.

**Context-dependent facts** need their context attached: historical verification verdict, enrollment generation, policy generation, and authorization decision.

The proposed intern-time verdict therefore needs more than "intern happens before finish." It needs the exact theorem that the relevant verification context cannot change between those points—or an explicit snapshot that the eventual acceptance uses. Interning a queued input before it reaches its acceptance context would be a different operation.

Similarly, caching a control target is sound; caching "this control may execute" without its authority context is not. Caching a payload digest can eliminate reclaim-time hashing; it cannot eliminate the current holder and release checks.

These distinctions follow directly from the D-2 proposal's use of keyring-at-intern and its outstanding prepare/finish correspondence obligation.

### Which boundary first? D-3 has now answered that

The buffer reader was the correct first boundary. Keep its result and qualify it; do not restart it under a larger abstraction project.

However, D-3's new `3 x H + framing` file bound is **an input-size policy bound, not by itself a proof of peak residency**. The reader still constructs retained lists and a transient list for each segment's seal. Its evidence honestly reports those costs. A large operator history budget must not be confused with available process memory.

For an auxiliary checkpoint, a separately stated execution-memory budget may cause a **named fallback to authoritative replay**. That is not an arbitrary cap on stored articles. It is choosing not to use a cache that cannot presently be processed safely. The fallback must happen before fatal allocation, not depend on catching an out-of-memory failure afterward.

### What I would land in the representation wave

Make the wave's endpoint **one native vertical slice**:

> POST -> interned retained record -> completed owner state -> pinned ARTICLE/OVER -> checkpoint -> reopen, without restoring a long-lived list payload in either the record or acceptance state.

Combine the arena transition with **PKT-307's single-payload checkpoint representation**. D-3 establishes that the second copy is in the checkpoint value itself—one in the configuration fold's node and one in the event index—not just an avoidable intermediate list. A versioned checkpoint representation that stores payload bytes once and references them from both structures addresses the actual cause.

Those persisted references should be **file-local references**, translated into runtime handles on load, not globally meaningful identities or assumptions about a particular process's arena numbering.

Cut the following from this wave: a general representation framework, online arena compaction, arbitrary parser rewrites, and migrating every BP/feed byte path simultaneously. Preserve the existing mutation serialization and use explicit lifetime rules for pinned references.

One caveat to carry forward: the arena currently grows by doubling arrays. That supports amortized efficiency, but does **not** establish a bounded individual scheduling step or bounded resize peak. Do not quote amortized seal cost as a latency guarantee; a later paged arena or incremental growth strategy may be warranted.

**Rejected alternative:** threading the arena through the entire old transition and proof vocabulary immediately. It creates broad signature/proof churn before delivering a coherent runtime boundary. Also reject retaining an old payload list indefinitely "for correspondence": the correspondence belongs in the proof, not in a permanent duplicate of the data.

---

## 2. Finding hidden whole-state work: build the detector and measurements before a universal cost proof

**Recommendation: build a small hot-path dependency checker plus dimensional work measurements first. Add cost theorems at the high-value boundaries it identifies.**

The important pattern is not merely "a recognizer exists." It is:

> A function invoked once per request or arrival traverses a collection whose size is independent of that request.

The BP evidence is a particularly good example. The uncapped reassembler has an impressive isolated result, while the complete arrival path projects to roughly 43 hours for the 10 MiB case. The record explicitly labels `fn-bpnf-heldp` re-encoding as the **likely, not yet profiled**, cause. Keep that distinction while investigating.

### The static tool should track size provenance

Reuse the existing s-expression reader and the style of `session_depth.py`: seeded facts, propagation, and an explicit "unknown" result where inference is insufficient. That checker already avoids pretending that ambiguous shared result records have a known session type.

For work, seed dimensions such as:

```text
B = bytes newly supplied by this request
K = records or bytes requested for this response
N = retained Store history
F = held fragments
J = queued jobs
```

Then report paths from host entries to operations that traverse those dimensions: recognizers, encoders, replay folds, `len`, `nthcdr`, append-to-history, repeated membership searches, and list conversions.

It must follow the **executed** path: `mbe` execution branches, attachments, guard evaluation, host wrappers, callbacks, and protected stobj exports. A theorem-side logical walk that is never executed is not a runtime defect; a guard walk omitted from the source-body analysis absolutely can be one.

A useful finding looks like:

```text
per-arrival entry
  -> family selector
  -> held-row recognizer
  -> encode held bundle
work dimension: all F retained rows, not newly received B bytes
```

Classify each path as intentional cold work, resumable work, output-proportional work, unexpected retained-state work, or unresolved. Do not begin with an enormous approved baseline that makes every existing problem disappear.

### Pair it with scaling tests that vary one dimension

Hold the request and profile constant while varying N. Hold N constant while varying payload size. Vary fragment count independently of total ADU size. Record primitive visits, bytes copied, allocated bytes, lock-hold time, CPU time, and wall time.

That separates "one expensive decode" from "decode every previous input again." It also catches purported caches that avoid re-encoding but still traverse the full prefix.

A few measured execution counters are worth more initially than a complicated static asymptotic analyzer. The checker finds suspects; measurements identify the dominant executed paths; proofs establish the replacement.

### Where the proofs should go

For each rewritten scheduler entry, prove a work statement in terms of **new input, touched records, and the work quantum**, not the entire operator capacity. For example:

W_step <= a + b*B + c*T,

where T is a bounded number of records actually visited in this step. Prove continuation/progress separately.

For fragments, maintain coverage information incrementally. **Use interval-union coverage, not the sum of fragment lengths**: overlaps and duplicates make the latter inadequate. Preserve the existing conflict-before-gap behavior when overlapping fragments disagree.

**Rejected alternative:** requiring a complete cost theorem for every host entry before removing the known traversals. That creates a second large formalization project and delays obvious repairs. Also reject treating a static checker's silence as a proof: dynamic attachments and host integration make that claim too strong.

---

## 3. v1 throughput: measured service objectives plus structural scaling guarantees

**Recommendation: promise a measured envelope for a named execution profile, supported by work bounds—not one in place of the other.**

The current evidence does not justify a universal "one POST per second" characterization. The matched baseline reports unsigned POST medians around **250–400 ms on ZFS**, versus roughly **18 ms for the 32 KiB tmpfs case**. Signed POST was not measured by that harness. Under reader contention, ARTICLE latency rises sharply. Also, the baseline's sub-millisecond greeting column is measured **before loading the store**, so it does not contradict the loaded-greeting problem.

Separate:

T_request = T_queue + T_semantic work + T_byte processing + T_durability + T_transport.

Representation improvements will not remove a storage-barrier latency floor. Mutex changes will not remove whole-history replay. A fast hash does not compensate for hashing all old articles again.

### The envelope I would aim to qualify

The following are **my proposed engineering targets**, not achieved results or predictions. Use one named Linux/storage/runtime profile, approximately 32 KiB articles, a stated group distribution, and three concurrent reader sessions. Measure latency at a declared sub-saturation offered load; measure sustainable throughput separately.

| Operation | N = 10,000 target | N = 100,000 target |
|---|---:|---:|
| Warm greeting after the store is loaded, p95 | <= 50 ms | <= 50 ms |
| OVER for a fixed 40-row window, p95 | <= 50 ms | <= 75 ms |
| Unsigned POST, final terminator to durable reply, p95 | <= 250 ms | <= 250 ms |
| Hybrid-signed POST, same interval, p95 | <= 500 ms | <= 500 ms |
| Sustained mixed posting with readers, no growing queue | >= 10 POST/s | >= 10 POST/s |
| Checkpoint-assisted reopen, with <= 128 suffix events | <= 15 s | <= 120 s |
| Full journal reopen | <= 30 s | <= 300 s |

The intended shape matters as much as those initial numbers: **ordinary request costs should not rise proportionally to retained history; recovery may scale with the state it must reconstruct.**

The POST goals require work on the publication/storage term, not just the arena. If a qualified storage profile cannot meet them, publish its weaker measured latency tier rather than weakening durable acceptance or calling tmpfs numbers deployment performance.

N is also insufficient by itself. Report total retained octets, signed/unsigned mix, groups per article, concurrent pins, and suffix length. A 100,000-article store of tiny messages and one holding gigabytes of article bodies are different workloads.

### Order of attack

**First, remove whole-history work from identity prepare and signed-record lookup.** The signed mission repair correctly recognizes composites, but its record explicitly charges each lookup an N-long walk plus composite decodes. That is a correctness fix with a clear next optimization boundary.

**Second, make loaded connection opening cheap and shorten reader-side critical sections.** Preserve one semantic writer. Pin an immutable view under the mutex, then perform appropriate byte rendering outside it through the proved reference-effect boundary. Do not merely drop the lock around code that still relies on mutable owner state.

**In parallel, remove quadratic cold-open validation.** D-3 now makes the large checkpoint usable, but its small-payload, large-N point still takes about 33 seconds. That makes the remaining record-count-dependent work a useful separate target.

Then examine the durable publication program under the unchanged acceptance invariant. Batching or a cheaper publication sequence may be legitimate, but acknowledgment must still follow the required durable boundary.

**Rejected alternative:** sharding the owner first. It buys concurrency proof debt while leaving the expensive algorithms intact. Also reject raising timeouts as the performance plan: that changes how long a failure takes, not the supported operating envelope.

---

## 4. Convergence: keep the current cut; make the next one complete across the relevant boundaries

**Recommendation: proceed with qualification of `b6759850` without chained packs. Do not wait for a feature whose native gate has not completed.**

That is now largely a decision already taken: the full closure is recorded. Preserve that immutable candidate as a useful evidence point. D-3 belongs to a later repaired candidate or the next convergence; its evidence does not retroactively change the bytes of `b6759850`.

For deployment, distinguish "cut for qualification" from "safe to deploy under the intended profile." The known large-checkpoint failure affects the earlier candidate. The later reader repair is valuable precisely because it closes that demonstrated operational hole.

### Two of the queued qualification facts need reframing

**T-1 admission is intentional, not an off-by-one defect.** The maintenance reservation keeps **4,096 octets and one transaction** for a release record. The merge record explicitly changes a 128-transaction profile to admit 127 ordinary articles and reports native maintenance/reclaim success on a history-byte-constrained store.

Test history-byte exhaustion and transaction-count exhaustion separately. Reclaiming bodies lowers byte use; it does not necessarily lower the number of historical transactions. One reserved release record is a specific emergency capability—not a theorem that arbitrarily many outstanding obligations can all complete at every full state.

Likewise, an old over-H store remaining refused is not evidence that the preventive fix failed. It means a **repair/upgrade path** is still needed. Such a path should validate against a proposed larger profile while preserving the complete history; it must not truncate accepted records merely to satisfy the old profile.

The checkpoint test should use the size of the **captured state**, not assume that K/2 is the whole checkpoint. A suffix threshold and a full-prefix snapshot are different dimensions.

### Priority order for the second convergence

| Rank | Capability | Why it belongs here |
|---:|---|---|
| **1** | **D-3 decoder integration and producer/reader/reopen qualification** | Closes the demonstrated restart failure. The implementation now exists; finish the combined evidence. |
| **2** | **Signed-history Message-ID index and incremental identity prepare** | Prevents signed correspondence from becoming progressively more expensive with history. |
| **3** | **Chained packs joined to maintenance and recovery** | Removes the single-compaction-unit bottleneck and makes the growing-store maintenance story materially broader. |
| **4** | **Multi-listener/multi-peer relay** | Removes the scripted direction changes and restarts that currently help the mission complete. |
| **5** | **10 MiB end-to-end article delivery** | Valuable only when sender jobs, receive work, persistence, restart, and receipts all support it—not merely the ADU codec. |
| **6** | **Remote consumer scope** | High future value, but adds authorization, disclosure, view rebasing, and transport contracts beyond the current owner-local experiment. |

The current BP width theorem explicitly acknowledges that the sender job image remains 131,072 bytes while larger receive-side widths exist. That is why the 10 MiB feature cannot be described as "just finish the fragment test."

I would require ranks 1–2 in the next convergence, and make 3–4 its major capability goals. Develop 5–6 in parallel where interfaces permit, without holding every unrelated improvement hostage to them.

**Rejected alternative:** waiting for all six. That recreates the broad convergence trap. Conversely, merging chains merely because the proofs passed transfers its still-unobserved integration risk into the candidate.

For the scale gate, build and preserve a source-identified fixture once. A five-hour fixture build should not repeatedly precede every attempt to refute one compaction property.

---

## 5. Exit codes and `CONFLICT`: one outcome algebra, not one unique number per reason

**Recommendation: use one native-fn outcome classification and one ACL2-owned code map. Move operator `NO-STORE` to ordinary refusal, exit 1. Keep BP interrupted at 6 and not-connected at 7.**

`NO-STORE` already has a useful diagnostic word and corrective instruction. It does not need a special process exit code to distinguish it from every other known refusal. The expensive mistake is making one code mean "initialize a store" in one context and "retain the job and retry transport" in another. The decision sheet documents that collision.

The structure should be:

exit(f, x) = code(classify(f, x)).

The disjointness theorem concerns **different normalized outcome classes**, not different verb families. Accepted commands across all families should share 0; many distinct refusal reasons should intentionally share 1.

I would use the existing coarse classes:

```text
0  success / already satisfied
1  known refusal, with a stable reason
3  indeterminate local durable authority; fenced
4  fault
5  usage / unsupported invocation
6  transport interrupted; local durable work retained
7  no connection established
```

Preserve structured detail about **whose state is uncertain**. A client that lost a POST reply does not know whether the server accepted it; that does not mean the client should run local Store recovery. Either explicitly scope this table to the native executable or align the external clients through a broader outcome record with a scope field.

Also, the decision sheet itself records that `bp decode` still uses 3 for "the clock cannot decide the lifetime." Therefore "3 means recover first everywhere" is not currently true. A pure decode with insufficient clock evidence should receive a non-fence classification and a specific reason, not send operators toward unnecessary recovery.

### Add `CONFLICT` now

Yes: **append `:conflict` to the FNCT status enumeration, retain exit 1, and print `CONFLICT`.** It tells a caller to investigate an identity/content disagreement rather than retry a malformed frame or seek permission.

Preserving existing discriminants is necessary but not sufficient for compatibility. The packet correctly notes that an old client treats the new value as bad and exits 4. Upgrade clients first/together, or explicitly negotiate/fall back to the old refusal class; test that behavior. Do not call an appended enum universally backward compatible.

**Rejected alternatives:** allocating distinct exits to every diagnostic reason, or maintaining incompatible per-family tables. The former creates an ever-expanding shell ABI; the latter forces every caller to reproduce family-specific interpretation.

---

## 6. v2: make independently operated correspondence the organizing goal

**Recommendation: the two spines should be durable consumer applications and independently operated disconnected networking.**

Operator usability and peering setup are the supporting path through which those spines become real—not separate feature programs competing with them.

The signed mission is a major advance. The destination now binds the signed composite its own Store committed instead of failing to find it and submitting again. The record reports all seven signed mission steps passing, and the refused-channel custody case now refuses correctly.

But its successful driver still restarts participants when relay listeners change direction. The consumer experiment remains local to an owner control socket, and its outbox still lacks the pre-send durable attempt record discussed in the previous review: `drive_outbox` calls `hybrid-author` before starting the transaction that records the attempt. That defect is still present in the inspected source.

Fix that before expanding the consumer contract: a consumer death after remote acceptance must not leave an apparently never-attempted outbox item that later becomes definitively refused.

### The first external observation

I would choose **a second operator on a second physical machine**, using the installed production artifact and operator instructions, with separately generated identities and no shared private-key/configuration shortcuts.

Have that person establish peering, exchange signed R and Q, disconnect their node, restart it, and inspect retained work. Then run the consumer transaction on each side. The decisive observation is not "a packet arrived": it is that the other operator can distinguish accepted, pending transport, unresolved acceptance, and processed application work without the developers interpreting internal state for them.

The application path should independently verify the author and signed source against its own trust configuration. Native verification by the receiving fn node is useful, but is not the same observation as independent consumer verification.

Do not expose the current same-UID owner control socket remotely and call that remote consumer support. Start with a narrow authenticated consumer profile, then add multi-group queries and visibility-version rebasing deliberately.

The existing 45-step operator walk is excellent regression material, but its record explicitly describes a script's observations. It is not yet evidence that another human can operate the system without assistance.

### Where ION and LTP fit

Keep ION as the next independent BPA interoperability target and retain the selected LTP-after-DTN trajectory. That tests a different implementation boundary from dtn7 and should follow a stable persistent relay/application loop, rather than become another substitute for operating that loop.

**Rejected alternative:** making remote consumers, a new transport, a new UI, and broad stranger onboarding four simultaneous release spines. It maximizes surface area before any one external participant can use the whole system.

---

## 7. Assurance: distinguish incomplete work from unsound conclusions

Most of the listed items are **debt, not missteps**.

**Model-only arena theorems:** legitimate preparatory work when classified as such. The arena record clearly says no host caller exists and claims no measured retained-memory improvement. Do not remove useful infrastructure merely to reduce a model-only count. Do not count it as a running-system capability either.

**Books crossing ten seconds only under load:** investigate and compare matched conditions. The BP record shows the same `bp-node-progress` source at about 11.2 seconds under concurrent load and 4.8 seconds alone. That does not justify rewriting its theorem or silently raising its baseline. It is chiefly scheduling/measurement evidence until a matched regression is demonstrated.

**Delegated decisions:** not an assurance defect category. Judge their semantic and operational consequences. The preventive admission repair, historical replay policy, and named maintenance reserve are substantive improvements; their existence should not generate another approval ritual.

**Changing `fn-bpn-limits-compose`:** correct to stop asserting something false. "Uncited" is not the justification; the changed domain and explicit replacement scope are. The new theorem is a collection of codec-width relations, not a proof that the entire sender-to-receiver path accepts every profile-admitted ADU. Keep that limitation visible until the sender job boundary and the rest of the path compose.

**Fragment/job relation proved only at cold start:** acceptable debt while hot execution still checks the premises it needs. It becomes a misstep if the optimization removes those checks and relies on preservation that has not been established. The invariant must survive reception, family replacement, forwarding, deletion, failed publication, rotation, and restart—not just initialization.

I would also prioritize the explicit guard-verification gaps on called code. The signed-binding record says the relevant BP books are not guard-verified; the reclamation record says the same for `store-reclaim-pack`. Those are concrete execution-boundary obligations, more informative than a total count of model-only theorems.

### A new actual misstep: the rollback checker proves the wrong abstraction

This one deserves a focused correction.

`fnn-rollback-history` constructs an unlocked list of **transaction sequence numbers and file sizes**. `fn-native-operator-snapshot-loss` then compares those lists as prefixes and renders the result as a statement about whether one snapshot is an earlier history and how many later transactions restoration loses. The host and logical source both confirm that projection.

But consider:

```text
snapshot: sequence 0, valid article A, encoded length 4096
current:  sequence 0, valid article B, encoded length 4096
          sequence 1, another transaction
```

The descriptors pass the prefix test. The report says restoration loses one later transaction. In fact, it also replaces B with A. **No hash collision, malformed record, or exotic crash behavior is needed.**

This is a source-level abstraction error; I have not run a native reproduction. The theorem about descriptor prefixes can be entirely correct while the operator-facing history claim is false.

Repair it by observing coherent, authoritative logical histories—including selected packs and suffixes—and comparing exact canonical events or appropriate history commitments with their stated cryptographic assumptions. Bind the observations to a stable view while comparing them. A fast sequence/size check may be retained as an initial rejection filter or an explicitly approximate count, but not as proof of history ancestry.

This is closely related to the earlier restore-witness issue: **matching counters, lengths, or high-water marks does not establish identical history.**

### Another boundary worth keeping visible

D-3 properly labels some impractically large hypothesis-removal cases as failed proof attempts rather than executable counterexamples. That honesty is good. A `must-fail` on the u64-size hypothesis is not "teeth" demonstrating necessity when the witness would require 2^64 octets. Record that as an unprovided necessity witness, or use a separately justified reduced-width model; do not count proof-search refusal as semantic evidence.

### The one rule I would add to AGENTS.md

> **A producer's admitted domain is a lifecycle contract: any change to a bound, representation, or summary must show that downstream consumers and recovery preserve its meaning within the declared execution-resource profile. Passing the producer's codec or publication test alone is not completion.**

That single rule addresses the checkpoint writer/reader mismatch, the sender-job/ADU mismatch, hidden per-arrival work, and summaries that discard information their consumers need. It adds a concrete completion criterion, not another permission gate.

---

## What I would tell the deputy to do next

**Finish qualifying D-3, then run the representation wave around one payload-owning native lifecycle rather than a global predicate edit. Pair the signed-history index with removal of whole-history identity preparation. Finish chained-pack maintenance and persistent multi-peer relaying. Repair the consumer attempt journal before widening its remote scope.**

For the next external test, put the installed system in another operator's hands on another machine. Let their actual failed or confusing actions determine the next small changes.

And keep the strongest lesson of this wave: **a fast primitive, a true theorem, and a successful scripted trace are each useful—but the valuable result is their composition into a node that can keep accepting, retaining, serving, forwarding, maintaining, and reopening the same data without changing what it promised.**
