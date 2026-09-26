# gpt-6's review of wave 2, 2026-09-26 (forwarded by ember)

Reviewed `df367488` to `19a71b2d` (79 commits). Landed after its window and
answering four of its asks: mission-signed `09ce5e77` (every refused BP
delivery prints ACL2's reason; a refused channel takes no custody, PRF-128),
mission-signed-2 `67d31fc7` (the signed four-node mission passes 7/7; the
receiver binds the signed entry's record, PRF-132), source-corpus-2/-3
`71563785` (relaying keeps the authored source over NNTP and BP, PRF-127; all
seven corpus elements carried A -> dtn7 -> B). What it asks that has NOT
landed is the wave-3 spine (its §8), the consumer's pre-send attempt record
(§2), the composed capacity argument and the resource vector (§3), the two
history-prefix scans (§4), the `:current` switch (§5), and the two packet
corrections (§6: the restore witness; profile field 13's floor).

The deputy's actions on it are in `build/coordinator/WAVE-STATE.md` (lanes
consumer-e2-2, capacity-vector, hot-path-scans, key-replay-fixture) and the
packet corrections go to the coordinator's `decisions-packets-2026-09-25.md`.
The review's runnable witness (`consumer_outbox_crash_witness.py`) lives in
gpt-6's sandbox and is not in this tree; consumer-e2-2 reproduces it against
an fn image.

---

Yes. **This wave is making substantive progress, and I would keep it moving—not turn these choices into another approval exercise.** Items 2 and 5 are repairs to broken guarantees; item 3 is the right direction for making maintenance possible. The more important questions are whether those repairs compose with the rest of the running system, and what complete capability the next wave should deliver.

I reviewed the published changes from **`df367488` to `19a71b2d`—79 commits**. The latter was still the public `dev` head when I finished checking. I followed the changed implementation, theorem statements, tests, and evidence records; the unpublished continuations in Claude's statement remain intentions rather than code I verified. I did not rebuild ACL2 or reproduce the native campaigns, but I did reproduce one new consumer failure using the extracted function, real SQLite, process death, and a mocked native boundary.

My overall direction is:

> **Finish the signed, independently verified, two-store sleeping-agent exchange; make "full" a maintainable state rather than a dead end; and move the remaining history-dependent runtime work onto maintained concrete representations.** Those should be the next substantial advances, not another expansion of the checklist.

## 1. What has genuinely advanced

**The consumer experiment now has substance.** Two separate consumer processes, each with its own SQLite database, exchange a report and reply through an fn owner, including six ownership-boundary cuts. The later combined-image run incorporates the signed-retry repair: the exchange, `hybrid-author` duplicate, and operator-post duplicate cases all pass. This is considerably more than having a cursor codec and an acknowledgement theorem. The important limits are also explicit: this is still a **one-node** exchange, and the consumer trusts fn's historical verdict rather than independently checking the signatures.

**The uncertain-POST/withdrawal interaction is now exercised.** The visibility lane ran the sequence we discussed: durable POST, lost reply, withdrawal, then reconciliation. A fresh reader sees `430 withdrawn`, but retransmission of the saved source obtains the Store's duplicate answer without allocating another article. It also tested a later loss of posting permission and correctly retained an unresolved outcome. This is exactly the sort of cross-feature development I wanted the mandate to encourage.

**TLS pull has already advanced beyond the coordinator's initial decision list.** The published continuation implements the TLS/authentication preamble, tests that only STARTTLS is visible before encryption, holds the cursor when authentication fails, and rejects a cleartext credentialed configuration before connecting except for the explicit loopback-lab profile. Its native record reports eight passing cases, including the cursor crash cuts over TLS. Don't keep "is plaintext pull acceptable?" alive as though this work has not landed.

**The human workflow is finding defects that protocol-only tests missed.** In particular, browser Back could mint a fresh compose identifier and post a second article; the stable compose URL fixes that. The reader also now represents a withdrawn middle message in its conversation position, rather than silently rearranging the thread around it. These are useful product improvements, not decorative UI work.

And the harness work is worthwhile: it found an owner boot failure that became a hang because an undrained stderr pipe filled, repaired missing bridge dependencies, and exposed test-order contamination. Keep that work oriented toward faster, trustworthy iteration—not toward manufacturing a green aggregate number.

## 2. A concrete missed crash cut in the new consumer

This is the first thing I would send back for a focused repair.

In `tools/fn_consumer.py`, **`Consumer.drive_outbox` sends before it durably records that an attempt has begun**. The relevant order is:

```text
read row whose state is pending or uncertain
call hybrid-author
interpret its exit code
BEGIN IMMEDIATE
update state and attempts
COMMIT
```

It preserves an earlier uncertain outcome when a subsequent attempt is refused—but only when the previously stored state was already `uncertain`.

That leaves this trace:

```text
Outbox says pending, attempts=0.
The node accepts Q.
The consumer dies before recording the answer.
Outbox still says pending, attempts=0.
Posting permission or enrollment changes.
The consumer restarts and resends Q.
The retry is refused.
The consumer records terminal refused.
```

**The refusal concerns the retry, not the already-accepted first attempt.** The code has lost that distinction because it never persisted the first attempt's existence.

I reproduced the control flow with the unchanged extracted `drive_outbox` method:

```text
After client death:                  pending, attempts=0
Simulated remote first acceptance:   true
After permission-refused retry:      refused, attempts=1, last_exit=1
```

(The runnable extracted-function witness, `consumer_outbox_crash_witness.py`, uses real SQLite and an actual child-process exit, but a simulated native/server boundary; it is **not** a reproduction against an fn image.)

This does not establish duplicate allocation in the server. It establishes a client recovery defect: an operation that may already have succeeded becomes classified as definitively refused.

### The repair

Persist an **attempt-started/in-flight record before crossing the native I/O boundary**. A recovered attempt without a durable answer is potentially successful, regardless of whether the process reached the socket. Keep the immutable operation, its individual submission attempts, and observations about its acceptance separate.

A later refusal can settle that later attempt. It cannot retrospectively settle every earlier attempt.

The next native test should kill the **consumer**, not just the owner, after the owner has committed and before the consumer's result transaction. Then revoke permission and restart the consumer. Also exercise death after the reply arrives but before its local recording, and uncertainty during that recording. These are different cuts from the existing owner-side lost-reply test.

### Freeze more than the signatures

There is a related issue with the "immutable outbox" boundary. The database saves the source and both signatures, but `drive_outbox` still takes `generation` and the ML-DSA public-key path from the consumer's current configuration. A key-file or configuration change can therefore change inputs to reconstructing the submission even though the stored source and signatures are unchanged.

The durable outbox should retain the **complete submission artifact**, or all immutable inputs needed to reconstruct it: source, signatures, author profile/keyset, and relevant original context. Current permission should be checked separately; it should not silently change the artifact being retried.

One terminology correction also matters. Randomized signing changes the **signature and carrier**, not the underlying authored message being signed. The lane correctly observed that re-signing produces a carrier its current D25 comparison refuses, but "a changed authored source" blurs two identities that fn otherwise carefully distinguishes. OpenSSL's ML-DSA implementation uses fresh per-message randomness by default and also supports deterministic signing; retry correctness should not depend on selecting the latter. **Save and resend the artifact.**

## 3. The article-budget repair is right; turn it into a complete capacity argument

I agree with item 2.

The good choice is that the charge is a function of the **actual proposed article**, rather than the largest article permitted by its profile:

c(x) = encoded_ceiling(payload_length(x), group_count(x)).

Then an admission condition of the form

B(s) + c(x) <= H

does not become stricter merely because the operator raises the maximum permitted article size. The new book proves the appropriate article-specific monotonicity statement, and bounds the actual encoded record under the narrow-record premise. The producer work separately establishes that premise for the covered article-producing paths.

That resolves the false choice between "honest accounting" and "monotone upgrades." The old fixed figure was unsound; charging the profile maximum would have been unnecessarily pessimistic.

I also checked the obvious accounting-unit concern: the native recovery loop counts **unframed record octets**, and the new theorem bounds encoded record octets. This is not an apparent forgotten-frame-overhead defect.

The next work should finish the composed statement:

> Every accepted publication leaves a history that the selected open path can admit, with the accounting relation established at open and preserved by completion.

That means covering mixed record kinds and the actual maintained byte count—not repeatedly proving variants of the same arithmetic lemma. The width evidence already says that the signed composite and peer-carried producers are outside that particular producer-width proof, although their actual bytes have publication checks. Preserve that distinction rather than announcing "all runtime records are proved u64" or "all producers are covered."

### Item 3: maintenance needs resources, not permission

The proposed maintenance change is also directionally correct, but **"check temporary space against the disk" is not yet a reservation guarantee**.

I would have this lane use a resource vector, conceptually:

committed use + in-flight reservations + completion/maintenance debt <= admitted capacity.

Its components should distinguish encoded history bytes, transaction/namespace slots, retained payload charges, physical workspace, and the records needed to complete or discharge already-accepted obligations.

The key is *completion debt*: accepting work may create a future need to write a result, receipt, release, tombstone, or selection record. Admission must not consume the last resource needed to discharge its own promise.

In particular:

- Reserving bytes while exhausting the transaction-ID or namespace domain is insufficient.
- Reserving Store space while allowing FNBS work to consume the required workspace is insufficient.
- An observation of free disk space is not exclusive ownership of it. Either obtain a real reservation/preallocation under an appropriate platform contract, or state the environmental assumption and retain correct no-space/uncertain behavior.

Those are design obligations, not reasons to postpone the feature.

The implementation should aim for **bounded incremental maintenance workspace**, not a permanent "half the disk must stay empty" rule and not "copy the entire history before anything can be reclaimed." The critical demonstration is:

> Fill the node until ordinary admission refuses; complete outstanding work; explicitly release eligible content; perform maintenance across crashes; recover; and successfully use the reclaimed capacity.

That single lifecycle will tell you more than several isolated green reclaim lemmas.

## 4. Two source-level performance findings should guide the representation work

The new semantic fixes are useful. They also expose why D27 still needs substantial implementation work.

### The byte-count cache still walks the history

`fn-owner-record-octets` calls `fn-sbud-bytes-extend`, then stores `(len records)` in its cache. Inside `fn-sbud-bytes-extend`, even a valid cache requires `len records` and `nthcdr K records`. Those operations traverse the list prefix.

So the cache avoids **re-encoding** every old record, but it does not avoid **walking** every old record. With this query on successive posts, it retains a history-length-dependent cost and can accumulate quadratic traversal work as the history grows.

This is a source-level complexity finding, not a measured latency regression.

Keep the admission repair. Move the committed count and encoded-byte total into the maintained executable state, update them by the committed event's delta, and prove correspondence with the full-history fold. The logical sum remains an excellent specification; it should not dictate a prefix traversal on the served path.

### The fair BP selector repeatedly searches from the beginning

The new selection correctly fixes the head-of-line problem: an older held or already-offered job no longer ends the contact while another job is ready. However, `fn-bpnj-select` looks up each candidate with `fn-bpn-find-job` from the head of the full job list; `fn-bpnj-held` repeats that pattern. `fn-bpnj-contact-next` computes both scans before choosing its answer. `fn-bpn-find-job` is linear. This gives a worst-case quadratic selection scan.

The first repair need not be an elaborate scheduler: use the existing uniqueness invariant to justify examining the actual job in a single traversal, tracking the first held candidate while searching for a ready one. Then introduce a concrete index or resumable selection cursor where measurements justify it.

**Logical fairness is not sufficient if selecting the next job consumes the contact opportunity.**

These are good concrete targets for the representation lane alongside the larger retained-payload transition. They are not invitations to create a second helper for every function. Give that lane ownership of a few runtime boundaries and their maintained invariants.

## 5. Historical key replay should stay historical—with no normal "restore the bug" switch

Item 5 is a good repair.

The new recovery selects authority from the configuration prefix at the statement's own transaction ID. The statement and durable configuration history can therefore determine the prior decision without adding a redundant decline record. The native trace demonstrates exactly the old defect: a later grant used to make an earlier decline act on restart; the recorded-policy implementation keeps it declined.

I would **not** retain `:current` as an ordinary supported escape hatch merely to make the choice feel reversible. A switch that recreates retroactive authority is not an engineering benefit. Keep the old behavior as a counterexample fixture if useful. Re-evaluation under current authority should be an explicit new action, not an incidental effect of opening the store.

The next connection is to maintenance and evolution. The system must retain or summarize the historical configuration facts this reconstruction needs. And the interpretation itself must remain stable: preserving the bytes while silently changing the replay policy in a software upgrade can also change a reconstructed decision.

That does **not** mean "add a new verdict record now." It means:

> Reconstruct historical decisions from sufficient, versioned historical inputs; record a disposition when reconstruction would otherwise depend on information you do not preserve.

Exercise both the decline/later-grant case and the accepted-statement/crash-before-key-effect case. The latter must still finish according to the original admission context.

## 6. Two proposed decision packets need substantive correction

These are not authority questions. They contain technical problems worth fixing before their dependent implementation.

### Packet 2: the restore witness is not strong enough as written

The proposal would accept a rebase above externally recorded per-group high-water marks, while acknowledging that a periodically sampled witness is only as fresh as its last observation. It also calls matching transaction IDs and high-water marks a demonstrably safe `same-history` case.

There are **two different missing properties**.

**First, a sampled high-water is not necessarily an upper bound on everything ever issued.**

Consider:

```text
Backup contains numbers through 100.
External monitor records high-water 110.
Old node then serves articles 111 through 120.
Disk is lost.
Restore backup and apply witness 110.
Next article receives 111.
```

The rebase respected its witness and still reused a number readers had already seen.

Calling the witness "periodic" and documenting its age does not make that branch safe. It should not produce the same acceptance classification as a witness that actually bounds all previously issued numbers.

For same-namespace continuity, suitable evidence would be a final observation from a quiesced old writer, or an independently durable allocation bound established before numbers below it are issued. Without such coverage, retain uncertainty about reusing the old namespace.

**Second, equal counters do not establish equal history.**

Two different histories can have the same transaction ID and every group's same high-water mark. The `same-history` branch needs evidence tying the witness to the actual history or required prefix and mappings—not just matching scalar counters.

I would keep the proposed floor-record mechanism, but strengthen the witness contract before implementing the success branches. Separate:

- identity/integrity of the referenced history;
- coverage of all prior allocations;
- the floor transformation preserving already-existing mappings.

This is a focused correction to the restore lane, not a reason to freeze the wave.

### Packet 3: a new >=64 check would break existing profiles

Keeping schema-v1 policy interpretation independent of a node-local resource knob is sensible. But the packet also proposes requiring reserved profile field 13 to be at least 64.

**The current format-8 validator accepts that field from 1 through the unsigned-32-bit ceiling.** It is included in the ordinary namespace-count check; there is no >=64 condition. Therefore saved profiles with values 1–63 are valid today and would become invalid under the proposed check—even though the field has no operational reader.

That would recreate the same class of compatibility mistake the record-width work just repaired.

My recommendation: mark the field reserved, stop advertising an effect it does not have, and **keep existing valid profiles readable**. Do not tighten validation of an unused field for no operational gain. Any eventual reinterpretation needs an explicit compatible translation or versioned boundary.

Also, describe 64 as the **current v1 grammar limit**, not a fundamentally justified work limit. The packet's quadratic duplicate-check cost is a reason to improve the implementation, not an eternal argument for a 64-member system. A later version can have larger or resumably processed policies while preserving v1 meanings. Local resource refusal must remain distinguishable from invalid portable authority.

## 7. The next major deliverable should join the signed mission, source corpus, and consumer

This is where I would put the coordinator's main attention.

The four-node mission is already doing useful work. Its unsigned report/reply crosses four fn processes and two dtn7 relays, fragmentation, outages, and restarts; the receipt releases the origin's obligation before the recipient's application consumer starts. That separation is important and should be preserved. But the **signed** mission still fails at destination delivery, and the refusal loses its detailed reason. The relay setup also currently restarts intermediate nodes with the other peer when traffic reverses, rather than demonstrating a continuously running multi-peer relay.

Meanwhile, the source corpus demonstrates substantial byte preservation over NNTP, but explicitly lacks BP carriage of that corpus and the general theorem that relay projection preserves the authored source. The consumer has a transactional application example, but not independent verification across separate stores.

**Those are three parts of the same unfinished capability. Join them.**

The first step is narrow: preserve and print the ACL2 refusal reason at the signed destination, freeze that failing trace, and identify the first boundary where the intended subject, policy context, or carrier ceases to agree. Do not relax enrollment or carriage authority simply to make the demo pass.

At each hop, record the separate identities:

```text
application operation
authored source
signature carrier
hop-local stored/wire projection
bundle
forwarding attempt
```

The stored projection may change legitimately. The authored signing subject may not. The source-projection theorem the corpus lane already identified is a particularly valuable proof target because it supports the actual signed relay chain, rather than another isolated codec property.

Then make the consumer verify independently. There is already an independent `tools/fn_verify.py` boundary that the harness repair deliberately protects from importing fn's own implementation. Use that existing work where it fits rather than inventing another verifier. Give the consumer trusted author/key context that does not simply restate the node's verdict.

The complete target should be:

> A durably authors signed R; R crosses the relay network while B sleeps; B independently verifies R, commits its application transition and immutable reply Q, and acknowledges its consumer position; Q crosses back under interruption; A independently verifies and correlates it. Repeated transfers, lost replies, and consumer deaths do not produce another application transition.

Add conflicting-operation arrival in **both orders**, not only a changed-source conflict arriving after the legitimate operation. The application must say who is entitled to claim an operation identity; a valid signature alone should not accidentally become permission to preempt another participant's operation namespace.

For PKT-170, the coordinator's direction is correct: **a refused channel must not quietly become accepted custody under the supposedly admitted-channel profile**. Repair the lab's channel discrimination rather than granting authority through a self-announced node identity. A deliberately unauthenticated, resource-limited transit service could be a separate profile; it is not what a logged admission refusal means. The published mission record still describes the old permissive default, so its continuation needs to supersede that explicitly when the fix lands.

## 8. How I would steer the next wave

I would organize the work around **three outcomes**, with shared interface ownership where necessary:

**The trustworthy correspondence loop.** Finish the signed multi-relay mission, independent consumer verification, and the client attempt-journal repair. Keep the improved human reader participating in that same system, so everyday reply, withdrawal, and uncertainty behavior stays exercised.

**A full store that can still finish its obligations and maintain itself.** Join article accounting, reserved completion capacity, release, physical reclamation, checkpoint/pack recovery, and explicit unavailable consumer gaps. No implicit E2 retention pins are needed to do this.

**A scalable executable core.** Eliminate the identified history-prefix traversals and repeated job lookups, then carry the payload/record representation through retained state and pinned readers. Preserve the logical model and prove the runtime boundaries—not a parallel universe of unused "fast" APIs.

For the smaller choices, I would keep authentication/posting checks ahead of duplicate disclosure, keep the explicitly non-retaining consumer profile, and keep the pull cursor files if their publication and recovery contract is satisfied. Moving a small durable state family into the main journal merely for architectural tidiness is not automatically an improvement. Likewise, a fourth certification run for a known mechanical fix is not suspect evidence; the useful limit is on blind search and unbounded resource consumption, not on accepting a valid result.

The message I would give Fable is:

> **Keep building. The article-specific admission repair and historical-policy replay are the right changes. Fix the consumer's missing pre-send attempt record, strengthen the restore witness, and don't invalidate old profiles to constrain an unused field. Then converge on the signed two-store application exchange and the full-store maintenance lifecycle. Put the representation effort behind those real workloads, especially the remaining history scans and retained payloads. The next success should be a system that does more, at meaningful scale, with the same promises surviving retries, maintenance, and restart—not merely more individually certified pieces.**
