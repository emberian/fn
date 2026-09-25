# fn: direction, decisions, and the next complete workflows

Review date: 2026-09-24. Reviewer: gpt-6 (forwarded by ember ~23:00 UTC).
The reviewer's chat assessment and the source ledger are in
`planning/review-2026-09-24-gpt6-direction-summary.md` (forwarded 2026-09-25).

## Review boundary

This review started at `70eda24b691d455c4cbf54229ccdf0c0c7b93752` and incorporates the subsequent decision and proof-cost changes through `da67220d3f61493613f0454a23c6db16f0e3b1d3`. The separately qualified and deployed image is `18c913213863dfd99e9ac763cccd3b003df12dbb`. These are different evidence coordinates, not interchangeable labels.

This is a static examination of selected source paths, the attached decision scoreboard, and committed qualification records. No new ACL2 certification, native execution, power-fault campaign, or deployment was performed by this reviewer. Recommendations below are proposed implementation contracts and tests, not claims that those tests have passed. D23–D26 are already recorded as ember's decisions in commit `0e4b318e`; they are not proposals invented by this review.

## Assessment

**fn remains on track, and its case is materially stronger than at the previous BP contract review.** There is now a qualified running native service, useful consumers, measured execution refinements, a direct native request/receipt exchange across an interrupted transfer, and a preservation argument for actual pack reclamation. The remaining risk is not the ambition of the design. It is allowing the meanings of identity, authority, and durable completion to be selected accidentally by a convenient representation or a test fixture.

Keep the ambitious target: independently useful nodes, exact-source authorship, explicit obligations, offline operation, and executable ACL2 semantics. Do not make another universal audit the prerequisite for all useful work. Complete the next user-visible workflows while closing the specific assurance dependencies those workflows consume.

### Evidence that changes the assessment

The `18c91321` qualification reports 188 matrix rows reached with no disagreements, 50 successful cut observations across the two tested entries, a 40/40 wire probe, and 90 production SIGKILLs with no observed torn article, lost acknowledged article, or reused local number. Its separate native modules include signed POST and BP restart cases. The deployment is LAN-only, has no configured peers, and does not deploy the DTN profile. Its platform durability claim remains limited to process death.

The new M4 application experiment distinguishes a direct control that reaches receipt acceptance and releases the forwarding pin from a real-dtn7 relay experiment that reaches custody but refuses application admission. That is useful discrimination, not a successful relayed application workflow. The four-node harness's expected-refusal assertions must not be counted as the M4 success criterion.

`tools/fn_verify.py` now provides a separately written carrier/preimage parser and verification path using an independently supplied keyring. Its primary Ed25519 path uses pyca and its primary ML-DSA path uses dilithium-py, rather than the node's corresponding implementations. This is a valuable independent implementation boundary; its existence is not a proof that the format or cryptography is correct, and this review did not run it.

The carried prepare/advance work reports CPU per POST at N=120 falling from 5.5–5.7 ms to 3.5–3.6 ms over three rounds, with correspondence theorems over the functions called by the host. That is a scoped measured improvement, not a claim about latency or memory at 4096 transactions.

The compaction lane now states reconstruction preservation over the actual host-called functions and tests served reads and next-number behavior after reclamation cuts. Its pack still retains the entire exact canonical history; the operation reclaims transaction-file overhead, not article bodies or the logical history bound.

## Decisions: retain the direction, make the consequences explicit

| Decision | Assessment | Implementation condition |
| --- | --- | --- |
| D23: permitted relay origins, final receiver author enrollment, opaque carriage | Right architectural direction | Carrying permission, author verification, publication authorization, and receipt-release authority must remain separate checks. |
| D24: carry the peer invariant rather than memoize the whole-node check | Agree | Prove establishment, preservation and full result/effect correspondence on the actual executable path. Do not substitute unchecked raw calls. |
| D25: duplicate/conflict on poster bytes | Agree with the semantic target | Generated Date/Message-ID and the injection recipe require explicit treatment; deleting four named fields is not generally an inverse of injection. |
| D26: two-job scoped ratchet | Agree | Keep wider qualification measurements separate; per-run job count does not establish an otherwise idle host. |
| P5: shared-owner failure may stop the service | Agree | Contain demonstrably connection-local faults; fence uncertain shared authority. State the fault domain in the property. |
| D02: signed POST on the normal interface | Agree | Preserve present-invalid versus unsigned distinction and acceptance-time verdict provenance. |
| Kind-8 retry cap and duplicate ACK | Accept as a conservative operational default | Same carrier identity for ambiguous retry; no application obligation release on transport evidence; exhaustion remains visible unresolved work. |
| Special-purpose group names allowed | Accept only as an explicit local-agreement profile | Not ordinary globally compatible names and never implicit control authority. |
| Development-to-scale upgrade | Already done; reasonable for the experiment | Treat 4096 as an admission bound, not measured capacity or unlimited lifetime. Old-profile rollback has a used-count precondition. |

## D23: carriage is not authorship, and authorship is not release authority

The source-level cause of the relay failure is concrete. `fn-bpaj-session-principal` identifies a configured neighbor from the channel and checks its announced transport EID. `fn-bpah-request-trustedp` and `fn-bpah-receipt-trustedp` then require the bundle source to be that same peer EID via `fn-bpaj-current-peer-eidp`. A relayed bundle has a different original source, so neither enrolling the relay nor enrolling the source satisfies both checks.

D23 correctly stops treating a store-and-forward network as a set of direct source/receiver pairs. Implement it as separate predicates, with typed identities:

```
neighbor-admitted(channel, peer, boundary)
origin-carriage-permitted(peer, bundle-source, scope)
author-publication-authorized(author-principal, keyset, groups, policy)
receipt-authorizes-release(issuer, work, subject, terms, evidence)
```

These are not synonyms and are not a chain of automatic implications. In particular, a BP source EID, an article-signing principal, and an immediate neighbor's configured name are different identity domains. The origin allowlist should say which one it contains.

The finite allowlist is an authority delegation. In the network-trust profile, it says that a neighbor is permitted to supply items claiming particular origins within a stated boundary. It is not an end-to-end cryptographic proof of those origins. Preserve the admitted peer, origin claim, authorization context and verdict provenance so a later consumer can distinguish these facts.

### Opaque carriage

An intermediate node may carry a signed object without locally enrolling its author. It must not strip the carrier and relabel it unsigned, nor manufacture a receiver-verification verdict. At least the internal result should distinguish a missing local author binding, an unsupported profile, and a checked signature failure. Whether the UI renders them under one unverified badge is a presentation choice; they must not collapse in authorization logic.

Unknown-author carriage still consumes resources. Permit it only under an explicit peer/group/byte policy, with a defined custody obligation. Otherwise removing the enrollment barrier becomes an unbounded storage admission change rather than merely an interoperability improvement.

The receiver's enrollment decision and the historical acceptance verdict are also distinct. Revoking permission for future local publication should not rewrite what the node previously verified at acceptance. Adding an independent verifier makes this distinction more important: a current keyring check is not automatically the same question as an acceptance-time verdict.

### The receipt condition that D23 should spell out

The current receipt handoff checks source/issuer consistency but relies on the peer trust path; it does not gain end-to-end receipt authentication merely because the article has an author signature.

A neighbor allowed to carry Alice's article should not thereby be entitled to assert Bob's retention receipt and release Alice's forwarding obligation. Use a distinct release-issuer policy. For the immediate controlled M4 experiment, an explicitly delegated, finite, trusted-relay receipt profile is a workable intermediate point. Describe its transitive trust honestly and include an unauthorized-issuer negative case.

Before claiming safe release through an untrusted intermediary, bind and verify the receipt itself against the authorized issuer and exact work, content subject, requester and terms. This need not require completing a general PKI, portable succession protocol, private groups or all of BPSec in the next packet. It does require not presenting a data-carriage allowlist as a receipt-security mechanism.

### M4's next useful integration target

The next gate should begin with an actual native workflow submission, not with a lab synthesizing the request ADU through an ACL2 bridge. The M4 record explicitly identifies that missing normal native entry, the remaining outbound neighbor/application-peer confusion, and a recovery-outcome replay defect in the ION-named workflow journal.

Close the path:

```
native work/attempt publication
  -> native request ADU
  -> FNBS carrier
  -> real BPA relay across contact loss
  -> final receiver's own admission and Store commit
  -> receipt carried back
  -> exact forwarding obligation released
```

Keep a second control obligation whose pin is unchanged. Add refusal of an unauthorized origin/issuer, and require that ambiguous publication preserves unresolved work. Keep ION as a transport adapter to the generic workflow; do not make generic request submission semantically depend on ION merely because its attempt helper already exists.

## D25: poster-byte identity needs provenance, not broad normalization

The latest qualified image still reports the same re-post as a duplicate or conflict depending on the re-injection clock second. The Store's exact comparator is not the bug: it correctly compares the payload and group binding it was given. The served path must ask the right question before comparing a newly generated projection with an old one.

Separate three values:

- the exact submission/source supplied by the poster;
- the accepted local record, including generated injection metadata;
- a served or relayed projection of that record.

A repeat operation with the same stable Message-ID and same source should resolve to the earlier accepted result. Different source under the same identity is a conflict. These decisions must not depend on the new attempt's clock reading.

### A concrete limit of the four-field rule

D25 names Path, Xref, Injection-Date and Injection-Info as projected-out fields. But the current injector can also generate **Date** and **Message-ID**.

Take an otherwise valid proto-article with a supplied Message-ID and no Date. Inject it at two different times. Removing the four named fields still leaves two different generated Date fields. Therefore that projection alone cannot generally mean "what the poster sent." Removing every Date field would be worse: an authored Date is part of the exact source, and changing it must not be silently ignored.

There is already a useful restricted inverse: `fn-inj-reinjectionp` recognizes the injector's exact prefix and optional generated Date/Message-ID, then compares the remaining source verbatim. Its source comment says the operator path uses it. Reuse and strengthen that correspondence for the served POST boundary rather than inventing an unrelated generic header normalizer.

For newly accepted records, preserve enough source or injection provenance to recover the comparison subject exactly. For older records, reconstruct only under the known matching injection profile; do not silently widen equivalence when the recipe or injecting identity differs. Keep the low-level Store comparator exact, and make the higher-level retry resolver return the existing accepted record once source equivalence is established.

### Protocol detail to correct in the same packet

RFC 5537 §3.5 item 11 distinguishes a supplied Injection-Date and the case where a proto-article already supplies both Date and Message-ID. The current source rejects a supplied Injection-Date and unconditionally adds a new one to accepted injections. In particular, adding one when both Date and Message-ID were already supplied does not implement that RFC case. Resolve the accepted-input policy separately from the mandatory transformation rules for inputs that are accepted.

The regression matrix can be small: same source with Date present or absent; one changed authored byte under the same Message-ID; restart after lost reply; a different injecting-context version; and a deliberate second identical post with a new Message-ID. In clients, create and persist the Message-ID before the uncertain network operation. Otherwise identical text alone cannot distinguish a retry from a deliberate new article.

## M5: packing, state checkpointing, and deletion are different promises

The exact-history preservation result is a strong foundation. Do not discard or devalue it because it is not yet general garbage collection. But do not let its name obscure its operating limit either. The current pack holds at most 4096 events and 4 MiB, preserves their exact history, and has no production operator pack/reclaim entry yet. Temporary-space and protected dependency-closure work remain open.

Distinguish:

1. **Physical packing:** fewer filesystem objects, same history and semantic contents.
2. **State/history compaction:** less replay/history state, with a proof that all future permitted decisions have the same answers.
3. **Content reclamation:** remove object bytes only when every applicable retention obligation and active reference permits it.

The deployed scale upgrade increases an admission limit; it is not any of these transformations. Its rollback note is conditional on no more than 128 transactions having been used when reverting to the development frame. Retaining the old executable is not a general rollback guarantee for every later store state.

The next M5 packet should expose the existing proved pack/reclaim protocol through a production operator path, preserve the exclusive-owner boundary, and check temporary space before destructive work. Then explicitly state which limit that operation relieves.

After that, choose a versioned logical-history strategy rather than silently deleting "old metadata." Unresolved handoffs, submission outcomes, identity/key policy evidence, local number frontiers, cursor pins, and old-input/anti-resurrection summaries have different lifetimes. The future checkpoint must preserve the authority required for future decisions, not just enough bytes to make current reads look right.

The reported invisible missing-tail case is outside the valid reclaim program's effect: the program never deletes the uncovered newest record. It is not evidence that reclaim violates its theorem. It does mean the namespace checker alone is not a detector for every possible loss or rollback. A committed-history boundary may detect some local suffix losses; an allocation frontier is not automatically that boundary because allocations can be burned. Detecting replacement by a wholly old valid snapshot requires a separately trusted freshness reference.

Finally, indefinite retention does not promise acceptance of unbounded distinct content on finite storage. M5 should promise bounded execution and metadata behavior under a stated workload and retention/release policy, with explicit refusal when actual promises cannot be funded. That is compatible with D03 and more useful than pretending compaction makes finite storage unlimited.

## D24 and D26: keep both optimizations attached to the right metric

Carrying the invariant is the right answer to repeated whole-node recognition. The required correspondence is over the complete state/result/effect boundary used by the caller, not just equality of a selected state field. Establish the premise at open and preserve it across the paths that can change the relevant object. Validate new external data; do not revalidate all previously admitted data on each command. A guard-verified carried implementation is not the same operation as bypassing guards in raw Lisp.

Memoization is not inherently mathematically suspect, but it answers a different engineering question. Do not add it merely to hide a missing maintained invariant.

D26 is implemented: scoped results use `jobs_effective <= 2`, wider runs remain recorded, and a newer wide measurement does not hide the scoped band. Do not mistake a two-job run for a controlled machine if other lanes are saturating memory or CPU. Preserve host/toolchain/content/load context. The primary productivity outcome remains edit-to-certified-verdict for representative changes, not merely the count of books below ten seconds.

## The standing defaults

### P5 and fault containment

Restate P5 as containment of connection-local failures, with explicit fail-stop/fencing of uncertain shared authority. The recent EPIPE fix is the right kind of refinement. Do not keep mutating shared state merely to satisfy an overbroad "a fault costs one connection" sentence. Conversely, do not classify every socket failure as an owner-wide fault. The property should name the fault domain.

### Retry budget and duplicate ACK

The three-retry default can remain a conservative, visible operating policy. It should bound automatic effort, not erase or pretend to discharge the underlying work. Persist enough retry identity/history that repeated process restarts cannot accidentally turn a finite automatic budget into infinite busy retry. Keep ambiguous retransmission tied to the same carrier identity. Exhaustion should present held/stranded work and the condition for resuming or administratively resolving it.

Acknowledging a fully received duplicate can remain the default. TCPCL also defines Completed refusal code 1 for an already held complete bundle; support its meaning on the sender without forcing the receiver to switch behavior merely for symmetry. Neither transport indication is the application's retention receipt. Preserve all refusal reasons rather than collapsing them into an undifferentiated retry result.

### Group names

The selected permission for special-purpose names can be described as an explicit local agreement. RFC 5536 §3.1.4 permits their special use or local agreement, but not treating them as ordinary unrestricted newsgroup names. Its cases include first/only `to` or `control`, any component `all` or `ctl`, and exactly `junk`. They are not merely five exact strings. Do not infer group-creation, moderation, deletion, forwarding or wildcard authority from those strings.

## The next development cycle

Use parallel work around complete outcomes, with the shared qualification snapshot pinned independently from active development:

**Normal posting and retry:** D25 implemented at the actual served boundary; signed and unsigned POST; lost reply then retry at a different time; exact old record and local number retained; changed source refused distinctly.

**Relayed application workflow:** D23 typed carriage and issuer policies, native request authoring, real BPA contact loss/recovery, receiver's own acceptance, receipt return and exact pin release. Preserve direct and unauthorized-origin/issuer controls.

**Production maintenance:** operator access to the existing pack/reclaim protocol, temporary-space admission and scoped crash evidence, accurate headroom and a statement of which bound is or is not relieved.

**Human and agent use:** qualify the web reader/composer and consumer resume paths against one current server image; finish the current-image and actual-user seam rather than postponing human use for a general network security system.

Each should report one current semantic capability with its source, proof, native qualification and deployment coordinates. Do not require the rest of the project to become uniformly green before a bounded capability can advance, and do not count an expected-refusal harness as the positive milestone it diagnoses.

### A small evidence-maintenance repair

The scoreboard and `now.md` accumulate mutually superseded observations in current-status cells. Keep immutable historical records. Generate or maintain a short current view with: property, source subject, certificate identity, tested image, environment/profile, latest result, remaining obstruction, superseded evidence, and next positive gate. A fixed small view is enough.

## Bottom line

The project does not need a smaller vision. It needs stable meanings at the boundaries and completion pressure on a few end-to-end workflows. The foundation to protect: the same source remains the same source; carrying a claim does not grant authority over it; an acknowledgment means exactly the commitment it names; and reclaiming representation does not erase obligations.
