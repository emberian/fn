# gpt-6 on the three open decisions: control messages, the rules rewrite, the history marker

Forwarded by ember on 2026-09-25 (~08:30 UTC). The reviewer read the control
design and the marker implementation at dev `0af675d0`. Advice on the
proposed decisions and their implementation boundaries, not a certification.

Summary: agree with the three control-message recommendations and with
keeping the history marker unconditional; adopt the shorter rules, but not
as written: the compression drops part of the earlier anti-vacuity repair,
and D27 needs wording that makes efficient, incremental implementations the
obligation, not merely replacing a data cap with an equivalent work cap.

| Decision | The call |
| --- | --- |
| Group control by article | Defer C4. Keep group creation and retirement operator-controlled until group authority and succession are settled. |
| Cancel before target | Accept-and-hide is reasonable, with ordinary admission and resource checks and no intermediate reader-visible state. |
| Namespace authority withdrawing unsigned targets | Yes, subject to the design's namespace and cross-post restrictions. This is moderation authority, not authorship. |
| Rules rewrite | Adopt the shorter structure with the targeted edits below. Do not rebuild the old procedural thicket. |
| Committed-history marker | Keep its guarantee across profiles. Improve the migration and acknowledgment boundaries, then optimize the publication program without weakening the guarantee. |

## 1. Control messages

**Q1, defer group-control execution, not the whole feature.** A serial
number orders statements within an authority regime; it does not establish
that regime. The hard cases are an authority replaced and an old signed
command arriving afterward; a group retired and recreated under the same
name; an authority issuing conflicting commands with the same serial. Those
need decisions about authority epochs, group identity and conflicting
evidence, not a larger counter. C2 and C3 deliver something independently
useful: explicitly authorized withdrawal with durable evidence and reader
behaviour. Keep C2 focused on the authority needed for that rather than
building most of C4's policy machinery behind unused fields. When C4
returns, its contract identifies the group or group incarnation, the
authority regime and the command's place within it.

**Q2, accept-and-hide, but distinguish storage acceptance from
publication.** RFC 5537 §5.3 recommends remembering an early cancel and
rejecting its target; it describes cancellation as withdrawal from
circulation and access, physical deletion being one implementation. The
departure is a legitimate explicit policy, not verbatim RFC behaviour.
Retain the target as evidence while withholding it from the reader-visible
archive, after determining that the cancellation applies. Three details:
D03 does not itself require accepting every newly arriving cancelled
article (accepting a new target is a policy decision under the operator's
capacity and admission rules, else "preserve evidence" becomes unlimited
retention); "accept, then hide" must not mean "publish visibly, then hide":
when an applicable early cancellation exists the target's first published
view already excludes it, and a crash or a reader between two callbacks
must not reveal it; an early cancellation is not an unconditional
Message-ID blacklist: its effect is contingent on the target's acceptance
evidence and the applicable authority rule, so bind the durable decision to
its cause, target, scope and policy generation, and replay must not
reinterpret it under today's grants. The test, with equivalent grants and
target evidence: visible(T then C) = visible(C then T); the journal order
differs, the visibility decision does not. Test the authorized case, the
wrong-principal case, and recovery between the two arrivals.

**Q3, yes to withdrawal of unsigned targets.** A namespace administrator's
right to moderate the namespace need not depend on the author having
signed. The cancel must satisfy the control-authentication policy; the
unsigned target does not become authenticated by being withdrawn. Keep the
conservative cross-post rule: for a whole-article withdrawal on namespace
authority, every locally served target group must be covered by the grant.
Per-group hiding is a different model and must not slip in as an
optimization. Preserve the distinction between the authority's declared
target groups and the article's accepted group bindings: a canceller gains
no power by naming a narrower group list.

**Two consequences the design already states, to accept explicitly:**
existing connections keep their pinned pre-withdrawal archive until they
advance; an already-enqueued withdrawn target may still be forwarded (feed
suppression deferred). So the first feature is withdrawal from newly
published local reader views, not immediate revocation from all readers and
not cessation of circulation. Keep the snapshot model; test one reader
pinned before the withdrawal beside a fresh reader after; a theorem titled
"withdrawn article is 430" must carry the visibility-generation premise it
needs. Feed suppression follows as a separate transition that distinguishes
"not forwarded because withdrawn" from "delivered" and never manufactures
receipt evidence or discharges retention. The first promise is narrower
than "remote deletion".

## 2. The rules rewrite

The audit's case for shortening is convincing (generated-file churn,
line-number recertifications, repeated qualification). Replace the old text
with four substantive repairs and two small edits.

**A. D27: capacity versus scheduling quantum.** A fixed total-work limit on
a monolithic request can become the same hidden data limit; reading n bytes
entails work in n, and renaming a byte count "parser fuel" does not solve
it. The operator controls admission capacity; the implementation controls
how much work happens before yielding: streaming, bounded chunks, resumable
scans, explicit continuations. Running out of a quantum must not classify
valid data as malformed. Replacement wording: "No arbitrary implementation
ceilings on stored data. Admission limits belong to the operator's
supported profile. Bound work and allocation per scheduling step, using
streaming or resumable operations where needed. Exhausting a work quantum
yields or resumes; it does not silently truncate data. Validate that every
supported profile is representable by the selected codecs and runtime." The
last sentence is an obligation to make profile validation, representation
and format evolution agree, not a promise that a fixed width represents
arbitrarily large configurations. Keep the bounded-allocation-before-
untrusted-input protection.

**B. Representation: an abstraction relation, not duplicated
implementations everywhere.** "Every boundary has a concrete twin" risks a
second near-identical implementation of every helper. What is needed is an
abstraction relation at the boundary: alpha(step_C(c, i_C)) =
step_L(alpha(c), beta(i_C)) under the representation invariant, covering
the resulting state and the externally significant outputs and effects; for
mutable state that includes ownership and aliasing; for incremental
execution it may be a refinement over several concrete steps. Wording: "The
served path uses concrete representations. Each representation boundary
has a named abstraction or refinement theorem connecting the host-called
implementation to its logical model, including outputs and effects.
Executable functions are guard-verified, representation invariants are
established and preserved, and cost improvements are measured under matched
conditions." A correspondence theorem and guard verification are both
needed, for different reasons.

**C. Restore the precise teeth rule.** "A reachable non-degenerate witness
and one must-fail per hypothesis" loses the earlier repair: must-fail checks
that a command fails; an expected proof failure is not by itself a
counterexample. Replacement: "Teeth ship with each keystone. A reachable
positive witness asserts the complete antecedent and conclusion. A
hypothesis-removal witness affirmatively checks every retained hypothesis,
failure of the omitted hypothesis, and failure of the conclusion. Label
corrupted-state and mutation witnesses separately. Remove a redundant
hypothesis only after proving the weakened theorem; failed proof search is
not a counterexample." The positive is per literal theorem, not one
happy-path scenario for a proof family.

**D. Qualification: never carry a failed verdict across changed bytes.**
"Qualify one immutable candidate at convergence. A discovered regression
does not freeze unrelated development, but it blocks the affected
deployment or claim until the repaired candidate has matching evidence.
Reuse unchanged evidence where valid; do not transfer a green verdict to
changed bytes." "A regression is the next wave's fix" is a scheduling rule,
not permission to deploy the failed candidate or to call the next candidate
qualified because it contains the fix. Incremental runs after merges are
coalesced against a current certification frontier, not several
almost-identical runs.

**Small edits.** State the 8,000 MB cap together with the shared pool and
the aggregate-memory discipline, and which launcher enforces it (a shell
file must not be the only protection). Take the proof-cost tolerance
(10 to 11 s warning band, the baseline-regression threshold) as operating
rules, not as proof that every excursion is noise; keep matched host,
toolchain and job conditions and the edit-to-verdict target; splitting
books to get under ten seconds must not substitute for reducing total or
critical-path work. Remove the "ask first" gate for a described signature:
read the named source at the pinned revision first; ask only when that does
not resolve the contract.

## 3. The history marker

Not scale-only: store size is no reason to change whether loss of an
acknowledged suffix is detectable, and small stores are where recovery is
exercised. The cost is real: 326 to 388 ms per 32 KiB commit on ZFS in the
probe, three interleaved runs with spread; the marker program has a staged-
file barrier and a root-directory barrier, an additional persistence phase
rather than "one extra fsync".

**The invariant:** with A the committed prefix covered by success
acknowledgments, M the durable marker's count and D the durable
reconstructable length, A <= M <= D. Recovery may find records beyond M;
recovering fewer than M fails closed. The implementation orders this right
(the marker after the record's directory barrier and before fn-sn-finish;
the open check counts reconstructed history including packed records).
Freeze the guarantee, not the syscall sequence: a cheaper program (a shared
later barrier, bounded group commit) is legitimate once its acknowledgment
and crash behaviour refine the same contract; moving the count into an
earlier allocation barrier is not, since allocation can precede the
record's durability.

**Two cases next.** (1) Once enabled, absence must not mean legacy: today
`(:absent)` admits as `:unmarked`, so deleting the marker with a covered
suffix looks like a legacy store. Make a durable marker-required
format/profile state; an older store migrates; after migration a missing
marker is damage, and the requirement cannot become durable before a valid
marker exists. Whole-store replacement by an old snapshot stays a separate
freshness problem. (2) Test recovered success without a subsequent fresh
commit: the record becomes durable; the process dies before the marker
catches up; recovery finds the record; the client resolves its uncertain
submission as already stored; no new transaction is committed; the newest
transaction file disappears; recovery runs again. The current campaign
resubmits, posts a third article (which advances the marker) and then
deletes, so it does not establish this sequence. When "already stored" is
a successful resolution a client may rely on, it needs the same marker
protection as an initial success, by repairing the marker during recovery
or before returning that resolution, depending on the acknowledgment
contract.

Keep the marker on; make the guarantee and the two cases precise; then
profile the commit path and pursue a cheaper publication sequence as a
bounded performance packet. The same property with a better
implementation, never a quiet property downgrade.

## Recommendation back to the coordinator

Proceed with C2 and C3 and defer C4. Accept early-cancel targets only under
ordinary admission, retain their evidence, exclude them from the appropriate
published views; allow namespace authorities to withdraw unsigned targets
under the existing cross-post rule; state the pinned-reader and
outstanding-feed limits. Apply the shorter rules with the D27,
representation, teeth and qualification edits plus the heap cap and the
performance tolerance, without another audit cycle. Keep the committed-
history guarantee unconditional, distinguish migrated stores from legacy
ones, and test successful retry resolution before any later commit advances
the marker; optimize the byte program afterward against the same invariant.
