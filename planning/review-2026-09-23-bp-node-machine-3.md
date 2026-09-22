# fn BP contract review 3 (gpt-6, 2026-09-23), at 9d6ca463

Supplied by ember on 2026-09-23 from gpt-6's third static review, of the
patched contract `specs/bp-node-machine.md` at `dev` 9d6ca463 and the
dialogue `design-dialogue-2026-09-23-bp-2.md`. Kept verbatim. Its answers to
the eight questions are the decisions (all eight recommendations stand,
with the amendments in §1 below); its §2 to §4 are fixture and definition
changes owned by the slices that the handoff to Codex carries; its §5 is
the per-slice list.

---

Review subject: `9d6ca463db1687706eafdb6ba4db682511efc861`, especially `specs/bp-node-machine.md` §§5.0, 11.1, T6 and §4.2, plus the eight questions in the coordinator's handoff.

## Scope and disposition

This is a static review of the pinned contract and selected implementation books. No ACL2 certification, native-image run, or physical crash campaign was performed. Most of the revised machine, publisher-relation and service-loop functions remain proposed definitions. Findings about those functions are contract inconsistencies or obligations, not claims that a deployed implementation has exhibited the behavior.

The architectural defaults can stand. The most consequential remaining work is:

1. Make the counterexample suite executable evidence rather than a collection of successful expected failures. Some of its literal fixtures cannot satisfy their stated retained hypotheses.
2. Give T6 an FNBS-specific, byte-level publisher relation and an explicit inherited-history/base convention. The existing article Store K3/K4 theorems are not directly about the FNBS namespace or decoder.
3. Make continuation cover the service that actually emits an action. The four held-entry action classes do not cover owed receipt handoffs or the whole fragment-plan protocol, and outbox retry after resources return is not specified.
4. Propagate principal partitioning to reception-time duplicate/conflict handling; reassembly partitioning alone is too late.

These should become focused test/definition changes in the existing lanes, not another architectural redesign.

## 1. Answers to the eight questions

### Q1: Boundary for the two-process gate

The recommendation is fine: use the expressly stated whole-host trust boundary for A, and namespaces for B when useful for the contact/fault harness. Record that the A gate supplies no separation from mutually untrusted co-resident processes. A namespace deployment must still name which host/kernel/administrative actors are trusted; it is not a cryptographic peer identity.

The admission test is still meaningful in A: channel selection must select a configured peer first, and a mismatched announced EID must refuse rather than select another principal. Do not interpret a successful controlled-host test as evidence for a stronger production boundary.

### Q2: Three identity roles versus signed receipts in v0

The first recommendation is fine. Fix and version the identity slots, request subject and receipt-issuer authorization, and claim only the profile actually checked by the image. Do not imply that signing a request also authenticates the receipt which discharges it.

An unsigned receipt accepted under a network-trust profile is authorized only under that declared profile. In particular, hop admission does not establish end-to-end issuer authenticity through an untrusted relay. This is a claim boundary, not a demand to move signed BP receipts onto the current gate's critical path.

### Q3: Authoritative history at its bound

Refuse `(:capacity :history)` in v0. That is preferable to premature watermarks whose semantics have not been fixed. Never evict authoritative outcomes or owed/handed-off dispositions as if they were report observations.

Also distinguish transport admission from application commitment. A request should not acquire an unfulfillable receipt-handoff obligation because the metadata capacity needed to record it was not reserved or checked. A reservation/admission contract for the handoff's metadata is separate from journal cleanup debt. This can be expressed in the existing admission machinery.

### Q4: Fast reassembler domain

Keep all-input equality. The logical reference predicate need not be the literal algorithm the fast implementation executes. If `fn-bpf-inputsp` is expensive, implement a bounded admission/checking path and prove it equivalent, rather than automatically weakening the correspondence theorem.

Require ordinary malformed-input tests to establish that the native path returns `(:invalid :bounds)` without a reader/guard failure. The all-input equality is a semantic guarantee; it is not itself a work bound.

### Q5: Different principals' fragments

Choose principal-separated active sets for the v0 profile, but amend reception as well. The present receive algorithm checks global bundle identity before reaching principal-specific reassembly. A different principal can occupy that identity first and cause the honest peer's fragment to be refused or deduplicated away.

Keep wire bundle identity separate from the local admitted-claim identity. One possible representation shares immutable bytes between principal-specific admission records for exact duplicates; contradictory bytes remain distinct claims subject to policy. The exact representation is the lane's choice, but the property must cover the receive branch and the held-entry uniqueness invariant, not just `fn-bpn-active-set`.

Do not call this general denial-of-service isolation: live slots, history and execution budgets remain shared unless per-principal quotas are separately adopted.

### Q6: Send-time image growth

The worst-case envelope recommendation is fine. Quantify the bound over permitted forwarding observations and all mutable metadata/encoding changes, and check the actual image again. Do not rely on the phrase "a few octets." Re-fragmentation is then needed for a genuinely smaller negotiated MRU, not ordinary aging within the planned envelope.

### Q7: Indefinitely uncertain owner

The definitive-response premise is fine for v0. Do not invent a recovery-time bound ahead of the owner's recovery proof. An outstanding response can be pending before its allowed deadline and violated after that deadline; the monitor should not report an incomplete window as already satisfied.

The premise should be associated with the target operation/eligible service prefix, not satisfied by unrelated definitive responses while the target stays uncertain.

### Q8: Checkpoint representation

Use chunks and a manifest through the existing publisher. Reuse the physical publication theorem, not an assumption that ordinary lifecycle replay already understands checkpoint records.

Keep the physical accounting explicit. The spec defines physical usage as `next-token - generation-base`, but checkpoint chunks and their manifest do not consume those lifecycle tokens. If they count toward the same per-generation cap, physical usage must include them, e.g. `checkpoint-records + next-token - generation-base`. If they have a separate bounded budget, name it as such. The affordability theorem includes checkpoint cost; the admission counter must not subsequently forget it.

## 2. Counterexample suite: what still does not establish non-vacuity

### 2.1 Exact negative witnesses do not imply a satisfiable full antecedent

Consider the valid but vacuous formula

```lisp
(implies (and (equal x 0) (equal x 1)) nil)
```

Dropping either equality yields a false formula. At `x=0` and `x=1`, respectively, an exact negative witness satisfies every retained hypothesis and falsifies the conclusion. Thus *all* hypothesis-removal tests can be genuine counterexamples while the original antecedent has no model.

Section 5.0(1), requiring the whole antecedent to hold, is the right defense. It must be applied to every literal theorem, not once per T1 to T6 group. A non-vacuity check must be an active, successful assertion/certified ground fact before that theorem gets an assurance status. A pending positive form is an open test, not evidence.

ACL2's `must-fail` tests whether a command fails with the requested error class. Its own documentation includes a malformed `defun` as a successful example. Therefore "all must-fails passed" can also mean translation or event errors, not semantic counterexamples. Proof search failure is not a proof of falsity.

For a theorem `H1 ∧ ... ∧ Hn => C`, use this structure:

```text
positive:
    assert reachable(w+)
    assert H1(w+) ∧ ... ∧ Hn(w+)
    assert C(w+)

negative for Hi:
    assert all referenced functions/forms are admitted and well formed
    assert H1(w-) ∧ ... ∧ H(i-1)(w-) ∧ H(i+1)(w-) ∧ ... ∧ Hn(w-)
    assert ¬Hi(w-)
    assert ¬C(w-)
    classify reachable versus deliberately corrupted
    optionally also require the weakened theorem command to fail
```

The affirmative conjunctions must not be hidden inside the expected-failure wrapper. Missing definitions and disabled positives must be shown as open, not successful negatives. Where attachments participate, distinguish evaluation evidence from ordinary logical ground theorems.

Section 5.0(4) should say "remove after proving the weakened theorem," not "remove when the lane did not find a counterexample." Failed search does not establish redundancy.

### 2.2 Literal fixture repairs

#### N04 is outside the held-bundle profile

The suite uses an older 200 KB entry. The declared maximum held bundle image is 131,072 octets. It cannot serve as the claimed reachable, invariant-preserving older entry.

Use, for example, a valid bundle with a 48 KiB payload and the no-fragment flag, a session MRU of 32 KiB, and a later fitting 8 KiB bundle. Assert the actual encoded sizes, not merely the payload sizes. The no-fragment flag makes the older entry genuinely infeasible even after C lands; otherwise a successful fragment plan is a legitimate action for it.

#### N05's old boundary is now a refusal case

Let `F = remaining - D - R - control-reserve`. A kind-8 attempt spends one record and raises debt by one, so admission requires `F >= 2`.

The suite still describes an attempt and its failed result starting from `C + 2N + 1` free records. For N plain retained entries with `D=2N`, R=0 and C the margin, that supplies only F=1. The repaired machine must refuse to start the attempt.

Split the fixture:

* F=1: kind 8 is refused without durable mutation.
* F=2: kind 8 and its failed kind 9 both complete; free credit returns to zero above the reserved margin.
* A debt-paying discard at the boundary remains admitted.

Keep the old one-free-credit trace only as the mutant's counterexample.

#### T1's wire-corrupt state is not an exact invariant-removal tooth on the checked dispatcher

The logical `fn-bpn-step` still checks `fn-bpn-machine-statep` and returns no effects on failure. The revised state recognizer includes wire/encoding agreement. Corrupting that agreement therefore prevents the required `:deliver` effect from existing; the effect-membership hypothesis fails too.

Use a state that preserves the weaker machine recognizer while violating the stronger authorization/lifecycle invariant, and actually causes the checked dispatcher to emit the bad effect. A forged but structurally well-formed pending authorization is a candidate to investigate. If the weakened theorem still holds, prove that instead of manufacturing a tooth. A corruption test of `step-fast` is a different subject and must be labelled as such.

#### T4's proposed fragment-parent negative violates the retained extent bound

The re-fragmentation theorem retains

```lisp
(<= (+ (fn-bpp-fragment-offset p) (len payload))
    (fn-bpp-total-adu-length p))
```

and a successful, nonempty fragmentation result. `fn-bpp-blockp` requires a whole parent's offset and total fields to be nil. A whole parent cannot satisfy that retained extent condition for a positive payload length. Thus the proposed "drop fragment-parent; use a whole parent" test also violates another hypothesis.

Prove the implication from the remaining premises to fragment-parent and remove the redundant clause if it closes. At minimum, withdraw that claimed exact negative witness.

#### T3's second theorem needs its own positive

The suite lists the anchored wall-less expiration as its headline positive; that falsifies the second theorem's `no-anchors` hypothesis and belongs to its negative tests.

A useful full-antecedent positive for the second theorem is an unanchored, wall-less transit bundle whose expiry is uncertain and whose hop limit causes a deletion. Its deletion is not lifetime expiry. Reuse the reason-removal fixture if it satisfies all the retained conditions.

#### Add a literal row for T6's physical theorem

N06 at the machine level is not a positive witness to the physical theorem unless the same example constructs the byte-store state, establishes the publisher relation, selects an admissible byte crash, and scans that resulting directory.

Require a valid nonempty FNBS frame and at least two distinct crash choices. Empty journals and externally supplied `(confirmed ++ candidate)` values do not establish that the native namespace can inhabit the theorem's antecedent.

### 2.3 Two conditional safety statements should not be advertised as behavior coverage

`fn-bpn-unsupported-adu-class-is-refused-durably` constrains an already-proposed kind-7 record. It does not itself establish that an eligible unsupported ADU generates that proposal, nor that a publication completes. Pair it with the transition witness and the persistence-completion fact.

The TCPCL theorem shown in §9.2 excludes a final ACK from the immediate result of `fn-tcl-refuse-held-final`. The prose additionally promises that no later session step sends one. A one-step statement is insufficient for that trace claim. Require a refused-transfer invariant preserved by later steps, or narrow the prose. Extend N12 with late/duplicate continuation input and flush/pump actions, checking that no later final ACK escapes.

## 3. T6 and the actual byte model

### 3.1 What improved

The one-epoch equation, independent `issued` slot, normalization fixed point, unconditional attempt clearing for anchored and unanchored entries, and stronger queue-answer binding all address the prior review's specific objections. Keep those changes.

The remaining concern is not that the new physical theorem has already been proved incorrectly. Its central functions are not defined in the contract at sufficient detail to judge that. The relation is currently described as "the FNBS publisher's relation ... preserved by its actual operation sequence." That is the obligation to discharge, not its definition.

### 3.2 Existing K3/K4 do not directly instantiate to FNBS

At the pinned revision:

* `fn-bs-record-of-octets` uses `fn-frame-store-decode` and `fn-store-event-decode-exact`.
* `fn-bs-read-records` reads `:transactions`, uses `fn-bs-txn-name`, and checks Store-event sequence numbers.
* `fn-bs-scan-store` expects the Store's config/frontier names and transaction namespace.
* `fn-bs-store-relation` relates that image to `fn-sf-statep` and its phase/candidate/history.
* K4 additionally uses `fn-snt-relation` and the article Store reopen function `fn-sn-open-observed`.

Those are not the FNBS lifecycle codec, names, state or reopen entry. Supplying a real FNBS frame to the Store decoder is not a correspondence proof. Choosing `dir` to mean an article Store image instead does not verify the native FNBS publisher.

The actual crash predicate in those theorems is `fn-bs-crash-imagep`. The draft's `fn-bs-byte-crash-image-p` needs an explicitly defined wrapper/equivalence, or should use the existing name and full byte-store state directly. A directory alone is insufficient to determine inode writes, aliases and pending filesystem operations.

The appropriate reusable level is the byte primitives and their preservation lemmas: fenced contents, quiet directories, per-name namespace outcomes, freshness/known inodes, together with the `fn-jpub-*` publication control machine. An explicit namespace/codec refinement to the Store relation is an alternative, but it is additional work, not an automatic application of K3/K4.

### 3.3 A sufficient non-circular relation

Use a concrete relation between the full byte-store state, publisher program state, an epoch base descriptor and the machine/operation trace. It should state at least:

1. **Inherited prefix:** the selected generation/checkpoint and pre-epoch journal prefix are bound to the logical base by actual names and encoded contents. All names which this running epoch treats as inherited authority have been durably established.
2. **Confirmed records:** the confirmed epoch delta has exact canonical names, exact FNBS encodings and known immutable inode targets; callbacks counted as confirmed actually completed the matching operation.
3. **Outstanding publication:** at most one unresolved publication has its token, record, stage inode/name, final name and control phase bound to `issued`. It survives the uncertainty callback.
4. **Isolation:** writes before the file barrier target private staging only; no subsequent write aliases an authoritative inode. Parent namespace publication and writer ownership are part of the initialization/input contract.
5. **Phase/byte correspondence:** before linking, the candidate has no public authority name; link only occurs after its exact contents were successfully fenced; the namespace barrier decides when the public name is durable. A failure before linking cannot silently become authority.
6. **Frontier discipline:** the candidate's logical token and physical position are the ones the lifecycle expects; no unrelated second publisher can insert another candidate.

These clauses constrain program-reachable states. They do not assume that every crash already produces the desired decoded journal. Prove initialization, per-syscall preservation, and the crash projection as separate results; retain a native-cut-to-program-counter mapping.

Under these facts, byte tears are still permitted on private staging. An authoritative candidate can be absent or point to the *fenced exact contents* because the program never publishes it before the file barrier. This derives the relevant complete-or-absent property without assuming an atomic record directory.

The current `fnn-bps-open` is a useful correspondence target: it acquires spool ownership and barriers the parent and lifecycle directory before treating recovered final names as durable. Preserve and model that recovery establishment, rather than assuming an arbitrary logical epoch base has a physically stable directory.

### 3.4 The inherited-prefix / epoch-delta convention is missing

Let:

* B be a recovered, nonempty logical epoch base;
* J0 be the physical history/checkpoint that establishes B;
* C be the new epoch's confirmed records;
* u be its optional unresolved issued record.

The physical scan gives `J0 ++ C` or `J0 ++ C ++ [u]`, not simply C or `C ++ [u]`.

The draft defines `confirmed-journal base events` from only the current epoch's confirmations. It defines `journal-of-directory crashed` without a base/suffix parameter, while `epoch-basep` explicitly allows recovered nonempty states. The zero-event case should be a mandatory positive: recover a nonempty journal, take no new events, crash, and apply the physical theorem. If the scanner returns the full directory and observed-journal expects an empty delta, the antecedent cannot model this ordinary state.

Choose a convention explicitly:

* full-history scanning plus an epoch-base descriptor/checkpoint from which replay starts; or
* a checked physical-prefix binding and an extracted epoch suffix.

Do not erase the issue by defining the publisher relation only for freshly empty stores. Also test a second recovery after new work in the new epoch.

### 3.5 Process epochs and journal generations are not interchangeable

`epoch-event-listp` excludes only `:restart`. It therefore appears to include `:generation-selected`, whose operational effect changes `generation` and `generation-base`. The durable projection keeps both. But confirmed-journal is specified to collect only matching durable lifecycle publication results.

A successful selection without a lifecycle record thus changes the left side of the raw replay equation without the specified delta changing the right side. Either:

* exclude authority-selection/rotation transitions from the running-journal-segment equation and use the rotation theorem as another bridge; or
* include the publication/selection history and its replay semantics explicitly.

Similarly, the `normalize` fixed point resets `generation` only through kept fields, but it drops route generation; the checkpoint paragraph claims to retain configuration-generation provenance. Give any required durable provenance its own field rather than relying on a volatile route-generation field that projection discards.

### 3.6 Minimum physical witnesses for A2

Use actual encoded FNBS records for each:

* valid nonempty inherited history, zero epoch events;
* private stage torn before the file barrier: no public record;
* successful file barrier and unbarriered link: candidate absent and candidate present;
* successful directory barrier before its callback: candidate present, `issued` unresolved;
* directory/publication uncertainty callback delivered before death: candidate absent/present as the model permits, with `pending=nil` and `issued` retained;
* recovery establishment, new operation, second crash;
* arbitrary garbage under an authoritative name outside the relation: explicit recovery fault, never silently treated as an absent record.

The theorem's soundness statement need not claim every conservative observed-journal alternative is physically realizable at every cut. Keep physical soundness, model completeness and recovery acceptance separate.

## 4. Waits and continuation

### 4.1 The T6 continuation domain is wider than its action domain

`owedp` includes bundle keys, receipt-handoff keys and open-family keys. `enabled-action-p` is described using the four-class progress step or `start-one`. Those actions select held bundles. They do not select an owed handoff and construct its `:transmit`; that happens in §9.4's outbox/service path. The family materialization/termination steps also need explicit entries in the action algebra.

Move the composed continuation property to the service loop, or extend a core action-descriptor interface so it can return a handoff/family action without importing the application Store into the BP core. A bundle-only theorem may stay on the machine. Do not make an owed handoff vacuously "blocked on some future clock." A wakeup must enable a named action for that obligation key.

### 4.2 A handoff can stay owed after capacity returns

Section 9.4 issues handoff transmits after a creating kind 7 and at recovery. It does not specify retry after a failed/refused enqueue when capacity or credit becomes available.

A legal schedule is:

```text
local request A and carrier B fill the held slots
A is delivered; kind 7 creates owed handoff H
H's immediate receipt transmit is refused for live-slot capacity
A is discarded and a slot becomes available
periodic progress continues, but there is no new kind 7 and no restart
H stays owed; no specified action retries the receipt enqueue
```

The resource is now available. This is not an environmental outage; it is a missing internal continuation.

Make owed handoffs persistent ready-work in the service runner. Retry a refused handoff enqueue when its relevant dependency changes. Give the test a final condition that the receipt is actually queued after capacity returns, without restarting or creating an unrelated handoff.

### 4.3 The dependency signature must determine whether the decision could change

The table is an improvement, but several predicates lack the recorded state needed to evaluate their English description:

| Wait | Problem | Repair |
|---|---|---|
| `(:route rg)` | Correct shape if configuration generation is monotone and the route-change path invalidates the affected entry. | Test route installation at a newer generation and actual subsequent dispatch; test unchanged/stale generation separately. |
| `(:mru peer mru)` | "route-generation changes" has no recorded generation in the wait; same-MRU session changes may still change availability. | Carry dependency versions, or explicitly invalidate on the relevant session/route events; bind the wait to the current next-hop decision. |
| `(:after m)` | Deadline is adequate only if eligible work is re-examined when m is reached; equality at the boundary matters. | Test `m-1` versus m, and restart reclassification of volatile waits. |
| `(:fragments key n)` | Equal cardinality does not imply an unchanged active set. Membership, coherence and principal partition can change. | Use a generation of the exact active set/coherence partition; prove every membership/coherence change invalidates it. |
| `(:credit)` | "free credit has grown" is not decidable from a bare tag alone; distinct records need distinct credit and resource conditions. | Store the needed threshold and/or a resource generation, and re-evaluate full admission. Add live-slot/byte/history dependencies where relevant. |

A count ABA alone is not a demonstrated deadlock in every conceivable implementation: a newly received fragment's dispatch could happen to rescue it. It is nevertheless insufficient to prove that a cached blocked decision remains valid. The implementation must name the rescuing transition or use a complete dependency version.

A compact contract is: a wait records its dependency versions and the condition needed by its action; if neither changes, the blocked decision remains valid; when an enabling change occurs, the entry becomes eligible. This avoids whole-state rescans without making a cache entry authority.

### 4.4 The global yield rule can suppress a different eligible candidate

Section 9.1 says that after an event proposes nothing or refuses, the same *kind* of progress event is not reissued until an external input changes time/session/routes or completes an operation. But §4.2 may have just changed internal scheduling state by tagging only one candidate as blocked.

For N04, the first `:resume` can mark the oldest entry MRU-blocked; a later entry is ready. Globally yielding `:resume` now delays that different ready entry until an unrelated input.

Apply no-repeat to the same obligation/action with unchanged dependencies, not the whole event kind. Treat installing a new wait or advancing a selector as bounded scheduling progress, with the existing turn budget preventing spin.

The four-event fairness statement also needs an honest event alphabet. A pending publication may block machine progress until a completion arrives. Distinguish scheduling opportunities from persistence callbacks/no-op `:clock`s. In A1, prove a selector-level bound; in B, translate it to loop turns with the actual completion/service premises.

### 4.5 Principal partitioning must precede deduplication

Two concrete tests should accompany Q5:

1. Peer P sends fragment F0. Peer Q sends the *same* F0 and Q's complementary F1. A global duplicate answer must not discard the admission evidence Q's own active set needs to assemble.
2. Peer P first sends different content under the bundle identity Q will use. Q's honest fragment must not be rejected solely because P occupied a global held-entry key.

The current §4.1 step 4 consults global live identity; §7.2's `(ADU key, principal)` partition is later. A reassembled-bundle/correlation shortcut is also keyed by ADU key in §4.1 and must respect whatever admission partition the policy promises.

This is local evidence isolation. It does not make a peer honest, and does not turn an unauthenticated source EID into author authority.

## 5. Minimal lane-facing changes

### A1

Repair N04/N05 fixtures and exact negative-witness checking; keep pending/undefined tests out of green evidence. Define action selection and wake invalidation together, including the handoff action descriptor or a clearly scoped bundle-only continuation theorem. Give physical theorem/replay consumers the fields needed by the base and publication protocol. Amend reception provenance/duplicate handling before freezing the data representation used by C2.

### A2

Write the FNBS-specific publisher relation and its successful nonempty byte witnesses first. Use the actual byte crash predicate and byte-level lemmas. State the inherited-prefix/epoch-delta convention and separate ordinary journal epochs from authority-selection transitions. Preserve the current recovery barriers in the host correspondence.

### A3

Make owed handoffs retry on the actual resource dependency after a refused enqueue. Test capacity returning without a restart. Preserve the already adopted requester-owned post-handoff retry policy; this is completion of an owed handoff, not autonomous retransmission of an expired receipt carrier.

### C1/C2

Keep total fast/reference equality. Replace the impossible re-fragmentation negative witness. Define the full active-set key, including its principal and coherence partition, and make the reassembly wake token refer to that exact set. Cover materialization and plan termination in the service action set.

### E

Keep chunked checkpoints. Charge chunks/manifest in the physical budget, and bridge the selection transaction to T6 rather than treating it as an ordinary epoch event that leaves the confirmed journal unchanged.

## 6. Source ledger

All fn references are pinned to `9d6ca463db1687706eafdb6ba4db682511efc861`: `specs/bp-node-machine.md` §2.1 (debt rules), §2.6 (projection and issued operations), §3.6 (rotation), §4.1 to §4.2 (reception, selection and waits), §5.0 (teeth rules), T1 to T3, T4, T6, §7 (principal-specific reassembly and family plans), §9 (service loop and TCPCL), §9.4 (handoff outbox), §11.1 (counterexample suite); `books/bp-node-machine.lisp:640-656` (the checked dispatcher); `books/bp-primary.lisp:473-490` (the whole-primary representation); `books/byte-store-scan.lisp:328-410` (the Store decoder and namespace scan) and `:436-610` (the byte/Store relation and authority clauses); `books/byte-store-keystones.lisp:30-119` (the K3/K4 subjects); `books/byte-store-relation.lisp:1-175` (the initialization and input-contract precedent); `books/journal-publish.lisp` (the immutable publication control machine); `host/native/bp-service.lisp:245-306` (native lifecycle recovery establishment); ACL2's `books/std/testing/must-fail.lisp` (read from its default branch).

The source ranges are reading locations; no claim of certification follows from a theorem's presence in a specification or source file.
