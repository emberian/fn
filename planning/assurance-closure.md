# Assurance closure matrix

This is a finite work inventory for closing the assurance gaps already named by
the requirements, proof registry, and subsystem specifications. It does not
change a registry status. `Certified` below means that the cited evidence has
established the stated scope in a clean run; `Assigned` means current work is
being attempted and is not evidence of completion.
The historical integrated baseline is the
[54-root/45-test checkpoint](../tests/evidence/2026-09-18-assurance.md), with its
explicit original test failure and corrected recheck. Later targeted results
remain distinct from that frozen source set. The subsequent [75-root/67-test batch](../tests/evidence/2026-09-18-composed-store.md)
passed with unchanged input sources; current owners and next exits are in
[current work](now.md).

The closure test for every mechanizable row is a theorem over reachable,
bounded, non-vacuous states (including the rejecting cases), plus the named
scenario and an exact certification record. A socket, Python, or filesystem
experiment is integration evidence; it does not replace the theorem. Platform,
cryptographic, peer, and contact facts are environmental qualifications and
must remain hypotheses of the code claims.

## Matrix

| Pillar and stable IDs | Exact missing claim | Present evidence (scope only) | Closure criterion | Dependencies | Current state |
| --- | --- | --- | --- | --- | --- |
| **Core traces, allocation, and live node** — `PRF-001..004`; `OBJ-001/002/005`; `STO-002`; `RET-001/002`; `SCN-002/007/015` | Lift one-step acceptance/retention properties to arbitrary finite event traces, including refusal, retry, stale completion, lost reply, cross-post, capacity, and crash-result branches; show the live node transition is the same accepted transaction and preserves all article-to-membership-to-pin bindings. | Acceptance/node invariant books cover initial states, transition lemmas, immutable binding, local-number preservation, staged completion, and general retention accounting. The finite node trace book now certifies arbitrary valid and malformed event traces, including old binding preservation; mixed live and resolution traces are also certified for their named scope. This remains a logical trace claim and does not establish physical completion or host adoption. | A trace-induction theorem over the actual node event type proves invariant preservation, one-use local allocation, idempotent identity/retry effects, and atomic membership/obligation publication; the live bridge has a correspondence theorem for every accepted effect and rejects stale generations. `SCN-002`, `SCN-007`, and `SCN-015` pass the same claims through the simulator and host bridge. | `PRF-007`, `PRF-014`; exact event/effect schema; bounded resource profile. | Finite node and mixed live/resolution trace claims are **Certified** for their stated scopes. Actual host adoption passed the integrated 67-test suite; physical completion remains open. |
| **Crash matrix and arbitrary traces** — `PRF-007`; `STO-003..005`; `FLR-001/002`; `SCN-003/006/015` | For every crash point around frontier replacement, data write, publication, directory barrier, completion, and recovery barrier, prove the resulting image is old-or-new as specified, retains acknowledged records, may retain a complete unacknowledged record, never exposes a partial transaction, and fences after uncertainty. Cover arbitrary finite repetitions, not only one crash. | `books/store-files-invariants.lisp` proves transition/crash recognizer preservation, stable-prefix retention, candidate survival, one-crash acknowledged retention, and fence/gate properties. `run_store.py` and `tests/test_store.py` exercise injected failures, replay, and mutation gating. The isolated journal is explicitly not the file adapter refinement. | Exhaustive bounded small-state traces plus an inductive arbitrary-trace theorem establish the store-files obligations and `SCN-003/006/015` pass with actual recovery outcomes. Every uncertainty path reaches `fenced` and only successful scan/replay/rebarrier returns `ready`; no theorem treats a diagnostic prefix as recovered state. | Store-files abstraction relation; `PRF-001`; codec/frame recognizers; named A-DURABILITY/A-WRITE-ISOLATION hypotheses. | Crash/trace closure is **Certified** for finite file-kernel trace/prefix claims and the declared finite tests; physical correspondence and platform qualification remain separate. |
| **Live file/node refinement** — `PRF-007/014`; `STO-002..005`; `HST-001/003/004`; `SCN-003/015` | Prove that the running file adapter, allocation frontier, recovery scanner, ACL2 node, and completion gate implement one coherent abstraction relation, including pending node state and all recovery faults. | The adapter invokes the actual ACL2 replay/node definitions; file-kernel proofs model publication and allocator ordering; finite live and resolution trace correspondence and the observed-image loader are now certified for their named scopes. Actual host adoption is merged and passed the integrated 67-test suite. | A correspondence theorem maps every accepted physical image and every permitted adapter transition to the logical node, including record txid gaps, frontier dominance, pending completion, recovery fences, and exact effect identity. Integration tests demonstrate replay/refusal/uncertainty equivalence on generated traces. | `PRF-007`; `PRF-001`; exact store frame grammar; host event/result contract. | Finite live/resolution traces and observed loading are **Certified** for stated scopes. Actual host adoption is integrated and tested; full physical refinement remains open. |
| **Codec canonicality and schema evolution** — `PRF-005`; `ENC-001/003/004`; `OBJ-001/002`; `SCN-013` | Close accepted-input canonicality and deterministic preimages across the composed record, native article, statement, batch, signature, and frame schemas; reject non-minimal/duplicate/unknown-authority forms while preserving bounded opaque unknown objects. | CBOR primitive round trips and exact accepted-input re-encoding are certified; provisional records have value round trips; article parsing preserves exact source bytes. Record reverse canonicality and primitive/record guard graphs are now certified; native/batch/signature schemas, domain separation and unknown-schema policy composition remain open. | Freeze the selected schema/profile and golden vectors; prove `decode(encode(x)) = x`, unique accepted encoding, rejected alternate encodings, deterministic domain-separated preimages, bounded unknown-object carriage, and version/algorithm separation. `SCN-013` covers boundaries, malformed declarations, vectors, and independent decoding. | D01/D08/D09; article identity/provenance model; transfer grammar; signature suite; frame/recovery grammar. | Record accepted-input canonicality has passed targeted certification; native/schema/signature closure is **Unassigned** and remains open. |
| **Parser recognizers, work, and raw execution** — `PRF-016`; `ENC-002`; `HST-001/004`; `NNT-003`; `SCN-013/014/015` | Prove complete recognizer/decoder correspondence and explicit length, nesting, allocation, and work bounds for article, UTF-8 wildmat/DP, wire, CBOR/record, and transfer inputs; show host raw execution is guard-safe and never evaluates input. | Article parser has exact-source reconstruction and bounded local limits; semantic fields operate on successful parser views. The exact full wildmat matcher work and transfer public bound are now certified for their named scopes; CBOR/records preflight limits and wire/article guard graphs are certified. The host remains an interpreted ACL2 bridge; base guard graphs and actual composed storage adoption are integrated. | For each parser, prove accepted output is recognized by the corresponding output predicate, malformed/oversized input rejects before unbounded allocation, work is bounded by the published profile, and arbitrary socket partitions preserve results. Guard verification covers every raw host call used by the adapter. | D16 resource profile; exact wire/object grammars; `PRF-006`; host event/effect schema. | Wildmat exact matching, transfer public bounds, and the current guard graphs are **Certified** for stated scopes. No claim of fully raw host execution follows from the base guard graphs; physical/platform qualification remains separate. |
| **Article injection, provenance, native schema, and signatures** — `OBJ-003/007`; `ENC-003/004`; `NNT-004`; `PRF-005/013`; `SCN-012` | Turn the proto-article subset into the selected complete injection profile: required fields, generated fields, configured-group authorization, source/projection separation, legacy gateway provenance, native signed source, signature preimage, key/rotation policy, and conflict handling. | `article-fields` certifies exact Message-ID/Newsgroups grammar, multiplicity/status classification, source-field preservation, and narrow routing checks. Article syntax preserves unknown fields/body bytes. No complete injection, native envelope, signature verification/authority confinement, or gateway policy is implemented. | Freeze D01/D09 profile and vectors; prove injection accepts/rejects exactly the selected RFC/fn domain, preserves source and provenance, signs/verifies the specified bytes, cannot grant administrative authority from content, and distinguishes trace mutation from authored conflict. `SCN-012` passes valid/invalid/forged/unrelated-signature cases. | D01/D02/D09/D11; parser and codec closure; authorization policy; cryptographic primitive/environment qualification. | Article grammar work is **Assigned** and its narrow results are **Certified**. Complete injection/native/signature work is **Unassigned/high impact**. |
| **NNTP wire, session, and effects** — `PRF-006/015`; `NNT-001..006`; `HST-002`; `SCN-014/015` | Complete the selected RFC profile and session refinement: command grammar/error precedence, cursor state, capabilities, POST/injection, OVER, listings, multiline framing, per-session bounds, serialization, partial output, disconnect, and durable effect outcomes. | Wire book proves bounded CRLF/dot framing and partition behavior. The full selected command/session preservation theorems, finite-session preservation, and effect typing are now certified for their named scope, alongside reader and independent-client evidence. Physical durable completion and host adoption remain separate. | RFC clause matrix is complete for the advertised bundle; executable session theorem relates every command/input partition to state/effects and exact responses; POST success follows durable completion and retry identity; independent client/transcript, fragmentation, oversized input, concurrent-session, and restart cases pass. Advertisements contain only certified bundles. | Article injection/signatures; `PRF-014`; `PRF-007`; RFC 3977/5536/5537 audit; selected D05 profile. | Full command/session/finite-session preservation and effect typing are **Certified** for stated scopes. Native injection/signature and physical qualification remain open; the stored-reader host is integrated. |
| **Retention authorization, receipts, handoff, and GC** — `PRF-004/012/013`; `RET-001..006`; `REP-006`; `SCN-007/008/016/017` | Prove obligations are charged before acceptance, receipts are typed and bound, only committed authorized evidence releases the exact obligation, handoff survives lost/replayed receipts and restart, and GC/expiry protects dependency closure and duplicate history. | Abstract retention books prove finite accounting, independent pins, evidence-gated release, identity preservation, and general release invariants. Local records persist an archive pin. No durable receipt protocol, real authorization context, node-level release/GC, or history/resurrection policy is implemented. | Define receipt grammar and authorization context; prove sender/receiver trace theorem with lost/stale/wrong-subject/wrong-incarnation evidence; implement durable release decision and dependency-closure GC with crash recovery; pass `SCN-008/016/017`. No transport ACK can release a pin. | D12/D13; native authority/signature profile; store/checkpoint/compaction closure; peer A-PEER and node-survival hypotheses. | **Assigned** to the active BP workflow/journal lanes for receipt/handoff; authorized GC remains open. Existing accounting/release lemmas are **Certified** only for abstract supplied evidence. |
| **Transfer correctness, work, persistence, and complete acceptance** — `PRF-011/016`; `REP-001..003`; `OBJ-004`; `SCN-009/013` | Extend volatile fragment assembly to a serialized portable batch/chunk grammar, complete-object and dependency validation, durable progress/restart, duplicate/reorder/conflict semantics, bounded work, and atomic article/obligation acceptance; incomplete input must never emit an acceptance receipt. | Exchange proves bounded fact-set merge under fixed validation hypotheses; transfer proves initialization, invalid/duplicate paths, out-of-order chunks, gaps, overlap conflicts, reservations, and unverified candidates. The public transfer work bound is now certified for its named scope. Wire grammar, persistent queue/progress, dependency closure, receipt integration, and full application acceptance remain open. | Prove merge algebra and transfer transition/work invariants over arbitrary fragment traces; persist and recover progress idempotently; validate complete dependency closure before publication; pass reordered/overlap/duplicate/crash/restart vectors and independent codec vectors for `SCN-009`. | D08/D15/D16; codec canonicality; store/refinement; retention/receipt integration; `PRF-007`. | Transfer public work bounds and current assembly claims are **Certified** for stated scopes. Persistence, dependency, receipt, and application acceptance remain open. |
| **Replication, restore/fork identity, scheduler, and BP handoff** — `PRF-011/017/018`; `OBJ-004/006`; `FLR-004`; `REP-004..006`; `SCN-001/010/011/017` | Establish origin/incarnation non-reuse after restore/clone, preserve conflicting evidence, schedule durable transfer work with fairness/resource policy, and keep BP/LTP transport status distinct from fn acceptance and retention. | No evidence closes restore/fork, long-contact, scheduler, or BP scenarios. Fact merging is only under fixed local validation hypotheses; transfer staging is volatile and transport-independent. | Prove origin identity/restore state machine; specify bounded queue/retry/fairness and prove conditional progress under A-FAIRNESS; implement durable scheduler and receipt handoff; run four-node delayed/reordered/replayed/clock-jump/restore traces and a versioned BP adapter interoperability profile. | D10/D11/D12/D15; transfer persistence; retention handoff; platform/clock observations; A-IDENTITY/A-FAIRNESS/A-PEER. | **Assigned/current priority** to real BPA, durable workflow, receipt and ingress lanes. No liveness or DTN completion may be inferred from safety proofs. |
| **Checkpoint, index, compaction, retention closure, and rollback detection** — `PRF-008..010`; `STO-001/006..008`; `RET-005/006`; `FLR-003`; `SCN-004..006/016` | Prove checkpoint+suffix equivalence, complete index reconstruction/range results, crash-safe compaction with protected dependency closure, explicit corruption/salvage, history/tombstone policy, and detection of whole-store rollback by an external freshness anchor. | Replay reconstructs current node from contiguous records; real files detect checksum/truncation/schema/gap/symlink faults; no checkpoint, index, compaction, GC, repair workflow, or freshness anchor is present. | Implement and prove checkpoint/index/compaction machines against authoritative replay; enumerate crash cuts; show all protected roots and duplicate history survive; make corruption enter explicit repair state; qualify anchor behavior and pass `SCN-004/005/006/016`. | Store-file refinement; retention/transfer dependency graph; D06/D13/D14; platform anchor and media-loss model. | **Assigned** checkpoint and derived index artifacts are certified in isolation and await integration; physical persistence, compaction and freshness remain open. |
| **Platform, rollback, and environmental qualification** — `FLR-001..003`; `HST-003/004`; `STO-003..008`; `SCN-003/006/015` | Establish the supported OS/filesystem/device profile for barriers, namespace durability, write isolation, locking, error identity, media corruption, backup freshness, and rollback anchors. State exactly which facts remain assumptions. | macOS development adapter has barriers, locking, allocation frontier, injected process/file failures, and recovery tests. Specs explicitly say this is not power-loss or platform qualification; whole-store replacement by an older valid image is undetected without an anchor. | Publish one selected qualification profile (D14), fault-injection/power-loss evidence with OS/filesystem/device and write-unit scope, rollback-anchor design/tests, and a trust-boundary statement. Mechanized theorems remain conditional on these facts; no environmental test is relabeled as ACL2 proof. | `PRF-007/014`; store adapter correspondence; D14; hardware/filesystem access; external freshness service/anchor. | **Unassigned/high impact**. Current adapter tests are **integration evidence**, not qualification. |
| **Private profile and cryptographic deployment policy** — `SEC-001..004`; `OBJ-007`; `ENC-003`; `SCN-018` | Decide and document trust/metadata boundaries, ciphertext/archive/secret separation, private authorship and equality leakage, group crypto/key custody/rotation/recovery, and disconnection behavior. | No implementation or scenario evidence. D04 selects first-release private scope direction, while crypto suite/key workflow and metadata policy remain open. | Produce a reviewed profile and threat/metadata vectors; specify key lifecycle and failure recovery; demonstrate crypto adapter plus retention/replication interaction. Keep cryptographic integrity assumptions separate from storage durability and authority theorems. | D04/D09; native schema/signature work; retention and replication policies; selected crypto library/version. | **Unassigned**, separate from the current public NNTP/storage wave. |

## Highest-impact follow-on gaps

1. Complete the active BP path: actual durable jobs, attempt intent, bounded inbox,
   article acceptance and recoverable application receipts through a pinned BPA.
   Contact outage, restart, duplicate delivery, expiry and lost receipt are exits.
2. Integrate the certified field/NNTP guard, checkpoint and index artifacts in one
   bounded batch; finish the public article-parser work bound independently.
3. Complete native schema/signature/authority and injection after the concrete
   D01/D09 profile is established; the laboratory BP payload does not select it.
4. Continue physical refinement/accounting, persistent checkpoint publication,
   protected compaction/GC and restore identity. Logical helper proofs alone do
   not close those implementation obligations.
5. Select a platform qualification profile and independent freshness anchor.
   Current results remain conditional on A-DURABILITY, A-WRITE-ISOLATION and A-HOST.

The current article, transfer, wire, NNTP, UTF-8/DP, trace/fault, and canonicality
agents can contribute closure evidence to the assigned rows above. Targeted certification closes only its named mathematical claim and records
the exact source digest and hypotheses. Root records the combined evidence
separately after freezing and certifying the integrated dependency set.

## Closure results in the 54-root checkpoint

These are scoped results, not a claim that an entire matrix row is finished:

- Wire event-yield state preservation and exact consumed-prefix/suffix accounting.
- Wildmat DP/reference equivalence, rightmost precedence, UTF-8 scalar/progress
  safety, and successful-parser output recognition.
- General transfer reserve/add-chunk preservation and byte accounting; complete
  candidate length/octet/retained-byte agreement and missing-range correctness.
- Arbitrary finite file-kernel trace preservation, stable-prefix retention, and
  earlier acknowledgement retention with the explicit ghost-history premise.
- Bounded exhaustive kernel exploration: 211 states and 9,038 edges, with exhausted
  work queue in the declared frontier/record domain.
- Successful exact schema-0 record decoding re-encodes the identical input.
- Live node/file actual-completion gate and full-node replay-extension equality.
- Article successful-output syntax recognition and component bounds.
- All 21 CBOR and 45 record functions guard verified; transfer hot-path costed
  execution corresponds to actual values and has polynomial bounds.
- Forty-seven real-file fault-injection rows; six process-death boundaries with
  lost-success retries; independent cbor2 interoperability in 38 cases.
- Reproduced and repaired host lock/descriptor lifecycle bugs and mutations from
  read-only or closed Store owners.

## Later targeted closure, separate from the historical checkpoint

These results are certified for their named scopes and are not the 54-root
checkpoint; they are included in the subsequent 75-root integration result:

- Arbitrary finite node traces, mixed live/resolution traces, and observed-image
  loading are certified; the composed host-adoption suite passed the integrated run.
- Full selected NNTP command/session and finite-session preservation, including
  effect typing, is certified alongside the existing reader evidence.
- Exact full wildmat matcher work and the public transfer work bound are
  certified for their stated profiles.
- Root's current guard closure adds fifteen guarded books. The cumulative count
  is 533 functions across 15 base books, including the new file/wrapper, transfer and exchange graphs.
- Native schema/signature, receipt and authorized GC, checkpoint/index/
  compaction, physical/platform qualification, rollback freshness, and related
  host adoption remain open.

The [evidence record](../tests/evidence/2026-09-18-assurance.json) attaches the
exact manifests and source set. All real filesystem results remain distinct from
power-loss qualification. The subsequent 75-root integration batch passed and
has its own linked evidence record.

## Next independent implementation batch

After the frozen adapter batch, Sol supplied an executable logical
checkpoint and general checkpoint-plus-suffix equivalence proof (PRF-008),
including consumed allocator gaps. Luna supplied a derived group/number index and
both soundness and range completeness against authoritative article memberships
(PRF-010). Work is isolated until actual certification. No persisted checkpoint
or index schema, compaction, or physical publication guarantee follows yet.
Remaining NNTP and semantic-field guard graphs are assigned.

## Active BP vertical slice

The user's A06 clarification makes BP-backed disconnected exchange current work,
not a post-M5 additional interface. Terra owns a pinned existing BPA experiment,
Sol owns durable workflow/attempt/receipt semantics and trace proofs, and a second
Sol lane owns the actual workflow journal and crash-tested ACL2 bridge. This
activates the previously unassigned scheduler/receipt/storage seams; it does not
claim their implementation or certification is already complete. The
[BP path](../specs/bp-path.md) supplies the first two-node exit and fault cuts.
