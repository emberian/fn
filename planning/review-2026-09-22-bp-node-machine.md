# fn BP node: design review and landing brief (gpt-6, 2026-09-22)

Supplied by ember on 2026-09-22 from a static review by gpt-6 of
`specs/bp-node-machine.md` at `dev` a388826f. Kept verbatim below as the
record the design's revision answers: the design's author revises the spec
against it, and its findings F-A to F-N, its integration order A to E and its
traces BP-R01 to BP-R24 are the contract a phase-2 lane is briefed from.

---

**Review date:** September 22, 2026
**Repository:** `emberian/fn`
**Pinned revision:** `a388826f15c7977082668965e967064b3bf5520f` (`dev` when inspected)
**Primary design:** supplied "The BP node processing machine (T12a)," also merged as `specs/bp-node-machine.md`.
**Predecessor:** supplied `specs/bp-design.md`; its superseded machine sections are historical, not competing current requirements.

## Scope and confidence

This is a static design/code review. I read the supplied documents and the repository's machine, authorization, codec, scheduler, workflow, receiver join, peer-admission, fragment, and native-adapter paths at the pinned revision. I also checked the published protocol documents and their errata pages. I did **not** run ACL2, certify a changed book, build a native image, reproduce a socket failure, or inspect the deployment machines. Proposed tests below are not passing-test claims. In particular, the design's statement that no deployed node has lifecycle records is not independently verified here.

Findings distinguish **existing code**, **contradictions in the proposed design**, and **composition obligations not yet specified**. A design contradiction is not a claim that an unimplemented feature already fails in production.

## Executive decision

Approve the direction: one held-bundle machine, durable-record-authorized effects, independent application obligations, native scheduling policy, and application receipts carried as ordinary bundles. Do not hand the present T12a text to an implementation lane unchanged.

The principal risk is not a missing setter lemma. It is a mismatch between the lifetime of a carrier and the lifetime of the work, observations, and outbound effects associated with it. The machine can preserve its local invariant while losing a receipt handoff, losing the association needed to interpret a delayed report, or becoming unable to make progress. The scheduler has a related boundary problem: its current successful-attempt macrostep supplies a storage-success observation internally.

The recommended unit of integration is a **durable, restartable article-and-receipt round trip**, followed by relay and fragmentation extensions. This does not postpone DTN beyond v0. It changes the order in which the existing v0 commitment is completed.

---

## 1. Answers to the twelve questions

These answer §12 of the T12a document in order.

| # | Decision | Conditions and implementation consequences |
|---|---|---|
| 1 | **Yes: one held-bundle collection and one BP transition authority.** | Do not introduce separate inbound and outbound lifecycle machines. Separate bundle identity, submission identity, forwarding-attempt identity, and ingress provenance inside the contract. They are not interchangeable uses of `origin`. |
| 2 | **Retire kinds 2–4 rather than building a legacy migration for test-only state.** | Verify the operational premise before rollout. Reject old records with a clear unsupported-schema diagnosis; never treat their presence as an empty store or silently reset a directory. Keep historical fixtures/evidence. |
| 3 | **Use the existing peer-row configuration family for now.** | The composing update must preserve unrelated rows. Live route selection uses the current configuration; recovery of an already committed routing decision must not require that its old route still exists. Specify reconfiguration of already forward-pending bundles. |
| 4 | **Reuse the native ACL2 scheduler's policy, but not its current atomic storage-success shortcut.** | `fn-sched-drive-attempt` supplies `:durable` itself. Introduce a real prepare/persist/complete boundary or an explicitly proved refinement from that macrostep. Contact-open/close are currently scheduler inputs, not emitted session-management effects. |
| 5 | **Release the data-carrier ACK after durable BP acceptance, before application acceptance.** | A late capacity refusal must not become a successful ACK. Recovery must redrive subsequent work. The callback must release the ACK explicitly at this boundary rather than waiting for recursive delivery/effect processing to return. |
| 6 | **Implement all four report assertions in v0; default generation off.** | Enable reports explicitly in the lab/operator configuration, with resource policy. Correct the report wire grammar and support timed incoming status items. A report is not a receipt and must not become necessary for eventual work retry. |
| 7 | **Keep proactive fragmentation and reassembly in v0.** | Land a restart-safe family transformation, capacity accounting, and an executable refinement before connecting the reference fragment routines to the native path. They should follow the whole-bundle vertical slice, not precede its receipt/recovery closure. |
| 8 | **One authoritative receive record on the machine path.** | FNBS can replace the separate receive-evidence publication there. Define the evidence retained for original input versus transformed/reassembled images. Keep the interop verbs and their evidence namespace until the replacement actually has its gate. |
| 9 | **Raise the reassembly limit to 65,538.** | Check request/receipt ADU, bundle image, frame, transfer, fragment-count, aggregate memory, and execution-cost limits together. A two-byte constant change does not establish support for every maximum-sized ADU. |
| 10 | **Sequence the new replay proof after the new record schema exists.** | But replay, recovery normalization, and physical persistence cuts must co-land with the behaviors whose ACKs depend on them. "Prove replay later" is not an acceptable receive-path boundary. |
| 11 | **Keep `:resume`.** | Make it a bounded service-loop action. Yield after nonprogress/refusal, retain result correlation, and avoid recursive immediate retries that consume the journal while time or contact conditions have not changed. |
| 12 | **Send application receipts through the BP machine.** | The FNRJ-to-FNBS handoff must be restartable and idempotent. Address the receipt to the original requester; let routing select its next hop. Receipt ADUs need their own delivery branch into the sender workflow/release join. |

The report default is a standards correction: RFC 9171 §5.1 requires generation disabled by default. An explicitly enabled test configuration is different from a binary profile that enables it implicitly.

## 2. What should be preserved

### 2.1 The existing pending-proposal authorization is substantive

`books/bp-node-machine-authorization.lisp`, especially `fn-bpn-proposal-effectsp` and `fn-bpn-pending-authorizedp`, binds a proposed record to its exact success, refusal, and uncertainty effects. For an attempt, this includes the peer, route, job key, and wire image. That is a useful foundation, not just a type predicate.

Retain this structure while widening the machine. For new mutable forwarding images, the corresponding authorization must bind the actual image and the observations/configuration used to construct it. Do not weaken it to "the output is a typed `:cl-send`."

### 2.2 The article obligation should remain independent of the carrier

The architecture's central question, what has a node promised, and what evidence permits release, is the right organizing principle. A discarded or expired bundle must not mean that an article's archive or forwarding obligation disappeared. Conversely, an outstanding work does not require keeping every old carrier's complete bytes forever.

The missing middle is a compact, durable binding between a work attempt and its transport identities, plus a restartable way to regenerate required application effects.

### 2.3 Logical reference models and efficient implementations may differ

The fragment book explicitly describes itself as a specification to refine rather than a production reassembler. The project's checked/fast correspondence pattern is appropriate here. Preserve the simple model for reasoning; prove an executable implementation equivalent, including conflict and gap diagnostics.

---

## 3. Findings that change the implementation contract

### F-A. Native scheduler adoption currently crosses a fabricated persistence boundary

**Classification:** existing reference-model behavior; blocker to the proposed native integration.

**Source:** `books/scheduler.lisp`, `fn-sched-drive-attempt`:

```lisp
(let* ((r1 (fn-bp-step wf (fn-bp-attempt-prepare-event
                           txid 0 work-id attempt-id)))
       (s1 (fn-bp-result-state r1)))
  (fn-bp-step s1 (fn-bp-storage-complete-event txid 0 :durable)))
```

This is a successful-storage macrostep. It is not a physical storage observation. `fn-sched-tick-step` can therefore return the workflow's `:submit` without this function having asked the native publisher to persist the FNWF attempt.

That may be perfectly appropriate for a scheduler model with a successful-storage environment. It is not sufficient for the statement that native adoption makes every scheduler keystone apply verbatim to the service.

**Repair:** preserve selection, aging, and charging policy, but split execution into selection/attempt preparation, actual journal publication, and a matching completion event. Charge the scheduler at the specified real completion boundary. Alternatively, prove that a concrete two-phase runner refines the existing successful macrostep on its successful branch, and separately specify refusal and uncertainty.

`fn-sched-step` also takes `:contact-open` and `:contact-close` as inputs and returns no effects for them. The proposed relay of "the scheduler's open/close effects" needs an actual service-level definition.

**Gate:** fail or interrupt FNWF publication after selection but before its success observation. There must be no BP transmission attributable to a durable application attempt that never existed.

### F-B. Discard removes the information needed for delayed status reports

**Classification:** direct contradiction between T12a's receive/discard rules and its relay-expiry gate.

**Sources:** T12a §4.1 step 4, §4.4 step 2, §9.6; `books/bp-workflow.lisp`, `fn-bp-retryable-statusp`.

A concrete proposed trace:

```text
home: author B for work W
home: forward B to relay successfully
home: discard B on the next sweep
relay: B expires before the destination contact
relay: send deletion report naming B
home: look for B among held local-origin bundles -> absent
home: emit receive-observed, but no transport event for W
```

The document's own relay-expiry gate expects this report to make the home workflow retry. Its lookup cannot do so after normal discard. The current workflow does not automatically retry a `:forwarded` attempt.

**Repair:** retain a durable carrier-to-attempt binding until the work's lifecycle no longer needs it. This can live with the application attempt or as compact metadata; it need not retain payload bytes or create a second forwarding machine. Specify correlation for fragment reports as well as whole bundles.

More importantly, implement an explicit receipt-loss policy that can retry without receiving a report. The existing `fn-bp-request-retry`/`:retry-request` path is a useful starting point.

**Gate:** exercise the exact trace above after the home carrier is physically absent from the live bundle collection. Then repeat with the deletion report dropped entirely. The second run should demonstrate the configured retry policy, not a falsely claimed report-driven transition.

### F-C. The application receipt handoff is not yet a recoverable outbox

**Classification:** composition obligation, made critical by moving the ACK earlier.

**Sources:** T12a §9.2; `host/native/bp-app.lisp`, `fnn-bpapp-accept-locked`, `fnn-bpapp-pause-after-decision`, `fnn-bpapp-deliver`.

The existing host explicitly has a crash cut after a durable application receipt decision and before a receipt bundle is authored/offered. The new design moves receipt transmission into `:transmit`, but merely moving the call does not close this cut.

If the incoming carrier has been acknowledged, and delivery completion removes its final constraint, a crash before the receipt enters FNBS can leave a committed article and receipt fact without a queued return carrier. An upstream node may have no reason to retransmit that carrier.

**Repair:** a committed FNRJ receipt must remain discoverable as owed output until the durable handoff condition is satisfied. Recovery must enumerate/redrive it. Enqueue must use a stable operation identity. Define what happens when a receipt carrier later expires: either the receipt's delivery policy reauthors it, or a requester retry regenerates it from the committed receipt fact. Do not rely on a one-shot callback.

Delivery routing must distinguish request ADUs, receipt ADUs, and administrative records. The request receiver join is not itself the receipt-consumption/release path.

**Gate:** kill after application Store commit, after receipt decision, before FNBS enqueue, after FNBS enqueue but before local completion, and after the receipt carrier is discarded. Verify one accepted article and preservation of the return obligation, allowing duplicate carrier transmissions.

### F-D. "Normal callback return" is not the new ACK contract

**Classification:** existing host behavior conflicting with the proposed boundary.

**Sources:** `host/native/tcpcl.lisp`, `fnn-tcl-act`; T12a §3.2, §9.1.

Currently `fnn-tcl-act` flushes the held final ACK after the delivery callback returns normally. The T12a effect table also says `:receive-refused` returns normally after a completed transfer, including a capacity refusal.

A START capacity query is advisory without a reservation: another transfer may consume capacity, and a transfer may lack the optional length information. If the final receive decision refuses capacity but a success ACK leaves, the sender can mark forwarding complete without a durable received copy.

**Repair:** make the callback's disposition explicit: stored, durable duplicate, administrative observation, refusal, or uncertainty. Do not map all normal returns to accepted data. RFC 9174 §5.2.4 permits refusal after inspecting received bundle data; the native adapter must connect that disposition to the session machine before releasing a final success ACK.

Also, emitting `:receive-stored` before another `:persist` in a list does not itself release a held socket ACK. The host must perform that release at the intended point, and queue later application work rather than recursively completing it first.

**Gate:** two transfers that both pass the initial capacity query but cannot both fit at END; also a transfer without the length extension. Exactly the durably admitted transfers receive the strong data-carrier success acknowledgment.

### F-E. Same bundle identity does not imply the same hop-local wire image

**Classification:** internal contradiction in the new design.

**Sources:** T12a §4.1 step 3 and §4.3 step 3.

Reception accepts a duplicate only when its wire bytes are identical. Forwarding intentionally updates Bundle Age, Previous Node, and Hop Count while retaining the bundle's identity.

A retry after a lost ACK can therefore arrive with the same identity and a different legitimate forwarding image, and be classified as `:identity-conflict`.

**Repair:** explicitly define duplicate equivalence for the supported profile. Separate immutable content/identity from mutable forwarding metadata and any security-block rules. Do not simply accept every same-ID input: genuinely conflicting content still needs a conflict result and evidence policy.

Local submission idempotence has a related issue. The current enqueue function reconstructs the bundle from the new observation before comparing it to an existing job. With a changed wall-clock creation timestamp, retrying an otherwise identical operation need not reproduce the original bundle. Reuse the persisted submission result rather than reauthoring from the retry's current clock.

**Gate:** lost ACK followed by a retry with increased age; exact retransmission; same ID with changed payload; repeated submission under changed observation; redrive after the live carrier was discarded.

### F-F. Reassembly currently leaves fragments retained, and can require a sixty-fifth slot

**Classification:** direct design contradiction and capacity gap.

**Sources:** T12a §3.3 kinds 5–8, §4.2, §7.1.

Kind 5 gives a fragment `:dispatch-pending`. `:await-fragments` adds `:reassembly-pending`. Kind 7 removes only the latter from consumed fragments. Therefore the old fragments still have `:dispatch-pending` and are not discardable under the definition of `fn-bpn-retainedp`.

In addition, kind 7 appends a reassembled entry while retaining all fragment entries. At `max-held = 64`, a valid assembly of 64 fragments cannot append a sixty-fifth entry while preserving the state bound.

**Repair:** give the transformation a complete before/after resource equation. Prefer an atomic logical replacement of the consumed fragment family by the reassembled entry, retaining the fragment records in the journal as provenance. Another admissible design reserves sufficient transformation headroom before acknowledging the last fragment. Whichever approach is chosen, explicitly finish the fragments' dispatch obligation.

Exclude deleted/conflicting fragments from future active assembly input, and preserve an unambiguous origin/admission context for the resulting ADU.

**Gate:** full capacity with a complete cover; repeated reassembly after restart; a conflict followed by a later valid fragment; gap completion; exact live-set and resource changes after success.

### F-G. Proactive fragmentation is a multi-record protocol, not just a call to `cut`

**Classification:** missing transition/recovery contract.

**Sources:** T12a §3.3 kind 5, §4.3, §7.2.

The draft says newly stored children are already forward-pending, but kind 5 permits only dispatch-pending new entries. It also stores children one at a time and deletes the parent after the last, without specifying durable plan progress or a child-family identifier.

Copying the parent's `origin` to every child does not by itself define which child a duplicate local submission names, when a work attempt is considered forwarded, or how partial family creation resumes. A fragment successfully forwarded is not evidence that all its siblings were forwarded.

**Repair:** define a deterministic, durable family plan or an atomic replacement transaction. Bind parent identity, child identities, boundaries, total ADU length, origin lineage, and completion policy. Continue ordinary child dispatch through the existing machine; do not introduce a host-side fragmentation controller.

MRU checks must concern the actual encoded outgoing fragment image after mutable blocks and encoding-length changes. A fixed overhead constant needs a proved bound over the allowed extension-block profile; tiny MRUs can be impossible, not merely require more cuts.

**Gate:** crash after every child record; restart with a proper prefix of children; capacity exhausted mid-plan; forwarding some children before a later crash; MRUs around encoding-length boundaries and the minimum feasible image size.

### F-H. The fragment reference implementation is not suitable for direct native execution

**Classification:** existing code cost; integration blocker under the proposed direct call.

**Sources:** `books/bp-fragment.lisp`, header, `fn-bpf-coversp`, `fn-bpf-cell-of`, `fn-bpf-canvas`, `fn-bpf-extent`.

For each output position, `fn-bpf-coversp` computes the length of a fragment's list of bytes. `fn-bpf-cell-of` then uses `nth` to reach the relevant byte. Even a single length-L fragment consequently induces quadratic list traversal under ordinary list execution. The cutting helper also repeatedly uses `nth` from the original payload.

This is a source-level complexity finding, not a measured native runtime. The file's own header says production should refine the specification instead of executing it directly. The lane brief currently permits changing that file only to raise the length bound, yet proposes wiring its reference reassembler into the machine.

**Repair:** broaden the lane to allow a proved executable refinement. A cursor-based cutter avoids repeated prefix traversal. A bounded array/occupancy pass or a properly maintained interval/cursor representation can reassemble in time tied to output length plus supplied fragment bytes, rather than repeated full-list traversal. Preserve all four outcomes, conflict precedence, and the least conflict/gap positions.

Also audit the entire checked/fast host path. Replacing `fn-bpn-step` alone does not remove repeated checks from `fn-bpn-existing-sequence` or any facade/publisher that still evaluates a whole-state recognizer.

**Gate:** scale payload and held-set sizes independently. Measure allocations, processing cost, and latency for success, gaps, overlap, and conflict on the actual native image; prove the fast/reference equation separately.

### F-I. Replay must not re-decide history using today's routes

**Classification:** direct conflict between persistence and configuration rules.

**Sources:** T12a §2.4 and §3.3.

The routing table is deliberately not persisted in FNBS. Yet record applicability is specified to require that a dispatch disposition names a route the table currently holds. A valid historical dispatch can then fail recovery after a configuration change removes that route.

**Repair:** separate live authorization from historical record applicability. A historical record must contain enough evidence to replay its committed semantic decision without consulting transient session state or a later routing table. Validate current routes when selecting new actions. Define how a route change invalidates or refreshes the next hop of already forward-pending bundles.

**Gate:** commit a dispatch through peer A, change configuration to peer B, restart, and preserve the held work without treating the journal as corrupt. Then demonstrate the specified new forwarding policy.

### F-J. K6 needs a provenance and exact-binding contract, not just a peer lookup

**Classification:** missing join invariant; risk of weakening the existing receiver.

**Sources:** T12a §2.3, §6, §9.2; `books/bp-native-app.lisp`, `fn-bpaj-record-lookup`, `fn-bpaj-dispatch`; `books/peer-inbound.lisp`, `fn-peer-decide-transfer`; `host/native/bp-app.lisp`.

The peer decision's `:have` means history contains that Message-ID. The receiver lookup requires a unique, accepted Store record with matching payload and content subject, and the dispatcher additionally protects owner generation and planned transaction identity. These are different statements. `:have` cannot automatically authorize a receipt for this request.

The planned `origin` also conflates different notions:

```text
(:cl xfer-id peer-eid)       ; no session identity
(:reassembled adu-key)      ; no ingress peer/admission context
(:local work attempt gen)  ; no remote ingress peer at all
```

K6 later expects a peer derived from that origin. Its behavior for reassembled input and local self-delivery is not defined. The proposed delivery effect does not explicitly carry the Previous Node information cited by the loop-check contract.

**Repair:** preserve separately the bundle source/destination, admitted peer principal, session/transfer identity, configuration generation, and fragment lineage. Define which of those carries authority. An announced unauthenticated peer EID is not a principal merely because it is in a record.

Use `:want` to enter the shared transit submission path. On `:have`, still require the exact accepted-record binding needed by the receipt join. Keep stale-generation, wrong-transaction, conflict, and busy cases. Write the submit-soundness theorem before asserting a full iff; completeness needs a composed coherence invariant connecting node, Store, joined receiver state, and configuration.

For return receipts, the current host uses the original bundle source. Preserve that property when replacing the connection-local send with routed enqueue.

**Gate:** same Message-ID/different content, conflicting accepted records, stale generation, missing duplicate record, reassembled request, self-delivery, multi-hop receipt return, and an unconfigured or unauthenticated session identity.

### F-K. The proposed theorem text contains vacuous and false cases

**Classification:** specification defects, not failed ACL2 runs.

1. **Record patterns omit their inner token.** Kind 11 is `(:deleted token id reason)`, but T2/T3 match `(:deleted id reason)` inside the persist effect. Kind 7 and kind 12 have the corresponding mismatch. An implication with an impossible antecedent can certify without saying anything about the real transition.
2. **T2's hypotheses include local fragments.** After fixing the record shape, a conflicting local fragment may still be dispatch-pending when the design deletes it as `:block-unintelligible`. The proposed "only expiry" conclusion is false for that case. Either restrict the subject to deliverable whole bundles or enumerate the allowed fragment dispositions.
3. **T5 reverses the work lookup in its conclusion.** The current API is `(fn-bp-find-work work-id works)`. The draft supplies the result state and work ID in the wrong places. It also needs the `fn-bp-state-works` projection.
4. **T6 compares unnormalized replay to resumed live state.** End a trace immediately after a durable attempt record. Raw replay has that attempt; `resume-held` removes it. Normalize both sides consistently, or prove a raw durable-state equality and a separate recovery theorem.
5. **The administrative exclusion is not closed under local authoring.** Reception special-cases local administrative input, but generic dispatch sends any whole local-destination bundle to the application. A locally authored status report addressed to this node needs the administrative path too.

These are reasons to repair the literal contract before a proof lane uses it as its brief. They are not reasons to abandon the proof plan.

**Repair:** use record constructors/selectors in theorem statements. For each implication, add a positive reachable trace that asserts the complete antecedent and the actual emitted record, in addition to its conclusion. This specifically detects shape-vacuity.

Do not require a counterexample for every syntactic hypothesis unconditionally. Redundant hypotheses have none; they should be removed. Deliberately corrupted states can test an invariant's necessity, but are not reachable from a correct initial state under the invariant-preserving transition system. Keep those two classes of witness distinct.

### F-L. A clock sweep alone does not protect delivery/forwarding boundaries

**Classification:** gap in the new transition contract.

**Sources:** T12a §4.1–§4.4; `books/bp-node.lisp`, `fn-bpn-receive`, `fn-bpn-forward-decision`.

The old receive/forward helpers explicitly consult expiry. The new dispatch and start-one algorithms do not. They can perform work before the next separate sweep even when a current observation would classify the bundle as expired.

**Repair:** define a shared progress boundary that processes decidable expiry before a delivery/forwarding action, or carry the appropriate observation through each action. An uncertain clock need not prevent durable reception. The theorem should constrain the evidence authorizing expiry, not unnecessarily insist that the outer event tag is always `:clock`.

Observe also that the proposed delivery-result vocabulary lacks the current join's `:busy` outcome. A transient busy/deferred receiver should not be silently mapped to permanent application refusal.

**Gate:** deliver and forward with an already-expired observation before any periodic sweep; uncertainty that later becomes decidable; busy delivery followed by recovery and successful admission.

### F-M. The finite journal budget is distinct from live-bundle capacity

**Classification:** existing code limit and misleading proposed operational inference.

**Sources:** `books/bp-node-machine.lisp`, `fn-bpn-propose`; `books/bp-node-machine-codec.lisp`, namespace bounds; T12a §3.3, §8.

The 4,096-record namespace survives discard. Removing the sixty-fifth-bundle failure does not make the lifecycle indefinitely reusable. At five records per simple lifecycle, the illustrative ceiling is about 819 lifecycles; attempts, reports, fragments, and other records consume the same budget.

At the pinned revision, `fn-bpn-propose` returns its refusal with unchanged state on record-budget exhaustion. It does not set the fence as the design's prose claims.

A bundle's lifetime is not a numerical bound on retries: nothing in the supplied event model requires time to advance between `:resume` events, and repeated failed attempts each spend journal records. Moreover, selecting by the smallest *last mutation token* is not FIFO by arrival.

**Repair:** distinguish live slots, live bytes, staged/transformation space, historical metadata, and remaining journal authority. Budget terminal/cleanup work rather than admitting a carrier with no remaining path to dispatch or retire it. Define explicit nonprogress retry policy. Store an immutable arrival order if FIFO is the intended theorem.

The current v0 can be explicitly bounded, but broad continuous agent use needs a narrow checkpoint/rollover story. This is not an argument to import all v1 object reclamation into T12a.

**Gate:** exceed one journal lifetime, separately from holding 64 bundles; exercise admission near the last token, repeated No Resources refusals without clock progress, and cleanup/control traffic under pressure.

### F-N. The host runner needs a reliable event queue and operation correlation

**Classification:** integration obligation created by persistent sessions and multiple producers.

**Sources:** T12a §3, §4.6, §9; current `fn-bpn-contact-step`, `fnn-bps-drive-effects`, `fnn-tcl-session`.

One pending proposal is a reasonable simplification only if other events are queued/retried rather than dropped. The current contact step ignores events while a proposal is pending. In the new design, network callbacks, timer events, configuration changes, report generation, and publication completions can all contend for that boundary.

Chaining a dispatch proposal inside `:persist-result` can also leave the machine pending before earlier returned effects are executed. If an earlier `:report-due` immediately re-enters the machine with `:author-report`, it collides with that pending dispatch.

Finally, a forwarding attempt represented only as `(:attempting peer)` and completed by `(id peer outcome)` does not distinguish an old session's result from a newer attempt for the same bundle/peer.

**Repair:** define the serialized service reducer and its bounded inbox. Queue follow-on semantic work; execute exactly identified I/O operations; correlate completion with an attempt token and session/incarnation as required. Specify whether there can be more than one session per peer. A single Boolean contact must not be cleared by one session while another permitted session is still active.

**Gate:** late outcome from an earlier session, contact close during publication, report generation during chained dispatch publication, two sessions for one peer, and restart while external completions remain outstanding.

---

## 4. Protocol/profile corrections and interoperability scope

The report grammar in T12a §7.4 needs correction. Each assertion is an array containing a Boolean and optionally a time, not a bare Boolean. Fragment offset and payload length are separate report fields, not one nested pair. The subject's flag governs reported times; fn's choice not to request them on its own bundles does not decide what an incoming subject requested. Report generation under the stated conditions is generally SHOULD, not the draft's blanket MAY characterization. [RFC 9171 §6.1.1 and processing sections.]

Use this structural example as an implementation target, not as a captured interop vector:

```text
[1, [ [[true], [false], [false], [false]], reason, source, [time, sequence] ]]
```

The old design explicitly includes handling of unprocessable extension-block flags. The new receive algorithm lists decode and primary-flag validation but not that processing pass. Do not equate `fn-bpb-bundlep` with complete semantic validation: the current bundle recognizer establishes structural block/primary/payload properties. Add explicit disposition for unsupported blocks, including the supported security profile, before claiming the stronger delivery property.

Route locally authored administrative bundles through the administrative element as well as received ones. RFC 9713 additionally clarifies ignoring malformed/unsupported administrative ADUs without redefining the containing bundle's delivery outcome.

The current errata/status check also matters for the interop matrix, without expanding the first vertical slice:

- RFC 9171 erratum 8043 is verified and clarifies zeroing the CRC value bytes, not its CBOR byte-string header. Independent CRC-bearing vectors should test this.
- Fragmentation-related errata 8376 and 8377 are held for document update, not adopted replacement normative text. Do not silently treat proposed text as the standard or claim general fragmentation/BPSec composition from payload inversion alone.
- RFC 9758 updates `ipn` representations; the existing dtn-focused gate is not evidence for every current `ipn` encoding.
- TCPCL erratum 8770 was reported in February 2026 and remained reported in the consulted listing. It concerns cancellation within a session; it is not an adopted requirement on this implementation.

The supplied predecessor already says its foreign bundle vector has no CRC. A round trip against that vector cannot answer the CRC interoperability question.

## 5. The proof stack to target

The following are proposed contracts, not certified events.

### 5.1 Local semantic validity and effect authorization

The invariant should connect each held identifier to its primary/payload identity, wire to bundle encoding, lifecycle state to allowed constraints, and each pending proposal to exactly the effects its durable record authorizes. Include lineage, submission-ticket, and attempt-result relationships rather than merely their field types.

### 5.2 Raw replay and recovery normalization are different theorems

A useful shape is:

```text
durable_projection(live_execution)
    = durable_projection(replay(valid_confirmed_journal))

recovered_state
    = reanchor(clear_external_inflight(replay(observed_valid_journal)), observation)
```

The two journals need not be identical at a crash cut: a record may have reached the authoritative directory before the process observed its `:durable` result. Model that cut explicitly, including the allowed observed-file outcomes. Do not hide it by defining the journal solely as records acknowledged back into the live machine.

Current configuration and session availability are installed after/reconciled with recovery, not used to invalidate historical decisions.

### 5.3 Recoverable effects, not merely replayable records

For every durable state with owed work, recovery must reconstruct an enabled continuation or an explicit retained blocked state with a specified wakeup. This includes dispatch, deferred delivery, interrupted forwarding, partial fragmentation, committed receipt publication, and receipt consumption/release.

A journal can replay perfectly and still fail this property.

### 5.4 The Store/receiver/workflow composition

A receiver's acceptance/duplicate receipt must bind the exact committed Store record and policy context. At the sender, only the authorized durable receipt/release path may remove the forwarding pin, while the independent archive pin remains. Do not prove this against a shadow workflow node image while the native owner's Store remains unchanged.

The current `host/bp-release-owner-host.lisp` calls `fn-bprl-replay-journal`, while the inspected `books/bp-release.lisp` defines record application but not that replay function. The supplied design identifies an unlanded branch containing it. This is an image-closure integration finding to resolve with the actual definitions and a clean build; this review did not execute the build or exhaustively search every possible image-loaded definition.

### 5.5 Conditional progress and resource assumptions

State preservation and "reports cannot release a pin" are safety properties. The project also needs an explicit conditional progress statement: admitted outstanding work does not remain permanently stranded when its configured contact, resource, persistence, recovery, and retry-policy assumptions keep becoming satisfiable.

Make those assumptions visible. Arbitrary outages, indefinitely uncertain time, exhausted journal space, and an adversarial peer do not become progress guarantees because a FIFO selector exists. Report observations must not disable the independent receipt-loss recovery policy.

## 6. Recommended integration order

Keep the project's decisions: DTN in v0, native signatures in v0 on their own path, LTP after DTN, one-box peering tests first, five overall lanes, and convergence after two or three batches. Do not allocate every lane to simultaneous edits of the BP record algebra.

### Integration A: Correct contracts and close the whole-bundle round trip

Joint responsibility of T12a/T12b/T12d interfaces, with one owner for each changed base book.

Correct record shapes, identities, effect completion, the scheduler storage boundary, and receiver binding. Build two native processes exchanging one ordinary article and a return application receipt through FNBS. Verify the actual owner Store and pins, not just workflow/log projections. Land the local preservation/authorization and relevant replay equations with the behavior.

### Integration B: Relay, delayed/lost observations, and persistent sessions

Add the service runner, real contact/session mapping, stable carrier correlation, explicit receipt-loss retry, and multi-hop receipt routing. Run the three-process nonoverlapping-contact gate, including the sender discarding its first carrier before the relay expires it. Repeat without any status report.

### Integration C: Fragment transformations and executable correspondence

First certify the logical fragment lemmas and fast/reference equality. Then add capacity-accounted, restart-safe fragmentation/reassembly to the same machine. Do not connect the quadratic reference reassembler first and call optimization a later optional task.

### Integration D: Reports and independent wire evidence

Enable reports explicitly for these tests. Add the corrected report codec, administrative demultiplexing, unsupported-block cases, and independent CRC-bearing and timed-status vectors. Keep each conformance claim scoped to its actual supported profile and peer/feature row.

### Integration E: Exhaustion and sustained-operation envelope

Exercise record-budget exhaustion separately from live queue saturation. Establish retry throttling, control/cleanup headroom, and a documented checkpoint/rollover or bounded-run limit. Keep broad deployment claims behind this operating-envelope result.

The existing phase-2/phase-3 split can remain an organizational label, but changed semantics and their safety/replay obligations should not be separated into a long proof-after-implementation interval.

## 7. Acceptance traces to add to the brief

All are **proposed**, not run in this review.

| ID | Trace | Required observation |
|---|---|---|
| BP-R01 | Scheduler selects work; FNWF persistence refuses/has uncertain outcome | No unearned durable-attempt transmission; refusal and uncertainty remain distinct |
| BP-R02 | FNBS receive record becomes durable; kill before dispatch | Recovery resumes the owed dispatch without needing a second arrival |
| BP-R03 | Application Store commits; kill before receipt decision | Replay binds the exact accepted record, without duplicate article acceptance |
| BP-R04 | Receipt decision commits; kill before FNBS enqueue | Receipt output is rediscovered and enqueued |
| BP-R05 | FNBS receipt enqueue commits; kill before handoff completion | Stable idempotent redrive; no lost receipt obligation |
| BP-R06 | Final ACK lost; sender retransmits with changed Bundle Age | Valid duplicate handling, not identity-conflict |
| BP-R07 | Same bundle ID arrives with changed payload | Explicit conflict; no replacement or false duplicate receipt |
| BP-R08 | Sender discards carrier; relay expires it; delayed report returns | Work correlation survives carrier discard |
| BP-R09 | Same relay expiry, but report is dropped | Configured application retry still progresses |
| BP-R10 | Two transfers pass START capacity check; only one fits at END | Only durable acceptance receives the strong data-carrier ACK |
| BP-R11 | Complete fragment cover at held-entry capacity | Reassembly has a valid resource transition; no sixty-fifth-slot deadlock |
| BP-R12 | Crash after each prefix of fragment children | Deterministic family recovery; no premature parent retirement |
| BP-R13 | Conflict, gap, agreeing overlap, and later valid completion | Correct reference outcomes and no poisoned retired-fragment input |
| BP-R14 | Change/remove a route; restart historical journal | History replays without demanding the old route still exist |
| BP-R15 | Previous session result arrives during a newer attempt | Stale outcome cannot complete/cancel the wrong attempt |
| BP-R16 | Whole bundle already expired before a progress action | No application/network action bypasses the selected expiry policy |
| BP-R17 | Receiver returns busy, then becomes available | Deferred delivery remains owed and later completes |
| BP-R18 | Report addressed locally, including locally authored report | Administrative processing, not request-article admission |
| BP-R19 | Same Message-ID with different content; stale owner/tx identity | No unearned accepted/duplicate application receipt |
| BP-R20 | Receipt crosses a relay in reverse direction | Original requester is destination; relay is only next hop |
| BP-R21 | More than 4,096 lifecycle records; near-last-token admission | Explicit resource behavior, cleanup headroom, no silent frozen accepted work |
| BP-R22 | Payload/fragment/held-set scaling on native image | Measured execution and memory envelope; reference/fast agreement separately proved |
| BP-R23 | Independent CRC and timed-status vectors | Cross-implementation codec evidence beyond self-round-trip |
| BP-R24 | Repeated hostile or nonprogress refusal with no time advance | Bounded service work per turn and explicit retry yield/backoff |

For the proof "teeth," each positive trace should first assert that the theorem's antecedent actually holds for the real constructor-produced event/record. Then check the conclusion. This avoids counting an unreachable, misspelled record shape as evidence.

## 8. Suggested handoff language

> Approve the one-held-list BP architecture and keep DTN in v0. Revise the T12a contract before implementation: preserve durable work/carrier correlation after payload discard; give FNRJ receipts a restartable FNBS handoff; replace the scheduler's internally supplied `:durable` with a real persistence boundary; correct the theorem record shapes and recovery normalization; define a capacity-accounted, restartable fragment-family transformation and its fast refinement; and preserve exact Store/receiver binding and ingress provenance through K6. Keep `:resume`, but run it through a bounded serialized service loop with attempt/session correlation. Status reports are implemented but explicitly enabled, not on by default. Land the two-node article/receipt/release vertical slice with its crash cuts before relay and fragmentation widen it. The three-node gate must pass after sender carrier discard and also with status reports lost. A sixty-fifth accepted bundle is not the journal-longevity gate.

## Source ledger

Repository references below are all to `a388826f15c7977082668965e967064b3bf5520f`. Function names are the most reliable navigation anchors.

- Supplied/new design: `specs/bp-node-machine.md`, especially §§2–9 and §12.
- Supplied/predecessor design: `specs/bp-design.md`, current status, interoperability and security sections; superseded sections are treated as historical.
- Architecture and project decisions: `docs/architecture.md`; `planning/plan-2026-09-22-trajectory.md` §0; `AGENTS.md`.
- BP machine: `books/bp-node-machine.lisp`: `fn-bpn-enqueue-step`, `fn-bpn-propose`, `fn-bpn-contact-step`, `fn-bpn-persist-result-step`, `fn-bpn-replay-records`, `fn-bpn-restart-step`, `fn-bpn-step`.
- Effect authorization: `books/bp-node-machine-authorization.lisp`: `fn-bpn-proposal-effectsp`, `fn-bpn-pending-authorizedp`.
- Persistence codec: `books/bp-node-machine-codec.lisp`: record/namespace limits, recovery, record encoding/decoding.
- Node helpers: `books/bp-node.lisp`: `fn-bpn-anchor-of`, `fn-bpn-receive`, `fn-bpn-forward-decision`.
- Bundle structure: `books/bp-bundle.lisp`: `fn-bpb-splitp`, bundle record, decoder/encoder.
- Fragmentation: `books/bp-fragment.lisp`: header, `fn-bpf-inputsp`, `fn-bpf-coversp`, `fn-bpf-cell-of`, `fn-bpf-canvas`, `fn-bpf-reassemble`, `fn-bpf-extent`, `fn-bpf-fragment`.
- Scheduler: `books/scheduler.lisp`: `fn-sched-drive-attempt`, `fn-sched-tick-step`, `fn-sched-step`.
- Workflow: `books/bp-workflow.lisp`: retry predicates, `fn-bp-find-work`, transport ranks/observation, `fn-bp-request-retry`, restart.
- Receiver join: `books/bp-native-app.lisp`: `fn-bpaj-record-matches-requestp`, `fn-bpaj-record-lookup`, `fn-bpaj-dispatch`.
- Transit decision: `books/peer-inbound.lisp`: `fn-peer-decide-transfer`, `fn-peer-injection-arguments`.
- Native service: `host/native/bp-service.lisp`: `fnn-bps-step`, publication, synchronous send, effect driver.
- TCPCL host: `host/native/tcpcl.lisp`: `fnn-tcl-act`, held ACK flush/drop, outcome handling, session loop.
- Application host: `host/native/bp-app.lisp`: locked receiver/Store join, pause-after-decision cut, receipt authoring and destination.
- Release seam: `host/bp-release-owner-host.lisp`; `books/bp-release.lisp`.
- Frame field limits: `books/frame-fields.lisp`.
- External primary references: RFC 9171 §§5.1, 5.5–5.11, 6.1.1; RFC 9174 §5.2.3–5.2.4; RFC 9713 §2; RFC 9758; RFC Editor errata listings for RFCs 9171 and 9174, inspected September 22, 2026.
